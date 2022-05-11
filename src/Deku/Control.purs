module Bolson.Control
  ( flatten
  , globalPortal
  , portal
  , fix
  , switcher
  ) where

import Prelude

import Bolson.Core (Child(..), DynamicChildren(..), Element(..), Entity(..), EventfulElement(..), FixedChildren(..), PSR)
import Control.Alt ((<|>))
import Control.Lazy as Lazy
import Control.Monad.ST.Class (class MonadST, liftST)
import Control.Monad.ST.Internal as Ref
import Data.FastVect.FastVect (toArray, Vect)
import Data.Filterable (filter)
import Data.Foldable (foldl, for_, oneOf, oneOfMap, traverse_)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Maybe (Maybe(..))
import Data.Tuple (snd)
import Data.Tuple.Nested ((/\))
import FRP.Event (AnEvent, keepLatest, makeEvent, mapAccum, memoize, subscribe)
import FRP.Event.Class (bang)
import Foreign.Object as Object
import Prim.Int (class Compare)
import Prim.Ordering (GT)
import Unsafe.Coerce (unsafeCoerce)

----

newtype MutAr a = MutAr (Array a)

foreign import mutAr :: forall m a. Array a -> m (MutAr a)
foreign import unsafeUpdateMutAr :: forall m a. Int -> a -> MutAr a -> m Unit
foreign import readAr :: forall m a. MutAr a -> m (Array a)

enteq
  :: forall m obj logic lock0 lock1
   . Entity logic obj m lock0
  -> Entity logic obj m lock1
enteq = unsafeCoerce -- it'd be nice to use proof here...

internalPortal
  :: forall n s m logic obj interpreter lock0 lock1 payload
   . Compare n (-1) GT
  => MonadST s m
  => Boolean
  -> (String -> String)
  -> (logic -> interpreter -> String -> payload)
  -> (interpreter -> m String)
  -> (interpreter -> { id :: String, parent :: String, scope :: String } -> payload)
  -> (obj -> Element interpreter m lock0 payload)
  -> (Element interpreter m lock0 payload -> obj)
  -> (interpreter -> { id :: String, parent :: String, scope :: String } -> payload)
  -> (interpreter -> { id :: String } -> payload)
  -> (Entity logic obj m lock0 -> Entity logic obj m lock0)
  -> Vect n (Entity logic obj m lock0)
  -> ( Vect n (Entity logic obj m lock1)
       -> (Entity logic obj m lock0 -> Entity logic obj m lock1)
       -> Entity logic obj m lock1
     )
  -> Entity logic obj m lock0
internalPortal isGlobal scopeF doLogic ids disconnectElement toElt fromElt giveNewParent deleteFromCache wrapElt toBeam closure = Element' $ fromElt $ Element go
  where
  go psr interpreter = makeEvent \k -> do
    av <- mutAr (map (const "") $ toArray toBeam)
    let
      actualized = oneOf $ mapWithIndex
        ( \ix -> Lazy.fix \f i -> case i of
            Element' beamable -> toElt beamable # \(Element elt) -> elt
              { parent: Nothing
              , scope: scopeF psr.scope
              , raiseId: \id -> unsafeUpdateMutAr ix id av
              }
              interpreter
            _ -> f (wrapElt i)
        )
        (toArray toBeam)
    u0 <- subscribe actualized k
    av2 <- liftST $ Ref.new (pure unit)
    let
      asIds :: Array String -> Vect n String
      asIds = unsafeCoerce
    idz <- asIds <$> readAr av
    let
      -- we never connect or disconnect the referentially opaque node
      -- instead, it is always managed inside a referentially transparent node
      -- that can be properly connected and disconnected
      injectable = map
        ( \id -> Element' $ fromElt $ Element
            \{ parent, scope, raiseId } itp ->
              makeEvent \k2 -> do
                raiseId id
                for_ parent \pt -> k2 (giveNewParent itp { id, parent: pt, scope })
                pure (pure unit)
        )
        idz
      realized = flatten doLogic ids disconnectElement wrapElt toElt fromElt psr interpreter
        ( -- we will likely need some sort of unsafe coerce here...
             enteq ( closure injectable
                ( unsafeCoerce
                    :: Entity logic obj m lock0 -> Entity logic obj m lock1
                )
            )
        )
    u <- subscribe realized k
    void $ liftST $ Ref.write u av2
    -- cancel immediately, as it should be run synchronously
    -- so if this actually does something then we have a problem
    pure do
      u0
      when (not isGlobal) $ for_ (toArray idz) \id -> k
        (deleteFromCache interpreter { id })
      join (liftST $ Ref.read av2)

globalPortal
  :: forall n s m logic obj interpreter lock payload
   . Compare n (-1) GT
  => MonadST s m
  => (logic -> interpreter -> String -> payload)
  -> (interpreter -> m String)
  -> (interpreter -> { id :: String, parent :: String, scope :: String } -> payload)
  -> (obj -> Element interpreter m lock payload)
  -> (Element interpreter m lock payload -> obj)
  -> (interpreter -> { id :: String, parent :: String, scope :: String } -> payload)
  -> (interpreter -> { id :: String } -> payload)
  -> (Entity logic obj m lock -> Entity logic obj m lock)
  -> Vect n (Entity logic obj m lock)
  -> ( Vect n (Entity logic obj m lock)       -> Entity logic obj m lock)
  -> Entity logic obj m lock
globalPortal doLogic ids disconnectElement toElt fromElt giveNewParent deleteFromCache wrapElt toBeam closure = internalPortal true (const "@portal@") doLogic ids disconnectElement toElt fromElt giveNewParent deleteFromCache wrapElt  toBeam (\x _ -> closure x)

portal
  :: forall n s m logic obj interpreter lock payload
   . Compare n (-1) GT
  => MonadST s m
  => (logic -> interpreter -> String -> payload)
  -> (interpreter -> m String)
  -> (interpreter -> { id :: String, parent :: String, scope :: String } -> payload)
  -> (obj -> Element interpreter m lock payload)
  -> (Element interpreter m lock payload -> obj)
  -> (interpreter -> { id :: String, parent :: String, scope :: String } -> payload)
  -> (interpreter -> { id :: String } -> payload)
  -> (Entity logic obj m lock -> Entity logic obj m lock)
  -> Vect n (Entity logic obj m lock)
  -> (forall lock1. Vect n (Entity logic obj m lock1)
       -> (Entity logic obj m lock -> Entity logic obj m lock1)
       -> Entity logic obj m lock1
     )
  -> Entity logic obj m lock
portal doLogic ids disconnectElement toElt fromElt giveNewParent deleteFromCache wrapElt toBeam closure = internalPortal false identity doLogic ids disconnectElement toElt fromElt giveNewParent deleteFromCache wrapElt  toBeam closure

data Stage = Begin | Middle | End

flatten
  :: forall s m obj logic interpreter lock payload
   . Applicative m
  => MonadST s m
  => (logic -> interpreter -> String -> payload)
  -> (interpreter -> m String)
  -> (interpreter -> { id :: String, parent :: String, scope :: String } -> payload)
  -> (Entity logic obj m lock -> Entity logic obj m lock)
  -> (obj -> Element interpreter m lock payload)
  -> (Element interpreter m lock payload -> obj)
  -> PSR m
  -> interpreter
  -> Entity logic obj m lock
  -> AnEvent m payload
flatten
  doLogic
  ids
  disconnectElement
  wrapElt
  toElt
  fromElt
  psr
  interpreter = case _ of
  FixedChildren' (FixedChildren f) -> oneOfMap (flatten doLogic ids disconnectElement wrapElt toElt fromElt psr interpreter) f
  EventfulElement' (EventfulElement e) -> keepLatest
    (map (flatten doLogic ids disconnectElement wrapElt toElt fromElt psr interpreter) e)
  Element' e -> element (toElt e)
  DynamicChildren' (DynamicChildren children) ->
    makeEvent \(k :: payload -> m Unit) -> do
      cancelInner <- liftST $ Ref.new Object.empty
      cancelOuter <-
        -- each child gets its own scope
        subscribe children \inner ->
          do
            -- holds the previous id
            myUnsubId <- ids interpreter
            myUnsub <- liftST $ Ref.new (pure unit)
            eltsUnsubId <- ids interpreter
            eltsUnsub <- liftST $ Ref.new (pure unit)
            myId <- liftST $ Ref.new Nothing
            myImmediateCancellation <- liftST $ Ref.new (pure unit)
            myScope <- ids interpreter
            stageRef <- liftST $ Ref.new Begin
            c0 <- subscribe inner \kid' -> do
              stage <- liftST $ Ref.read stageRef
              case kid', stage of
                Logic logic, Middle -> (liftST $ Ref.read myId) >>= traverse_
                  (k <<< doLogic logic interpreter)
                Remove, Middle -> do
                  void $ liftST $ Ref.write End stageRef
                  let
                    mic =
                      ( (liftST $ Ref.read myId) >>= traverse_ \old ->
                          for_ psr.parent \pnt -> k
                            ( disconnectElement interpreter
                                { id: old, parent: pnt, scope: myScope }
                            )
                      ) *> join (liftST $ Ref.read myUnsub)
                        *> join (liftST $ Ref.read eltsUnsub)
                        *>
                          ( void $ liftST $ Ref.modify
                              (Object.delete myUnsubId)
                              cancelInner
                          )
                        *>
                          ( void $ liftST $ Ref.modify
                              (Object.delete eltsUnsubId)
                              cancelInner
                          )
                  (void $ liftST $ Ref.write mic myImmediateCancellation) *> mic
                Insert kid, Begin -> do
                  -- holds the current id
                  void $ liftST $ Ref.write Middle stageRef
                  c1 <- subscribe
                    ( flatten
                        doLogic
                        ids
                        disconnectElement
                        wrapElt
                        toElt
                        fromElt
                        { parent: psr.parent
                        , scope: myScope
                        , raiseId: \id -> do
                            void $ liftST $ Ref.write (Just id) myId
                        }
                        interpreter
                        -- hack to make sure that kid only ever raises its
                        -- ID once
                        -- if it is anything other than an element we wrap it in one
                        -- otherwise, we'd risk raising many ids to a parent
                        case kid of
                          Element' _ -> kid
                          _ -> wrapElt kid
                    )
                    k
                  void $ liftST $ Ref.modify (Object.insert eltsUnsubId c1)
                    cancelInner
                  void $ liftST $ Ref.write c1 eltsUnsub
                _, _ -> pure unit
            void $ liftST $ Ref.write c0 myUnsub
            void $ liftST $ Ref.modify (Object.insert myUnsubId c0) cancelInner
            join (liftST $ Ref.read myImmediateCancellation)
      pure do
        (liftST $ Ref.read cancelInner) >>= foldl (*>) (pure unit)
        cancelOuter
  where
  element (Element e) = e psr interpreter

fix
  :: forall s m obj logic interpreter lock payload
   . MonadST s m => (logic -> interpreter -> String -> payload)
  -> (interpreter -> m String)
  -> (interpreter -> { id :: String, parent :: String, scope :: String } -> payload)
  -> (Entity logic obj m lock -> Entity logic obj m lock)
  -> (obj -> Element interpreter m lock payload)
  -> (Element interpreter m lock payload -> obj)
  -> (interpreter -> { id :: String, parent :: String, scope :: String } -> payload)
  -> (Entity logic obj m lock -> Entity logic obj m lock)
  -> Entity logic obj m lock
fix
  doLogic
  ids
  disconnectElement
  wrapElt
  toElt
  fromElt
  connectToParent
  f = Element' $ fromElt $ Element go
  where
  go i interpret = makeEvent \k -> do
    av <- liftST $ Ref.new Nothing
    let
      nn = f $ Element' $ fromElt $ Element \ii _ -> makeEvent \k0 -> do
        (liftST $ Ref.read av) >>= case _ of
          Nothing -> pure unit
          -- only do the connection if not silence
          Just r -> for_ ii.parent \p' ->
            when (r /= p') (ii.raiseId r *> k0 (connectToParent interpret { id: r, parent: p', scope: ii.scope }))
        pure (pure unit)
    subscribe
      ( flatten doLogic
          ids
          disconnectElement
          wrapElt
          toElt
          fromElt
          { parent: i.parent
          , scope: i.scope
          , raiseId: \s -> do
              i.raiseId s
              void $ liftST $ Ref.write (Just s) av
          }
          interpret
          nn
      )
      k

switcher
  :: forall s m i logic obj lock
   . MonadST s m
  => (i -> Entity logic obj m lock)
  -> AnEvent m i
  -> Entity logic obj m lock
switcher f event = DynamicChildren' $ DynamicChildren $ keepLatest
  $ memoize (counter event) \cenv -> map
    ( \(p /\ n) -> bang (Insert $ f p) <|>
        ((const Remove) <$> filter (eq (n + 1) <<< snd) cenv)
    )
    cenv
  where
  -- counter :: forall a. AnEvent m a → AnEvent m (a /\ Int)
  counter ev = mapAccum fn ev 0
    where
    fn a b = (b + 1) /\ (a /\ b)
