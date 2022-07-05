module Bolson.Control
  ( flatten
  , globalPortalComplexComplex
  , globalPortalSimpleComplex
  , globalPortalComplexSimple
  , portalComplexComplex
  , portalSimpleComplex
  , portalComplexSimple
  , fixComplexComplex
  , switcher
  ) where

import Prelude

import Bolson.Core (Child(..), DynamicChildren(..), Element(..), Entity(..), EventfulElement(..), FixedChildren(..), PSR, Scope(..))
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

type Neg1 = -1

newtype MutAr a = MutAr (Array a)

foreign import mutAr :: forall m a. Array a -> m (MutAr a)
foreign import unsafeUpdateMutAr :: forall m a. Int -> a -> MutAr a -> m Unit
foreign import readAr :: forall m a. MutAr a -> m (Array a)

type Portal logic specialization interpreter obj1 obj2 m lock payload =
  { giveNewParent ::
      interpreter
      -> { id :: String, parent :: String, scope :: Scope }
      -> specialization
      -> payload
  , wrapElt ::
      Entity logic (obj1 lock payload) m lock
      -> Entity logic (obj1 lock payload) m lock
  , deleteFromCache :: interpreter -> { id :: String } -> payload
  , fromEltO1 :: Element interpreter m lock payload -> obj1 lock payload
  , fromEltO2 :: Element interpreter m lock payload -> obj2 lock payload
  , toElt :: obj1 lock payload -> Element interpreter m lock payload
  }

type PortalComplex logic specialization interpreter obj1 obj2 m lock payload =
  { giveNewParent ::
      interpreter
      -> { id :: String, parent :: String, scope :: Scope }
      -> specialization
      -> payload
  , wrapElt ::
      Entity logic (obj1 lock payload) m lock
      -> Entity logic (obj1 lock payload) m lock
  , deleteFromCache :: interpreter -> { id :: String } -> payload
  , fromEltO1 :: Element interpreter m lock payload -> obj1 lock payload
  , fromEltO2 :: Element interpreter m lock payload -> obj2 lock payload
  , toEltO1 :: obj1 lock payload -> Element interpreter m lock payload
  , toEltO2 :: obj2 lock payload -> Element interpreter m lock payload
  }

type PortalSimple specialization interpreter obj1 obj2 m lock payload =
  { giveNewParent ::
      interpreter
      -> { id :: String, parent :: String, scope :: Scope }
      -> specialization
      -> payload
  , deleteFromCache :: interpreter -> { id :: String } -> payload
  , fromEltO1 :: Element interpreter m lock payload -> obj1 lock payload
  , fromEltO2 :: Element interpreter m lock payload -> obj2 lock payload
  , toElt :: obj1 lock payload -> Element interpreter m lock payload
  }

internalPortalSimpleComplex
  :: forall n s m logic obj1 obj2 specialization interpreter lock0 lock1 payload
   . Compare n Neg1 GT
  => MonadST s m
  => Boolean
  -> (Scope -> Scope)
  -> Flatten logic interpreter obj2 m lock0 payload
  -> PortalSimple specialization interpreter obj1 obj2 m lock0 payload
  -> Vect n (obj1 lock0 payload)
  -> ( Vect n (specialization -> (obj1 lock1 payload))
       -> (obj1 lock0 payload -> obj1 lock1 payload)
       -> Entity logic (obj2 lock1 payload) m lock1
     )
  -> Entity logic (obj2 lock0 payload) m lock0
internalPortalSimpleComplex
  isGlobal
  scopeF
  flatArgs
  { giveNewParent
  , deleteFromCache
  , fromEltO1
  , fromEltO2
  , toElt
  }
  toBeam
  closure = Element' $ fromEltO2 $ Element go
  where
  go psr interpreter = makeEvent \k -> do
    av <- mutAr (map (const "") $ toArray toBeam)
    let
      actualized = oneOf $ mapWithIndex
        ( \ix i -> toElt i # \(Element elt) -> elt
            { parent: Nothing
            , scope: scopeF psr.scope
            -- here, it is safe to override raiseId without calling
            -- the passed-in raiseId because psr.raiseId
            -- is actually for the top-most element of the closure,
            -- _not_ this element
            -- we use raiseId to harvest the id of the element
            , raiseId: \id _ -> unsafeUpdateMutAr ix id av
            }
            interpreter
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
        ( \id specialization -> fromEltO1 $ Element
            \{ parent, scope, raiseId } itp ->
              makeEvent \k2 -> do
                raiseId id scope
                for_ parent \pt -> k2
                  (giveNewParent itp { id, parent: pt, scope } specialization)
                pure (pure unit)
        )
        idz
      realized = flatten flatArgs psr
        interpreter
        ( -- we will likely need some sort of unsafe coerce here...
          ( unsafeCoerce
              :: Entity logic (obj2 lock1 payload) m lock1
              -> Entity logic (obj2 lock0 payload) m lock0
          )
            ( closure
                ( ( unsafeCoerce
                      :: Vect n (specialization -> (obj1 lock0 payload))
                      -> Vect n (specialization -> (obj1 lock1 payload))
                  ) injectable
                )
                ( unsafeCoerce
                    :: obj1 lock0 payload -> obj1 lock1 payload
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

internalPortalComplexComplex
  :: forall n s m logic obj1 obj2 specialization interpreter lock0 lock1 payload
   . Compare n Neg1 GT
  => MonadST s m
  => Boolean
  -> (Scope -> Scope)
  -> Flatten logic interpreter obj2 m lock0 payload
  -> Portal logic specialization interpreter obj1 obj2 m lock0 payload
  -> Vect n (Entity logic (obj1 lock0 payload) m lock0)
  -> ( Vect n (specialization -> Entity logic (obj1 lock1 payload) m lock1)
       -> ( Entity logic (obj1 lock0 payload) m lock0
            -> Entity logic (obj1 lock1 payload) m lock1
          )
       -> Entity logic (obj2 lock1 payload) m lock1
     )
  -> Entity logic (obj2 lock0 payload) m lock0
internalPortalComplexComplex
  isGlobal
  scopeF
  flatArgs
  { giveNewParent
  , deleteFromCache
  , fromEltO1
  , fromEltO2
  , wrapElt
  , toElt
  }
  toBeam
  closure = Element' $ fromEltO2 $ Element go
  where
  go psr interpreter = makeEvent \k -> do
    av <- mutAr (map (const "") $ toArray toBeam)
    let
      actualized = oneOf $ mapWithIndex
        ( \ix -> Lazy.fix \f i -> case i of
            Element' beamable -> toElt beamable # \(Element elt) -> elt
              { parent: Nothing
              , scope: scopeF psr.scope
              -- here, it is safe to override raiseId without calling
              -- the passed-in raiseId because psr.raiseId
              -- is actually for the top-most element of the closure,
              -- _not_ this element
              -- we use raiseId to harvest the id of the element
              , raiseId: \id _ -> unsafeUpdateMutAr ix id av
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
        ( \id specialization -> Element' $ fromEltO1 $ Element
            \{ parent, scope, raiseId } itp ->
              makeEvent \k2 -> do
                raiseId id scope
                for_ parent \pt -> k2
                  (giveNewParent itp { id, parent: pt, scope } specialization)
                pure (pure unit)
        )
        idz
      realized = flatten flatArgs psr
        interpreter
        ( -- we will likely need some sort of unsafe coerce here...
          ( unsafeCoerce
              :: Entity logic (obj2 lock1 payload) m lock1
              -> Entity logic (obj2 lock0 payload) m lock0
          )
            ( closure
                ( ( unsafeCoerce
                      :: Vect n
                           ( specialization
                             -> Entity logic (obj1 lock0 payload) m lock0
                           )
                      -> Vect n
                           ( specialization
                             -> Entity logic (obj1 lock1 payload) m lock1
                           )
                  ) injectable
                )
                ( unsafeCoerce
                    :: Entity logic (obj1 lock0 payload) m lock0
                    -> Entity logic (obj1 lock1 payload) m lock1
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

internalPortalComplexSimple
  :: forall n s m logic obj1 obj2 specialization interpreter lock0 lock1 payload
   . Compare n Neg1 GT
  => MonadST s m
  => Boolean
  -> (Scope -> Scope)
  -> PortalComplex logic specialization interpreter obj1 obj2 m lock0 payload
  -> Vect n (Entity logic (obj1 lock0 payload) m lock0)
  -> ( Vect n
         ( specialization
           -> Entity logic (obj1 lock1 payload) m lock1
         )
       -> ( Entity logic (obj1 lock0 payload) m lock0
            -> Entity logic (obj1 lock1 payload) m lock1
          )
       -> obj2 lock1 payload
     )
  -> obj2 lock0 payload
internalPortalComplexSimple
  isGlobal
  scopeF
  { giveNewParent
  , deleteFromCache
  , fromEltO1
  , fromEltO2
  , wrapElt
  , toEltO1
  , toEltO2
  }
  toBeam
  closure = fromEltO2 $ Element go
  where
  go psr interpreter = makeEvent \k -> do
    av <- mutAr (map (const "") $ toArray toBeam)
    let
      actualized = oneOf $ mapWithIndex
        ( \ix -> Lazy.fix \f i -> case i of
            Element' beamable -> toEltO1 beamable # \(Element elt) -> elt
              { parent: Nothing
              , scope: scopeF psr.scope
              -- here, it is safe to override raiseId without calling
              -- the passed-in raiseId because psr.raiseId
              -- is actually for the top-most element of the closure,
              -- _not_ this element
              -- we use raiseId to harvest the id of the element
              , raiseId: \id _ -> unsafeUpdateMutAr ix id av
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
        ( \id specialization -> Element' $ fromEltO1 $ Element
            \{ parent, scope, raiseId } itp ->
              makeEvent \k2 -> do
                raiseId id scope
                for_ parent \pt -> k2
                  (giveNewParent itp { id, parent: pt, scope } specialization)
                pure (pure unit)
        )
        idz
      Element realized = toEltO2
        ( -- we will likely need some sort of unsafe coerce here...
          (unsafeCoerce :: obj2 lock1 payload -> obj2 lock0 payload)
            ( ( closure
                  ( ( unsafeCoerce
                        :: Vect n
                             ( specialization
                               -> Entity logic (obj1 lock0 payload) m lock0
                             )
                        -> Vect n
                             ( specialization
                               -> Entity logic (obj1 lock1 payload) m lock1
                             )
                    ) injectable
                  )
                  ( unsafeCoerce
                      :: Entity logic (obj1 lock0 payload) m lock0
                      -> Entity logic (obj1 lock1 payload) m lock1
                  )
              )
            )
        )
    u <- subscribe (realized psr interpreter) k
    void $ liftST $ Ref.write u av2
    -- cancel immediately, as it should be run synchronously
    -- so if this actually does something then we have a problem
    pure do
      u0
      when (not isGlobal) $ for_ (toArray idz) \id -> k
        (deleteFromCache interpreter { id })
      join (liftST $ Ref.read av2)

globalPortalComplexComplex
  :: forall n s m logic obj1 obj2 specialization interpreter lock payload
   . Compare n Neg1 GT
  => MonadST s m
  => Flatten logic interpreter obj2 m lock payload
  -> Portal logic specialization interpreter obj1 obj2 m lock payload
  -> Vect n (Entity logic (obj1 lock payload) m lock)
  -> ( Vect n (specialization -> Entity logic (obj1 lock payload) m lock)
       -> Entity logic (obj2 lock payload) m lock
     )
  -> Entity logic (obj2 lock payload) m lock
globalPortalComplexComplex
  flatArgs
  portalArgs
  toBeam
  closure = internalPortalComplexComplex true (const Global) flatArgs
  portalArgs
  toBeam
  (\x _ -> closure x)

globalPortalSimpleComplex
  :: forall n s m logic obj1 obj2 specialization interpreter lock payload
   . Compare n Neg1 GT
  => MonadST s m
  => Flatten logic interpreter obj2 m lock payload
  -> PortalSimple specialization interpreter obj1 obj2 m lock
       payload
  -> Vect n (obj1 lock payload)
  -> ( Vect n (specialization -> obj1 lock payload)
       -> Entity logic (obj2 lock payload) m lock
     )
  -> Entity logic (obj2 lock payload) m lock
globalPortalSimpleComplex
  flatArgs
  portalArgs
  toBeam
  closure = internalPortalSimpleComplex true (const Global) flatArgs
  portalArgs
  toBeam
  (\x _ -> closure x)

globalPortalComplexSimple
  :: forall n s m logic obj1 obj2 specialization interpreter lock payload
   . Compare n Neg1 GT
  => MonadST s m
  => PortalComplex logic specialization interpreter obj1 obj2 m lock
       payload
  -> Vect n (Entity logic (obj1 lock payload) m lock)
  -> ( Vect n (specialization -> Entity logic (obj1 lock payload) m lock)
       -> obj2 lock payload
     )
  -> obj2 lock payload
globalPortalComplexSimple
  portalArgs
  toBeam
  closure = internalPortalComplexSimple true (const Global)
  portalArgs
  toBeam
  (\x _ -> closure x)

portalComplexComplex
  :: forall n s m logic obj1 obj2 specialization interpreter lock payload
   . Compare n Neg1 GT
  => MonadST s m
  => Flatten logic interpreter obj2 m lock payload
  -> Portal logic specialization interpreter obj1 obj2 m lock payload
  -> Vect n (Entity logic (obj1 lock payload) m lock)
  -> ( forall lock1
        . Vect n (specialization -> Entity logic (obj1 lock1 payload) m lock1)
       -> ( Entity logic (obj1 lock payload) m lock
            -> Entity logic (obj1 lock1 payload) m lock1
          )
       -> Entity logic (obj2 lock1 payload) m lock1
     )
  -> Entity logic (obj2 lock payload) m lock
portalComplexComplex
  flatArgs
  portalArgs
  toBeam
  closure = internalPortalComplexComplex false identity flatArgs
  portalArgs
  toBeam
  closure

portalSimpleComplex
  :: forall n s m logic obj1 obj2 specialization interpreter lock payload
   . Compare n Neg1 GT
  => MonadST s m
  => Flatten logic interpreter obj2 m lock payload
  -> PortalSimple specialization interpreter obj1 obj2 m lock
       payload
  -> Vect n (obj1 lock payload)
  -> ( forall lock1
        . Vect n (specialization -> obj1 lock payload)
       -> (obj1 lock payload -> obj1 lock1 payload)
       -> Entity logic (obj2 lock1 payload) m lock1
     )
  -> Entity logic (obj2 lock payload) m lock
portalSimpleComplex
  flatArgs
  portalArgs
  toBeam
  closure = internalPortalSimpleComplex false identity flatArgs
  portalArgs
  toBeam
  closure

portalComplexSimple
  :: forall n s m logic obj1 obj2 specialization interpreter lock payload
   . Compare n Neg1 GT
  => MonadST s m
  => PortalComplex logic specialization interpreter obj1 obj2 m lock
       payload
  -> Vect n (Entity logic (obj1 lock payload) m lock)
  -> ( forall lock1
        . Vect n (specialization -> Entity logic (obj1 lock1 payload) m lock1)
       -> ( Entity logic (obj1 lock payload) m lock
            -> Entity logic (obj1 lock1 payload) m lock1
          )
       -> obj2 lock1 payload
     )
  -> obj2 lock payload
portalComplexSimple
  portalArgs
  toBeam
  closure = internalPortalComplexSimple false identity
  portalArgs
  toBeam
  closure

data Stage = Begin | Middle | End

type Flatten logic interpreter obj m lock payload =
  { doLogic :: logic -> interpreter -> String -> payload
  , ids :: interpreter -> m String
  , dynamicElementInserted ::
      interpreter
      -> { id :: String, parent :: String, scope :: Scope }
      -> payload
  , dynamicElementRemoved ::
      interpreter
      -> { id :: String, parent :: String, scope :: Scope }
      -> payload
  , toElt :: obj lock payload -> Element interpreter m lock payload
  }

flatten
  :: forall s m obj logic interpreter lock payload
   . Applicative m
  => MonadST s m
  => Flatten logic interpreter obj m lock payload
  -> PSR m
  -> interpreter
  -> Entity logic (obj lock payload) m lock
  -> AnEvent m payload
flatten
  flatArgs@
    { doLogic
    , ids
    , dynamicElementInserted
    , dynamicElementRemoved
    , toElt
    }
  psr
  interpreter = case _ of
  FixedChildren' (FixedChildren f) -> oneOfMap
    ( flatten flatArgs psr
        interpreter
    )
    f
  EventfulElement' (EventfulElement e) -> flatten flatArgs psr interpreter
    (switcher identity e)
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
            myScope <- Local <$> ids interpreter
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
                            ( dynamicElementRemoved interpreter
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
                        flatArgs
                        { parent: psr.parent
                        , scope: myScope
                        , raiseId: \id scope -> do
                            -- we make sure that the scopes are equal
                            -- otherwise, we are hitting the `raiseId` from
                            -- a higher-in-the-tree `dyn`, in which case we
                            -- don't want to raise it out of its context.
                            when (scope == myScope) do
                              -- todo: is there ever a case where a parent
                              -- can legitimately not exist here?
                              for_ psr.parent \parent -> k
                                ( dynamicElementInserted interpreter
                                    { id, parent, scope }
                                )
                              void $ liftST $ Ref.write (Just id) myId
                            psr.raiseId id scope
                        }
                        interpreter
                        -- hack to make sure that kid only ever raises its
                        -- ID once
                        -- if it is anything other than an element we wrap it in one
                        -- otherwise, we'd risk raising many ids to a parent
                        kid
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

type Fix interpreter obj m lock payload =
  { connectToParent ::
      interpreter -> { id :: String, parent :: String } -> payload
  , fromElt :: Element interpreter m lock payload -> obj lock payload
  }

fixComplexComplex
  :: forall s m obj logic interpreter lock payload
   . MonadST s m
  => Flatten logic interpreter obj m lock payload
  -> Fix interpreter obj m lock payload
  -> ( Entity logic (obj lock payload) m lock
       -> Entity logic (obj lock payload) m lock
     )
  -> Entity logic (obj lock payload) m lock
fixComplexComplex
  flatArgs
  { connectToParent, fromElt }
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
            when (r /= p')
              ( ii.raiseId r ii.scope *> k0
                  (connectToParent interpret { id: r, parent: p' })
              )
        pure (pure unit)
    subscribe
      ( flatten
          flatArgs
          { parent: i.parent
          , scope: i.scope
          , raiseId: \s scope -> do
              -- theoretically, the scopes could be different
              -- for example, if there is a fix around the dyn
              -- then the outer scope (i.scope) will be different than
              -- the inner scope passed to this function
              -- (i'm not totally sure about this, but it sounds sensible!)
              -- for this reason, we always want to pass the inner scope
              i.raiseId s scope
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
