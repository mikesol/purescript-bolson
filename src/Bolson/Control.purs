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
import Control.Monad.ST.Global as Region
import Control.Monad.ST.Internal (ST)
import Control.Monad.ST.Internal as Ref
import Data.FastVect.FastVect (toArray, Vect)
import Data.Filterable (filter)
import Data.Foldable (foldl, for_, oneOf, oneOfMap, traverse_)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Maybe (Maybe(..))
import Data.Tuple (snd)
import Data.Tuple.Nested ((/\))
import FRP.Event (Event, keepLatest, makePureEvent, mapAccum, memoize, subscribePure)
import Foreign.Object as Object
import Prim.Int (class Compare)
import Prim.Ordering (GT)
import Unsafe.Coerce (unsafeCoerce)

----

type Neg1 = -1

newtype MutAr a = MutAr (Array a)

foreign import mutAr :: forall s a. Array a -> ST s (MutAr a)
foreign import unsafeUpdateMutAr :: forall s a. Int -> a -> MutAr a -> ST s Unit
foreign import readAr :: forall s a. MutAr a -> ST s (Array a)

type Portal logic specialization interpreter obj1 obj2 r lock payload =
  { giveNewParent ::
      interpreter
      -> { id :: String, parent :: String, scope :: Scope }
      -> specialization
      -> payload
  , wrapElt ::
      Entity logic (obj1 lock payload) lock
      -> Entity logic (obj1 lock payload) lock
  , deleteFromCache :: interpreter -> { id :: String } -> payload
  , fromEltO1 :: Element interpreter r lock payload -> obj1 lock payload
  , fromEltO2 :: Element interpreter r lock payload -> obj2 lock payload
  , toElt :: obj1 lock payload -> Element interpreter r lock payload
  }

type PortalComplex logic specialization interpreter obj1 obj2 r lock payload =
  { giveNewParent ::
      interpreter
      -> { id :: String, parent :: String, scope :: Scope }
      -> specialization
      -> payload
  , wrapElt ::
      Entity logic (obj1 lock payload) lock
      -> Entity logic (obj1 lock payload) lock
  , deleteFromCache :: interpreter -> { id :: String } -> payload
  , fromEltO1 :: Element interpreter r lock payload -> obj1 lock payload
  , fromEltO2 :: Element interpreter r lock payload -> obj2 lock payload
  , toEltO1 :: obj1 lock payload -> Element interpreter r lock payload
  , toEltO2 :: obj2 lock payload -> Element interpreter r lock payload
  }

type PortalSimple specialization interpreter obj1 obj2 r lock payload =
  { giveNewParent ::
      interpreter
      -> { id :: String, parent :: String, scope :: Scope }
      -> specialization
      -> payload
  , deleteFromCache :: interpreter -> { id :: String } -> payload
  , fromEltO1 :: Element interpreter r lock payload -> obj1 lock payload
  , fromEltO2 :: Element interpreter r lock payload -> obj2 lock payload
  , toElt :: obj1 lock payload -> Element interpreter r lock payload
  }

internalPortalSimpleComplex
  :: forall n r logic obj1 obj2 specialization interpreter lock0 lock1 payload
   . Compare n Neg1 GT
  
  => Boolean
  -> (Scope -> Scope)
  -> Flatten logic interpreter obj2 r lock0 payload
  -> PortalSimple specialization interpreter obj1 obj2 r lock0 payload
  -> Vect n (obj1 lock0 payload)
  -> ( Vect n (specialization -> (obj1 lock1 payload))
       -> (obj1 lock0 payload -> obj1 lock1 payload)
       -> Entity logic (obj2 lock1 payload) lock1
     )
  -> Entity logic (obj2 lock0 payload) lock0
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
  go psr interpreter = makePureEvent \k -> do
    av <-  mutAr (map (const "") $ toArray toBeam)
    let
      actualized = oneOf $ mapWithIndex
        ( \ix i -> toElt i # \(Element elt) -> elt
            ( psr
                { parent = Nothing
                , scope = scopeF psr.scope
                , raiseId = \id ->  unsafeUpdateMutAr ix id av
                }
            )
            interpreter
        )
        (toArray toBeam)
    u0 <- subscribePure actualized k
    av2 <-  Ref.new (pure unit)
    let
      asIds :: Array String -> Vect n String
      asIds = unsafeCoerce
    idz <- asIds <$> ( readAr av)
    let
      -- we never connect or disconnect the referentially opaque node
      -- instead, it is always managed inside a referentially transparent node
      -- that can be properly connected and disconnected
      injectable = map
        ( \id specialization -> fromEltO1 $ Element
            \{ parent, scope, raiseId } itp ->
              makePureEvent \k2 -> do
                raiseId id
                for_ parent \pt -> k2
                  (giveNewParent itp { id, parent: pt, scope } specialization)
                pure (pure unit)
        )
        idz
      realized = flatten flatArgs psr
        interpreter
        ( -- we will likely need some sort of unsafe coerce here...
          (unsafeCoerce :: Entity logic (obj2 lock1 payload) lock1 -> Entity logic (obj2 lock0 payload) lock0)
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
    u <- subscribePure realized k
    void $  Ref.write u av2
    -- cancel immediately, as it should be run synchronously
    -- so if this actually does something then we have a problem
    pure do
      u0
      when (not isGlobal) $ for_ (toArray idz) \id -> k
        (deleteFromCache interpreter { id })
      join ( Ref.read av2)

internalPortalComplexComplex
  :: forall n r logic obj1 obj2 specialization interpreter lock0 lock1 payload
   . Compare n Neg1 GT
  
  => Boolean
  -> (Scope -> Scope)
  -> Flatten logic interpreter obj2 r lock0 payload
  -> Portal logic specialization interpreter obj1 obj2 r lock0 payload
  -> Vect n (Entity logic (obj1 lock0 payload) lock0)
  -> ( Vect n (specialization -> Entity logic (obj1 lock1 payload) lock1)
       -> ( Entity logic (obj1 lock0 payload) lock0
            -> Entity logic (obj1 lock1 payload) lock1
          )
       -> Entity logic (obj2 lock1 payload) lock1
     )
  -> Entity logic (obj2 lock0 payload) lock0
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
  go psr interpreter = makePureEvent \k -> do
    av <-  mutAr (map (const "") $ toArray toBeam)
    let
      actualized = oneOf $ mapWithIndex
        ( \ix -> Lazy.fix \f i -> case i of
            Element' beamable -> toElt beamable # \(Element elt) -> elt
              ( psr
                  { parent = Nothing
                  , scope = scopeF psr.scope
                  , raiseId = \id ->  unsafeUpdateMutAr ix id av
                  }
              )
              interpreter
            _ -> f (wrapElt i)
        )
        (toArray toBeam)
    u0 <- subscribePure actualized k
    av2 <-  Ref.new (pure unit)
    let
      asIds :: Array String -> Vect n String
      asIds = unsafeCoerce
    idz <- asIds <$> ( readAr av)
    let
      -- we never connect or disconnect the referentially opaque node
      -- instead, it is always managed inside a referentially transparent node
      -- that can be properly connected and disconnected
      injectable = map
        ( \id specialization -> Element' $ fromEltO1 $ Element
            \{ parent, scope, raiseId } itp ->
              makePureEvent \k2 -> do
                raiseId id
                for_ parent \pt -> k2
                  (giveNewParent itp { id, parent: pt, scope } specialization)
                pure (pure unit)
        )
        idz
      realized = flatten flatArgs psr
        interpreter
        ( -- we will likely need some sort of unsafe coerce here...
          ( unsafeCoerce
              :: Entity logic (obj2 lock1 payload) lock1
              -> Entity logic (obj2 lock0 payload) lock0
          )
            ( closure
                ( ( unsafeCoerce
                      :: Vect n
                           ( specialization
                             -> Entity logic (obj1 lock0 payload) lock0
                           )
                      -> Vect n
                           ( specialization
                             -> Entity logic (obj1 lock1 payload) lock1
                           )
                  ) injectable
                )
                ( unsafeCoerce
                    :: Entity logic (obj1 lock0 payload) lock0
                    -> Entity logic (obj1 lock1 payload) lock1
                )
            )
        )
    u <- subscribePure realized k
    void $  Ref.write u av2
    -- cancel immediately, as it should be run synchronously
    -- so if this actually does something then we have a problem
    pure do
      u0
      when (not isGlobal) $ for_ (toArray idz) \id -> k
        (deleteFromCache interpreter { id })
      join ( Ref.read av2)

internalPortalComplexSimple
  :: forall n r logic obj1 obj2 specialization interpreter lock0 lock1 payload
   . Compare n Neg1 GT
  
  => Boolean
  -> (Scope -> Scope)
  -> PortalComplex logic specialization interpreter obj1 obj2 r lock0 payload
  -> Vect n (Entity logic (obj1 lock0 payload) lock0)
  -> ( Vect n
         ( specialization
           -> Entity logic (obj1 lock1 payload) lock1
         )
       -> ( Entity logic (obj1 lock0 payload) lock0
            -> Entity logic (obj1 lock1 payload) lock1
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
  go psr interpreter = makePureEvent \k -> do
    av <-  mutAr (map (const "") $ toArray toBeam)
    let
      actualized = oneOf $ mapWithIndex
        ( \ix -> Lazy.fix \f i -> case i of
            Element' beamable -> toEltO1 beamable # \(Element elt) -> elt
              ( psr
                  { parent = Nothing
                  , scope = scopeF psr.scope
                  , raiseId = \id ->  unsafeUpdateMutAr ix id av
                  }
              )
              interpreter
            _ -> f (wrapElt i)
        )
        (toArray toBeam)
    u0 <- subscribePure actualized k
    av2 <-  Ref.new (pure unit)
    let
      asIds :: Array String -> Vect n String
      asIds = unsafeCoerce
    idz <- asIds <$> ( readAr av)
    let
      -- we never connect or disconnect the referentially opaque node
      -- instead, it is always managed inside a referentially transparent node
      -- that can be properly connected and disconnected
      injectable = map
        ( \id specialization -> Element' $ fromEltO1 $ Element
            \{ parent, scope, raiseId } itp ->
              makePureEvent \k2 -> do
                raiseId id
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
                               -> Entity logic (obj1 lock0 payload) lock0
                             )
                        -> Vect n
                             ( specialization
                               -> Entity logic (obj1 lock1 payload) lock1
                             )
                    ) injectable
                  )
                  ( unsafeCoerce
                      :: Entity logic (obj1 lock0 payload) lock0 -> Entity logic (obj1 lock1 payload) lock1
                  )
              )
            )
        )
    u <- subscribePure (realized psr interpreter) k
    void $  Ref.write u av2
    -- cancel immediately, as it should be run synchronously
    -- so if this actually does something then we have a problem
    pure do
      u0
      when (not isGlobal) $ for_ (toArray idz) \id -> k
        (deleteFromCache interpreter { id })
      join ( Ref.read av2)

globalPortalComplexComplex
  :: forall n r logic obj1 obj2 specialization interpreter lock payload
   . Compare n Neg1 GT
  
  => Flatten logic interpreter obj2 r lock payload
  -> Portal logic specialization interpreter obj1 obj2 r lock payload
  -> Vect n (Entity logic (obj1 lock payload) lock)
  -> ( Vect n (specialization -> Entity logic (obj1 lock payload) lock)
       -> Entity logic (obj2 lock payload) lock
     )
  -> Entity logic (obj2 lock payload) lock
globalPortalComplexComplex
  flatArgs
  portalArgs
  toBeam
  closure = internalPortalComplexComplex true (const Global) flatArgs
  portalArgs
  toBeam
  (\x _ -> closure x)

globalPortalSimpleComplex
  :: forall n r logic obj1 obj2 specialization interpreter lock payload
   . Compare n Neg1 GT
  
  => Flatten logic interpreter obj2 r lock payload
  -> PortalSimple specialization interpreter obj1 obj2 r lock
       payload
  -> Vect n (obj1 lock payload)
  -> ( Vect n (specialization -> obj1 lock payload)
       -> Entity logic (obj2 lock payload) lock
     )
  -> Entity logic (obj2 lock payload) lock
globalPortalSimpleComplex
  flatArgs
  portalArgs
  toBeam
  closure = internalPortalSimpleComplex true (const Global) flatArgs
  portalArgs
  toBeam
  (\x _ -> closure x)

globalPortalComplexSimple
  :: forall n r logic obj1 obj2 specialization interpreter lock payload
   . Compare n Neg1 GT
  
  => PortalComplex logic specialization interpreter obj1 obj2 r lock
       payload
  -> Vect n (Entity logic (obj1 lock payload) lock)
  -> ( Vect n (specialization -> Entity logic (obj1 lock payload) lock)
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
  :: forall n r logic obj1 obj2 specialization interpreter lock payload
   . Compare n Neg1 GT
  
  => Flatten logic interpreter obj2 r lock payload
  -> Portal logic specialization interpreter obj1 obj2 r lock payload
  -> Vect n (Entity logic (obj1 lock payload) lock)
  -> ( forall lock1
        . Vect n (specialization -> Entity logic (obj1 lock1 payload) lock1)
       -> ( Entity logic (obj1 lock payload) lock
            -> Entity logic (obj1 lock1 payload) lock1
          )
       -> Entity logic (obj2 lock1 payload) lock1
     )
  -> Entity logic (obj2 lock payload) lock
portalComplexComplex
  flatArgs
  portalArgs
  toBeam
  closure = internalPortalComplexComplex false identity flatArgs
  portalArgs
  toBeam
  closure

portalSimpleComplex
  :: forall n r logic obj1 obj2 specialization interpreter lock payload
   . Compare n Neg1 GT
  
  => Flatten logic interpreter obj2 r lock payload
  -> PortalSimple specialization interpreter obj1 obj2 r lock payload
  -> Vect n (obj1 lock payload)
  -> ( forall lock1
        . Vect n (specialization -> obj1 lock payload)
       -> (obj1 lock payload -> obj1 lock1 payload)
       -> Entity logic (obj2 lock1 payload) lock1
     )
  -> Entity logic (obj2 lock payload) lock
portalSimpleComplex
  flatArgs
  portalArgs
  toBeam
  closure = internalPortalSimpleComplex false identity flatArgs
  portalArgs
  toBeam
  closure

portalComplexSimple
  :: forall n r logic obj1 obj2 specialization interpreter lock payload
   . Compare n Neg1 GT
  
  => PortalComplex logic specialization interpreter obj1 obj2 r lock
       payload
  -> Vect n (Entity logic (obj1 lock payload) lock)
  -> ( forall lock1
        . Vect n (specialization -> Entity logic (obj1 lock1 payload) lock1)
       -> ( Entity logic (obj1 lock payload) lock
            -> Entity logic (obj1 lock1 payload) lock1
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

type Flatten logic interpreter obj r lock payload =
  { doLogic :: logic -> interpreter -> String -> payload
  , ids :: interpreter -> ST Region.Global String
  , disconnectElement ::
      interpreter
      -> { id :: String, parent :: String, scope :: Scope }
      -> payload
  , toElt :: obj lock payload -> Element interpreter r lock payload
  }

flatten
  :: forall r obj logic interpreter lock payload
   . Flatten logic interpreter obj r lock payload
  -> PSR r
  -> interpreter
  -> Entity logic (obj lock payload) lock
  -> Event payload
flatten
  flatArgs@
    { doLogic
    , ids
    , disconnectElement
    , toElt
    }
  psr
  interpreter = case _ of
  FixedChildren' (FixedChildren f) -> oneOfMap
    ( flatten flatArgs psr
        interpreter
    )
    f
  EventfulElement' (EventfulElement e) -> keepLatest
    ( map
        (flatten flatArgs psr interpreter)
        e
    )
  Element' e -> element (toElt e)
  DynamicChildren' (DynamicChildren children) ->
    makePureEvent \(k :: payload -> ST Region.Global Unit) -> do
      cancelInner <-  Ref.new Object.empty
      cancelOuter <-
        -- each child gets its own scope
        subscribePure children \inner ->
          do
            -- holds the previous id
            myUnsubId <- ids interpreter
            myUnsub <-  Ref.new (pure unit)
            eltsUnsubId <- ids interpreter
            eltsUnsub <-  Ref.new (pure unit)
            myIds <-  Ref.new []
            myImmediateCancellation <-  Ref.new (pure unit)
            myScope <- Local <$> ids interpreter
            stageRef <-  Ref.new Begin
            c0 <- subscribePure inner \kid' -> do
              stage <-  Ref.read stageRef
              case kid', stage of
                Logic logic, Middle -> ( Ref.read myIds) >>= traverse_
                  (k <<< doLogic logic interpreter)
                Remove, Middle -> do
                  void $  Ref.write End stageRef
                  let
                    mic = do
                      idRef <-  Ref.read myIds
                      for_ idRef \old ->
                          for_ psr.parent \pnt -> k
                            ( disconnectElement interpreter
                                { id: old, parent: pnt, scope: myScope }
                            )
                      join ( Ref.read myUnsub)
                      join ( Ref.read eltsUnsub)
                      void $  Ref.modify
                              (Object.delete myUnsubId)
                              cancelInner
                      void $  Ref.modify
                              (Object.delete eltsUnsubId)
                              cancelInner
                  void $  Ref.write mic myImmediateCancellation
                  mic
                Insert kid, Begin -> do
                  -- holds the current id
                  void $  Ref.write Middle stageRef
                  c1 <- subscribePure
                    ( flatten
                        flatArgs
                        ( psr
                            { scope = myScope
                            , raiseId = \id -> do
                                void $  Ref.modify (append [ id ]) myIds
                            }
                        )
                        interpreter
                        -- hack to make sure that kid only ever raises its
                        -- ID once
                        -- if it is anything other than an element we wrap it in one
                        -- otherwise, we'd risk raising many ids to a parent
                        kid
                    )
                    k
                  void $  Ref.modify (Object.insert eltsUnsubId c1)
                    cancelInner
                  void $  Ref.write c1 eltsUnsub
                _, _ -> pure unit
            void $  Ref.write c0 myUnsub
            void $  Ref.modify (Object.insert myUnsubId c0) cancelInner
            join ( Ref.read myImmediateCancellation)
      pure do
        ( Ref.read cancelInner) >>= foldl (*>) (pure unit)
        cancelOuter
  where
  element (Element e) = e psr interpreter

type Fix interpreter obj r lock payload =
  { connectToParent ::
      interpreter -> { id :: String, parent :: String } -> payload
  , fromElt :: Element interpreter r lock payload -> obj lock payload
  }

fixComplexComplex
  :: forall r obj logic interpreter lock payload
   . Flatten logic interpreter obj r lock payload
  -> Fix interpreter obj r lock payload
  -> (Entity logic (obj lock payload) lock -> Entity logic (obj lock payload) lock)
  -> Entity logic (obj lock payload) lock
fixComplexComplex
  flatArgs
  { connectToParent, fromElt }
  f = Element' $ fromElt $ Element go
  where
  go i interpret = makePureEvent \k -> do
    av <-  Ref.new Nothing
    let
      nn = f $ Element' $ fromElt $ Element \ii _ -> makePureEvent \k0 -> do
        ( Ref.read av) >>= case _ of
          Nothing -> pure unit
          -- only do the connection if not silence
          Just r -> for_ ii.parent \p' ->
            when (r /= p')
              ( ii.raiseId r *> k0
                  (connectToParent interpret { id: r, parent: p' })
              )
        pure (pure unit)
    subscribePure
      ( flatten
          flatArgs
          ( i
              { parent = i.parent
              , scope = i.scope
              , raiseId = \s -> do
                  i.raiseId s
                  void $  Ref.write (Just s) av
              }
          )
          interpret
          nn
      )
      k

switcher
  :: forall i logic obj lock
   . (i -> Entity logic obj lock)
  -> Event i
  -> Entity logic obj lock
switcher f event = DynamicChildren' $ DynamicChildren $ keepLatest
  $ memoize (counter event) \cenv -> map
      ( \(p /\ n) -> pure (Insert $ f p) <|>
          ((const Remove) <$> filter (eq (n + 1) <<< snd) cenv)
      )
      cenv
  where
  -- counter :: forall a. Event a → Event (a /\ Int)
  counter ev = mapAccum fn ev 0
    where
    fn a b = (b + 1) /\ (a /\ b)
