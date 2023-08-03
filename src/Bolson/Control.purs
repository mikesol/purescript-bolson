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
  , Flatten
  , Portal
  , PortalComplex
  , PortalSimple
  , Fix
  ) where

import Prelude

import Bolson.Core (Child(..), DynamicChildren(..), Element(..), Entity(..), FixedChildren(..), PSR, Scope(..))
import Control.Lazy as Lazy
import Control.Monad.ST.Class (class MonadST, liftST)
import Control.Monad.ST.Global as Global
import Control.Monad.ST.Global as Region
import Control.Monad.ST.Internal (ST)
import Control.Monad.ST.Internal as Ref
import Control.Monad.ST.Internal as ST
import Control.Plus (empty)
import Data.FastVect.FastVect (toArray, Vect)
import Data.Filterable (compact, filter)
import Data.Foldable (foldMap, foldl, for_, traverse_)
import Data.List ((:))
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Monoid (guard)
import Data.Traversable (traverse)
import Data.TraversableWithIndex (traverseWithIndex)
import Data.Tuple (Tuple(..), fst, snd)
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import FRP.Event (Event, create, keepLatest, makeEvent, mapAccum, memoize, merge, subscribe)
import Foreign.Object as Object
import Prim.Int (class Compare)
import Prim.Ordering (GT)
import Prim.Row (class Lacks)
import Record.Builder as RB
import Type.Proxy (Proxy(..))
import Unsafe.Coerce (unsafeCoerce)

----

type Neg1 = -1

newtype MutAr a = MutAr (Array a)

foreign import mutAr :: forall s a. Array a -> ST s (MutAr a)
foreign import unsafeUpdateMutAr :: forall s a. Int -> a -> MutAr a -> ST s Unit
foreign import readAr :: forall s a. MutAr a -> ST s (Array a)

type Portal logic specialization interpreter obj1 obj2 r payload =
  { giveNewParent ::
      interpreter
      -> { id :: String
         , parent :: String
         , scope :: Scope
         , raiseId :: String -> ST.ST Region.Global Unit
         | r
         }
      -> Entity logic (obj1 payload)
      -> specialization
      -> payload
  , wrapElt ::
      Entity logic (obj1 payload)
      -> Entity logic (obj1 payload)
  , deleteFromCache :: interpreter -> { id :: String } -> payload
  , fromEltO1 :: Element interpreter r payload -> obj1 payload
  , fromEltO2 :: Element interpreter r payload -> obj2 payload
  , toElt :: obj1 payload -> Element interpreter r payload
  }

type PortalComplex logic specialization interpreter obj1 obj2 r payload =
  { giveNewParent ::
      interpreter
      -> { id :: String
         , parent :: String
         , scope :: Scope
         , raiseId :: String -> ST.ST Region.Global Unit
         | r
         }
      -> Entity logic (obj1 payload)
      -> specialization
      -> payload
  , wrapElt ::
      Entity logic (obj1 payload)
      -> Entity logic (obj1 payload)
  , deleteFromCache :: interpreter -> { id :: String } -> payload
  , fromEltO1 :: Element interpreter r payload -> obj1 payload
  , fromEltO2 :: Element interpreter r payload -> obj2 payload
  , toEltO1 :: obj1 payload -> Element interpreter r payload
  , toEltO2 :: obj2 payload -> Element interpreter r payload
  }

type PortalSimple logic specialization interpreter obj1 obj2 r payload =
  { giveNewParent ::
      interpreter
      -> { id :: String
         , parent :: String
         , scope :: Scope
         , raiseId :: String -> ST.ST Region.Global Unit
         | r
         }
      -> Entity logic (obj1 payload)
      -> specialization
      -> payload
  , deleteFromCache :: interpreter -> { id :: String } -> payload
  , fromEltO1 :: Element interpreter r payload -> obj1 payload
  , fromEltO2 :: Element interpreter r payload -> obj2 payload
  , toElt :: obj1 payload -> Element interpreter r payload
  }

internalPortalSimpleComplex
  :: forall n r logic obj1 obj2 specialization interpreter payload
   . Compare n Neg1 GT
  => Lacks "id" r
  => Lacks "raiseId" r
  => Boolean
  -> (Scope -> Scope)
  -> Flatten logic interpreter obj2 r payload
  -> PortalSimple logic specialization interpreter obj1 obj2 r payload
  -> Vect n (obj1 payload)
  -> ( Vect n (specialization -> (obj1 payload))
       -> Entity logic (obj2 payload)
     )
  -> Entity logic (obj2 payload)
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
  go psr interpreter = do
    av <- mutAr
      ( toArray toBeam $>
          { id: ""
          , entity: Element'
              (fromEltO1 (Element \_ _ -> pure $ Tuple [] $ Tuple [] empty))
          }
      )
    actualized' <- traverseWithIndex
      ( \ix entity -> toElt entity # \(Element elt) -> elt
          ( psr
              { parent = Nothing
              , scope = scopeF psr.scope
              , raiseId = \id -> unsafeUpdateMutAr ix
                  { id, entity: Element' entity }
                  av
              }
          )
          interpreter
      )
      (toArray toBeam)
    let actualized = merge (map (snd <<< snd) actualized')
    let
      asIds
        :: Array { id :: String, entity :: Entity logic (obj1 payload) }
        -> Vect n { id :: String, entity :: Entity logic (obj1 payload) }
      asIds = unsafeCoerce
    idz <- asIds <$> (readAr av)
    let
      -- we never connect or disconnect the referentially opaque node
      -- instead, it is always managed inside a referentially transparent node
      -- that can be properly connected and disconnected
      injectable = map
        ( \{ id, entity } specialization -> fromEltO1 $ Element
            \psr2 itp -> do
              psr2.raiseId id
              pure
                $ Tuple
                    ( compact
                        [ psr2.parent <#> \pt ->
                            pure
                              ( giveNewParent itp
                                  ( RB.build
                                      ( RB.insert (Proxy :: _ "id") id >>>
                                          RB.modify (Proxy :: _ "parent")
                                            (const pt)
                                      )
                                      psr2
                                  )
                                  entity
                                  specialization
                              )
                        ]
                    )
                $ Tuple []
                $ empty
        )
        idz
    Tuple sub (Tuple unsub elt) <- flatten flatArgs psr interpreter
      (closure (injectable))
    let onSubscribe = join $ map fst actualized' <> [ sub ]
    let
      onUnsubscribe = append unsub $ guard (not isGlobal) $
        ( map
            (\{ id } -> pure $ deleteFromCache interpreter { id })
            (toArray idz) <> join (map (fst <<< snd) actualized')
        )
    pure $ Tuple onSubscribe $ Tuple onUnsubscribe $ makeEvent \k -> do
      u0 <- subscribe actualized k
      u1 <- subscribe elt k
      pure do
        u0
        u1

internalPortalComplexComplex
  :: forall n r logic obj1 obj2 specialization interpreter payload
   . Compare n Neg1 GT
  => Lacks "id" r
  => Lacks "raiseId" r
  => Boolean
  -> (Scope -> Scope)
  -> Flatten logic interpreter obj2 r payload
  -> Portal logic specialization interpreter obj1 obj2 r payload
  -> Vect n (Entity logic (obj1 payload))
  -> ( Vect n (specialization -> Entity logic (obj1 payload))
       -> Entity logic (obj2 payload)
     )
  -> Entity logic (obj2 payload)
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
  go psr interpreter = do
    av <- mutAr
      ( toArray toBeam $>
          { id: ""
          , entity: Element'
              (fromEltO1 (Element \_ _ -> pure $ Tuple [] $ Tuple [] empty))
          }
      )
    actualized' <- traverseWithIndex
      ( \ix -> Lazy.fix \f entity -> case entity of
          Element' beamable -> toElt beamable # \(Element elt) -> elt
            ( psr
                { parent = Nothing
                , scope = scopeF psr.scope
                , raiseId = \id -> unsafeUpdateMutAr ix { id, entity } av
                }
            )
            interpreter
          _ -> f (wrapElt entity)
      )
      (toArray toBeam)
    let actualized = merge (map (snd <<< snd) actualized')
    let
      asIds
        :: Array { id :: String, entity :: Entity logic (obj1 payload) }
        -> Vect n { id :: String, entity :: Entity logic (obj1 payload) }
      asIds = unsafeCoerce
    idz <- asIds <$> (readAr av)
    let
      injectable = map
        ( \{ id, entity } specialization -> Element' $ fromEltO1 $ Element
            \psr2 itp -> do
              psr2.raiseId id
              pure
                $ Tuple
                    ( compact
                        [ psr2.parent <#> \pt ->
                            pure
                              ( giveNewParent itp
                                  ( RB.build
                                      ( RB.insert (Proxy :: _ "id") id >>>
                                          RB.modify (Proxy :: _ "parent")
                                            (const pt)
                                      )
                                      psr2
                                  )
                                  entity
                                  specialization
                              )
                        ]
                    )
                $ Tuple []
                $ empty
        )
        idz
    Tuple sub (Tuple unsub elt) <- flatten flatArgs psr interpreter
      (closure (injectable))
    let onSubscribe = join $ map fst actualized' <> [ sub ]
    let
      onUnsubscribe = append unsub $ guard (not isGlobal) $
        map
          (\{ id } -> pure $ deleteFromCache interpreter { id })
          (toArray idz) <> join (map (fst <<< snd) actualized')
    pure $ Tuple onSubscribe $ Tuple onUnsubscribe $ makeEvent \k -> do
      u0 <- subscribe actualized k
      u1 <- subscribe elt k
      pure do
        u0
        u1

internalPortalComplexSimple
  :: forall n r logic obj1 obj2 specialization interpreter payload
   . Compare n Neg1 GT
  => Lacks "id" r
  => Lacks "raiseId" r
  => Boolean
  -> (Scope -> Scope)
  -> PortalComplex logic specialization interpreter obj1 obj2 r payload
  -> Vect n (Entity logic (obj1 payload))
  -> (Vect n (specialization -> Entity logic (obj1 payload)) -> obj2 payload)
  -> obj2 payload
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
  go psr interpreter = do
    -- we initialize a mutable array with empty ids and empty elements
    -- for each element in the portal vector
    av <- mutAr
      ( toArray toBeam $>
          { id: ""
          , entity: Element'
              (fromEltO1 (Element \_ _ -> pure $ Tuple [] $ Tuple [] empty))
          }
      )
    -- We intercept all of the elements in the portal vector
    -- and turn them into instructions and events.
    --
    -- This is very much like flatten on its simplest branch.
    --
    -- Crucially, when an id is raised, we update mutAr
    -- with the entity so we know what things can be beamed around.
    --
    -- We'll need this later when we actually do the beaming.
    --
    -- We also give the framework the option to wrap the element
    -- so that we are dealing with a singleton (Element'), otherwise it gets too thorny.
    actualized' <- traverseWithIndex
      ( \ix -> Lazy.fix \f entity -> case entity of
          Element' beamable -> toEltO1 beamable # \(Element elt) -> elt
            ( psr
                { parent = Nothing
                , scope = scopeF psr.scope
                , raiseId = \id -> unsafeUpdateMutAr ix { id, entity } av
                }
            )
            interpreter
          _ -> f (wrapElt entity)
      )
      (toArray toBeam)
    -- these represent the events of every sub-element in the portal's vector
    let actualized = merge (map (snd <<< snd) actualized')
    -- this is the id we'll use for deferred unloading
    let
      asIds
        :: Array { id :: String, entity :: Entity logic (obj1 payload) }
        -> Vect n { id :: String, entity :: Entity logic (obj1 payload) }
      asIds = unsafeCoerce
    -- now, when we read the ids, we will have all of the ids of the "beamable" elements in the vector
    -- this is because the left-bind above that produces actualized' triggers all of the `raiseId` in the elements
    idz <- asIds <$> (readAr av)
    -- here's the bait and switch: instead of injecting the beamables into the closure,
    -- we inject completely empty elements
    -- they have no moving parts, so it's an empty event
    -- the only thing they do is signal that they're
    -- in fact from the portal (the raiseId)
    -- and provide a side-effect to run immediately upon subscription, meaning the give-new-parent
    let
      injectable = map
        ( \{ id, entity } specialization -> Element' $ fromEltO1 $ Element
            \psr2 itp -> do
              psr2.raiseId id
              pure
                $ Tuple
                    ( compact
                        [ psr2.parent <#> \pt ->
                            pure
                              ( giveNewParent itp
                                  ( RB.build
                                      ( RB.insert (Proxy :: _ "id") id >>>
                                          RB.modify (Proxy :: _ "parent")
                                            (const pt)
                                      )
                                      psr2
                                  )
                                  entity
                                  specialization
                              )
                        ]
                    )
                $ Tuple []
                $ empty
        )
        idz
      -- now, the elements are simply the evaluation of the closure
      Element realized = toEltO2 (closure (injectable))
    -- we get the top-level element yielded by the portal
    realized' <- realized psr interpreter
    -- here's everything we need on subscription, so we can issue it immediately
    let onSubscribe = join $ map fst actualized' <> [ fst realized' ]
    -- When we unsubscribe from the portal, we want to delete everything
    -- with one of the ids we created.
    let
      onUnsubscribe = append (fst (snd realized')) $ guard (not isGlobal) $
        map
          (\{ id } -> pure $ deleteFromCache interpreter { id })
          (toArray idz) <> join (map (fst <<< snd) actualized')
    pure $ Tuple onSubscribe $ Tuple onUnsubscribe $ makeEvent \k -> do
      -- Triggers all of the effects in the beamable elements
      u0 <- subscribe actualized k
      -- Triggers all of the effects in the element yielded by the closure
      u1 <- subscribe (snd $ snd realized') k
      pure do
        u0
        u1

globalPortalComplexComplex
  :: forall n r logic obj1 obj2 specialization interpreter payload
   . Compare n Neg1 GT
  => Lacks "id" r
  => Lacks "raiseId" r
  => Flatten logic interpreter obj2 r payload
  -> Portal logic specialization interpreter obj1 obj2 r payload
  -> Vect n (Entity logic (obj1 payload))
  -> ( Vect n (specialization -> Entity logic (obj1 payload))
       -> Entity logic (obj2 payload)
     )
  -> Entity logic (obj2 payload)
globalPortalComplexComplex
  flatArgs
  portalArgs
  toBeam
  closure = internalPortalComplexComplex true (const Global) flatArgs
  portalArgs
  toBeam
  closure

globalPortalSimpleComplex
  :: forall n r logic obj1 obj2 specialization interpreter payload
   . Compare n Neg1 GT
  => Lacks "id" r
  => Lacks "raiseId" r
  => Flatten logic interpreter obj2 r payload
  -> PortalSimple logic specialization interpreter obj1 obj2 r
       payload
  -> Vect n (obj1 payload)
  -> ( Vect n (specialization -> obj1 payload)
       -> Entity logic (obj2 payload)
     )
  -> Entity logic (obj2 payload)
globalPortalSimpleComplex
  flatArgs
  portalArgs
  toBeam
  closure = internalPortalSimpleComplex true (const Global) flatArgs
  portalArgs
  toBeam
  closure

globalPortalComplexSimple
  :: forall n r logic obj1 obj2 specialization interpreter payload
   . Compare n Neg1 GT
  => Lacks "id" r
  => Lacks "raiseId" r
  => PortalComplex logic specialization interpreter obj1 obj2 r
       payload
  -> Vect n (Entity logic (obj1 payload))
  -> ( Vect n (specialization -> Entity logic (obj1 payload))
       -> obj2 payload
     )
  -> obj2 payload
globalPortalComplexSimple
  portalArgs
  toBeam
  closure = internalPortalComplexSimple true (const Global)
  portalArgs
  toBeam
  closure

portalComplexComplex
  :: forall n r logic obj1 obj2 specialization interpreter payload
   . Compare n Neg1 GT
  => Lacks "id" r
  => Lacks "raiseId" r
  => Flatten logic interpreter obj2 r payload
  -> Portal logic specialization interpreter obj1 obj2 r payload
  -> Vect n (Entity logic (obj1 payload))
  -> ( Vect n (specialization -> Entity logic (obj1 payload))
       -> Entity logic (obj2 payload)
     )
  -> Entity logic (obj2 payload)
portalComplexComplex
  flatArgs
  portalArgs
  toBeam
  closure = internalPortalComplexComplex false identity flatArgs
  portalArgs
  toBeam
  closure

portalSimpleComplex
  :: forall n r logic obj1 obj2 specialization interpreter payload
   . Compare n Neg1 GT
  => Lacks "id" r
  => Lacks "raiseId" r
  => Flatten logic interpreter obj2 r payload
  -> PortalSimple logic specialization interpreter obj1 obj2 r payload
  -> Vect n (obj1 payload)
  -> ( Vect n (specialization -> obj1 payload)
       -> Entity logic (obj2 payload)
     )
  -> Entity logic (obj2 payload)
portalSimpleComplex
  flatArgs
  portalArgs
  toBeam
  closure = internalPortalSimpleComplex false identity flatArgs
  portalArgs
  toBeam
  closure

portalComplexSimple
  :: forall n r logic obj1 obj2 specialization interpreter payload
   . Compare n Neg1 GT
  => Lacks "id" r
  => Lacks "raiseId" r
  => PortalComplex logic specialization interpreter obj1 obj2 r
       payload
  -> Vect n (Entity logic (obj1 payload))
  -> ( Vect n (specialization -> Entity logic (obj1 payload))
       -> obj2 payload
     )
  -> obj2 payload
portalComplexSimple
  portalArgs
  toBeam
  closure = internalPortalComplexSimple false identity
  portalArgs
  toBeam
  closure

data Stage = Listening | Closed

type Flatten logic interpreter obj r payload =
  { doLogic :: logic -> interpreter -> String -> payload
  , ids :: interpreter -> ST Region.Global Int
  , disconnectElement ::
      interpreter
      -> { id :: String, parent :: String, scope :: Scope }
      -> payload
  , deferPayload :: interpreter -> List.List Int -> payload -> payload
  , forcePayload :: interpreter -> List.List Int -> payload
  , redecorateDeferredPayload ::
      interpreter -> List.List Int -> payload -> payload
  , toElt :: obj payload -> Element interpreter r payload
  }

flatten
  :: forall r obj logic interpreter payload
   . Flatten logic interpreter obj r payload
  -> PSR r
  -> interpreter
  -> Entity logic (obj payload)
  -> ST Global.Global
       (Tuple (Array (ST Global.Global payload)) (Tuple (Array (ST Global.Global payload)) (Event payload)))
flatten
  flatArgs@
    { doLogic
    , ids
    , deferPayload
    , forcePayload
    , disconnectElement
    , redecorateDeferredPayload
    , toElt
    }
  psr
  interpreter = case _ of
  FixedChildren' (FixedChildren f) -> do
    o <- traverse (flatten flatArgs psr interpreter) f
    pure $ (map <<< map) merge
      $ foldMap (\(Tuple a (Tuple b c)) -> Tuple a (Tuple b [ c ])) o
  Element' e -> element (toElt e)
  DynamicChildren' (DynamicChildren (Tuple initialChildren children)) -> do
    fireId1 <- ids interpreter
    cancelInner <- Ref.new Object.empty
    initialEvent <- create
    let
      subscriber
        :: forall m
         . MonadST Region.Global m
        => (ST Region.Global payload -> m Unit)
        -> (payload -> Effect Unit)
        -> Tuple (Event (Child logic)) (Entity logic (obj payload))
        -> m Unit
      subscriber k1 k2 inner =
        do
          fireId2 <- liftST $ ids interpreter
          -- holds the previous id
          myUnsubId <- liftST $ ids interpreter
          myUnsub <- liftST $ Ref.new (pure unit)
          eltsUnsubId <- liftST $ ids interpreter
          eltsUnsub <- liftST $ Ref.new (pure unit)
          myIds <- liftST $ Ref.new []
          myScope <- liftST $ Local <$>
            ( case psr.scope of
                Global -> show <$> ids interpreter
                Local l -> pure l <> pure "!" <> show <$> ids interpreter
            )
          stageRef <- liftST $ Ref.new Listening
          let fireList = (fireId1 : fireId2 : List.Nil)
          void $ liftST $ Ref.write Listening stageRef
          Tuple sub (Tuple unsub evt) <- liftST $ flatten
            flatArgs
            ( psr
                { scope = myScope
                , raiseId = \id -> do
                    void $ Ref.modify (append [ id ]) myIds
                }
            )
            interpreter
            (snd inner)
          for_ unsub $ k1 <<< map (deferPayload interpreter fireList)
          for_ sub $ k1
          c1 <- liftST $ subscribe
            (map (redecorateDeferredPayload interpreter fireList) evt)
            k2
          void $ liftST $ Ref.modify (Object.insert (show eltsUnsubId) c1)
            cancelInner
          void $ liftST $ Ref.write c1 eltsUnsub
          c0 <- liftST $ subscribe (fst inner) \kid' -> do
            stage <- liftST $ Ref.read stageRef
            case kid', stage of
              Logic lgc, Listening -> do
                cid <- liftST $ Ref.read myIds
                traverse_ (k2 <<< doLogic lgc interpreter) cid
              Remove, Listening -> do
                void $ liftST $ Ref.write Closed stageRef
                idRef <- liftST $ Ref.read myIds
                for_ idRef \old ->
                  for_ psr.parent \pnt -> k2
                    ( disconnectElement interpreter
                        { id: old, parent: pnt, scope: myScope }
                    )
                -- we force after the disconnect element
                -- because assumedly the forcing has clean-up-y stuff
                -- so we want to disconnect before we clean up, lest
                -- we try to disconnect something that has already been deleted
                k2 $ forcePayload interpreter (fireId1 : fireId2 : List.Nil)
                myu <- liftST $ Ref.read myUnsub
                liftST myu
                eltu <- liftST $ Ref.read eltsUnsub
                liftST eltu
                void $ liftST $ Ref.modify
                  (Object.delete $ show myUnsubId)
                  cancelInner
                void $ liftST $ Ref.modify
                  (Object.delete $ show eltsUnsubId)
                  cancelInner
              _, _ -> pure unit
          void $ liftST $ Ref.write c0 myUnsub
          void $ liftST $ Ref.modify (Object.insert (show myUnsubId) c0)
            cancelInner
    r <- Ref.new []
    let kInit i = void $ Ref.modify (_ <> [ i ]) r
    for_ initialChildren (subscriber kInit initialEvent.push)
    o <- Ref.read r
    pure $ Tuple o $ Tuple [ pure (forcePayload interpreter $ pure fireId1) ] $ merge
      [ initialEvent.event
      , makeEvent \k -> do
          cancelOuter <-
            -- each child gets its own scope
            subscribe children (subscriber (liftST >=> k) k)
          pure do
            (Ref.read cancelInner) >>= foldl (*>) (pure unit)
            cancelOuter
      ]
  where
  element (Element e) = e psr interpreter

type Fix interpreter obj r payload =
  { connectToParent ::
      interpreter -> { id :: String, parent :: String } -> payload
  , fromElt :: Element interpreter r payload -> obj payload
  }

fixComplexComplex
  :: forall r obj logic interpreter payload
   . Flatten logic interpreter obj r payload
  -> Fix interpreter obj r payload
  -> (Entity logic (obj payload) -> Entity logic (obj payload))
  -> Entity logic (obj payload)
fixComplexComplex
  flatArgs
  { connectToParent, fromElt }
  f = Element' $ fromElt $ Element go
  where
  go i interpret = do
    av <- Ref.new Nothing
    let
      nn = f $ Element' $ fromElt $ Element \ii _ -> do
        av' <- Ref.read av
        case av', ii.parent of
          Just r, Just p'
            | r /= p' -> pure
                $ Tuple [ pure $ connectToParent interpret { id: r, parent: p' } ]
                $ Tuple [] empty
          _, _ -> pure $ Tuple [] $ Tuple [] empty
    flatten flatArgs
      ( i
          { parent = i.parent
          , scope = i.scope
          , raiseId = \s -> do
              i.raiseId s
              void $ Ref.write (Just s) av
          }
      )
      interpret
      nn

switcher
  :: forall i logic obj
   . (i -> Entity logic obj)
  -> Event i
  -> Entity logic obj
switcher f event = DynamicChildren' $ DynamicChildren $ Tuple [] $ keepLatest
  $ memoize (counter event) \cenv -> map
      ( \(p /\ n) -> Tuple
          ((const Remove) <$> filter (eq (n + 1) <<< snd) (counter event))
          (f p)

      )
      cenv
  where
  counter :: forall a. Event a → Event (a /\ Int)
  counter ev = mapAccum fn 0 ev
    where
    fn a b = (a + 1) /\ (b /\ a)
