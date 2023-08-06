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
  , behaving
  , behaving_
  , behaving'
  , Flatten
  , Portal
  , PortalComplex
  , PortalSimple
  , Fix
  ) where

import Prelude

import Bolson.Core (Child(..), DynamicChildren(..), Element(..), Entity(..), FixedChildren(..), PSR, Scope(..))
import Control.Lazy as Lazy
import Control.Monad.ST.Class (liftST)
import Control.Monad.ST.Global as Region
import Control.Monad.ST.Internal (ST)
import Control.Monad.ST.Internal as Ref
import Control.Monad.ST.Internal as ST
import Control.Plus (empty)
import Data.FastVect.FastVect (toArray, Vect)
import Data.Filterable (compact, filter)
import Data.Foldable (foldl, for_)
import Data.FunctorWithIndex (mapWithIndex)
import Data.List ((:))
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), fst, snd)
import Data.Tuple.Nested (type (/\), (/\))
import FRP.Behavior (Behavior, behavior, sample)
import FRP.Event (Event, keepLatest, makeLemmingEvent, mapAccum, memoize, merge)
import FRP.Event.Class (once)
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
         , deferralPath :: List.List Int
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
         , deferralPath :: List.List Int
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
         , deferralPath :: List.List Int
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

behaving' :: forall a. (forall b. (a -> b) -> Event (a -> b) -> (a -> ST Region.Global Unit) -> (forall c.  Event c -> ((b -> ST Region.Global Unit) -> c -> ST Region.Global Unit) -> ST Region.Global Unit) -> ST Region.Global Unit) -> Behavior a
behaving' iii = behavior \e -> makeLemmingEvent \subscribe kx -> do
  urf <- Ref.new (pure unit)
  ugh <- subscribe e \f -> do
    iii f e (f >>> kx) \z fkx -> do
      acsu <- subscribe z (fkx kx)
      void $ Ref.modify (_ *> acsu) urf
  pure do
    liftST $ join (Ref.read urf)
    ugh

behaving_ :: forall a. (forall b. Event (a -> b) -> (a -> ST Region.Global Unit) -> (forall c.  Event c -> ((b -> ST Region.Global Unit) -> c -> ST Region.Global Unit) -> ST Region.Global Unit) -> ST Region.Global Unit) -> Behavior a
behaving_ iii = behaving' \_ -> iii

behaving :: forall a. (forall b. Event (a -> b) -> (a -> ST Region.Global Unit) -> (Event b -> ST Region.Global Unit) -> ST Region.Global Unit) -> Behavior a
behaving iii = behaving_ \a b c -> iii a b (flip c identity)

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
  go psr interpreter = behaving \e kx subscribe -> do
    -- we initialize a mutable array with empty ids and empty elements
    -- for each element in the portal vector
    av <- mutAr
      ( toArray toBeam $>
          { id: ""
          , entity: Element'
              (fromEltO1 (Element \_ _ -> behavior \_ -> empty))
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
    let
      actualized = mapWithIndex
        ( \ix entity -> toElt entity # \(Element elt) -> sample
            ( elt
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
            e
        )
        (toArray toBeam)
    subscribe (merge actualized)
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
        ( \{ id, entity } specialization -> fromEltO1 $ Element
            \psr2 itp -> behaving \_ kxkx _ -> do
              liftST $ psr2.raiseId id
              for_
                ( compact
                    [ psr2.parent <#> \pt ->
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
                kxkx
        )
        idz
      -- now, the elements are simply the evaluation of the closure

      realized = flatten flatArgs (closure injectable) psr interpreter

    subscribe (sample realized e)
    -- When we unsubscribe from the portal, we want to delete everything
    -- with one of the ids we created.
    when (not isGlobal) do
      for_ (toArray idz) \{ id } -> do
        kx (deleteFromCache interpreter { id })

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
  go psr interpreter = behaving \e kx subscribe -> do
    -- we initialize a mutable array with empty ids and empty elements
    -- for each element in the portal vector
    av <- mutAr
      ( toArray toBeam $>
          { id: ""
          , entity: Element'
              (fromEltO1 (Element \_ _ -> behavior \_ -> empty))
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
    let
      actualized = mapWithIndex
        ( \ix -> Lazy.fix \ff entity -> case entity of
            Element' beamable -> toElt beamable # \(Element elt) -> sample
              ( elt
                  ( psr
                      { parent = Nothing
                      , scope = scopeF psr.scope
                      , raiseId = \id -> unsafeUpdateMutAr ix { id, entity } av
                      }
                  )
                  interpreter
              )
              e
            _ -> ff (wrapElt entity)
        )
        (toArray toBeam)
    subscribe (merge actualized)
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
            \psr2 itp -> behaving \_ kxkx _ -> do
              liftST $ psr2.raiseId id
              for_
                ( compact
                    [ psr2.parent <#> \pt ->
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
                kxkx
        )
        idz
      -- now, the elements are simply the evaluation of the closure
      realized = flatten flatArgs (closure (injectable)) psr interpreter

    subscribe (sample realized e)
    -- When we unsubscribe from the portal, we want to delete everything
    -- with one of the ids we created.
    when (not isGlobal) do
      for_ (toArray idz) \{ id } -> do
        kx (deleteFromCache interpreter { id })

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
  go psr interpreter = behaving \e kx subscribe -> do
    -- we initialize a mutable array with empty ids and empty elements
    -- for each element in the portal vector
    av <- mutAr
      ( toArray toBeam $>
          { id: ""
          , entity: Element'
              (fromEltO1 (Element \_ _ -> behavior \_ -> empty))
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
    let
      actualized = mapWithIndex
        ( \ix -> Lazy.fix \ff entity -> case entity of
            Element' beamable -> toEltO1 beamable # \(Element elt) -> sample
              ( elt
                  ( psr
                      { parent = Nothing
                      , scope = scopeF psr.scope
                      , raiseId = \id -> unsafeUpdateMutAr ix { id, entity } av
                      }
                  )
                  interpreter
              )
              e
            _ -> ff (wrapElt entity)
        )
        (toArray toBeam)
    subscribe (merge actualized)
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
            \psr2 itp -> behavior \ne -> makeLemmingEvent \sub2 kk -> sub2 ne \ff -> do
              liftST $ psr2.raiseId id
              for_
                ( compact
                    [ psr2.parent <#> \pt ->
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
                (kk <<< ff)
        )
        idz
      -- now, the elements are simply the evaluation of the closure
      Element realized = toEltO2 (closure (injectable))
    subscribe (sample (realized psr interpreter) e)
    -- When we unsubscribe from the portal, we want to delete everything
    -- with one of the ids we created.
    when (not isGlobal) do
      for_ (toArray idz) \{ id } -> do
        kx (deleteFromCache interpreter { id })

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
  , toElt :: obj payload -> Element interpreter r payload
  }

flatten
  :: forall r obj logic interpreter payload
   . Flatten logic interpreter obj r payload
  -> Entity logic (obj payload)
  -> PSR r
  -> interpreter
  -> Behavior payload
flatten
  flatArgs@
    { doLogic
    , ids
    , deferPayload
    , forcePayload
    , disconnectElement
    , toElt
    }
  etty
  psr
  interpreter = case etty of
  FixedChildren' (FixedChildren fc) -> behavior \e ->
    merge $ map (\ex -> sample (flatten flatArgs ex psr interpreter) e) fc
  Element' e -> element (toElt e)
  -- todo: cancelInner is preventing this from using `behaving`
  -- is there a way to fix that?
  DynamicChildren' (DynamicChildren children) -> behavior \e0 -> makeLemmingEvent \subscribe k0 -> do
    urf <- Ref.new (pure unit)
    cancelInner <- liftST $ Ref.new Object.empty
    ugh <- subscribe e0 \f -> do
      -- fireId1 is only needed for global clean up
      -- if we clean the dyn and removes haven't been called, this will pick it up
      fireId1 <- liftST $ ids interpreter
      k0 $ f (deferPayload interpreter psr.deferralPath (forcePayload interpreter $  List.snoc psr.deferralPath fireId1))
      cancelOuter <- subscribe children \inner -> do
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
        void $ liftST $ Ref.write Listening stageRef
        -- for the inner dyn, we pass it a singleton via `once`
        let
          evt = sample
            ( flatten
                flatArgs
                (snd inner)
                ( psr
                    { scope = myScope
                    , deferralPath = psr.deferralPath <> (fireId1 : fireId2 : List.Nil)
                    , raiseId = \id -> do
                        void $ Ref.modify (append [ id ]) myIds
                    }
                )
                interpreter
            )
            (once children $> identity)
        c1 <- liftST $ subscribe
          evt
          (k0 <<< f)
        void $ liftST $ Ref.modify (Object.insert (show eltsUnsubId) c1)
          cancelInner
        void $ liftST $ Ref.write c1 eltsUnsub
        c0 <- liftST $ subscribe (fst inner) \kid' -> do
          stage <- liftST $ Ref.read stageRef
          case kid', stage of
            Logic lgc, Listening -> do
              cid <- liftST $ Ref.read myIds
              for_ cid (k0 <<< f <<< doLogic lgc interpreter)
            Remove, Listening -> do
              void $ liftST $ Ref.write Closed stageRef
              idRef <- liftST $ Ref.read myIds
              for_ idRef \old ->
                for_ psr.parent \pnt -> k0 $ f
                  ( disconnectElement interpreter
                      { id: old, parent: pnt, scope: myScope }
                  )
              -- we force after the disconnect element
              -- because assumedly the forcing has clean-up-y stuff
              -- so we want to disconnect before we clean up, lest
              -- we try to disconnect something that has already been deleted
              k0 $ f $ forcePayload interpreter $ psr.deferralPath <> (fireId1 : fireId2 : List.Nil)
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
      void $ Ref.modify (_ *> cancelOuter) urf

    pure do
      liftST $ join (Ref.read urf)
      ugh
      (Ref.read cancelInner) >>= foldl (*>) (pure unit)

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
  fx = Element' $ fromElt $ Element go
  where
  go i interpret = behavior \ez -> makeLemmingEvent \subex kz -> do
    urf <- Ref.new (pure unit)
    uu <- subex ez \_ -> do
      av <- Ref.new Nothing
      let
        nn = fx $ Element' $ fromElt $ Element \ii _ -> behavior \e -> makeLemmingEvent \subscribe k -> subscribe e \f -> do
          av' <- Ref.read av
          case av', ii.parent of
            Just r, Just p'
              | r /= p' -> k $ f $ connectToParent interpret { id: r, parent: p' }
            _, _ -> pure unit
      ud <- subex
        ( sample
            ( flatten flatArgs
                nn
                ( i
                    { parent = i.parent
                    , scope = i.scope
                    , raiseId = \s -> do
                        i.raiseId s
                        void $ Ref.write (Just s) av
                    }
                )
                interpret
            )
            ez
        )
        kz
      void $ Ref.modify (_ *> ud) urf
    pure do
      join (Ref.read urf)
      uu

switcher
  :: forall i logic obj
   . (i -> Entity logic obj)
  -> Event i
  -> Entity logic obj
switcher f event = DynamicChildren' $ DynamicChildren $ keepLatest
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
