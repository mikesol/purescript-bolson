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

import Bolson.Core (BStage(..), Child(..), DynamicChildren(..), Element(..), Entity(..), EventfulElement(..), FixedChildren(..), PSR, Scope(..))
import Control.Lazy as Lazy
import Control.Monad.ST.Class (liftST)
import Control.Monad.ST.Global as Global
import Control.Monad.ST.Global as Region
import Control.Monad.ST.Internal (ST)
import Control.Monad.ST.Internal as Ref
import Control.Monad.ST.Internal as ST
import Control.Monad.ST.Uncurried (STFn1, mkSTFn1, mkSTFn2, runSTFn1, runSTFn2)
import Control.Plus (empty)
import Data.Array as Array
import Data.FastVect.FastVect (toArray, Vect)
import Data.Filterable (compact, filter)
import Data.Foldable (foldMap, foldl, for_, traverse_)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Maybe (Maybe(..))
import Data.Monoid (guard)
import Data.Traversable (traverse)
import Data.TraversableWithIndex (traverseWithIndex)
import Data.Tuple (Tuple(..), fst, snd)
import Data.Tuple.Nested (type (/\), (/\))
import FRP.Event (Event, Subscriber(..), keepLatest, makeEvent, mapAccum, memoize, merge, subscribe)
import FRP.Event.Class (once_)
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
      -> { id :: String, parent :: String, scope :: Scope, raiseId :: String -> ST.ST Region.Global Unit | r }
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
      -> { id :: String, parent :: String, scope :: Scope, raiseId :: String -> ST.ST Region.Global Unit | r }
      -> Entity logic (obj1 payload)
      -> specialization
      -> payload
  , freshStage :: ST Global.Global Int
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
      -> { id :: String, parent :: String, scope :: Scope, raiseId :: String -> ST.ST Region.Global Unit | r }
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
  go psr interpreter = makeEvent \k -> do
    av <- mutAr (toArray toBeam $> { id: "", entity: EventfulElement' (EventfulElement empty) })
    let
      actualized = merge $ mapWithIndex
        ( \ix entity -> toElt entity # \(Element elt) -> elt
            ( psr
                { parent = Nothing
                , scope = scopeF psr.scope
                , raiseId = \id -> unsafeUpdateMutAr ix { id, entity: Element' entity } av
                }
            )
            interpreter
        )
        (toArray toBeam)
    u0 <- subscribe actualized k
    av2 <- Ref.new (pure unit)
    let
      asIds :: Array { id :: String, entity :: Entity logic (obj1 payload) } -> Vect n { id :: String, entity :: Entity logic (obj1 payload) }
      asIds = unsafeCoerce
    idz <- asIds <$> (readAr av)
    let
      -- we never connect or disconnect the referentially opaque node
      -- instead, it is always managed inside a referentially transparent node
      -- that can be properly connected and disconnected
      injectable = map
        ( \{ id, entity } specialization -> fromEltO1 $ Element
            \psr2 itp ->
              makeEvent $ \k2 -> do
                psr2.raiseId id
                for_ psr2.parent \pt -> runSTFn1 k2
                  (giveNewParent itp (RB.build (RB.insert (Proxy :: _ "id") id >>> RB.modify (Proxy :: _ "parent") (const pt)) psr2) entity specialization)
                pure (pure unit)
        )
        idz
      realized = flatten flatArgs psr
        interpreter
        ( -- we will likely need some sort of unsafe coerce here...
          (unsafeCoerce :: Entity logic (obj2 payload) -> Entity logic (obj2 payload))
            ( closure
                ( ( unsafeCoerce
                      :: Vect n (specialization -> (obj1 payload))
                      -> Vect n (specialization -> (obj1 payload))
                  ) injectable
                )
            )
        )
    u <- subscribe realized k
    void $ Ref.write u av2
    -- cancel immediately, as it should be run synchronously
    -- so if this actually does something then we have a problem
    pure do
      u0
      when (not isGlobal) $ for_ (toArray idz) \{ id } -> runSTFn1 k
        (deleteFromCache interpreter { id })
      av2c <- Ref.read av2
      av2c

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
  -> (Vect n (specialization -> Entity logic (obj1 payload)) -> Entity logic (obj2 payload))
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
  go psr interpreter = makeEvent \k -> do
    av <- mutAr (toArray toBeam $> { id: "", entity: EventfulElement' (EventfulElement empty) })
    let
      actualized = merge $ mapWithIndex
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
    u0 <- subscribe actualized k
    av2 <- Ref.new (pure unit)
    let
      asIds :: Array { id :: String, entity :: Entity logic (obj1 payload) } -> Vect n { id :: String, entity :: Entity logic (obj1 payload) }
      asIds = unsafeCoerce
    idz <- asIds <$> (readAr av)
    let
      -- we never connect or disconnect the referentially opaque node
      -- instead, it is always managed inside a referentially transparent node
      -- that can be properly connected and disconnected
      injectable = map
        ( \{ id, entity } specialization -> Element' $ fromEltO1 $ Element
            \psr2 itp ->
              makeEvent \k2 -> do
                psr2.raiseId id
                for_ psr2.parent \pt -> runSTFn1 k2
                  (giveNewParent itp (RB.build (RB.insert (Proxy :: _ "id") id >>> RB.modify (Proxy :: _ "parent") (const pt)) psr2) entity specialization)
                pure (pure unit)
        )
        idz
      realized = flatten flatArgs psr
        interpreter
        ( -- we will likely need some sort of unsafe coerce here...
          ( unsafeCoerce
              :: Entity logic (obj2 payload)
              -> Entity logic (obj2 payload)
          )
            ( closure
                ( ( unsafeCoerce
                      :: Vect n
                           ( specialization
                             -> Entity logic (obj1 payload)
                           )
                      -> Vect n
                           ( specialization
                             -> Entity logic (obj1 payload)
                           )
                  ) injectable
                )
            )
        )
    u <- subscribe realized k
    void $ Ref.write u av2
    -- cancel immediately, as it should be run synchronously
    -- so if this actually does something then we have a problem
    pure do
      u0
      when (not isGlobal) $ for_ (toArray idz) \{ id } -> runSTFn1 k
        (deleteFromCache interpreter { id })
      av2c <- Ref.read av2
      av2c

internalPortalComplexSimple
  :: forall n r logic obj1 obj2 specialization interpreter payload
   . Compare n Neg1 GT
  => Lacks "id" r
  => Lacks "raiseId" r
  => Boolean
  -> (Scope -> Scope)
  -> PortalComplex logic specialization interpreter obj1 obj2 r payload
  -> Vect n (Entity logic (obj1 payload))
  -> ( Vect n
         ( specialization
           -> Entity logic (obj1 payload)
         )
       -> obj2 payload
     )
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
    av <- mutAr (toArray toBeam $> { id: "", entity: EventfulElement' (EventfulElement empty) })
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
    let actualized = merge (map (snd <<< snd) actualized')
    let
      asIds :: Array { id :: String, entity :: Entity logic (obj1 payload) } -> Vect n { id :: String, entity :: Entity logic (obj1 payload) }
      asIds = unsafeCoerce
    idz <- asIds <$> (readAr av)
    let
      -- we never connect or disconnect the referentially opaque node
      -- instead, it is always managed inside a referentially transparent node
      -- that can be properly connected and disconnected
      injectable = map
        ( \{ id, entity } specialization -> Element' $ fromEltO1 $ Element
            \psr2 itp ->
              pure
                $ Tuple
                    ( compact
                        [ psr2.parent <#> \pt ->
                            (giveNewParent itp (RB.build (RB.insert (Proxy :: _ "id") id >>> RB.modify (Proxy :: _ "parent") (const pt)) psr2) entity specialization)
                        ]
                    )
                $ Tuple []
                $ makeEvent \k2 -> do
                    psr2.raiseId id
                    pure (pure unit)
        )
        idz
      Element realized = toEltO2
        ( closure
            (injectable)

        )
    realized' <- realized psr interpreter
    let onSubscribe = join $ Array.cons (fst realized') $ map fst actualized'
    let
      onUnsubscribe = guard (not isGlobal) $ map
        ( \{ id } -> deleteFromCache interpreter { id } )
        (toArray idz)
    pure $ Tuple onSubscribe $ Tuple onUnsubscribe $ makeEvent \k -> do
      u0 <- subscribe actualized k
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

data Stage = Begin | Middle | End

type Flatten logic interpreter obj r payload =
  { doLogic :: logic -> interpreter -> String -> payload
  , ids :: interpreter -> ST Region.Global Int
  , disconnectElement ::
      interpreter
      -> { id :: String, parent :: String, scope :: Scope }
      -> payload
  , toElt :: obj payload -> Element interpreter r payload
  }

flatten
  :: forall r obj logic interpreter payload
   . Flatten logic interpreter obj r payload
  -> PSR r
  -> interpreter
  -> Entity logic (obj payload)
  -> ST Global.Global (Tuple (Array payload) (Tuple (Array (BStage payload)) (Event (BStage payload))))
flatten
  flatArgs@
    { doLogic
    , ids
    , disconnectElement
    , toElt
    }
  psr
  interpreter = case _ of
  FixedChildren' (FixedChildren f) -> do
    o <- traverse (flatten flatArgs psr interpreter) f
    pure $ (map <<< map) merge
      $ foldMap (\(Tuple a (Tuple b c)) -> Tuple a (Tuple b [ c ])) o
  EventfulElement' (EventfulElement e) -> do
    usu0 <- Ref.new []
    usu1 <- Ref.new (pure unit)
    fireId <- ids
    pure $ Tuple [] $ Tuple [BFire fireId] $ makeEvent \k -> do
      s <- subscribe (map (flatten flatArgs psr interpreter) e) \i -> do
        usus0 <- liftST $ Ref.read usu0
        for_ usus0 k
        usus1 <- liftST $ Ref.read usu1
        liftST $ usus1
        Tuple sub (Tuple unsub pld) <- liftST i
        for_ sub k
        void $ liftST $ Ref.write unsub usu0
        u <- liftST $ subscribe pld k
        void $ liftST $ Ref.write u usu1
      pure do
        s
        join (Ref.read usu1)
  Element' e -> element (toElt e)
  DynamicChildren' (DynamicChildren children) ->
    makeEvent \(k :: STFn1 payload Region.Global Unit) -> do
      cancelInner <- Ref.new Object.empty
      cancelOuter <-
        -- each child gets its own scope
        subscribe children \inner ->
          do
            -- holds the previous id
            myUnsubId <- ids interpreter
            myUnsub <- Ref.new (pure unit)
            eltsUnsubId <- ids interpreter
            eltsUnsub <- Ref.new (pure unit)
            myIds <- Ref.new []
            myImmediateCancellation <- Ref.new (pure unit)
            myScope <- Local <$>
              ( case psr.scope of
                  Global -> ids interpreter
                  Local l -> pure l <> pure "!" <> ids interpreter
              )
            stageRef <- Ref.new Begin
            c0 <- subscribe inner \kid' -> do
              stage <- Ref.read stageRef
              case kid', stage of
                Logic logic, Middle -> do
                  curId <- Ref.read myIds
                  traverse_ (\i -> runSTFn1 k (doLogic logic interpreter i)) curId
                Remove, Middle -> do
                  void $ Ref.write End stageRef
                  let
                    mic = do
                      idRef <- Ref.read myIds
                      for_ idRef \old ->
                        for_ psr.parent \pnt -> runSTFn1 k
                          ( disconnectElement interpreter
                              { id: old, parent: pnt, scope: myScope }
                          )
                      myu <- Ref.read myUnsub
                      myu
                      eltu <- Ref.read eltsUnsub
                      eltu
                      void $ Ref.modify
                        (Object.delete myUnsubId)
                        cancelInner
                      void $ Ref.modify
                        (Object.delete eltsUnsubId)
                        cancelInner
                  void $ Ref.write mic myImmediateCancellation
                  mic
                Insert kid, Begin -> do
                  -- holds the current id
                  void $ Ref.write Middle stageRef
                  c1 <- subscribe
                    ( flatten
                        flatArgs
                        ( psr
                            { scope = myScope
                            , raiseId = \id -> do
                                void $ Ref.modify (append [ id ]) myIds
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
                  void $ Ref.modify (Object.insert eltsUnsubId c1)
                    cancelInner
                  void $ Ref.write c1 eltsUnsub
                _, _ -> pure unit
            void $ Ref.write c0 myUnsub
            void $ Ref.modify (Object.insert myUnsubId c0) cancelInner
            mican <- Ref.read myImmediateCancellation
            mican
      pure do
        (Ref.read cancelInner) >>= foldl (*>) (pure unit)
        cancelOuter
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
  go i interpret = makeEvent \k -> do
    av <- Ref.new Nothing
    let
      nn = f $ Element' $ fromElt $ Element \ii _ -> makeEvent \k0 -> do
        (Ref.read av) >>= case _ of
          Nothing -> pure unit
          -- only do the connection if not silence
          Just r -> for_ ii.parent \p' ->
            when (r /= p')
              ( do
                  ii.raiseId r
                  runSTFn1 k0 (connectToParent interpret { id: r, parent: p' })
              )
        pure (pure unit)
    subscribe
      ( flatten
          flatArgs
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
      )
      k

switcher
  :: forall i logic obj
   . (i -> Entity logic obj)
  -> Event i
  -> Entity logic obj
switcher f event = DynamicChildren' $ DynamicChildren $ keepLatest
  $ memoize (counter event) \cenv -> map
      ( \(p /\ n) -> merge
          [ ((const Remove) <$> filter (eq (n + 1) <<< snd) (counter event))
          , once_ event (Insert $ f p)
          ]
      )
      cenv
  where
  counter :: forall a. Event a → Event (a /\ Int)
  counter ev = mapAccum fn 0 ev
    where
    fn a b = (a + 1) /\ (b /\ a)
