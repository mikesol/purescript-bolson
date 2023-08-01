module Bolson.Core where

import Prelude

import Control.Monad.ST (ST)
import Control.Monad.ST.Global as ST
import Data.Bifunctor (bimap)
import Data.Maybe (Maybe)
import Data.Tuple (Tuple)
import FRP.Event (Event)

type HeadElement' interpreter payload =
  interpreter -> ST ST.Global (Tuple (Array payload) (Tuple (Array payload) (Event payload)))

type Element' interpreter r payload =
  PSR r -> HeadElement' interpreter payload

newtype Element interpreter r payload = Element (Element' interpreter r payload)

data Child (logic :: Type)
  = Remove
  | Logic logic

newtype DynamicChildren logic obj = DynamicChildren
  ( Tuple
      (Array (Tuple (Event (Child logic)) (Entity logic obj)))
      (Event (Tuple (Event (Child logic)) (Entity logic obj)))
  )

newtype FixedChildren logic obj = FixedChildren
  (Array (Entity logic obj))

newtype EventfulElement logic obj = EventfulElement
  (Event (Entity logic obj))

data Scope = Local String | Global

derive instance Eq Scope
derive instance Ord Scope

type PSR r =
  { parent :: Maybe String
  , scope :: Scope
  , raiseId :: String -> ST ST.Global Unit
  | r
  }

data Entity logic obj
  = DynamicChildren' (DynamicChildren logic obj)
  | FixedChildren' (FixedChildren logic obj)
  | EventfulElement' (EventfulElement logic obj)
  | Element' obj

instance Functor (Entity logic) where
  map f = case _ of
    DynamicChildren' (DynamicChildren a) ->
      DynamicChildren' (DynamicChildren (bimap (map (map (map f))) (map (map (map f))) a))
    FixedChildren' (FixedChildren a) ->
      FixedChildren' (FixedChildren (map (map f) a))
    EventfulElement' (EventfulElement a) ->
      EventfulElement' (EventfulElement (map (map f) a))
    Element' a -> Element' (f a)

-- instance Apply (Entity logic) where
--   apply = ap

-- instance Applicative (Entity logic) where
--   pure = Element'

-- instance Bind (Entity logic) where
--   bind m f = case m of
--     DynamicChildren' (DynamicChildren a) ->
--       DynamicChildren' (DynamicChildren (map (map (map f)) a))
--     FixedChildren' (FixedChildren a) ->
--       FixedChildren' (FixedChildren (map (join <<< (map f)) a))
--     EventfulElement' (EventfulElement a) ->
--       EventfulElement' (EventfulElement (map (join <<< (map f)) a))
--     Element' a -> f a

-- instance Monad (Entity logic)

fixed
  :: forall logic obj
   . Array (Entity logic obj)
  -> Entity logic obj
fixed a = FixedChildren' (FixedChildren a)

dyn
  :: forall logic obj
   . Tuple
       (Array (Tuple (Event (Child logic)) (Entity logic obj)))
       (Event (Tuple (Event (Child logic)) (Entity logic obj)))
  -> Entity logic obj
dyn a = DynamicChildren' (DynamicChildren a)

envy
  :: forall logic obj
   . Event (Entity logic obj)
  -> Entity logic obj
envy a = EventfulElement' (EventfulElement a)
