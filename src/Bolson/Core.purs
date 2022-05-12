module Bolson.Core where

import Prelude

import Control.Monad.ST.Class (class MonadST)
import Data.Maybe (Maybe)
import FRP.Event (AnEvent, bus)
import FRP.Event.VBus (class VBus, V, vbus)
import Prim.RowList (class RowToList)
import Type.Proxy (Proxy)

newtype Element interpreter m (lock :: Type) payload = Element
  (PSR m -> interpreter -> AnEvent m payload)

data Child (logic :: Type) (obj :: Type) m (lock :: Type)
  = Insert (Entity logic obj m lock)
  | Remove
  | Logic logic

newtype DynamicChildren logic obj m lock = DynamicChildren
  (AnEvent m (AnEvent m (Child logic obj m lock)))

newtype FixedChildren logic obj m lock = FixedChildren
  (Array (Entity logic obj m lock))

newtype EventfulElement logic obj m lock = EventfulElement
  (AnEvent m (Entity logic obj m lock))

data Scope = Local String | Global

derive instance Eq Scope
derive instance Ord Scope

type PSR m =
  { parent :: Maybe String
  , scope :: Scope
  , raiseId :: String -> m Unit
  }

data Entity logic obj m lock
  = DynamicChildren' (DynamicChildren logic obj m lock)
  | FixedChildren' (FixedChildren logic obj m lock)
  | EventfulElement' (EventfulElement logic obj m lock)
  | Element' obj

fixed
  :: forall logic obj m lock
   . Array (Entity logic obj m lock)
  -> Entity logic obj m lock
fixed a = FixedChildren' (FixedChildren a)

dyn
  :: forall logic obj m lock
   . AnEvent m (AnEvent m (Child logic obj m lock))
  -> Entity logic obj m lock
dyn a = DynamicChildren' (DynamicChildren a)

envy
  :: forall logic obj m lock
   . AnEvent m (Entity logic obj m lock)
  -> Entity logic obj m lock
envy a = EventfulElement' (EventfulElement a)

bussed
  :: forall s m lock logic obj a
   . MonadST s m
  => ((a -> m Unit) -> AnEvent m a -> Entity logic obj m lock)
  -> Entity logic obj m lock
bussed f = EventfulElement' (EventfulElement (bus f))

vbussed
  :: forall s m logic obj lock rbus bus push event u
   . RowToList bus rbus
  => MonadST s m
  => VBus rbus push event u
  => Proxy (V bus)
  -> ({ | push } -> { | event } -> Entity logic obj m lock)
  -> Entity logic obj m lock
vbussed px f = EventfulElement' (EventfulElement (vbus px f))
