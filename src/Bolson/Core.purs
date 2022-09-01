module Bolson.Core where

import Prelude

import Control.Monad.ST as ST
import Control.Monad.ST.Global as Region
import Data.Maybe (Maybe)
import Effect (Effect)
import FRP.Event (Event, bus)
import FRP.Event.VBus (class VBus, V, vbus)
import Prim.RowList (class RowToList)
import Type.Proxy (Proxy)

newtype Element interpreter r (lock :: Type) payload = Element
  (PSR r -> interpreter -> Event payload)

data Child (logic :: Type) (obj :: Type) (lock :: Type)
  = Insert (Entity logic obj lock)
  | Remove
  | Logic logic

newtype DynamicChildren logic obj lock = DynamicChildren
  (Event (Event (Child logic obj lock)))

newtype FixedChildren logic obj lock = FixedChildren
  (Array (Entity logic obj lock))

newtype EventfulElement logic obj lock = EventfulElement
  (Event (Entity logic obj lock))

data Scope = Local String | Global

derive instance Eq Scope
derive instance Ord Scope

type PSR r =
  { parent :: Maybe String
  , scope :: Scope
  , raiseId :: String -> ST.ST Region.Global Unit
  | r
  }

data Entity logic obj lock
  = DynamicChildren' (DynamicChildren logic obj lock)
  | FixedChildren' (FixedChildren logic obj lock)
  | EventfulElement' (EventfulElement logic obj lock)
  | Element' obj

fixed
  :: forall logic obj lock
   . Array (Entity logic obj lock)
  -> Entity logic obj lock
fixed a = FixedChildren' (FixedChildren a)

dyn
  :: forall logic obj lock
   . Event (Event (Child logic obj lock))
  -> Entity logic obj lock
dyn a = DynamicChildren' (DynamicChildren a)

envy
  :: forall logic obj lock
   . Event (Entity logic obj lock)
  -> Entity logic obj lock
envy a = EventfulElement' (EventfulElement a)

bussed
  :: forall lock logic obj a
   . ((a -> Effect Unit) -> Event a -> Entity logic obj lock)
  -> Entity logic obj lock
bussed f = EventfulElement' (EventfulElement (bus f))

vbussed
  :: forall logic obj lock rbus bus push event
   . RowToList bus rbus
  => VBus rbus push event
  => Proxy (V bus)
  -> ({ | push } -> { | event } -> Entity logic obj lock)
  -> Entity logic obj lock
vbussed px f = EventfulElement' (EventfulElement (vbus px f))
