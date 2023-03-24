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

newtype Element interpreter r payload = Element
  (PSR r -> interpreter -> Event payload)

data Child (logic :: Type) (obj :: Type)
  = Insert (Entity logic obj)
  | Remove
  | Logic logic

newtype DynamicChildren logic obj = DynamicChildren
  (Event (Event (Child logic obj)))

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
  , raiseId :: String -> ST.ST Region.Global Unit
  | r
  }

data Entity logic obj
  = DynamicChildren' (DynamicChildren logic obj)
  | FixedChildren' (FixedChildren logic obj)
  | EventfulElement' (EventfulElement logic obj)
  | Element' obj

fixed
  :: forall logic obj
   . Array (Entity logic obj)
  -> Entity logic obj
fixed a = FixedChildren' (FixedChildren a)

dyn
  :: forall logic obj
   . Event (Event (Child logic obj))
  -> Entity logic obj
dyn a = DynamicChildren' (DynamicChildren a)

envy
  :: forall logic obj
   . Event (Entity logic obj)
  -> Entity logic obj
envy a = EventfulElement' (EventfulElement a)

bussed
  :: forall logic obj a
   . ((a -> Effect Unit) -> Event a -> Entity logic obj)
  -> Entity logic obj
bussed f = EventfulElement' (EventfulElement (bus f))

vbussed
  :: forall logic obj rbus bus push event
   . RowToList bus rbus
  => VBus rbus push event
  => Proxy (V bus)
  -> ({ | push } -> { | event } -> Entity logic obj)
  -> Entity logic obj
vbussed px f = EventfulElement' (EventfulElement (vbus px f))
