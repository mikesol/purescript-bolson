module Bolson.Core where

import Prelude

import Data.Maybe (Maybe)
import FRP.Event (AnEvent)

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
  -- we raise both the ID and the scope
  , raiseId :: String -> Scope -> m Unit
  }

data Entity logic obj m lock
  = DynamicChildren' (DynamicChildren logic obj m lock)
  | Element' obj
