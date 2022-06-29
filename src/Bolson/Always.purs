module Bolson.Always where

import Prelude

import Data.Monoid.Always (class Always, always)
import Effect (Effect)
import Heterogeneous.Mapping (class HMap, class Mapping, hmap)
import Type.Equality (class TypeEquals)
import Type.Proxy (Proxy)

data AlwaysEffect (m :: Type -> Type) = AlwaysEffect (Proxy m)

instance
  ( Always (m2 Unit) (Effect Unit)
  , TypeEquals m1 m2
  ) =>
  Mapping (AlwaysEffect m1) (i -> m2 Unit) (i -> Effect Unit) where
  mapping (AlwaysEffect _) = map always

halways :: forall m i o. HMap (AlwaysEffect m) i o => Proxy m -> i -> o
halways p = hmap (AlwaysEffect p)
