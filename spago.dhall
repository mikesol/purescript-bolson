{ name = "purescript-bolson"
, dependencies =
  [ "control"
  , "effect"
  , "event"
  , "fast-vect"
  , "filterable"
  , "foldable-traversable"
  , "foreign-object"
  , "heterogeneous"
  , "maybe"
  , "monoid-extras"
  , "prelude"
  , "st"
  , "tuples"
  , "unsafe-coerce"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
