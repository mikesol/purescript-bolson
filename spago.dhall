{ name = "purescript-bolson"
, dependencies =
  [ "control"
  , "effect"
  , "fast-vect"
  , "filterable"
  , "foldable-traversable"
  , "foreign-object"
  , "heterogeneous"
  , "hyrule"
  , "maybe"
  , "monoid-extras"
  , "prelude"
  , "st"
  , "tuples"
  , "type-equality"
  , "unsafe-coerce"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
