{ name = "purescript-bolson"
, dependencies =
  [ "control"
  , "effect"
  , "fast-vect"
  , "filterable"
  , "foldable-traversable"
  , "foreign-object"
  , "hyrule"
  , "maybe"
  , "prelude"
  , "record"
  , "st"
  , "tuples"
  , "unsafe-coerce"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
