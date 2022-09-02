{ name = "purescript-bolson"
, dependencies =
  [ "control"
  , "effect"
  , "hyrule"
  , "fast-vect"
  , "filterable"
  , "foldable-traversable"
  , "foreign-object"
  , "maybe"
  , "prelude"
  , "st"
  , "tuples"
  , "unsafe-coerce"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
