{ name = "bolson"
, dependencies =
  [ "arrays"
  , "control"
  , "fast-vect"
  , "filterable"
  , "foldable-traversable"
  , "foreign-object"
  , "hyrule"
  , "lists"
  , "maybe"
  , "prelude"
  , "record"
  , "st"
  , "tuples"
  , "unsafe-coerce"
  ]
, repository = "https://github.com/mikesol/purescript-bolson"
, license = "Apache-2.0"
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
