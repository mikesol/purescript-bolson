let upstream =
      https://github.com/purescript/package-sets/releases/download/psc-0.15.7-20230227/packages.dhall
        sha256:0168e165b4cdb40ab6f7e01448075680097791c8d98f96d684b20d1eef96f3d0

in  upstream
  with hyrule =
    { dependencies =
      [ "aff"
      , "avar"
      , "free"
  , "arrays"
  , "control"
  , "datetime"
  , "effect"
  , "either"
  , "filterable"
  , "foldable-traversable"
  , "foreign-object"
  , "js-timers"
  , "maybe"
  , "newtype"
  , "now"
  , "ordered-collections"
  , "prelude"
  , "refs"
  , "st"
  , "tuples"
  , "unsafe-coerce"
  , "unsafe-reference"
  , "web-events"
  , "web-html"
  , "web-uievents"
      ]
    , repo = "https://github.com/mikesol/purescript-hyrule.git"
    , version = "ef74fae"
    }