# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html)

## [0.0.4] - June 1 2022

### Changed

- Returns `doLogic` to the old signature. Note that this will be called multiple times now for multiple `id`-s!
.
## [0.0.3] - June 1 2022

### Changed

- Avoids the need for flatten to wrap things in a neutral element. This makes it more flexible, which allows for easier embedding when it acts as a _producer_, meaning that it produces an arbitrary element that we don't know how to deal with. In this case, imposing the obligation to wrap it on the consumer makes the abstraction leaky, as we want the consumer to be polymorphic.

## [0.0.2] - May 12 2022

### Changed

- Provides a specialization for portal that allows applications to thread specialization information.

## [0.0.1] - May 12 2022

### Changed

- Gets rid of currying for many functions.

## [0.0.0] - May 11 2022

### Added

- An FRP application builder.