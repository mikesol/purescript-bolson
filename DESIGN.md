# Design

PureScript Bolson is a FRP framework builder. This document exists to explain some of the main architectual features of Bolson. Its main audiences are:

1. Folks that would like to hack on Bolson or any of the frameworks (Rito, Deku, Ocarina) that are built on top of it.
2. Folks that would like to build their own FRP frameworks in PureScript.

## Why do we need a framework builder?

Frameworks exist to help developers build things. So why do we need a framework like Bolson to build frameworks? When working with FRP, and especially with the [SDOM flavor of FRP](https://blog.functorial.com/posts/2018-03-12-You-Might-Not-Need-The-Virtual-DOM.html), dealing with referentially opaque elements is _really hard_. A referentially opaque element is something that, at a basic level, points to mutable memory.

1. In the DOM, this could be a `div` node.
2. In Web Audio, this could be a `gain` node.
3. In WebGL, this could be a shader.

What these all have in common is that, once created, they can be modified.

1. Our `div` can have its attributes set.
2. Our `gain` node can have its volume changed.
3. Our `shader` can have uniforms sent to it.

In all of these cases, we need a way to reference _and_ mutate the object. Boslon provides a set of primitives to make this hard problem less hard.

## The Element and the Entity

Bolson's main units of work are the `Element` and the `Entity`. In all of the frameworks that build on top of it, you'll either use these directly or create newtype wrappers around both `Element` and `Entity`.

> By using `Element` and `Entity`, you get certain powerful memory management behaviors "for free", which allows you to focus more on framework building and less on questions like "did I actually delete that shader?" or "I've removed my `div` from its parent, but is it still receiving events?".

### Element

The type of `Element` is defined as follows:

```purescript
newtype Element interpreter m (lock :: Type) payload = Element
  ({ parent :: Maybe String
    , scope :: Scope
    , raiseId :: String -> m Unit
    }
  -> interpreter
  -> AnEvent m payload
  )
```

It follows a general pattern in FRP that says "If you give me X, I'll give you Y." In this case, it's saying "If you give me a parent (that may or may not exist), a logical scope, a callback to report my `id`, and a way to interpret commands, I'll give you an event that emits some payload relevant to your framework." Let's break down all four parts of that contract.

1. The **parent** is the most opinionated of these four parameters, and represents the potential existence of a heirarchical relationship between an element and its parent(s) (thus the `Maybe` type).
  1. In a DOM, when we have `<ul><li>Hello</li></ul>`, the `ul` is the _parent_ of the `li`.
  2. In web audio, when we connect a sine-wave oscillator to a gain node, the gain node can be considered the oscilator's parent.
  3. In WebGL, when a transform matrix like a perspective camera is passed as a uniform to several different shaders, we can consider that matrix to be a parent
2. The **scope** is a logical memory group. If an element in a scope is deleted by the FRP framework, the other elements will be safely deleted.
3. The **raiseId** callback is a way for external elements (for example parents) to know the ID of newly created elements (for example, children).
4. The **interpreter** is a store of commands that is passed back to the framework when Bolson needs specific behavior. For example, it may ask the framework to assign a new parent, and it will pass it the interpreter that the framework gave it.

As a FRP-framework builder, you don't need to handle any of the internal complexities of working with this type. Once you use it (or a `newtype` around it), Bolson kicks in and does a host of thorny, corner-case heavy, highly-optimized state management.

### Entity

If the `Element` is the base unit of work in Bolson, an `Entity` represents how elements compose together. Frameworks will rarely expose the ability to create `Element`-s directly - instead, frameworks often expose an API to create an `Entity` with 0 or more `Element` inside of it.

An `Entity` should _always_ be created using one of the four entity-creation helper functions.

1. `elt` is used to turn an `Element` into an `Entity`. It is a singleton function.
2. `fixed` is used to turn an array of `Element`-s into an entity. This is useful, for example, when assigning a fixed number of nodes to a `div` if you're using Bolson to build a UI framework.
3. `envy` is used to turn `AnEvent` emitting `Entity`-s into an `Entity`. **NB**: `envy` has the behavior of `keepLatest`, so when a new entity is emitted, the old entity is replaced.
4. `dyn` is used to turn a nested event of child-management instructions into an `Entity`. This is useful when working with dynamic collections like a TODO MVC. The _outer_ emits streams of instructions, and the inner event is a logical instruction within a specific stream. Child instructions can be one of three things:
  1. `Insert` a child into a parent.
  2. Perform `Logic` on a child (for example, moving it within its parent).
  3. `Remove` a child from a `parent`.

## Control

Now that we have defined our two base types, `Element` and `Entity`, we can control them with Bolson's control functions. Bolson has three control primitives, and they are quite universal: the frameworks that use them (Deku, Ocarina, Rito...) are able to implement 95% of their logic on top of these primitives. They are **flatten**, **portal** and **fix**.

### Flatten

The `flatten` function is the most-used Bolson control function. It takes an entity and _flattens_ it to an event of type `AnEvent m payload`. Why the name "flatten"? Because `payload` represents atomic instructions in a given framework - the structure of the entity is "flattened" to a single event stream. For example, if you're building a DOM framework, you may construct a giant tree of elements using `dyn`, `fixed, `envy` and `elt`, and `flatten` will take this stream and turn it into a _single event_ emitting instructions of type `payload`. These instructions will be theings like "create an element", "set an attribute", "delete an element" etc. You don't need to worry about elements' ids, whether or not an element is actually present, or a host of other state management issues. Things "Just Work™" thanks to `flatten`'s internal logic.

### Portal

The `portal` family of functions deals with referentially-opaque elements that are used 0 or more times. Here are some important use cases of portal:

1. In the DOM, we may want to remove an element from one part of the DOM and attach it to another part of the DOM. This is common, for example, when working with video content on scrolling pages. A video may occupy a banner-width `div` on the top of the page and, as you scroll down, it seamlessly moves to an inset on the bottom-left.2. In Web Audio, we may want a single playback buffer to be treated by multiple DSP chains before it is mixed together.
3. In WebGL, we may want to use the same uniform for many shaders, for example when working with a perspective matrix.

Portal functions have slightly different signatures depending on what memory tradeoffs you'd like and how many elements you're working with, but the basic signature is always the same:

```purescript
entity -> (entity -> entity) -> entity
```

That is, if you create an entity and a scope in which the entity is used 0 or more times, Bolson will create an entity.

### Fix

`fix` is useful in frameworks that have fixed points, aka feedback loops. In WebGL, this can be a scene with two mirrors point at each other and an object in between them. In Web Audio, this can be an echo effect.

The simplified signature of `fix` is:

```purescript
(entity -> entity) -> entity
```

The first closure takes itself as an argument and returns itself. If this sounds like a head scratcher, you're not alone! Most fixed-point combinators have this signature. In fact, you can call `fix identity` to get an infinite loop (in Web Audio, this would be the equivalent of a gain node plugged into itself).

## Conclusion

Bolson is an FRP framework builder that provides two primitives, `Element` and `Entity`, and three control functions, `flatten`, `portal`, and `fix`. Using these building blocs, you can bootstrap an entire FRP framework for a given domain (animation, audio, the DOM) without having to worry about a whole class of problems that arise when dealing with referentialy-opaque objects in a pure functional language.

It may seem like overkill to provide framework builders with their own framework builder. Bolson arose from eliminating runaway code duplication in `deku` and `ocarina`, and then was used to implement `rito` from the ground up. My hope is that these three frameworks serve as a testament to the utility of this approach and that, when building your own FRP frameworks, you'll find some of the ideas in `bolson` useful and perhaps even elect to use it yourself.

Happy framework building!
