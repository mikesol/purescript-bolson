# purescript-bolson

![deku](./bolson.jpeg)

A library to help build frameworks using `purescript-event`.

## Why?

Often times, in an event based architectures, we need to manage the presence and absence of referentially opaque objects. This brings with it a certain set of tasks:

- assigning the objects pointers;
- deleting and dereferencing the objects when they're no longer necessary;
- modifying objects' properties; and
- connecting objects to other objects.

There is very little variation in how these things can be implemented, but there are all sorts of ways to get them wrong. In `purescript-deku`, `purescript-wags`, and `purescript-rito`, while each platform has its own flair, their cores are all implemented using this library.