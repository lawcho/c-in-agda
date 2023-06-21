# A subset of C embedded in Agda
## What's included

* [An imperative Agda EDSL with C-like syntax](src/LIL/Core.agda)
    * `while` loops, variables, arithmetic, `if_then_else`, and more
    * Simple types
    * Lightweight definition using PHOAS
* [Heavy syntactic sugar for C emulation](src/LIL/Sugared.agda)
* [A handful of examples](src/LIL/Examples.agda)
* [An interpreter](src/LIL/Interpreter)
    * Pure, so can run in `agda-mode`
    * Type-safe, thanks to [András Kovács's ST monad implementation](src/ST.agda)
* [An algebraic-effect library](src/Freer/Effect.agda)

## What's *not* included

* Support for C functions
* A pretty-printer to C

## Dependencies

* Agda (tested with `Agda version 2.6.4-fc88821`)
* Agda standard library (tested with git revision `833f0facb24151c82c50bdb2359d648cce9f9661`)

## Copying

Copying welcome.

Unless stated otherwise, all code is own work & public domain.
