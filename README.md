# CLASS Agda Playground

This repository defines a subset of the type system of the [CLASS] language.
I wrote this mostly as a way to understand and experiment with session types and linear logic, which I'll be needing for my thesis.
I might also later extend this to include operational semantics.

Here are some of the current limitations:
- Only includes the base muCLL process types.
- Typing contexts are implemented as lists, and thus sessions must be used in the same order they occur in the context. 
- Session name substitution isn't supported in the corecursive constructs.

[CLASS]: http://ctp.di.fct.unl.pt/CLASS/CLASS-thesisPedroRocha.pdf
