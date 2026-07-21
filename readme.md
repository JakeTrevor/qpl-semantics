# Quantum Semantics

This repo contains some ongoing work into mechanising the semantics of quantum programming languages.
It's liable to change a lot, as it's still fairly early days.

Currently, I have:
- Some work on permutations (`Semantics.Permutation`)
- Some quantum information theory (`Semantics.Quantum`)
- A bunch of infrastructure for strictly positive modular data types (`Semantics.container` and `Semantics.denotational`)
- A formalisation of lenses (`Semantics.lens`)


In progress:
- A formalisation of generalised ensemble states (GES)
- Various language fragments that can be glued together, with automatic (typeclass-based) inference of the semantics of the result.