# [Comparator](https://github.com/leanprover/comparator) challenges

Install `landrun`, `lean4export`, and `nanoda_bin`, and make them available on `PATH`. Then, from the repository root:

```sh
lake exe cache get
lake exe comparator ComparatorChallenges/NavierStokes.json
lake exe comparator ComparatorChallenges/Euler.json
```

Thank you to the [Formal Conjectures](https://google-deepmind.github.io/formal-conjectures/) authors for their [Lean formalization of the Navier–Stokes problem statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Millenium/NavierStokes.lean), which we adapted for these Comparator challenges.
