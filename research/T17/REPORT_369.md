# Report 369-T17-U1

Proved the lattice-lift iterated derivative bridge on a ball where the zero lattice copy is the sole supported term. The result states equality of all directional iterated Frechet derivatives and an `ℝ≥0∞` supremum bound.

Lean now contains `NSFormalization.Section3.T17.LatticeDeriv`, using the open spatial-ball neighborhood and Mathlib's eventual derivative congruence. The general existential `k` packaging is not included; the delivered theorem is the requested `k = 0` form.

Validation: module build, probe, and axioms audit were run; the axioms output is limited to `propext`, `Classical.choice`, and `Quot.sound`.
