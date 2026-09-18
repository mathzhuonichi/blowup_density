# Report 369-T17-U1

Proved the lattice-lift iterated derivative bridge on a ball where the zero lattice copy is the sole supported term. The result states equality of all directional iterated Frechet derivatives and an `ℝ≥0∞` supremum bound.

Lean now contains `NSFormalization.Section3.T17.LatticeDeriv`, using the open spatial-ball neighborhood and Mathlib's eventual derivative congruence. The general existential `k` packaging is not included; the delivered theorem is the requested `k = 0` form.

Validation: module build, probe, and axioms audit were run; the axioms output is limited to `propext`, `Classical.choice`, and `Quot.sound`.

## completion (lane 369 r1)

**What was proved.** The full U1 target: for a chart correction `w` with each
spatial slice supported in `ball x₀ ρ`, `r + ρ ≤ 1` and `ρ < r`, at *every*
spacetime point `z`, order `n` and direction tuple `u`, the lattice lift's
iterated Fréchet derivative equals — in norm — that of the single nearby Euclidean
copy `w (· - (0, latticeVector k))`:
`‖iteratedFDeriv ℝ n (latticeLift w) z u‖ = ‖iteratedFDeriv ℝ n w (z - (0, latticeVector k)) u‖`,
existentially in `k`, with the no-copy/zero case (`k = 0`, both sides `0`); plus
the all-`z` `ℝ≥0∞`/`⨆` corollary in the norm spelling
`CorrectionAPI.correction_derivative_bound` uses.

**What is in Lean now.** `NSFormalization.Section3.T17.LatticeDeriv` exports four
theorems, each `[propext, Classical.choice, Quot.sound]`:
`latticeLift_iteratedFDeriv_eq` and `latticeLift_iteratedFDeriv_norm_le_iSup`
(the `k = 0` fundamental-ball forms, unchanged from r0) and the new general
`latticeLift_iteratedFDeriv_eq_shift` and `latticeLift_iteratedFDeriv_norm_le_iSup'`.
Route: periodicity + `latticeLift_eq_of_ball` for a single-translate neighbourhood,
`Filter.EventuallyEq.iteratedFDeriv` and `iteratedFDeriv_comp_sub`; the zero case is
a `ball z.2 (r-ρ)` of vanishing lattice terms.

**Gap.** None for U1 itself.  Consumers U5/`correction_derivative_bound` and
U6/`force_derivative_bound` transport the registered `I02` Euclidean bounds through
`_eq_shift`; those are separate lanes.  The general theorem adds one honest
hypothesis over the `k = 0` form — the strict separation `hlt : ρ < r` (satisfied
downstream by `hεspace : ε·θRadius < r`), load-bearing per the negative probe.

**Commands run.** See `research/T17/ATTEMPTS_U1.md` (r1 section) for exact gates:
`lake build …T17.LatticeDeriv` (exit 0), `lake env lean` on the module, the updated
probe `lattice_deriv_closes.lean`, and `axioms_u1.lean` (all exit 0; four
declarations audit `[propext, Classical.choice, Quot.sound]`), two negative probes
(exit 1 as designed), and `make check` (exit 0).
