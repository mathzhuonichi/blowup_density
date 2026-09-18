# Report 369-T17-U1

> The authoritative summary is `## completion (lane 369 r1)` below (r2 name fix
> applied).  The r0 opening summary — which claimed the general existential was
> absent — was stale and has been removed per the re-review.

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
(now the `k = 0` fundamental-ball specializations, renamed with the `_ballZero` suffix) and the general U1 target `latticeLift_iteratedFDeriv_eq` and its `ℝ≥0∞`/`⨆`
corollary `latticeLift_iteratedFDeriv_norm_le_iSup`.
Route: periodicity + `latticeLift_eq_of_ball` for a single-translate neighbourhood,
`Filter.EventuallyEq.iteratedFDeriv` and `iteratedFDeriv_comp_sub`; the zero case is
a `ball z.2 (r-ρ)` of vanishing lattice terms.

**Gap.** None for U1 itself.  Consumers U5 (`correction_derivative_bound`) and U6
(`force_derivative_bound`) are **separate lanes, not started here**; they will
transport the registered `I02` Euclidean bounds through this bridge
(`latticeLift_iteratedFDeriv_eq`).  The general theorem adds one honest
hypothesis over the `k = 0` form — the strict separation `hlt : ρ < r` (satisfied
downstream by `hεspace : ε·θRadius < r`), load-bearing per the negative probe.

**Commands run.** See `research/T17/ATTEMPTS_U1.md` (r1 section) for exact gates:
`lake build …T17.LatticeDeriv` (exit 0), `lake env lean` on the module, the updated
probe `lattice_deriv_closes.lean`, and `axioms_u1.lean` (all exit 0; four
declarations audit `[propext, Classical.choice, Quot.sound]`), two negative probes
(exit 1 as designed), and `make check` (exit 0).

## r2 (API-name fix, 2026-09-18)

Per the lead ruling superseding the earlier "keep names" instruction, the public
API now matches the brief exactly:
- `latticeLift_iteratedFDeriv_eq` — the general arbitrary-`z` `∃ k` shifted-copy
  equality (the U1 target).
- `latticeLift_iteratedFDeriv_norm_le_iSup` — its all-`z` `ℝ≥0∞`/`⨆` corollary.
- `latticeLift_iteratedFDeriv_eq_ballZero` /
  `latticeLift_iteratedFDeriv_norm_le_iSup_ballZero` — the `k = 0` fundamental-ball
  specializations (formerly the bare names).

All probes and `axioms_u1.lean` updated to the new names; every declaration still
`[propext, Classical.choice, Quot.sound]`.  Reviewer probe `rev369_api_name.lean`
now compiles (exit 0), confirming `latticeLift_iteratedFDeriv_eq` carries the
required existential type.
