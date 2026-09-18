# Report 385 — T17 U5/U6 derivative bounds

## 1. What was proved

The two halves of `eq:derivativebounds` are proved for T17's concrete
correction data.  `correction_derivative_bound` gives the mixed `j`-time,
`m`-space estimate
`C_{j,m} (ε⁻¹)^(2j+m)` for every spacetime point and every spatial direction
tuple of norm at most one.  `force_derivative_bound` gives the spatial order
`m` estimate `C_m (ε⁻¹)^(2+m)` for the concrete T17 correction force.

## 2. What Lean contains now

`CorrectionDeriv.lean` exports `correctionDerivConst`, its nonnegativity
theorem, and `correction_derivative_bound`.  `ForceDeriv.lean` exports the
parallel `forceDerivConst`, nonnegativity theorem, and
`force_derivative_bound`.  The constants are exactly `Classical.choose` of the
Paper1 constants.  U5 transports through `correctionData_correction`; U6
transports through `force_eq`; both then use the arbitrary-point
`latticeLift_iteratedFDeriv_eq` and apply the relevant Euclidean Paper1 bound
at the selected shifted point.  The probe restates both concrete Spec fields
and closes each directly by `exact`, then instantiates them on T16 cutoffs at a
nonzero constant divergence-free periodic reference.

## 3. Gap

There is no U5/U6 proof gap.  Both Paper1 bounds genuinely require
`hv : ContDiff ℝ ∞ v`, so both concrete theorems expose it.  Final T17 assembly
must supply that global smoothness premise and `D.ε₀ ≤ 1`; this is the existing
U3/G1 assembly issue, not a residual analytic lemma in this lane.

## 4. Commands and results

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T17.CorrectionDeriv NSFormalization.Section3.T17.ForceDeriv` — success.
- `lake env lean` on both modules, `research/T17/probes/derivative_bounds_closes.lean`, and `research/T17/axioms_u5u6.lean` — success.
- The six module declarations and three probe declarations each print exactly `[propext, Classical.choice, Quot.sound]`.
- `make check` — success.
