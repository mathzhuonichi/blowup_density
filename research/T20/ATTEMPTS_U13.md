# T20 U13 attempts — assembly and registration

## Successful route

- Installed the canonical constants without a further radius shrink:
  `c := criticalSmallnessH1`, `C₀ := criticalTrilinearConst`,
  `C₁ := h1TrilinearConst`, `CH1 := 2`, and
  `Ccriterion := hTwoConst ^ 2 * CH1`.
- Used `yBound_of_le criticalSmallnessH1_le_half`; the remaining ten
  mathematical fields are the exact landed U1–U12 theorems, including lane
  452's `constantTransportCommutesLambda`.
- Transported each field mentioning the contract copy of `ClassicalSolutionT`
  through `Bindings.TorusLocalTheory.ofContract`.  Transported the final
  lifespan equality through `Bindings.TorusLocalTheory.maximalLifespanT_eq`, as
  prescribed by `research/T21/RECONCILIATION.md`.
- Proved non-vacuity using the T11 compact positive-time bump times a nonzero
  constant spatial vector.  A concrete half-order datum path proves its
  `criticalRho` finite; choosing
  `ν = ((criticalRho g).toReal + 1) / criticalSmallnessH1` gives strict
  smallness and the assembled global field gives infinite lifespan.

## Resolved registration collision

The lane brief requested `Contracts/V1/CriticalRegularity.lean`,
`Bindings/CriticalRegularity.lean`, `Tests/CriticalRegularity.lean`, and
`checkedCriticalRegularity`.  All four names are already the frozen registered
R43 whole-space contract (`R43.critical_regularity`).  Reusing them would alter
an existing V1 specification and fail `check_contracts.py --base-ref`.

The additive torus modules are therefore named `CriticalRegularityT.lean`, in
namespace `...CriticalRegularityT`, with public test declaration
`checkedCriticalRegularityT`.  The requested registry id remains exactly
`T03.critical_regularity`.  The existing R43 files and registry entry are
unchanged.

## Transient errors resolved

- Direct `lake env lean Bindings/CriticalRegularity.lean` initially imported a
  stale build artifact from the pre-existing R43 module.  Building the new
  module target made the collision explicit and led to the additive `T` suffix.
- The non-vacuity proof initially used a nonexistent
  `coordinateVector_ne_zero`; evaluating coordinate zero gives the elementary
  proof.
- `field_simp` needed `criticalSmallnessH1_pos.ne'`, and the ENNReal strict
  inequality was stabilized as an explicit `ofReal_toReal` calculation.

No residual proposition, placeholder, or missing local-existence input remains.
