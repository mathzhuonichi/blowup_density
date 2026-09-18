# T24 spec lane (350) — attempts and decisions

Statement-only lane.  No proofs attempted; the record below is the copy policy,
the ambient-space ruling, and the two falsities corrected from draft B.

## Copy header (verbatim vocabulary block)

`research/T24/Spec.lean:36-943` (from `noncomputable section` through
`end BlowupDensity.T15.Draft`) is byte-for-byte identical to
`research/T15/Spec.lean:17-924` (verified by `diff`).  It provides, in their own
namespaces:

- `T10.Draft` (from `research/T10/Spec.lean:255-268,272-359,364-387,393-411`):
  `IsPeriodicSobolevPath`, `forceSobolevENormT`, `MemForceT`, `forceClassT`,
  `pressureMeanT`, `PressureGaugeT`, `normalizePressureT`, `ClassicalSolutionT`,
  `energyEssSupT`, `energyGradientT`, `energyENormT`.
- `T13.Spec` (from `research/T13/Spec.lean:168-205,213-312`): `fundamentalCube`,
  `latticeVector`, `periodize`, `LocalizationAPI` (+ kernels/Gagliardo helpers).
- `T14.Draft` (from `research/T14/Spec.lean:44-108,120-132`): `accumulatedForce`,
  `PacketEnergyAPI`, `PacketImportAPI`, `PacketImportFamily`.
- `T15.Draft`: `scaledStartTime … normalizedScaledPressure`, `PlacementData`,
  `ScalingAPI` and their mixed/Sobolev auxiliaries, plus the `example … := rfl`
  drift checks against the registered `Contracts.V1` scaling defs.

Everything registered (`Contracts.V1.{Data,Packet,TorusData,Scaling,HomogeneousNorm}`)
is imported, never copied.  T24a uses only the registered `Contracts.V1` packet
vocabulary; it opens none of the copied namespaces.

## Ambient-space ruling (the finding neither draft got right)

`prop:affine` (`:669-671`) fixes the localized solution of Theorem 1.1 and a
cylinder `Q=B₀×(τ₀,τ₁)` with `B₀⋐ℝ³` and `0<τ₀<τ₁<1`.  This is a **whole-space**
statement with terminal time literally `1`, not a torus one.  Draft A left it
unspecified (`cylinder_hypotheses : Prop`); draft B re-based it onto
`ClassicalSolutionT ν 0 baseForce terminal` with a free `terminal` — a silent
change of ambient space.  Ruling (`RECONCILIATION.md §2`, approved §0): index
`AffineVariationAPI` by the registered `PacketAPI ν`, terminal `1`, whole-space
`navierStokesResidual`/`spatialDivergence`/`CompactPositiveTimeSupport`/
`SpeedUnboundedAtOne`/`energyENorm 1`.  So the three leaves live in two ambient
spaces: T24a whole space (T14 only), T24b/T24c torus (T10+T13+T14+T15 / T10).

## Two falsities corrected from draft B

1. `zero_from_rest` — B concluded `S.velocity = fun _ ↦ 0` (a whole-function
   equality).  `ClassicalSolutionT` constrains `velocity` only on the slab
   `Ico 0 T ×ˢ univ`; values at `t<0` are free, so a record with nonzero
   negative-time velocity exists and B's field is false.  Corrected to
   `∀ t ∈ Ico 0 T, ∀ x, S.velocity (t,x) = 0` (`:728`, "on its classical lifespan").
2. `component_support`/`component_force_support` — B wrote
   `tsupport ((component j).velocity (t,·)) ⊆ ball j`.  The periodized fields are
   spatially unit-periodic, so their `ℝ³`-`tsupport` contains every lattice
   translate and is never inside one ball.  Corrected to the fundamental-cube
   form `∀ t, ∀ x ∈ fundamentalCube, x ∉ ball j → … = 0` (the form T15's
   `velocity_singleCopy`/`force_singleCopy` + `eps_space` actually deliver).

## Seminorm choice

`ckSeminormE` is `∑_{k≤m} ⨆_{z∈K} ‖iteratedFDeriv ℝ k f z‖ₑ` in `ℝ≥0∞`.  B used a
real `sSup (Set.range …)`; Mathlib's real `sSup` of an unbounded range is `0`, so
an unbounded difference would satisfy `Tendsto … (𝓝 0)` vacuously.  `K` is
`tsupport b` itself (both differences vanish off `supp b`); the unused
`_hK : IsCompact K` argument is dropped.

## Elaboration

`cd verification && lake env lean ../research/T24/Spec.lean` → exit 0, no output
(0 errors, 0 warnings).  Anti-stub grep `': *True|:= *0$|→ *True'` is empty.
