# Lane 154-C01-v3-bounds — `energyDifferentialBound` + `l2Bound` (eq:RL2)

Module: `formalization/NSFormalization/Section4/C01/EnergyBounds.lean`
(namespace `NSFormalization.Section4.C01`). Conformance:
`research/C01/axioms_energy_bounds.lean` (every decl `[propext, Classical.choice, Quot.sound]`;
non-vacuity on `A04.zeroSol 1 2` with `memForceR_zero`).

## What was proved

* `energyDifferentialBound (w) (hf) {t} (ht : t ∈ Ioo 0 T) (E') (hderiv : HasDerivAt (fun s => l2Sq (slice w.velocity s)) E' t) : E' + 2·ν·gradientSq (slice w.velocity t) ≤ 2·l2Norm (slice f t)·l2Norm (slice w.velocity t)` — spec `:364-370`.
* `l2Bound (w) (hf) (hν : 0 < ν) {t} (ht : t ∈ Ico 0 T) : l2Norm (slice w.velocity t) ≤ energyBudget a f t` — spec `:383-387` = eq:RL2.
* helpers: `gradientSq`/`forcePrimitive`/`energyBudget` (spec-local defs), `l2Sq_nonneg`,
  `gradientSq_nonneg`, `l2Sq_eq_sq_l2Norm`, `l2Norm_eq_norm_toLp_{velocity,force}`,
  `pairing_le_l2Norm_mul` (Cauchy–Schwarz), `velocityL2Norm_continuousOn`,
  `velocityL2Sq_continuousOn`, `sqrt_energy_le_primitive'` (the generalization).

## Route that worked

`energyDifferentialBound`: `hderiv.unique (energyIdentity_l2Sq w hf ht)` gives
`E' = −2ν·gradientSq + 2·pairing` (the ascription to the local `gradientSq` typechecks by
defeq — `gradientSq z` unfolds to the raw integral `energyIdentity_l2Sq` carries). Then
`E' + 2ν·gradientSq = 2·pairing` by `ring`, and `pairing(u,f) ≤ ‖f‖₂‖u‖₂` by
`pairing_le_l2Norm_mul` (`pairing_eq_inner` + `real_inner_le_norm` +
`l2Norm_eq_norm_toLp_*` which are `norm_toLp_sq_eq_l2Sq` + `Real.sqrt_sq`).

`l2Bound`: generalize the scalar lemma, then apply on `[0,t]`. Endpoint value:
`slice w.velocity 0 = a` (`funext w.initial`), `forcePrimitive f 0 = 0`
(`integral_same`), so `√(E 0) = ‖a‖₂ = energyBudget a f 0` (equality). Continuity of the
energy through 0 is the velocity analogue of `ForceSlices.forceTimeRegularity`. Budget
continuity via `intervalIntegral.continuousOn_primitive_interval`; the FTC derivative via
`intervalIntegral.integral_hasDerivAt_right` with local `ContinuousAt`/`IntervalIntegrable`/
`StronglyMeasurableAtFilter` built from `forceTimeRegularity`'s `ContinuousOn … (Ici 0)`.

## Failed / corrected approaches

* **`sqrt_energy_le_primitive` (the frozen `Paper1` lemma) does not apply directly.** Its
  `hE0 : E 0 = 0`, `hN0 : N 0 = 0` are false here (`E 0 = ‖a‖₂² ≠ 0`, `N 0 = ‖a‖₂ ≠ 0`). The
  generalization keeps the whole antitone-`G` argument and changes only the endpoint: with
  `√(E 0) ≤ N 0`, `E 0 ≤ (N 0)²` (from `Real.sq_sqrt`), so
  `√(E 0 + δ²) ≤ N 0 + δ` (compare squares), giving `G 0 = √(E 0+δ²) − N 0 ≤ δ` — the same
  bound the original gets from `E 0 = N 0 = 0`. Done in-module, no `Paper1/` edit.
* **`by positivity` on `0 < 2·√(E x + δ²)` fails without `hs` in context.** `positivity`
  cannot prove `√(E x+δ²) > 0` on its own (argument sign unknown), but it *does* consult a
  local `hs : 0 < √(E x+δ²)`. I had dropped `hs` when inlining `hpos`; restoring the `have hs`
  before the `div_le_iff₀` fixed it (this is exactly why the frozen `ScalarEnergy` proof keeps
  that `have`).
* **The dissipation-drop `0 ≤ 2·ν·gradientSq` needs `hν`, not `positivity`.** `positivity`
  reports "failed to prove strict positivity" on `2·ν` because `ν`'s sign is a hypothesis, not
  structural; `mul_nonneg (mul_nonneg (by norm_num) hν.le) (gradientSq_nonneg _)` closes it.
* **`heq`/endpoint `rfl`.** After `rw [hfp0, add_zero]` the goal `√(l2Sq a) ≤ l2Norm a` is not
  syntactic `rfl` (l2Norm is a `def`); `exact le_of_eq rfl` (defeq unfold) closes it.
* **No `set` for the carrier-B packagings.** `set U := velocitySliceField w …` would make `U`
  opaque and block the defeq `U.field ≡ slice w.velocity t` that `pairing_eq_inner` /
  `norm_toLp_sq_eq_l2Sq` rely on; the fields are written out inline instead.

## V3 contract plan (`verification/Contracts/V3/EnergyAbsorptionPartial.lean`)

Extend the V2 API (`Contracts/V2/EnergyAbsorptionPartial.lean`) with the two fields
`energyDifferentialBound` (`Spec.lean:364-370`) and `l2Bound` (`Spec.lean:383-387`), stated
token-for-token, via `extends EnergyAbsorptionPartialV2API`. Bridges:

* `l2Bound` — `l2Norm`/`slice`/`energyBudget`/`forcePrimitive` are all `rfl`-equal to the
  implementation defs (`energyBudget`/`forcePrimitive` are the spec-local defs re-stated
  token-for-token in `EnergyBounds.lean`); the field binds by
  `NSFormalization.Section4.C01.l2Bound` directly (drop the contract's `a ∈ initialClassR`).
* `energyDifferentialBound` — the **single non-`rfl` bridge is the same one V2 used for
  `energyIdentity`'s gradient term**: the contract's `gradientSq` (through
  `Contracts.V1.gradientTensor`) equals the module's raw-integral `gradientSq` by
  `PiLp.norm_sq_eq_of_L2` + `coordinateVector = axis` + the `Data.spatialGradient = fderiv`
  `rfl`-facts (i.e. reuse V2's `gradientSq` bridge lemma verbatim). `pairing`, `l2Sq`,
  `l2Norm`, `slice` are `rfl`. `0 < ν` slack.

`Tests.EnergyAbsorptionPartialV3` should be the same 3 axioms; conformance already checked at
`research/C01/axioms_energy_bounds.lean`.
