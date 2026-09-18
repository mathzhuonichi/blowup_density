# T17 U4 — attempts, decisions, residuals (lane 375)

Target: the six force-profile fields of `CorrectionAPI`
(`research/T17/Spec.lean:805-837`) over the canonical T10/T15/T16 vocabulary,
via the Euclidean reuse of `Paper1/CorrectionForceProfile.lean`, stacked on lane
370's `Section3/T17/CorrectionProfile.lean`.

Delivered module: `formalization/NSFormalization/Section3/T17/ForceProfile.lean`
(namespace `NSFormalization.Section3.T17`).  Builds with 0 errors / 0 warnings;
every declaration prints exactly `[propext, Classical.choice, Quot.sound]`
(`research/T17/axioms_u4.lean`).  Probe:
`research/T17/probes/force_profile_closes.lean`.

## What worked (the route as delivered)

1. **The `def` bridge `rescaledForceProfile = forceProfile` needs one chain-rule
   step (not `rfl`).**  Unlike U3's potential bridge, the Spec's
   `rescaledForceProfile` (`Spec.lean:712`) writes its `(w·∇)v`-type summand as
   `ε² • spatialDerivative v (T+ε²σ, x₀+εz) (W z)` — the derivative of the *bare*
   reference `v` at the **physical** point, with an explicit `ε²`.  Paper1's
   `forceProfile_eq_operators` (`CorrectionForceProfile.lean:129`) instead uses
   `ε • spatialDerivative (slice referenceProfile ε) t x (W(t,x))` — the
   derivative of the *rescaled* reference `V_ε`, with a single `ε`.  The two are
   equal by the chain rule for `V_ε(z) = v(T+ε²σ, x₀+εz)`:
   `spatialDerivative V_ε t x = ε • spatialDerivative v (T+ε²t) (x₀+εx)`
   (`spatialDerivative_rescaledReference`, proved from
   `HasFDerivAt (fun y => x₀+ε•y) (ε • id) x = ((hasFDerivAt_id x).const_smul ε).const_add x₀`
   composed with the slice derivative; `.comp x`, `.fderiv`).  One extra `ε` gives
   `ε² • sd v … = ε • sd V_ε …` (`rescaledReference_spatialDerivative_smul`, via
   `smul_smul` + `ε·ε=ε²`).  With this, the def bridge is
   `rw [forceProfile_eq_operators, hW, hV]; simp only [rescaledForceProfile];
   rw [rescaledReference_spatialDerivative_smul …, smul_add, smul_add]; abel`
   where `hW : slice (profile …) ε = rescaledCorrectionProfile …` (lane 370
   bridge, funext) and `hV : slice (referenceProfile …) ε = rescaledReference …`
   (`rfl`).  The three `ε`-scaled advective terms differ only by the summand
   order (Spec: `(v·∇)W, (w·∇)v, (w·∇)W`; Paper1: `(w·∇)v, (v·∇)W, (w·∇)W`), so
   `abel` closes after distributing `smul_add`.

2. **smooth / support / uniform are transports through the bridge** (identical
   shape to U3):
   * `force_profile_smooth`: rewrite `H_ε = fun z => forceProfile (ε,z)`, then
     `(forceProfile_smooth ν hv x₀ T hθ hη).comp (by fun_prop) |>.contDiffOn`.
   * `force_profile_support`: `closure_minimal` into `Icc(-2,2) ×ˢ closedBall 0
     θRadius`, chaining `forceProfile_support` (`⊆ tsupport (profile …)`) then
     `profile_support`, then T16 `theta/eta_support`.
   * `forceProfileConst := Classical.choose (forceProfile_uniform_derivative_bound …)`;
     `_nonneg := (choose_spec …).1`; `force_profile_uniform` = bridge + lane 370's
     `norm_iteratedFDeriv_slice_le` (reused verbatim) + `(choose_spec …).2` on
     `ε ∈ Icc 0 1` (from `ε ∈ Ioc 0 D.ε₀` and `D.ε₀ ≤ 1`).

3. **identity (chart force)** (`physicalForce_eq_rescaledForceProfile`): the
   affine `inverseScale ε` of the correction chart cancels
   (`inverseScale_correctionChartPoint`: `inverseScale ε (correctionChartPoint x₀
   T ε z − (T,x₀)) = z` for `ε ≠ 0`, one `inverseScale_apply` + `add_sub_cancel_left`
   + `inv_mul_cancel₀` per coordinate), so
   `physicalForce_eq_profile` (`:185`) followed by the reverse def bridge gives
   `Source.correctionForce ν v (physicalCorrection …) (correctionChartPoint x₀ T ε z)
      = (ε²)⁻¹ • rescaledForceProfile ν v x₀ T ε D z`.

## Residual gaps (honest partial)

**G0 — `force_profile_identity` is proved for the CHART force, not the Spec's
`correctionForce ν v D ε` (over `D.correction`).**  The Spec field
(`Spec.lean:834-837`) is
```
∀ ε ∈ Ioc 0 D.ε₀, ∀ z ∈ fixedProfileCylinder D,
  correctionForce ν v D ε (correctionChartPoint place ε z)
    = (ε ^ 2)⁻¹ • rescaledForceProfile ν v place ε D z
```
where `correctionForce ν v D ε` (`Spec.lean:725`, restated here as `T17.correctionForce`)
is built from the abstract T16 correction `D.correction ε`.  This module proves
```
Source.correctionForce ν v (physicalCorrection v x₀ T D.θ D.η ε)
    (correctionChartPoint x₀ T ε z)
  = (ε ^ 2)⁻¹ • rescaledForceProfile ν v x₀ T ε D z
```
(`physicalForce_eq_rescaledForceProfile`).  The **exact residual lemma** the
assembly (U12) must supply to close the Spec field, given a
`LocalPotentialAPI v U K x₀ r T δ D` witness `hpot` (the `CorrectionAPI.potential`
field):
```
force_eq_chart :
  ∀ ε ∈ Ioc (0:ℝ) D.ε₀, ∀ z ∈ fixedProfileCylinder D,
    correctionForce ν v D ε (correctionChartPoint x₀ T ε z)
      = Source.correctionForce ν v (physicalCorrection v x₀ T D.θ D.η ε)
          (correctionChartPoint x₀ T ε z)
```
Then `force_profile_identity` = `force_eq_chart` ▸ `physicalForce_eq_rescaledForceProfile`.
`force_eq_chart` decomposes into:
* (a) **operator reorder** `correctionForce ν v D ε p = Source.correctionForce ν v
  (D.correction ε) p` for all `p`.  The T17 operator (`Spec.lean:725`) lists the
  two middle summands as `(w·∇... spatialDerivative (D.correction ε) t x (v z)`
  then `spatialDerivative v t x (D.correction ε z)`; `Source.correctionForce`
  (`Source/Insertion.lean:92`) lists them in the opposite order.  Both summands
  are `spatialDerivative _ _ _ _`, so this is `add_comm` of the two — a pure
  algebraic reorder, no analysis.
* (b) **field lift on the chart neighborhood** `Source.correctionForce ν v
  (D.correction ε) p = Source.correctionForce ν v (physicalCorrection …) p` at
  `p = correctionChartPoint x₀ T ε z`.  Lane 370's
  `correction_eq_physicalCorrection hpot hε hx : D.correction ε (t,x) =
  physicalCorrection … (t,x)` holds for every `t` and every `x ∈ ball x₀ r`
  (spatial coord `x₀ + ε•z.2 ∈ ball x₀ r` by `hpot.eps_space`, cf. lane 370
  `correction_profile_identity`), so the two fields agree on the open
  neighbourhood `univ ×ˢ ball x₀ r` of `p`.  `Source.correctionForce` at `p` is a
  local operator (its `temporalDerivative / spatialLaplacian / spatialDerivative
  / advection` at `p` depend only on the germ), so `EventuallyEq → equality at p`
  via `Filter.EventuallyEq.fderiv_eq`-style locality.

This is exactly U2's `force_eq` (T17_SPLIT §1, lane 373) restricted to the chart
point; lane 373 proves the full periodized-lattice version
(`correctionForce ν v (correctionData …) ε = latticeLift (Source.correctionForce
ν v (physicalCorrection …))` via `reference_periodic` + operator locality +
`add_comm`).  **Not on this base** (`Section3/T17/` has only `CorrectionProfile.lean`;
`grep` confirms no `Transport.lean` / `force_eq`).  Per the brief, the chart-force
theorem is the U4 deliverable and this lift is left to U12/lane 373.

**G1 — the six fields need global `hv : ContDiff ℝ ∞ v` (carried over from U3).**
As in lane 370, the Paper1 `forceProfile_*` lemmas require global smoothness of
`v`; the reconciled `CorrectionAPI` (`Spec.lean:752-779`) exposes only
`reference_periodic`, no `reference_smooth`.  All six theorems take `hv` as an
explicit premise; U12 must add a `reference_smooth` field or truncate `v` to the
chart (T16 `BallPotential` style).

**G3 — `place : PlacementData P` bundling deferred (carried over from U3).**
Same as lane 370: bare `(x₀ : Space) (T : ℝ)` in place of `place.x₀ / place.T`
(`PlacementData` is parameterized by `Contracts.V1.PacketAPI`, unreachable from
`formalization/`).  The probe records this as the only deviation from the field
text (plus G0 for the identity).

Minor fixes during development:
* `simp` closes `(g'.comp (ε • id)) d = (ε • g') d` after `ext d`; the explicit
  `ContinuousLinearMap.comp_apply / smul_apply / …` simp args are all reported
  unused → bare `simp`.
* `ContinuousLinearMap.smul_apply` is **deprecated** at this pin → use `smul_apply`.
