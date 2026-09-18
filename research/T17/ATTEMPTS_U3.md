# T17 U3 — attempts, decisions, residuals (lane 370)

Target: the six correction-profile fields of `CorrectionAPI`
(`research/T17/Spec.lean:784-830`) over the canonical T10/T15/T16 vocabulary,
via the Euclidean reuse of `Paper1/CorrectionProfile.lean`.

Delivered module: `formalization/NSFormalization/Section3/T17/CorrectionProfile.lean`
(namespace `NSFormalization.Section3.T17`). Builds with 0 errors; every
declaration prints exactly `[propext, Classical.choice, Quot.sound]`
(`research/T17/axioms_u3.lean`). Probe: `research/T17/probes/correction_profile_closes.lean`.

## What worked (the route as delivered)

1. **The `def` bridge is essentially `rfl`.** The registered `𝒜_ε`
   (`Spec.lean:696` `rescaledPotential`) is the *literal display*
   `∫₀¹ ρ·(v(T+ε²σ, x₀+ερz) × z) dρ`. Restated over `RadialPotential.cross`, it is
   **definitionally equal** to `CorrectionProfile.jointPotential v x₀ T (ε,σ,z)`
   (checked by `example … := rfl`), so
   `(fun y => (D.η σ * D.θ y) • rescaledPotential v x₀ T ε (σ,y))
      = (fun y => cutPotential v x₀ T D.θ D.η (ε,σ,y))` by `rfl`.
   Then `profile_eq_curl_slice` (isolated middle of Paper1
   `profile_eq_localCorrection`) gives
   `profile v x₀ T θ η (ε,σ,y) = -SpatialCurl.curl (fun w => cutPotential v x₀ T θ η (ε,σ,w)) y`,
   whence `rescaledCorrectionProfile v x₀ T ε D z = profile v x₀ T D.θ D.η (ε,z)`.
   Key: `HasFDerivAt (fun w => (ε,σ,w)) spatialInclusion y` is proved by `prodMk`
   of two `hasFDerivAt_const` and `hasFDerivAt_id`; its derivative is defeq to
   `spatialInclusion`, so `rw [SpatialCurl.curl, ← hd.fderiv]; rfl` closes it.

2. **smooth / support / uniform are transports through the bridge.**
   * `correction_profile_smooth`: rewrite `W_ε = fun z => profile (ε,z)`, then
     `(profile_smooth hv x₀ T hθ hη).comp (by fun_prop)`, `.contDiffOn`.
   * `correction_profile_support`: `closure_minimal` into
     `Icc(-2,2) ×ˢ closedBall 0 θRadius` (closed) using Paper1 `profile_support`
     (`tsupport profile ⊆ univ ×ˢ (tsupport η ×ˢ tsupport θ)`), then T16
     `eta_support` (`⊆ Ioo(-2,2)`) and `theta_support` (`⊆ ball 0 θRadius`).
   * `correctionProfileConst := Classical.choose (profile_uniform_global_derivative_bound …)`;
     `_nonneg := (choose_spec …).1`; `correction_profile_uniform` = bridge +
     the slice bound `norm_iteratedFDeriv_slice_le` + `(choose_spec …).2` on
     `ε ∈ Icc 0 1` (from `ε ∈ Ioc 0 D.ε₀` and the premise `D.ε₀ ≤ 1`).

3. **Slice ≤ full derivative** (`norm_iteratedFDeriv_slice_le`): the slice
   `w ↦ g(ε,w)` is `g ∘ (affine w ↦ (ε,0)+inr(w-0))`; `iteratedFDeriv_affine_apply`
   (`a=(ε,0), L=inr, c=0`) rewrites the applied derivative to
   `iteratedFDeriv k g (ε,z) (fun i => inr(h i))`; `ContinuousMultilinearMap.opNorm_le_bound`
   + `le_opNorm`, with `‖inr(h i)‖ = ‖h i‖` (inr isometry, `Prod.norm_def`), gives
   `≤ ‖iteratedFDeriv k g (ε,z)‖`. The `(ε,0)+inr u = (ε,u)` step needs `simp` to
   discharge `ε+0`/`0+u` (not defeq on ℝ).

4. **identity** (`correction_profile_identity`): from a `LocalPotentialAPI` witness,
   `correction_eq_physicalCorrection` rewrites the abstract `D.correction ε (t,x)` on
   the chart ball via `correction_formula` (curl of the scaled cutoffs times
   `D.potential`) and `potential_formula` (= `timePotential v x₀`, by
   `centeredPotential_eq_integral`) into `physicalCorrection v x₀ T D.θ D.η ε (t,x)`
   (a `rfl` after the potential rewrite: `physicalCorrection = localCorrection` and
   `spatialCurl A (t,x) = curl (fun y => A(t,y)) x`). Then
   `physicalCorrection_rescale` maps the chart point to `profile (ε,σ,z)`, and the
   reverse bridge closes it. Chart membership `x₀+ε•z.2 ∈ ball x₀ r` from
   `z.2 ∈ closedBall 0 θRadius` (`‖z.2‖ ≤ θRadius`) and `eps_space` (`ε·θRadius < r`).

Minor fixes during development (recorded for the next lane):
* `rw [profile_eq_curl_slice …]` leaves a defeq goal; needs a trailing `rfl`
  (bare `exact` would risk the whnf timeout, cf. LESSONS lane 326).
* `contDiff_const.prod contDiff_id` failed to elaborate (`Invalid field prod`);
  use `by fun_prop` for `ContDiff ℝ ∞ (fun z => (ε, z))`.
* `ball_subset_closedBall` is `Metric.ball_subset_closedBall`.

## Residual gaps (honest partial)

**G1 — `CorrectionAPI` has no `reference_smooth` field.** All six fields, via the
Euclidean `profile_*` lemmas, require **global** `hv : ContDiff ℝ ∞ v`. The
reconciled `CorrectionAPI` (`Spec.lean:752-779`) carries `reference_periodic :
IsPeriodicOn univ v` but **no** global-smoothness field, and the `LocalPotentialAPI`
witness only gives `potential_smooth` (not v-smoothness; T16's `localPotentialStatement`
assumes v only `ContDiffOn` on the ball). So the six theorems here take `hv` as an
explicit premise. To wire them into the `CorrectionAPI` assembly (U12), the spec
needs either a `reference_smooth : ContDiff ℝ ∞ v` field, or the profile fields must
be re-proved via a truncation of v to the chart (exactly the ContDiffBump argument
T16 `BallPotential.lean` used to drop global smoothness to local). This is a
spec/assembly obligation, not closed by this lane. Flagged to the lead.

**G2 — identity non-vacuity is gated on the T16 `localPotential` assembly.**
`correction_profile_identity` is fully proved from a `LocalPotentialAPI v U K x₀ r T δ D`
hypothesis (the `CorrectionAPI.potential` field). A *concrete* witness (constant `v`
+ actual `D` satisfying `LocalPotentialAPI`) needs T16's `localPotential` constructor
(lane 358, `Section3/T16/Assembly.lean`), which is **not present in this worktree**
(base `512d706a`, 13 commits behind `origin/erenup/integration-section3`; `Section3/T16/`
has only `LocalPotential/BallPotential/LatticeLift`). The probe's non-vacuity
(`nonvacuous_correction_profile_fields`) therefore discharges only the five
cutoff-data-only fields (smooth/support/const/nonneg/uniform) with a concrete
constant reference + `exists_originCutoff`/`exists_timeCutoff` data. The identity's
non-vacuity waits on that assembly; the field theorem itself is complete.

**G3 — `place : PlacementData P` bundling deferred.** The reconciled `Spec.lean`
threads T15's `place : PlacementData P`; `PlacementData` is parameterized by the
registered `Contracts.V1.PacketAPI`, which lives in `verification/` and is
**unreachable from `formalization/`** (dependency chain: verification → formalization;
no `import Contracts` exists in formalization). No canonical T15 `PlacementData`
module exists in `formalization/` (lane 362 has not landed one). Copying the 24-field
`PacketAPI` verbatim purely to read `place.x₀`/`place.T` (the only two placement
fields U3's mathematics uses) is disproportionate (`不 over-engineer`). Following the
canonical T16 spelling (`LocalPotentialAPI … (x₀ : Space) (r T δ : ℝ)`, bare, no
`PacketAPI`), this module uses bare `(x₀ : Space) (T : ℝ)`; the assembly instantiates
`x₀ := place.x₀`, `T := place.T`. The probe records this substitution as the only
deviation from the field text.
