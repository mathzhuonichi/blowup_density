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

   **Identity route note (review ruling v).** The proof calls
   `NSFormalization.Paper1.CorrectionProfile.physicalCorrection_rescale`
   (`Paper1/CorrectionProfile.lean:130-183`) directly, at
   `CorrectionProfile.lean:285-287`:
   `physicalCorrection_rescale hv x₀ T ε σ hε.1.ne' y hθ hη :
     physicalCorrection v x₀ T D.θ D.η ε (T+ε²σ, x₀+ε•y) = profile v x₀ T D.θ D.η (ε,σ,y)`.
   This IS the chart-point form the `correctionChartPoint` requires
   (`correctionChartPoint x₀ T ε (σ,y) = (T+ε²σ, x₀+ε•y)` by `rfl`), so no
   `inverseScale` round-trip is needed. The brief's `physicalCorrection_eq_profile`
   (`Paper1/CorrectionProfile.lean:218-228`) is defined *from* `physicalCorrection_rescale`
   (it substitutes `σ = (ε²)⁻¹(p.1−T)`, `z = ε⁻¹(p.2−x₀)` via `inverseScale` and
   then cancels those factors back to the chart point); using `physicalCorrection_rescale`
   at the chart point is the same route without the cancel-then-uncancel step, i.e.
   the `inverseScale` composition specialized to `p = (T+ε²σ, x₀+εy)` reduces to it.

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

**G2 — RESOLVED (rev after review, 2026-09-18).** The identity non-vacuity was
gated on the T16 `localPotential` assembly, which was not in the lane's original
base. Per the lead ruling, `git merge --no-edit origin/erenup/integration-section3`
brought `Section3/T16/Assembly.lean` (#330) with `localPotential :
localPotentialStatement` / `localPotentialData`. The probe now builds a **real**
`LocalPotentialAPI` witness (`nonvacuous_correction_profile_identity`,
`research/T17/probes/correction_profile_closes.lean`) for the nonzero constant
divergence-free periodic reference `constRef = fun _ => coordinateVector 0`
(`U := 0`, `K := ∅`, `x₀ := 0`, `r := 1/4`, `T := δ := 1`), via
`localPotential constRef 0 ∅ 0 (1/4) 1 1 …` (periodicity `constRef_periodic`
by `rfl`; divergence-freeness `constRef_divergence_free` by `simp [spatialDivergence,
spatialDerivative]` + `fderiv_const`), and instantiates
`correction_profile_identity constRef_smooth hpot`. Periodicity and
divergence-freeness are now **proved theorems**, not comments (review point 2).

**G3 — `place : PlacementData P` bundling: bare `(x₀, T)` stands (lead ruling,
2026-09-18).** The review demanded "restore exact `PlacementData`-based signatures";
the lead **rejected** this. `PlacementData` is parameterized by the registered
`Contracts.V1.PacketAPI`, which lives in `verification/` and is **unreachable from
`formalization/`** (dependency chain: verification → formalization; no `import
Contracts` exists in formalization, confirmed by grep). No canonical T15
`PlacementData` module exists in `formalization/` (lane 362 has not landed one).
Copying the 24-field `PacketAPI` verbatim purely to read `place.x₀`/`place.T` (the
only two placement fields U3's mathematics uses) is disproportionate (`不
over-engineer`). Following the canonical T16 spelling (`LocalPotentialAPI …
(x₀ : Space) (r T δ : ℝ)`, bare, no `PacketAPI`), this module uses bare
`(x₀ : Space) (T : ℝ)`; the assembly (U12) instantiates `x₀ := place.x₀`,
`T := place.T`. Recorded in `research/T17/SPEC_ISSUES.md` (G3) and the module docstring
(Vocabulary note). This is the only deviation from the Spec field text.

## REPORT_370

(The `Artifact`/`Write` guard blocks new `REPORT_*.md` files for subagents, so the
four-part report lives here per the lead ruling iii.)

### 1. What was proved (theorems, exact statements)

Module `formalization/NSFormalization/Section3/T17/CorrectionProfile.lean`
(namespace `NSFormalization.Section3.T17`), the six `CorrectionAPI` correction-profile
fields (`research/T17/Spec.lean:784-830`) over canonical T16/Paper1 vocabulary,
bare `(x₀ : Space) (T : ℝ)` (= `place.x₀`, `place.T`):

- `rescaledCorrectionProfile_eq_profile` — bridge `W_ε = profile v x₀ T D.θ D.η (ε,·)`.
- `correction_profile_smooth` — `∀ ε ∈ Ioc 0 D.ε₀, ContDiffOn ℝ ∞ (rescaledCorrectionProfile v x₀ T ε D) (fixedProfileCylinder D)`.
- `correction_profile_support` — `∀ ε ∈ Ioc 0 D.ε₀, tsupport (rescaledCorrectionProfile v x₀ T ε D) ⊆ fixedProfileCylinder D`.
- `correctionProfileConst : ℕ → ℝ` (def), `correctionProfileConst_nonneg : ∀ k, 0 ≤ …`.
- `correction_profile_uniform` — `∀ k, ∀ ε ∈ Ioc 0 D.ε₀, ∀ z ∈ fixedProfileCylinder D, ‖iteratedFDeriv ℝ k (rescaledCorrectionProfile v x₀ T ε D) z‖ ≤ correctionProfileConst … k`.
- `correction_profile_identity` — `∀ ε ∈ Ioc 0 D.ε₀, ∀ z ∈ fixedProfileCylinder D, D.correction ε (correctionChartPoint x₀ T ε z) = rescaledCorrectionProfile v x₀ T ε D z`, from a `LocalPotentialAPI v U K x₀ r T δ D` witness.

Each field takes `hv : ContDiff ℝ ∞ v` (added premise vs `CorrectionAPI`, spec issue
G1). All 11 declarations depend only on `[propext, Classical.choice, Quot.sound]`.

### 2. What exists in Lean now (files, absolute)

- `/data_8T/ping/blowup_density/.claude/worktrees/370-T17-U3-correction-profile/formalization/NSFormalization/Section3/T17/CorrectionProfile.lean` (builds, 0 errors/warnings).
- `.../research/T17/probes/correction_profile_closes.lean` — Part A: six field
  restatements closed by `exact`; Part B: `nonvacuous_correction_profile_fields`
  (five cutoff-data-only fields) and `nonvacuous_correction_profile_identity` (real
  `LocalPotentialAPI` witness via `localPotential` on a nonzero constant
  divergence-free periodic reference — the identity is instantiated).
- `.../research/T17/axioms_u3.lean` (11 decls, standard three axioms).
- `.../research/T17/ATTEMPTS_U3.md`, `.../research/T17/T17_SPLIT.md` (U3 status),
  `.../research/T17/SPEC_ISSUES.md` (G1/G3), `.../logs/LESSONS.md`.

### 3. Gaps

- **G1 (spec, load-bearing, logged in SPEC_ISSUES.md):** the six fields need global
  `hv : ContDiff ℝ ∞ v`; `CorrectionAPI` has `reference_periodic` only. U12 must add
  `reference_smooth` or truncate v à la T16 `BallPotential`. `hv` is satisfiable
  (nonzero constant reference). No `sorry`/`axiom`/etc.; no placeholder/alias/goal-repackaging.
- **G2 — RESOLVED:** identity non-vacuity now instantiated via the merged T16
  `localPotential` assembly.
- **G3 (packaging, lead ruling):** bare `(x₀, T)` stands; `PlacementData` unreachable
  from `formalization/`; assembly instantiates `place.x₀`/`place.T`.

### 4. Commands and results (rev after review)

```
git merge --no-edit origin/erenup/integration-section3   → conflict only in logs/LESSONS.md (record file), resolved by union; merge committed
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T17.CorrectionProfile   → Build completed successfully; 0 errors/0 warnings on the module
cd verification && lake env lean ../formalization/NSFormalization/Section3/T17/CorrectionProfile.lean   → rc 0
cd verification && lake env lean ../research/T17/probes/correction_profile_closes.lean   → rc 0 (identity witness closes)
cd verification && lake env lean ../research/T17/axioms_u3.lean   → all 11 decls [propext, Classical.choice, Quot.sound]
make check   → all pass
```
