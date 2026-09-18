import NSFormalization.Section3.T16.LocalPotential
import NSFormalization.Paper1.CorrectionProfile

/-!
# T17 (`lem:correction`), Unit U3: the fixed-cylinder correction profile

This module realizes, over the **canonical Section 3 vocabulary**, the six
correction-profile fields of the reconciled `CorrectionAPI`
(`research/T17/Spec.lean:781-830`, `paper/sections/03-torus.tex:245-260`):

* `correction_profile_smooth`     — `W_ε` is `C∞` on the fixed cylinder;
* `correction_profile_support`    — `tsupport W_ε ⊆ Icc (-2) 2 ×ˢ closedBall 0 θRadius`;
* `correctionProfileConst`        — the `ε`-independent derivative constants (data);
* `correctionProfileConst_nonneg` — they are nonnegative;
* `correction_profile_uniform`    — every fixed `iteratedFDeriv` order of `W_ε` is
  bounded by that constant, uniformly in `ε` on the cylinder;
* `correction_profile_identity`   — `w_ε(T+ε²σ, x₀+εz) = W_ε(z,σ)`.

## Route (RECONCILIATION §4 ①, brief U3)

The registered `𝒜_ε` (`rescaledPotential`) is the **literal display**
`∫₀¹ ρ·(v(T+ε²σ, x₀+ερz) × z) dρ`.  It is definitionally the Euclidean
`NSFormalization.Paper1.CorrectionProfile.jointPotential`, so `W_ε` is
definitionally the Euclidean `CorrectionProfile.profile`
(`rescaledCorrectionProfile_eq_profile`, proved from
`cutPotential_smooth`/`spatialInclusion`).  Every field is then a transport of
a Paper1 profile estimate: `profile_smooth` (`:49`), `profile_support` (`:187`),
`profile_uniform_global_derivative_bound` (`:201`) and, for the identity,
`physicalCorrection_rescale` (`:145`) after rewriting the abstract
`D.correction ε` through T16's `LocalPotentialAPI.correction_formula` and
`potential_formula` (which reduce it to `Paper1.physicalCorrection` on the
chart ball).

## Vocabulary note (placement bundling)

The reconciled `Spec.lean` threads a T15 `place : PlacementData P`; here we use
the two placement fields the correction mathematics actually reads, `x₀` and
`T`, as bare parameters, exactly as the canonical T16
`LocalPotentialAPI (v U : SpaceTimeField) (K : Set Space) (x₀ : Space)
(r T δ : ℝ)` does.  The `place`-bundled spelling is deferred to the (not yet
landed) T15 canonical module: `PlacementData` is parameterized by the
registered `Contracts.V1.PacketAPI`, which lives in `verification/` and is
unreachable from `formalization/`.  The T17 assembly instantiates
`x₀ := place.x₀`, `T := place.T`.
-/

noncomputable section

namespace NSFormalization.Section3.T17

open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T16 (CutoffData LocalPotentialAPI)
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField)
open NSFormalization.Paper1.RadialPotential (cross timePotential centeredPotential_eq_integral)
open NSFormalization.Paper1 (localCorrection)
open NSFormalization.Paper1.CorrectionProfile
open scoped ContDiff Topology

/-! ## 0. The T17 profile vocabulary (`Spec.lean:679-709`, canonical curl/cross) -/

/-- `03-torus.tex:247-253`, `Spec.lean:696-703`: the amplitude-one radial
potential profile `𝒜_ε(z,σ) = ∫₀¹ ρ·(v(T+ε²σ, x₀+ερz) × z) dρ`. -/
def rescaledPotential (v : SpaceTimeField) (x₀ : Space) (T ε : ℝ) : SpaceTimeField :=
  fun z => ∫ ρ in (0 : ℝ)..1,
    ρ • cross (v (T + ε ^ 2 * z.1, x₀ + ε • (ρ • z.2))) z.2

/-- `03-torus.tex:245-260`, `Spec.lean:679-682`: the fixed manuscript cylinder
in rescaled coordinates; its endpoints and radius are independent of `ε`. -/
def fixedProfileCylinder (D : CutoffData) : Set SpaceTime :=
  Icc (-2 : ℝ) 2 ×ˢ Metric.closedBall (0 : Space) D.θRadius

/-- `03-torus.tex:256-259`, `Spec.lean:684-687`: the correction chart based at
`T` (not at `t_ε = T-ε²`); `z ↦ (T + ε²z.1, x₀ + εz.2)`. -/
def correctionChartPoint (x₀ : Space) (T ε : ℝ) (z : SpaceTime) : SpaceTime :=
  (T + ε ^ 2 * z.1, x₀ + ε • z.2)

/-- `03-torus.tex:256-259`, `Spec.lean:706-709`: the exact amplitude-one
correction profile `W_ε = -curl_z(η(σ)θ(z)𝒜_ε)`. -/
def rescaledCorrectionProfile (v : SpaceTimeField) (x₀ : Space) (T ε : ℝ)
    (D : CutoffData) : SpaceTimeField :=
  fun z => -SpatialCurl.curl (fun y =>
    (D.η z.1 * D.θ y) • rescaledPotential v x₀ T ε (z.1, y)) z.2

/-! ## 1. The `def` bridge `W_ε = CorrectionProfile.profile` -/

/-- The Euclidean profile is the spatial-slice curl of the cut potential.  This
is the middle of `CorrectionProfile.profile_eq_localCorrection`, isolated. -/
theorem profile_eq_curl_slice {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η) (ε σ : ℝ) (y : Space) :
    profile v x₀ T θ η (ε, σ, y) =
      -SpatialCurl.curl (fun w => cutPotential v x₀ T θ η (ε, σ, w)) y := by
  have hF := cutPotential_smooth hv x₀ T hθ hη
  have hin : HasFDerivAt (fun w : Space => (ε, σ, w)) spatialInclusion y :=
    (hasFDerivAt_const (𝕜 := ℝ) ε y).prodMk
      ((hasFDerivAt_const (𝕜 := ℝ) σ y).prodMk (hasFDerivAt_id (𝕜 := ℝ) y))
  have hd := ((hF.differentiable (by simp)) (ε, σ, y)).hasFDerivAt.comp y hin
  show -SpatialCurl.curlLinear _ = -SpatialCurl.curl _ y
  rw [SpatialCurl.curl, ← hd.fderiv]
  rfl

/-- **The `def` bridge**: the T17 correction profile `W_ε` is definitionally the
Euclidean `CorrectionProfile.profile`, because the display `𝒜_ε`
(`rescaledPotential`) is definitionally `jointPotential`. -/
theorem rescaledCorrectionProfile_eq_profile {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T ε : ℝ) (D : CutoffData)
    (hθ : ContDiff ℝ ∞ D.θ) (hη : ContDiff ℝ ∞ D.η) (z : SpaceTime) :
    rescaledCorrectionProfile v x₀ T ε D z = profile v x₀ T D.θ D.η (ε, z) := by
  obtain ⟨σ, y⟩ := z
  show -SpatialCurl.curl
      (fun w => (D.η σ * D.θ w) • rescaledPotential v x₀ T ε (σ, w)) y
      = profile v x₀ T D.θ D.η (ε, σ, y)
  rw [profile_eq_curl_slice hv x₀ T hθ hη ε σ y]
  rfl

/-- The profile as a function of `z` (with `ε` fixed) is `C∞`. -/
theorem contDiff_rescaledCorrectionProfile {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T ε : ℝ) (D : CutoffData)
    (hθ : ContDiff ℝ ∞ D.θ) (hη : ContDiff ℝ ∞ D.η) :
    ContDiff ℝ ∞ (rescaledCorrectionProfile v x₀ T ε D) := by
  have hfun : rescaledCorrectionProfile v x₀ T ε D
      = (fun z => profile v x₀ T D.θ D.η (ε, z)) := by
    funext z; exact rescaledCorrectionProfile_eq_profile hv x₀ T ε D hθ hη z
  rw [hfun]
  have hmap : ContDiff ℝ ∞ (fun z : SpaceTime => ((ε, z) : ℝ × SpaceTime)) := by
    fun_prop
  exact (profile_smooth hv x₀ T hθ hη).comp hmap

/-! ## 2. Field `correction_profile_smooth` (`Spec.lean:784-786`) -/

/-- `03-torus.tex:256-260`: `W_ε` is `C∞` on the fixed cylinder. -/
theorem correction_profile_smooth {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) (D : CutoffData)
    (hθ : ContDiff ℝ ∞ D.θ) (hη : ContDiff ℝ ∞ D.η) :
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      ContDiffOn ℝ ∞ (rescaledCorrectionProfile v x₀ T ε D)
        (fixedProfileCylinder D) := by
  intro ε _
  exact (contDiff_rescaledCorrectionProfile hv x₀ T ε D hθ hη).contDiffOn

/-! ## 3. Field `correction_profile_support` (`Spec.lean:789-790`) -/

/-- `03-torus.tex:256-260`: `W_ε` is supported in the fixed cylinder. -/
theorem correction_profile_support {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) (D : CutoffData)
    (hθ : ContDiff ℝ ∞ D.θ) (hη : ContDiff ℝ ∞ D.η)
    (hθsupp : tsupport D.θ ⊆ Metric.ball (0 : Space) D.θRadius)
    (hηsupp : tsupport D.η ⊆ Ioo (-2 : ℝ) 2) :
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      tsupport (rescaledCorrectionProfile v x₀ T ε D) ⊆ fixedProfileCylinder D := by
  intro ε _
  have hfun : rescaledCorrectionProfile v x₀ T ε D
      = (fun z => profile v x₀ T D.θ D.η (ε, z)) := by
    funext z; exact rescaledCorrectionProfile_eq_profile hv x₀ T ε D hθ hη z
  rw [hfun]
  refine closure_minimal ?_ (isClosed_Icc.prod Metric.isClosed_closedBall)
  intro w hw
  have hmem : (ε, w) ∈ tsupport (profile v x₀ T D.θ D.η) :=
    subset_tsupport _ hw
  have hprof := profile_support hv x₀ T hθ hη hmem
  exact ⟨Ioo_subset_Icc_self (hηsupp hprof.2.1),
    Metric.ball_subset_closedBall (hθsupp hprof.2.2)⟩

/-! ## 4. Fields `correctionProfileConst` / `_nonneg` / `correction_profile_uniform`
(`Spec.lean:793-802`) -/

/-- `03-torus.tex:254-260`: the `ε`-independent uniform derivative constants,
selected before `ε`.  Extracted from
`CorrectionProfile.profile_uniform_global_derivative_bound`. -/
def correctionProfileConst {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) : ℕ → ℝ :=
  fun k => Classical.choose
    (profile_uniform_global_derivative_bound hv x₀ T hθ hη hθc hηc k)

/-- `03-torus.tex:254-260`: the profile constants are nonnegative. -/
theorem correctionProfileConst_nonneg {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    ∀ k, 0 ≤ correctionProfileConst hv x₀ T hθ hη hθc hηc k :=
  fun k => (Classical.choose_spec
    (profile_uniform_global_derivative_bound hv x₀ T hθ hη hθc hηc k)).1

/-- The slice derivative of a smooth `g : ℝ × SpaceTime → Space` at fixed first
coordinate is bounded by the full derivative, since the spatial inclusion is an
isometry. -/
theorem norm_iteratedFDeriv_slice_le {g : ℝ × SpaceTime → Space} (hg : ContDiff ℝ ∞ g)
    (ε : ℝ) (z : SpaceTime) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun w => g (ε, w)) z‖ ≤ ‖iteratedFDeriv ℝ k g (ε, z)‖ := by
  have hpt : ∀ u : SpaceTime,
      ((ε, (0 : SpaceTime)) : ℝ × SpaceTime) +
        ContinuousLinearMap.inr ℝ ℝ SpaceTime u = (ε, u) := by
    intro u; simp
  refine ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) ?_
  intro h
  have key : iteratedFDeriv ℝ k (fun w => g (ε, w)) z h
      = iteratedFDeriv ℝ k g (ε, z)
          (fun i => ContinuousLinearMap.inr ℝ ℝ SpaceTime (h i)) := by
    have hfun : (fun w : SpaceTime => g (ε, w))
        = (fun w : SpaceTime => g ((ε, (0 : SpaceTime)) +
            ContinuousLinearMap.inr ℝ ℝ SpaceTime (w - 0))) := by
      funext w; rw [sub_zero, hpt]
    rw [hfun, iteratedFDeriv_affine_apply hg
      (ContinuousLinearMap.inr ℝ ℝ SpaceTime) (ε, (0 : SpaceTime)) 0 z k h,
      sub_zero, hpt]
  rw [key]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => ?_)
  simp [ContinuousLinearMap.inr_apply, Prod.norm_def]

/-- `03-torus.tex:254-260`: every fixed derivative order of `W_ε` is bounded by
`correctionProfileConst k`, uniformly in `ε ∈ (0,ε₀]` and on the cylinder. -/
theorem correction_profile_uniform {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) (D : CutoffData)
    (hθ : ContDiff ℝ ∞ D.θ) (hη : ContDiff ℝ ∞ D.η)
    (hθc : HasCompactSupport D.θ) (hηc : HasCompactSupport D.η)
    (hε₀ : D.ε₀ ≤ 1) :
    ∀ k : ℕ, ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z ∈ fixedProfileCylinder D,
      ‖iteratedFDeriv ℝ k (rescaledCorrectionProfile v x₀ T ε D) z‖ ≤
        correctionProfileConst hv x₀ T hθ hη hθc hηc k := by
  intro k ε hε z _
  have hfun : rescaledCorrectionProfile v x₀ T ε D
      = (fun w => profile v x₀ T D.θ D.η (ε, w)) := by
    funext w; exact rescaledCorrectionProfile_eq_profile hv x₀ T ε D hθ hη w
  rw [hfun]
  have hεIcc : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1.le, hε.2.trans hε₀⟩
  refine (norm_iteratedFDeriv_slice_le (profile_smooth hv x₀ T hθ hη) ε z k).trans ?_
  exact (Classical.choose_spec
    (profile_uniform_global_derivative_bound hv x₀ T hθ hη hθc hηc k)).2 ε hεIcc z

/-! ## 5. Field `correction_profile_identity` (`Spec.lean:827-830`) -/

/-- The abstract T16 correction `D.correction ε` agrees, on the chart ball, with
the single Euclidean copy `Paper1.physicalCorrection`: its
`LocalPotentialAPI.correction_formula` and `potential_formula` reduce it to the
same radial cut potential that `physicalCorrection` is built from. -/
theorem correction_eq_physicalCorrection {v U : SpaceTimeField} {K : Set Space}
    {x₀ : Space} {r T δ : ℝ} {D : CutoffData}
    (hpot : LocalPotentialAPI v U K x₀ r T δ D)
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) D.ε₀) {t : ℝ} {x : Space}
    (hx : x ∈ Metric.ball x₀ r) :
    D.correction ε (t, x) = physicalCorrection v x₀ T D.θ D.η ε (t, x) := by
  have hDpot : ∀ y : Space, D.potential (t, y) = timePotential v x₀ (t, y) := by
    intro y
    rw [hpot.potential_formula t y]
    rw [show timePotential v x₀ (t, y)
        = ∫ ρ in (0 : ℝ)..1, ρ • cross (v (t, x₀ + ρ • (y - x₀))) (y - x₀) from
      centeredPotential_eq_integral (fun x => v (t, x)) x₀ y]
  rw [hpot.correction_formula ε hε t x hx]
  have hfun : (fun y => (temporalCutoff D.η T ε t * spatialCutoff D.θ x₀ ε y) •
        D.potential (t, y))
      = (fun y => (temporalCutoff D.η T ε t * spatialCutoff D.θ x₀ ε y) •
        timePotential v x₀ (t, y)) := by
    funext y; rw [hDpot y]
  rw [hfun]
  rfl

/-- `03-torus.tex:256-259`: the physical correction equals `W_ε` in the chart. -/
theorem correction_profile_identity {v U : SpaceTimeField} {K : Set Space}
    (hv : ContDiff ℝ ∞ v) {x₀ : Space} {r T δ : ℝ} {D : CutoffData}
    (hpot : LocalPotentialAPI v U K x₀ r T δ D) :
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z ∈ fixedProfileCylinder D,
      D.correction ε (correctionChartPoint x₀ T ε z) =
        rescaledCorrectionProfile v x₀ T ε D z := by
  intro ε hε z hz
  obtain ⟨σ, y⟩ := z
  obtain ⟨_, hy⟩ := hz
  have hθ : ContDiff ℝ ∞ D.θ := hpot.theta_smooth
  have hη : ContDiff ℝ ∞ D.η := hpot.eta_smooth
  have hyR : ‖y‖ ≤ D.θRadius := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hy
  have hxmem : x₀ + ε • y ∈ Metric.ball x₀ r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hnorm : ‖x₀ + ε • y - x₀‖ = ε * ‖y‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hε.1]
    rw [hnorm]
    calc ε * ‖y‖ ≤ ε * D.θRadius := mul_le_mul_of_nonneg_left hyR hε.1.le
      _ < r := hpot.eps_space ε hε
  have hchart : correctionChartPoint x₀ T ε (σ, y)
      = (T + ε ^ 2 * σ, x₀ + ε • y) := rfl
  rw [hchart, correction_eq_physicalCorrection hpot hε hxmem,
    physicalCorrection_rescale hv x₀ T ε σ hε.1.ne' y hθ hη]
  exact (rescaledCorrectionProfile_eq_profile hv x₀ T ε D hθ hη (σ, y)).symm

end NSFormalization.Section3.T17
