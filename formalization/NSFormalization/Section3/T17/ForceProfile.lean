import NSFormalization.Section3.T17.Transport
import NSFormalization.Section3.T17.CorrectionProfile
import NSFormalization.Paper1.CorrectionForceProfile
import Mathlib.Tactic.Module

/-!
# T17 (`lem:correction`), Unit U4: the fixed-cylinder force profile

This module realizes, over the **canonical Section 3 vocabulary**, the six
force-profile fields of the reconciled `CorrectionAPI`
(`research/T17/Spec.lean:805-837`, `paper/sections/03-torus.tex:262-273`):

* `force_profile_smooth`     — the bracketed force profile `H_ε` is `C∞` on the
  fixed cylinder;
* `force_profile_support`    — `tsupport (rescaledForceProfile …) ⊆ Icc (-2) 2 ×ˢ closedBall 0 θRadius`;
* `forceProfileConst`        — the `ε`-independent derivative constants (data);
* `forceProfileConst_nonneg` — they are nonnegative;
* `force_profile_uniform`    — every fixed `iteratedFDeriv` order of the force
  profile is bounded by that constant, uniformly in `ε` on the cylinder;
* `force_profile_identity`   — the physical force equals `ε⁻²` times the bracket.

## Route (`research/T17/RECONCILIATION.md` §4 ②, brief U4)

The Spec's `rescaledForceProfile` is the displayed force bracket
`∂ₜW − νΔW + ε(∇W·V) + ε²(∇v·W) + ε(W·∇)W` built from the T17 profile
`rescaledCorrectionProfile` (= `Paper1.CorrectionProfile.profile`, lane 370's
`rescaledCorrectionProfile_eq_profile`) and the rescaled reference
`rescaledReference` (= `Paper1.CorrectionForceProfile.slice referenceProfile`).
It is definitionally the Euclidean `CorrectionForceProfile.forceProfile` after
one chain-rule identity for the `ε²(∇v·W)` term (`rescaledForceProfile_eq_forceProfile`,
via `forceProfile_eq_operators`).  Every field is then a transport of a Paper1
force-profile estimate: `forceProfile_smooth` (`:57`), `forceProfile_support`
(`:75`), `forceProfile_uniform_derivative_bound` (`:204`) and, for the identity,
`physicalForce_eq_profile` (`:185`) after cancelling the affine `inverseScale ε`
of the correction chart.

## The `force_profile_identity` residual (chart force vs `D.correction`)

The Spec's `force_profile_identity` is stated over `correctionForce ν v D ε`,
built from the abstract T16 correction `D.correction ε` and the T17 force
operator (with the two middle summands reordered relative to
`Source.correctionForce`).  This module proves the identity for the **chart
force** `Source.correctionForce ν v (physicalCorrection …)`
(`physicalForce_eq_rescaledForceProfile`), which is exactly the honest,
tree-provable content: it needs `hv, hθ, hη` and `ε ≠ 0` only.  The lift from
the chart force to the Spec field is U2's `force_eq` (lane 373, not on this
base); its exact residual statement is recorded in `research/T17/ATTEMPTS_U4.md`.

## Vocabulary note (placement bundling)

As in lane 370's `CorrectionProfile.lean`, the two placement fields the
correction mathematics reads, `x₀` and `T`, appear as bare parameters, exactly
as canonical T16 `LocalPotentialAPI (v U : SpaceTimeField) (K : Set Space)
(x₀ : Space) (r T δ : ℝ)`.  The T17 assembly instantiates `x₀ := place.x₀`,
`T := place.T`.  The Paper1 force lemmas require **global** `hv : ContDiff ℝ ∞ v`
(the `reconciled `CorrectionAPI` exposes `reference_periodic` only, see lane 370
G1); it is taken here as an explicit premise.
-/

noncomputable section

namespace NSFormalization.Section3.T17

open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T16 (CutoffData LocalPotentialAPI)
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField)
open NSFormalization.Paper1.CorrectionProfile hiding rescaledReference
open NSFormalization.Paper1.CorrectionForceProfile
open scoped ContDiff Topology

/-! ## 0. The T17 force vocabulary (`Spec.lean:689,712-732`, canonical operators) -/

/-- `03-torus.tex:245,262-263`, `Spec.lean:689-694`: `V_ε(z,σ)=v(T+ε²σ,x₀+εz)`. -/
def rescaledReference (v : SpaceTimeField) (x₀ : Space) (T ε : ℝ) : SpaceTimeField :=
  fun z => v (T + ε ^ 2 * z.1, x₀ + ε • z.2)

/-- `03-torus.tex:264-272`, `Spec.lean:712-723`: the bracketed amplitude-one
force profile `H_ε = ∂ₜW − νΔW + ε(∇W·V) + ε²(∇v·W) + ε(W·∇)W`. -/
def rescaledForceProfile (ν : ℝ) (v : SpaceTimeField) (x₀ : Space) (T ε : ℝ)
    (D : CutoffData) : SpaceTimeField :=
  let W := rescaledCorrectionProfile v x₀ T ε D
  let V := rescaledReference v x₀ T ε
  fun z =>
    temporalDerivative W z.1 z.2 - ν • spatialLaplacian W z.1 z.2 +
      ε • spatialDerivative W z.1 z.2 (V z) +
      (ε ^ 2) • spatialDerivative v
        (T + ε ^ 2 * z.1) (x₀ + ε • z.2) (W z) +
      ε • advection W z.1 z.2

/-! ## 1. The chain rule for the rescaled reference and the `def` bridge -/

/-- The spatial derivative of the rescaled reference `V_ε` picks up exactly one
factor of `ε` from the inner dilation `y ↦ x₀ + ε•y`: chain rule with
`HasFDerivAt (fun y => x₀ + ε•y) (ε • id) x`. -/
theorem spatialDerivative_rescaledReference {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T ε t : ℝ) (x : Space) :
    spatialDerivative (rescaledReference v x₀ T ε) t x
      = ε • spatialDerivative v (T + ε ^ 2 * t) (x₀ + ε • x) := by
  have hA : HasFDerivAt (fun y : Space => x₀ + ε • y)
      (ε • ContinuousLinearMap.id ℝ Space) x :=
    ((hasFDerivAt_id x).const_smul ε).const_add x₀
  have hvslice : ContDiff ℝ ∞ (fun y : Space => v (T + ε ^ 2 * t, y)) :=
    hv.comp (by fun_prop)
  have hg : HasFDerivAt (fun y : Space => v (T + ε ^ 2 * t, y))
      (spatialDerivative v (T + ε ^ 2 * t) (x₀ + ε • x)) (x₀ + ε • x) :=
    (hvslice.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hcomp := hg.comp x hA
  have hfd : spatialDerivative (rescaledReference v x₀ T ε) t x
      = (spatialDerivative v (T + ε ^ 2 * t) (x₀ + ε • x)).comp
          (ε • ContinuousLinearMap.id ℝ Space) := hcomp.fderiv
  rw [hfd]
  ext d
  simp

/-- The `ε²(∇v·W)` display term of `rescaledForceProfile` is exactly the
`ε(∇V·W)` term of `forceProfile_eq_operators`: one factor of `ε` is absorbed by
`spatialDerivative_rescaledReference`. -/
theorem rescaledReference_spatialDerivative_smul {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T ε t : ℝ) (x d : Space) :
    (ε ^ 2) • spatialDerivative v (T + ε ^ 2 * t) (x₀ + ε • x) d
      = ε • spatialDerivative (rescaledReference v x₀ T ε) t x d := by
  have hεε : ε * ε = ε ^ 2 := (pow_two ε).symm
  rw [spatialDerivative_rescaledReference hv x₀ T ε t x,
    smul_apply, smul_smul, hεε]

/-- **The `def` bridge**: the T17 force profile `H_ε` is the Euclidean
`CorrectionForceProfile.forceProfile`.  Matched term by term through
`forceProfile_eq_operators`; the only non-definitional step is the chain-rule
identity `rescaledReference_spatialDerivative_smul` for the `ε²(∇v·W)` summand. -/
theorem rescaledForceProfile_eq_forceProfile (ν : ℝ) {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T ε : ℝ) (D : CutoffData)
    (hθ : ContDiff ℝ ∞ D.θ) (hη : ContDiff ℝ ∞ D.η) (z : SpaceTime) :
    rescaledForceProfile ν v x₀ T ε D z = forceProfile ν v x₀ T D.θ D.η (ε, z) := by
  obtain ⟨t, x⟩ := z
  have hW : slice (profile v x₀ T D.θ D.η) ε = rescaledCorrectionProfile v x₀ T ε D := by
    funext w; exact (rescaledCorrectionProfile_eq_profile hv x₀ T ε D hθ hη w).symm
  have hV : slice (referenceProfile v x₀ T) ε = rescaledReference v x₀ T ε := by
    funext w; rfl
  rw [forceProfile_eq_operators ν hv x₀ T ε t x hθ hη, hW, hV]
  simp only [rescaledForceProfile]
  rw [rescaledReference_spatialDerivative_smul hv x₀ T ε t x
    (rescaledCorrectionProfile v x₀ T ε D (t, x)), smul_add, smul_add]
  abel

/-! ## 2. Field `force_profile_smooth` (`Spec.lean:805-808`) -/

/-- `03-torus.tex:262-273`: `H_ε` is `C∞` on the fixed cylinder. -/
theorem force_profile_smooth (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) (D : CutoffData)
    (hθ : ContDiff ℝ ∞ D.θ) (hη : ContDiff ℝ ∞ D.η) :
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      ContDiffOn ℝ ∞ (rescaledForceProfile ν v x₀ T ε D)
        (fixedProfileCylinder D) := by
  intro ε _
  have hfun : rescaledForceProfile ν v x₀ T ε D
      = (fun z => forceProfile ν v x₀ T D.θ D.η (ε, z)) := by
    funext z; exact rescaledForceProfile_eq_forceProfile ν hv x₀ T ε D hθ hη z
  rw [hfun]
  exact ((forceProfile_smooth ν hv x₀ T hθ hη).comp (by fun_prop)).contDiffOn

/-! ## 3. Field `force_profile_support` (`Spec.lean:810-811`) -/

/-- `03-torus.tex:262-273`: `H_ε` is supported in the fixed cylinder. -/
theorem force_profile_support (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) (D : CutoffData)
    (hθ : ContDiff ℝ ∞ D.θ) (hη : ContDiff ℝ ∞ D.η)
    (hθsupp : tsupport D.θ ⊆ Metric.ball (0 : Space) D.θRadius)
    (hηsupp : tsupport D.η ⊆ Ioo (-2 : ℝ) 2) :
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      tsupport (rescaledForceProfile ν v x₀ T ε D) ⊆ fixedProfileCylinder D := by
  intro ε _
  have hfun : rescaledForceProfile ν v x₀ T ε D
      = (fun z => forceProfile ν v x₀ T D.θ D.η (ε, z)) := by
    funext z; exact rescaledForceProfile_eq_forceProfile ν hv x₀ T ε D hθ hη z
  rw [hfun]
  refine closure_minimal ?_ (isClosed_Icc.prod Metric.isClosed_closedBall)
  intro w hw
  have hmemF : (ε, w) ∈ tsupport (forceProfile ν v x₀ T D.θ D.η) :=
    subset_tsupport _ hw
  have hmem : (ε, w) ∈ tsupport (profile v x₀ T D.θ D.η) :=
    forceProfile_support ν v x₀ T D.θ D.η hmemF
  have hprof := profile_support hv x₀ T hθ hη hmem
  exact ⟨Ioo_subset_Icc_self (hηsupp hprof.2.1),
    Metric.ball_subset_closedBall (hθsupp hprof.2.2)⟩

/-! ## 4. Fields `forceProfileConst` / `_nonneg` / `force_profile_uniform`
(`Spec.lean:814-823`) -/

/-- `03-torus.tex:262-273`: the `ε`-independent uniform derivative constants,
selected before `ε`.  Extracted from
`CorrectionForceProfile.forceProfile_uniform_derivative_bound`. -/
def forceProfileConst (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) : ℕ → ℝ :=
  fun k => Classical.choose
    (forceProfile_uniform_derivative_bound ν hv x₀ T hθ hη hθc hηc k)

/-- `03-torus.tex:262-273`: the force-profile constants are nonnegative. -/
theorem forceProfileConst_nonneg (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    ∀ k, 0 ≤ forceProfileConst ν hv x₀ T hθ hη hθc hηc k :=
  fun k => (Classical.choose_spec
    (forceProfile_uniform_derivative_bound ν hv x₀ T hθ hη hθc hηc k)).1

/-- `03-torus.tex:262-273`: every fixed derivative order of `H_ε` is bounded by
`forceProfileConst k`, uniformly in `ε ∈ (0,ε₀]` and on the cylinder. -/
theorem force_profile_uniform (ν : ℝ) {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) (D : CutoffData)
    (hθ : ContDiff ℝ ∞ D.θ) (hη : ContDiff ℝ ∞ D.η)
    (hθc : HasCompactSupport D.θ) (hηc : HasCompactSupport D.η)
    (hε₀ : D.ε₀ ≤ 1) :
    ∀ k : ℕ, ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z ∈ fixedProfileCylinder D,
      ‖iteratedFDeriv ℝ k (rescaledForceProfile ν v x₀ T ε D) z‖ ≤
        forceProfileConst ν hv x₀ T hθ hη hθc hηc k := by
  intro k ε hε z _
  have hfun : rescaledForceProfile ν v x₀ T ε D
      = (fun w => forceProfile ν v x₀ T D.θ D.η (ε, w)) := by
    funext w; exact rescaledForceProfile_eq_forceProfile ν hv x₀ T ε D hθ hη w
  rw [hfun]
  have hεIcc : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1.le, hε.2.trans hε₀⟩
  refine (norm_iteratedFDeriv_slice_le (forceProfile_smooth ν hv x₀ T hθ hη) ε z k).trans ?_
  exact (Classical.choose_spec
    (forceProfile_uniform_derivative_bound ν hv x₀ T hθ hη hθc hηc k)).2 ε hεIcc z

/-! ## 5. Field `force_profile_identity` (`Spec.lean:834-837`), chart force -/

/-- The affine `inverseScale ε` of the correction chart is a right inverse of
`correctionChartPoint x₀ T ε`: `inverseScale ε ((T+ε²σ, x₀+εy) − (T,x₀)) = (σ,y)`. -/
theorem inverseScale_correctionChartPoint (x₀ : Space) (T ε : ℝ) (hε : ε ≠ 0)
    (z : SpaceTime) :
    inverseScale ε (correctionChartPoint x₀ T ε z - (T, x₀)) = z := by
  obtain ⟨σ, y⟩ := z
  have h2 : (ε ^ 2) ≠ 0 := pow_ne_zero 2 hε
  simp only [inverseScale_apply, correctionChartPoint, Prod.fst_sub, Prod.snd_sub,
    add_sub_cancel_left, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rw [← mul_assoc, inv_mul_cancel₀ h2, one_mul]
  · rw [smul_smul, inv_mul_cancel₀ hε, one_smul]

/-- `03-torus.tex:264-272`: the **chart force** equals `ε⁻²` times the bracket
`H_ε`.  This is the tree-provable content of `force_profile_identity`; the lift
to the Spec field's `correctionForce ν v D ε` (over `D.correction`) is U2's
`force_eq` (lane 373), whose exact residual is recorded in `ATTEMPTS_U4.md`. -/
theorem physicalForce_eq_rescaledForceProfile (ν : ℝ) {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T : ℝ) (D : CutoffData)
    (hθ : ContDiff ℝ ∞ D.θ) (hη : ContDiff ℝ ∞ D.η) :
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z ∈ fixedProfileCylinder D,
      Source.correctionForce ν v (physicalCorrection v x₀ T D.θ D.η ε)
          (correctionChartPoint x₀ T ε z) =
        (ε ^ 2)⁻¹ • rescaledForceProfile ν v x₀ T ε D z := by
  intro ε hε z _
  rw [physicalForce_eq_profile ν hv x₀ T ε hε.1.ne' hθ hη (correctionChartPoint x₀ T ε z),
    inverseScale_correctionChartPoint x₀ T ε hε.1.ne' z,
    rescaledForceProfile_eq_forceProfile ν hv x₀ T ε D hθ hη z]

end NSFormalization.Section3.T17
