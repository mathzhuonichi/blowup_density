import NSFormalization.Section3.T15.Blowup
import NSFormalization.Section3.T15.ForceMem
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# T15 U6/U7 conformance and concrete geometric probe

The first two examples copy the canonical `ScalingAPI` field types and close
them by a bare `exact`.  The concrete probe uses a compact spatial bump with a
`(1-t)⁻¹` amplitude, the cube-centred placement from the U2/U3 geometry, and
the zero force.  It therefore exercises genuine speed blow-up together with a
concrete `MemForceT` conclusion at scale `ε=1/2`.
-/

noncomputable section

namespace NSFormalization.Section3.T15

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Source.PacketScaling
open scoped ContDiff Topology

/-! ## Literal canonical field checks -/

section FieldChecks

variable {u f : VelocityField} {p : PressureField} {K : Set Space}
variable (hK : IsCompact K)
variable (hu : ∀ t ∈ Ico (0 : ℝ) 1,
  tsupport (fun x : Space => u (t, x)) ⊆ K)
variable (hspeed : SpeedUnboundedAtOne u)
variable (hfsmooth : ContDiff ℝ ∞ f)
variable (hfsupport : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
variable (place : PlacementData u p f K)

example : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    SpeedUnboundedAt place.T
      (periodizedScaledVelocity u place.x₀ place.T ε) := by
  exact unboundedSpeed hK hu hspeed place

example : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    MemForceT (periodizedScaledForce f place.x₀ place.T ε) := by
  exact force_mem hfsmooth hfsupport place

end FieldChecks

/-! ## Concrete nonzero blow-up geometry -/

def bfmCenter : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun _ => (1 / 2 : ℝ))

def bfmBump : ContDiffBump (0 : Space) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

def bfmField : Space → Space := fun x => bfmBump x • coordinateVector 0

def bfmVelocity : VelocityField :=
  fun z => (1 - z.1)⁻¹ • bfmField z.2

def bfmPressure : PressureField := fun _ => 0

def bfmForce : VelocityField := fun _ => 0

def bfmCarrier : Set Space := Metric.closedBall (0 : Space) (1 / 4)

theorem bfmField_tsupport : tsupport bfmField ⊆ bfmCarrier := by
  have hsub : Function.support bfmField ⊆ Function.support (⇑bfmBump) := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hz
    exact hx (by simp [bfmField, hz])
  have h : tsupport bfmField ⊆ tsupport (⇑bfmBump) := closure_mono hsub
  change tsupport bfmField ⊆ Metric.closedBall (0 : Space) (1 / 4)
  rwa [bfmBump.tsupport_eq] at h

theorem bfmVelocity_support : ∀ t ∈ Ico (0 : ℝ) 1,
    tsupport (fun x : Space => bfmVelocity (t, x)) ⊆ bfmCarrier := by
  intro t _
  have hsub : Function.support (fun x : Space => bfmVelocity (t, x)) ⊆
      Function.support bfmField := by
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hz
    exact hx (by simp [bfmVelocity, hz])
  exact (closure_mono hsub).trans bfmField_tsupport

theorem bfmSpeed : SpeedUnboundedAtOne bfmVelocity := by
  intro M hM δ hδ
  let d : ℝ := min (δ / 2) ((M + 1)⁻¹)
  let t : ℝ := 1 - d
  have hMp : 0 < M + 1 := by linarith
  have hd : 0 < d := lt_min (div_pos hδ (by norm_num)) (inv_pos.mpr hMp)
  have hdδ : d < δ :=
    (min_le_left _ _).trans_lt (by linarith)
  have hdinv : d < M⁻¹ :=
    (min_le_right _ _).trans_lt (inv_strictAnti₀ hM (by linarith))
  have hd1 : d < 1 :=
    (min_le_right _ _).trans_lt (by
      simpa only [inv_one] using inv_strictAnti₀ (show (0 : ℝ) < 1 by norm_num)
        (show (1 : ℝ) < M + 1 by linarith))
  have ht : t ∈ Ioo (0 : ℝ) 1 := by
    dsimp [t]
    constructor <;> linarith
  have hlarge : M < d⁻¹ := lt_inv_of_lt_inv₀ hd hdinv
  have hbump : bfmBump (0 : Space) = 1 :=
    bfmBump.one_of_mem_closedBall (by norm_num [bfmBump])
  have hfield : bfmField (0 : Space) = coordinateVector 0 := by
    simp [bfmField, hbump]
  refine ⟨t, 0, ht, ?_, ?_⟩
  · dsimp [t]
    linarith
  · have hnorm : ‖bfmVelocity (t, 0)‖ = d⁻¹ := by
      simp only [bfmVelocity, t, sub_sub_cancel, hfield, norm_smul, Real.norm_eq_abs]
      rw [abs_of_pos (inv_pos.mpr hd)]
      simp [coordinateVector]
    rwa [hnorm]

theorem bfmForce_smooth : ContDiff ℝ ∞ bfmForce := contDiff_const

theorem bfmForce_support :
    NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport bfmForce := by
  have hz : tsupport bfmForce = (∅ : Set SpaceTime) := by
    have hs : Function.support bfmForce = (∅ : Set SpaceTime) := by
      change Function.support (fun _ : SpaceTime => (0 : Space)) = ∅
      exact Function.support_eq_empty_iff.mpr rfl
    simp [tsupport, hs]
  constructor
  · rw [HasCompactSupport, hz]
    exact isCompact_empty
  · rw [hz]
    exact empty_subset _

theorem bfm_chartBall_in_cube :
    closure (Metric.ball bfmCenter (3 / 8 : ℝ)) ⊆ interior fundamentalCube := by
  refine (Metric.closure_ball_subset_closedBall).trans ?_
  rw [interior_fundamentalCube]
  intro x hx i
  have hd : ‖x - bfmCenter‖ ≤ 3 / 8 := by
    rw [← dist_eq_norm]
    exact hx
  have hcoord : |x i - bfmCenter i| ≤ 3 / 8 := by
    have h := abs_spaceCoord_le_norm (x - bfmCenter) i
    have heq : (x - bfmCenter) i = x i - bfmCenter i := rfl
    rw [heq] at h
    linarith
  have hc : bfmCenter i = 1 / 2 := rfl
  rw [hc, abs_le] at hcoord
  exact ⟨by linarith [hcoord.1], by linarith [hcoord.2]⟩

theorem bfm_eps_space : ∀ ε ∈ Ioc (0 : ℝ) (1 / 2), ∀ y ∈ bfmCarrier,
    bfmCenter + ε • y ∈ Metric.ball bfmCenter (3 / 8) := by
  intro ε hε y hy
  rw [Metric.mem_ball, dist_eq_norm]
  have hsub : bfmCenter + ε • y - bfmCenter = ε • y := by abel
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hε.1]
  have hyn : ‖y‖ ≤ 1 / 4 := by
    simpa only [bfmCarrier, Metric.mem_closedBall, dist_zero_right] using hy
  have hmul : ε * ‖y‖ ≤ (1 / 2 : ℝ) * (1 / 4) :=
    mul_le_mul hε.2 hyn (norm_nonneg _) (by norm_num)
  linarith

def bfmPlacement : PlacementData bfmVelocity bfmPressure bfmForce bfmCarrier where
  T := 1
  time_pos := by norm_num
  chartCenter := bfmCenter
  chartRadius := 3 / 8
  chartRadius_pos := by norm_num
  chartBall_in_cube := bfm_chartBall_in_cube
  x₀ := bfmCenter
  x₀_mem := by simp
  Kstar := bfmCarrier
  Kstar_compact := isCompact_closedBall _ _
  carrier_subset := Subset.rfl
  force_projection_subset := by
    intro t x h
    have hz : tsupport bfmForce = (∅ : Set SpaceTime) := by
      have hs : Function.support bfmForce = (∅ : Set SpaceTime) := by
        change Function.support (fun _ : SpaceTime => (0 : Space)) = ∅
        exact Function.support_eq_empty_iff.mpr rfl
      simp [tsupport, hs]
    rw [hz] at h
    exact h.elim
  ε₀ := 1 / 2
  eps_pos := by norm_num
  eps_le_one := by norm_num
  eps_time := by
    intro ε hε
    have hprod : 0 ≤ (1 / 2 - ε) * (1 / 2 + ε) :=
      mul_nonneg (sub_nonneg.mpr hε.2) (add_nonneg (by norm_num) hε.1.le)
    have hsquare : ε ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by nlinarith
    nlinarith
  eps_space := bfm_eps_space

/-- The two delivered fields fire simultaneously on explicit placement data;
the velocity is genuinely unbounded and the force is a concrete smooth compact
positive-time force (the zero member of the class). -/
theorem blowup_force_mem_concrete :
    SpeedUnboundedAt bfmPlacement.T
        (periodizedScaledVelocity bfmVelocity bfmPlacement.x₀ bfmPlacement.T (1 / 2)) ∧
      MemForceT
        (periodizedScaledForce bfmForce bfmPlacement.x₀ bfmPlacement.T (1 / 2)) := by
  have hε : (1 / 2 : ℝ) ∈ Ioc (0 : ℝ) bfmPlacement.ε₀ := by
    change (1 / 2 : ℝ) ∈ Ioc 0 (1 / 2)
    norm_num
  exact ⟨unboundedSpeed (isCompact_closedBall _ _) bfmVelocity_support bfmSpeed
      bfmPlacement (1 / 2) hε,
    force_mem bfmForce_smooth bfmForce_support bfmPlacement (1 / 2) hε⟩

end NSFormalization.Section3.T15
