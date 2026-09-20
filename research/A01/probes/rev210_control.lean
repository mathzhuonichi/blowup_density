import NSFormalization.Section4.A01.Continuation
import NSFormalization.Section4.A04.Forcing

/-!
Uniform Picard existence under the actual coefficient sup bounds.
This is not the requested physical H⁷/L¹-force horizon theorem: the vendor
ball budget uses a time supremum of the force. Nor does existence on a common
interval bound an independently chosen existential witness from below.
-/
noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory EulerCylinderSobolevSpace EulerSobolevHeat EulerQuadraticSource
open NSFormalization.Source.ForcedCylinderLocal
open scoped Topology ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

open A02 (SpatialField SpaceTimeField initialClassR)
open D01 (MemForceR sobolevENorm)
open A04 (forceSobolevENormL1)

/-- The unchanged H¹ obligation, parameterized by the horizon to be supplied.
The body is copied token-for-token from Spec.lean's field. No proof is asserted. -/
def HorizonLowerBoundH1 (horizon : ℝ → SpatialField → SpaceTimeField → ℝ) : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (a : SpatialField) (f : SpaceTimeField),
        a ∈ initialClassR → MemForceR f →
          sobolevENorm 1 a ≤ K → forceSobolevENormL1 1 f ≤ K →
            δ ≤ horizon ν a f

/-- Separate, also unresolved, requested H⁷/L¹ obligation. Changing spatial
order does not turn an L¹ force bound into the vendor's time supremum bound. -/
def HorizonLowerBoundH7L1 (horizon : ℝ → SpatialField → SpaceTimeField → ℝ) : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (a : SpatialField) (f : SpaceTimeField),
        a ∈ initialClassR → MemForceR f →
          sobolevENorm 7 a ≤ K → forceSobolevENormL1 7 f ≤ K →
            δ ≤ horizon ν a f

/-- The source ball bound is monotone on nonnegative radii. -/
theorem picard_ballBound_mono {X Y T : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [TopologicalSpace T] [CompactSpace T]
    (C : Coefficients T X Y) {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    C.ballBound r ≤ C.ballBound R := by
  let : SeminormedAddCommGroup (X →L[ℝ] X →L[ℝ] Y) := inferInstance
  unfold Coefficients.ballBound
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg C.projection)
  exact add_le_add
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hrR (norm_nonneg C.linear)))
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrR 2) (norm_nonneg C.quadratic))

/-- The source Lipschitz constant is monotone in the radius. -/
theorem picard_ballLipschitz_mono {X Y T : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [TopologicalSpace T] [CompactSpace T]
    (C : Coefficients T X Y) {r R : ℝ} (hrR : r ≤ R) :
    C.ballLipschitz r ≤ C.ballLipschitz R := by
  let : SeminormedAddCommGroup (X →L[ℝ] X →L[ℝ] Y) := inferInstance
  unfold Coefficients.ballLipschitz
  exact mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left hrR (mul_nonneg (by norm_num) (norm_nonneg C.quadratic))))
    (norm_nonneg C.projection)

/-- Both budgets transfer from larger coefficient bounds to smaller ones. -/
theorem picard_budget_mono {ν T M L M' L' : ℝ} (hT : 0 ≤ T)
    (hM : M ≤ M') (hL : L ≤ L')
    (hb : (T + 2 * parabolicConstant ν * Real.sqrt T) * M' < 1)
    (hl : (T + 2 * parabolicConstant ν * Real.sqrt T) * L' < 1) :
    (T + 2 * parabolicConstant ν * Real.sqrt T) * M < 1 ∧
    (T + 2 * parabolicConstant ν * Real.sqrt T) * L < 1 := by
  have hm : 0 ≤ T + 2 * parabolicConstant ν * Real.sqrt T :=
    add_nonneg hT (mul_nonneg (mul_nonneg (by norm_num) (parabolicConstant_nonneg ν))
      (Real.sqrt_nonneg T))
  exact ⟨(mul_le_mul_of_nonneg_left hM hm).trans_lt hb,
    (mul_le_mul_of_nonneg_left hL hm).trans_lt hl⟩

/-- A common positive horizon for H⁷ cylinder data and uniformly bounded
coefficient bundles. Both M and L are chosen before the bundle and datum.
This theorem deliberately does not carry the name horizon_lower_bound_H7. -/
theorem exists_uniform_H7_coefficient_horizon {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R) (M L : ℝ) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδS : δ ≤ S),
      ∀ (C : Coefficients (Icc (0 : ℝ) S) (SobolevSpace 1 7) (SobolevSpace 1 6)),
        C.ballBound (R+1) ≤ M → C.ballLipschitz (R+1) ≤ L →
        ∀ a : SobolevSpace 1 7, ‖a‖ ≤ R →
          ∃ u : C(Icc (0 : ℝ) δ, SobolevSpace 1 7),
            ‖u‖ ≤ R+1 ∧ u ⟨0, le_rfl, hδ.le⟩ = a ∧
              ∀ t, u t = quadraticDuhamel 1 ν hν
              hδ.le hδS C a u t := by
  obtain ⟨δ, hδ, hδS, hb, hl⟩ := exists_positive_time_budget ν M L 1 S one_pos hS
  refine ⟨δ, hδ, hδS, ?_⟩
  intro C hM hL a ha
  have hR1 : 0 ≤ R+1 := by linarith
  obtain ⟨hb', hl'⟩ := picard_budget_mono hδ.le hM hL hb hl
  let F := (C.comp (timeInclusion hδS)).apply
  have hbudget : ‖a‖ + (δ + 2 * parabolicConstant ν * Real.sqrt δ) *
      C.ballBound (R+1) ≤ R+1 := by linarith
  obtain ⟨u, hu, hsol⟩ := exists_viscous_mild_solution 1 6 ν hν δ hδ.le a F
    (C.comp (timeInclusion hδS)).continuous (R+1)
    (C.ballBound (R+1)) (C.ballLipschitz (R+1)) hR1
    (C.ballBound_nonneg _ hR1) (C.ballLipschitz_nonneg _ hR1)
    (fun t x hx => C.apply_bound _ hR1 (timeInclusion hδS t) x hx)
    (fun t x y hx hy => C.apply_sub_bound _ hR1 (timeInclusion hδS t) x y hx hy)
    hbudget hl'
  refine ⟨u, hu, ?_, hsol⟩
  have hzero := hsol ⟨0, le_rfl, hδ.le⟩
  simpa only [mul_zero, Real.toNNReal_zero, heatOperator_zero,
    intervalIntegral.integral_same, add_zero] using hzero

/-- Uniform H⁷ cylinder existence for a varying force path bounded in CₜH⁶.
The force bound B is a time supremum, not an L¹ norm. -/
theorem exists_uniform_H7_sup_force_horizon {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R) (B : ℝ) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδS : δ ≤ S),
      ∀ F : C(Icc (0 : ℝ) S, SobolevSpace 1 6), ‖F‖ ≤ B →
        ∀ a : SobolevSpace 1 7, ‖a‖ ≤ R →
          ∃ u : C(Icc (0 : ℝ) δ, SobolevSpace 1 7),
            ‖u‖ ≤ R+1 ∧ u ⟨0, le_rfl, hδ.le⟩ = a ∧
              ∀ t, u t = quadraticDuhamel 1 ν hν hδ.le hδS
              (coefficients 1 (le_refl 6) F) a u t := by
  let : SeminormedAddCommGroup (SobolevSpace 1 7 →L[ℝ]
      SobolevSpace 1 7 →L[ℝ] SobolevSpace 1 6) := inferInstance
  let : SeminormedAddCommGroup (SobolevSpace 1 7 →L[ℝ] SobolevSpace 1 6) := inferInstance
  let C₀ := coefficients 1 (le_refl 6)
    (0 : C(Icc (0 : ℝ) S, SobolevSpace 1 6))
  let M := ‖C₀.projection‖ * (B + ‖C₀.quadratic‖ * (R+1)^2)
  obtain ⟨δ, hδ, hδS, hlocal⟩ := exists_uniform_H7_coefficient_horizon hν hS hR
    M (C₀.ballLipschitz (R+1))
  refine ⟨δ, hδ, hδS, ?_⟩
  intro F hF a ha
  apply hlocal (coefficients 1 (le_refl 6) F) _ (le_refl _) a ha
  change ‖C₀.projection‖ * (‖-F‖ + ‖(0 : C(Icc (0 : ℝ) S,
    SobolevSpace 1 7 →L[ℝ] SobolevSpace 1 6))‖ * (R+1) +
    ‖C₀.quadratic‖ * (R+1)^2) ≤ M
  simp only [norm_neg, _root_.norm_zero, zero_mul, add_zero]
  exact mul_le_mul_of_nonneg_left (add_le_add hF le_rfl)
    (norm_nonneg C₀.projection)

/-- Non-vacuity: the uniform theorem applies to zero data and the actual
Navier–Stokes quadratic coefficient bundle with zero force. -/
theorem uniform_H7_zero {ν : ℝ} (hν : 0 < ν) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1),
      ∃ u : C(Icc (0 : ℝ) δ, SobolevSpace 1 7),
        ‖u‖ ≤ 1 ∧ u ⟨0, le_rfl, hδ.le⟩ = 0 ∧
          ∀ t, u t = quadraticDuhamel 1 ν hν hδ.le hδ1
            (coefficients 1 (le_refl 6) (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 6)))
            0 u t := by
  obtain ⟨δ, hδ, hδ1, hlocal⟩ := exists_uniform_H7_sup_force_horizon hν
    (show (0 : ℝ) < 1 by norm_num) (show (0 : ℝ) ≤ 0 from le_rfl) 0
  obtain ⟨u, hu, hu0, hsol⟩ := hlocal 0 (by simp) 0 (by simp)
  exact ⟨δ, hδ, hδ1, u, by simpa using hu, hu0, hsol⟩

end NSFormalization.Section4.A01
