import NSFormalization.Section4.A01.AprioriRows

/-! Reviewer probe for lane 149, gap `hword_jet`: the words it quantifies over include the
**angular** ones (direction `0`, `standardDirection 0 = (0,1)`), which no property of the spatial
slice `z` can control.  Under the angle invariance `hu` of residual row (iv) those words vanish,
so `hword_jet` is discharged trivially for them and only the *spatial* words need the
descent-to-classical-jet identity.  Conclusion: discharging `hword_jet` is **not** invariance-free. -/

noncomputable section
namespace Rev149Angular
open Set MeasureTheory
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity
open scoped ENNReal ContDiff
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

set_option autoImplicit false in
/-- Every derivative word whose **leading** direction is the angular one vanishes, for an
angle-invariant cylinder field. -/
theorem word_angular_eq_zero {q n : ℕ} (u : SobolevSpace 1 q)
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 q (0, θ) u = u)
    (hn : n < q) (w : Fin n → Fin 4) :
    word 1 u (Nat.succ_le_of_lt hn) (Fin.cons 0 w) = 0 := by
  have hword : ∀ θ : AddCircle (1 : ℝ),
      translation 1 (0, θ) (word 1 u hn.le w) = word 1 u hn.le w :=
    fun θ => congrArg (fun v : SobolevSpace 1 q => v.val ⟨⟨n, Nat.lt_succ_of_le hn.le⟩, w⟩) (hu θ)
  have hpath : ∀ t : ℝ,
      translationPath 1 (standardDirection 0) t = ((0 : Vector3), ((t : ℝ) : AddCircle (1 : ℝ))) := by
    intro t
    simp [translationPath, coveringMap, standardDirection_zero, Prod.smul_mk]
  have hderiv := word_hasDerivAt 1 u hn w 0
  have hfun : (fun t : ℝ =>
      translation 1 (translationPath 1 (standardDirection 0) t) (word 1 u hn.le w))
      = fun _ : ℝ => word 1 u hn.le w := by
    funext t
    rw [hpath t]
    exact hword ((t : ℝ) : AddCircle (1 : ℝ))
  rw [hfun] at hderiv
  exact ((hasDerivAt_const (0 : ℝ) (word 1 u hn.le w)).unique hderiv).symm

end Rev149Angular
