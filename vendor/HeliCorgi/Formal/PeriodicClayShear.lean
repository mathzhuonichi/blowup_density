import Formal.PeriodicClayCore
import Formal.PeriodicExplicitShear
import Mathlib.Tactic.FinCases

/-! A nonzero, arbitrary-amplitude periodic family satisfying the full
analytic solution predicate used in the formulation of CMI alternative B.
This is a specialization to shear data, not a proof of alternative B. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff
open Set

namespace ClayNS

theorem spatialDeriv_coordinate (j k : Fin 3) (g : ℝ → ℝ) (x : Point) :
    spatialDeriv j (fun y => g (y k)) x = if j = k then deriv g (x k) else 0 := by
  by_cases h : j = k
  · subst j
    simp [spatialDeriv]
  · simp [spatialDeriv, Function.update_of_ne (Ne.symm h), h]

theorem laplacian_coordinate (k : Fin 3) (g : ℝ → ℝ) (x : Point) :
    laplacian (fun y => g (y k)) x = deriv (deriv g) (x k) := by
  unfold laplacian
  have h (j : Fin 3) :
      spatialDeriv j (spatialDeriv j (fun y => g (y k))) x =
        if j = k then deriv (deriv g) (x k) else 0 := by
    by_cases hj : j = k
    · subst j
      have heq : spatialDeriv k (fun y => g (y k)) = fun y => deriv g (y k) := by
        funext y
        simp only [spatialDeriv_coordinate, if_true]
      rw [heq]
      simp only [spatialDeriv_coordinate, if_true]
    · have hz : spatialDeriv j (fun y => g (y k)) = fun _ => 0 := by
        funext y
        simp [spatialDeriv_coordinate, hj]
      rw [hz]
      simp [hj]
  simp_rw [h]
  simp

def shear (ν a : ℝ) : Velocity :=
  fun t x i => if i = 0 then ExplicitShear.profile ν a (2 * Real.pi) t (x 1) else 0

def shearDatum (a : ℝ) : Point → Point :=
  fun x i => if i = 0 then a * Real.sin (2 * Real.pi * x 1) else 0

theorem shear_initial (ν a : ℝ) (x : Point) : shear ν a 0 x = shearDatum a x := by
  funext i
  simp [shear, shearDatum, ExplicitShear.profile_initial]

theorem shear_contDiff (ν a : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × Point => shear ν a z.1 z.2) := by
  apply contDiff_pi.mpr
  intro i
  by_cases hi : i = 0
  · simp only [shear, hi, if_true]
    exact (ExplicitShear.profile_contDiff ν a (2 * Real.pi)).comp
      (contDiff_fst.prodMk ((contDiff_apply ℝ ℝ (1 : Fin 3)).comp contDiff_snd))
  · simpa only [shear, hi, if_false] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × Point => (0 : ℝ)))

theorem shear_periodic (ν a t : ℝ) : PeriodicSpatial (shear ν a t) := by
  intro x j
  funext i
  by_cases hi : i = 0
  · simp only [shear, hi, if_true]
    by_cases hj : j = 1
    · subst j
      simpa using ExplicitShear.profile_periodic ν a t (x 1)
    · simp [Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hj)]
  · simp [shear, hi]

theorem shear_divergence (ν a t : ℝ) (x : Point) :
    divergence (shear ν a t) x = 0 := by
  unfold divergence
  apply Finset.sum_eq_zero
  intro j hj
  fin_cases j <;> simp [shear, spatialDeriv]

theorem shear_convection (ν a t : ℝ) (x : Point) (i : Fin 3) :
    convection (shear ν a) t x i = 0 := by
  unfold convection
  apply Finset.sum_eq_zero
  intro j hj
  by_cases hi : i = 0
  · subst i
    fin_cases j <;> simp [shear, spatialDeriv]
  · simp [shear, hi, spatialDeriv]

theorem shear_momentum (ν a : ℝ) :
    Momentum ν (shear ν a) (fun _ _ => 0) (fun _ _ _ => 0) := by
  intro t ht x i
  rw [shear_convection]
  by_cases hi : i = 0
  · subst i
    simp only [shear, if_true, laplacian_coordinate,
      ExplicitShear.profile_space_second_deriv, partial_const, sub_zero, add_zero]
    convert! (ExplicitShear.profile_time_hasDerivAt ν a (2 * Real.pi) t (x 1)).hasDerivWithinAt
      (s := Ici 0) using 1
    ring
  · simpa [shear, hi, laplacian, spatialDeriv] using
      (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt (s := Ici 0)

theorem shear_datum_admissible (a : ℝ) : AdmissiblePeriodicDatum (shearDatum a) := by
  have heq : shearDatum a = shear 1 a 0 := by
    funext x
    exact (shear_initial 1 a x).symm
  rw [heq]
  refine ⟨?_, shear_periodic 1 a 0, shear_divergence 1 a 0⟩
  exact (shear_contDiff 1 a).comp (contDiff_const.prodMk contDiff_id)

theorem shear_global_periodic (ν a : ℝ) :
    GlobalPeriodicSolution ν (shearDatum a) (shear ν a) (fun _ _ => 0) := by
  refine ⟨(shear_contDiff ν a).contDiffOn, contDiff_const.contDiffOn,
    ?_, ?_, shear_momentum ν a, ?_, shear_initial ν a⟩
  · intro t ht
    exact shear_periodic ν a t
  · intro t ht x j
    rfl
  · intro t ht x
    exact shear_divergence ν a t x

/-- A genuine infinite-parameter specialization of B; no arbitrary-data claim. -/
theorem clayB_shear_specialization (ν a : ℝ) (_hν : 0 < ν) :
    AdmissiblePeriodicDatum (shearDatum a) ∧
    ∃ u : Velocity, ∃ p : Pressure, GlobalPeriodicSolution ν (shearDatum a) u p := by
  exact ⟨shear_datum_admissible a, shear ν a, (fun _ _ => 0), shear_global_periodic ν a⟩

theorem shear_datum_nonzero (a : ℝ) (ha : a ≠ 0) : shearDatum a ≠ (fun _ _ => 0) := by
  intro h
  have hz := congrFun (congrFun h (fun _ => (1 / 4 : ℝ))) 0
  have harg : 2 * Real.pi * (1 / 4 : ℝ) = Real.pi / 2 := by ring
  change a * Real.sin (2 * Real.pi * (1 / 4 : ℝ)) = 0 at hz
  rw [harg, Real.sin_pi_div_two, mul_one] at hz
  exact ha hz

theorem shear_kinetic_density (ν a t : ℝ) (x : Point) :
    kineticDensity (shear ν a t x) =
      (ExplicitShear.profile ν a (2 * Real.pi) t (x 1)) ^ 2 := by
  simp [kineticDensity, shear]

theorem shear_uniform_energy_density (ν a t : ℝ) (x : Point)
    (hν : 0 ≤ ν) (ht : 0 ≤ t) : kineticDensity (shear ν a t x) ≤ a ^ 2 := by
  rw [shear_kinetic_density]
  exact sq_le_sq.mpr (ExplicitShear.profile_abs_le ν a (2 * Real.pi) t (x 1) hν ht)

#print axioms clayB_shear_specialization
#print axioms shear_datum_nonzero
#print axioms shear_uniform_energy_density

end ClayNS
