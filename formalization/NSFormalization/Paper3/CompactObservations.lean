import NavierStokes.R3CompactIntegration

/-!
# Compact divergence-free fields have vanishing cell observations

This is an actual Lebesgue-integral ingredient of Paper 3, `thm:Rgrid`.
It does not assert the insertion theorem or the corresponding force-flux identity.
-/

noncomputable section

namespace NSFormalization.Paper3

open MeasureTheory InnerProductSpace
open NavierStokes NavierStokes.ProblemStatement NavierStokes.R3CompactIntegration
open scoped RealInnerProductSpace

/-- Each component of a compact smooth solenoidal field has zero integral on ℝ³.
The proof tests the source integration-by-parts theorem against a linear pressure. -/
theorem integral_component_eq_zero {u : Space → Space}
    (hu : ContDiff ℝ 1 u) (hs : HasCompactSupport u)
    (hd : ∀ x, Comparator.divergence u x = 0) (j : Fin 3) :
    (∫ x : Space, u x j) = 0 := by
  have h := integral_inner_gradient_eq_zero hu
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff hs hd
  have heq (x : Space) :
      ⟪u x, gradient (EuclideanSpace.proj j : Space →L[ℝ] ℝ) x⟫_ℝ = u x j := by
    rw [inner_gradient_right, ContinuousLinearMap.fderiv]
    rfl
  simpa only [heq] using h

/-- Restricting a component to a cell containing its support changes no integral. -/
theorem setIntegral_component_eq_zero {u : Space → Space}
    (hu : ContDiff ℝ 1 u) (hs : HasCompactSupport u)
    (hd : ∀ x, Comparator.divergence u x = 0)
    {C : Set Space} (hC : MeasurableSet C) (hsub : Function.support u ⊆ C)
    (j : Fin 3) : (∫ x in C, u x j) = 0 := by
  rw [← integral_indicator hC]
  have heq : C.indicator (fun x => u x j) = fun x => u x j := by
    funext x
    by_cases hx : x ∈ C
    · simp [hx]
    · have hz : u x = 0 := by
        by_contra hn
        exact hx (hsub hn)
      simp [hx, hz]
  rw [heq]
  exact integral_component_eq_zero hu hs hd j

/-- A cell disjoint from the support also records zero. -/
theorem setIntegral_component_eq_zero_of_disjoint {u : Space → Space}
    {C : Set Space} (hdis : Disjoint C (Function.support u)) (j : Fin 3) :
    (∫ x in C, u x j) = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro x hx
  have hz : u x = 0 := by
    by_contra hn
    exact Set.disjoint_left.mp hdis hx hn
  simp [hz]

/-- Cell observations normalize the actual component integral by the cell volume. -/
def componentCellAverage (C : Set Space) (u : Space → Space) (j : Fin 3) : ℝ :=
  (volume C).toReal⁻¹ * ∫ x in C, u x j

/-- The velocity observation of an integrable reference is preserved exactly
when the compact solenoidal perturbation lies inside this cell. -/
theorem componentCellAverage_add_eq {u v : Space → Space}
    (hu : ContDiff ℝ 1 u) (hs : HasCompactSupport u)
    (hd : ∀ x, Comparator.divergence u x = 0)
    {C : Set Space} (hC : MeasurableSet C) (hsub : Function.support u ⊆ C)
    (j : Fin 3) (hv : IntegrableOn (fun x => v x j) C) :
    componentCellAverage C (fun x => v x + u x) j = componentCellAverage C v j := by
  have hi : IntegrableOn (fun x => u x j) C :=
    ((component_contDiff hu j).continuous.integrable_of_hasCompactSupport
      (component_compact hs j)).integrableOn
  unfold componentCellAverage
  have hadd : (fun x => (v x + u x) j) = (fun x => v x j + u x j) := by
    rfl
  rw [hadd, integral_add hv hi, setIntegral_component_eq_zero hu hs hd hC hsub j,
    add_zero]

/-- A deterministic postprocessor cannot distinguish equal observation data. -/
theorem deterministic_output_eq {Data Output : Type*} (algorithm : Data → Output)
    {regularData singularData : Data} (h : regularData = singularData) :
    algorithm regularData = algorithm singularData := congrArg algorithm h

end NSFormalization.Paper3
