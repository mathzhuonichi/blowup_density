import NSFormalization.Section3.T17.Transport

/-!
Probe for lane 373 (T17 U2).  Instantiates the concrete correction data at a
nonzero constant divergence-free reference and checks the two structural
identities `correctionData_correction` (by `rfl`) and `correctionForce_eq_source`.
-/

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T17
open NSFormalization.Section3.T16 (latticeLift)
open NSFormalization.Section3.T10 (IsPeriodicOn)
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Paper1.CorrectionProfile (physicalCorrection)

noncomputable section

/-- A nonzero constant reference field. -/
def vConst : SpaceTimeField := fun _ => EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

/-- The reference is genuinely nonzero. -/
example : vConst ≠ 0 := by
  intro h
  have h0 : (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) = (0 : Space) := congrFun h (0, 0)
  have hn : ‖EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖ = 0 := by rw [h0, norm_zero]
  simp at hn

/-- The reference is divergence free (it is constant). -/
example (t : ℝ) (x : Space) : spatialDivergence vConst t x = 0 := by
  have : spatialDerivative vConst t x = 0 := by
    simp only [spatialDerivative, vConst]; exact fderiv_const_apply _
  simp [spatialDivergence, this]

/-- The reference is unit-periodic (it is constant). -/
example : IsPeriodicOn univ vConst := fun _ _ _ _ => rfl

/-- The concrete correction is, verbatim, the lattice lift of the single
Euclidean copy — checked by `rfl` at the nonzero constant reference. -/
example (x₀ : Space) (T : ℝ) (θ : Space → ℝ) (η : ℝ → ℝ) (O : Set Space) (θR ε₀ ε : ℝ) :
    (correctionData vConst x₀ T θ η O θR ε₀).correction ε
      = latticeLift (physicalCorrection vConst x₀ T θ η ε) := rfl

/-- The T17 force spelling agrees with the Section 4 operator on this data. -/
example (ν : ℝ) (x₀ : Space) (T : ℝ) (θ : Space → ℝ) (η : ℝ → ℝ) (O : Set Space) (θR ε₀ ε : ℝ) :
    correctionForce ν vConst (correctionData vConst x₀ T θ η O θR ε₀) ε
      = NSFormalization.Source.correctionForce ν vConst
          ((correctionData vConst x₀ T θ η O θR ε₀).correction ε) :=
  correctionForce_eq_source ν vConst (correctionData vConst x₀ T θ η O θR ε₀) ε

/-- The full transport identity is available with the T16 cutoff hypotheses. -/
example : True := by
  have _ := @force_eq
  have _ := @correctionForce_periodic
  trivial

end
