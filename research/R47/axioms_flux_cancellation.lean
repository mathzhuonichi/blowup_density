import Bindings.FluxCancellation

/-! Audit every declaration; probes instantiate the actual R42 family at a
positive scale and an interior time. No extra analytic hypotheses are supplied. -/
noncomputable section
open Set MeasureTheory
open BlowupDensity.Contracts.V1 BlowupDensity.Contracts.V1.Data
open BlowupDensity.Bindings

#print axioms compact_directional_integral
#print axioms compact_flux_integral
#print axioms tensorDifference_compact
#print axioms advectionDifference_integral
#print axioms pressureGradient_sub_timeConstant
#print axioms pressureGradientDifference_integral
#print axioms laplacianDifference_integral
#print axioms residualDifference_integral
#print axioms insertion_reference_pressure_smooth
#print axioms compactMomentumIntegral
#print axioms forceDifference_cell_integral_zero'
#print axioms force_gridObservation_eq'

-- Every R42 record supplies an admissible positive scale and interior time.
example {ν : ℝ} {P : PacketAPI ν} (A : InsertionFamilyAPI ν P)
    (grid : Grid) (k : Fin 3 → ℤ) (hB : A.ball ⊆ grid.cell k) :
    ∃ ε ∈ Ioc 0 A.ε₀, ∃ t ∈ Ioo 0 A.T,
      (∫ x in grid.cell k, (A.force ε (t,x) - A.g (t,x))) = 0 := by
  have hT : 0 < A.T := A.scaling.correction.time_pos
  refine ⟨A.ε₀, ⟨A.eps_pos, le_rfl⟩, A.T / 2, ⟨by linarith, by linarith⟩, ?_⟩
  exact forceDifference_cell_integral_zero' A ⟨A.eps_pos, le_rfl⟩
    ⟨by linarith, by linarith⟩ grid k hB

-- The exact formerly named input fires without a supplied flux hypothesis.
example {ν : ℝ} {P : PacketAPI ν} (A : InsertionFamilyAPI ν P)
    (grid : Grid) (k : Fin 3 → ℤ) (hB : A.ball ⊆ grid.cell k) :
    (∫ x in grid.cell k,
      (NavierStokesR3.ProblemStatement.navierStokesResidual ν
        (A.velocity A.ε₀) (A.pressure A.ε₀) (A.T / 2) x -
       NavierStokesR3.ProblemStatement.navierStokesResidual ν A.v A.π (A.T / 2) x)) =
    (∫ x : Space, deriv (fun s => A.velocity A.ε₀ (s,x) - A.v (s,x)) (A.T / 2)) := by
  have hT : 0 < A.T := A.scaling.correction.time_pos
  exact compactMomentumIntegral A A.ε₀ ⟨A.eps_pos, le_rfl⟩ grid k hB
    (A.T / 2) ⟨by linarith, by linarith⟩

-- Force observations use only the original regular-reference-force assumption.
example {ν : ℝ} {P : PacketAPI ν} (A : InsertionFamilyAPI ν P)
    (hg : MemForceR A.g) (grid : Grid) (k : Fin 3 → ℤ)
    (hB : A.ball ⊆ grid.cell k) :
    gridObservation grid (fun x => A.force A.ε₀ (A.T / 2,x)) =
      gridObservation grid (fun x => A.g (A.T / 2,x)) := by
  have hT : 0 < A.T := A.scaling.correction.time_pos
  exact force_gridObservation_eq' A hg ⟨A.eps_pos, le_rfl⟩
    ⟨by linarith, by linarith⟩ grid k hB

-- A nonconstant-in-time pressure gauge is harmless without time regularity assumptions.
example (p : PressureField) (x : Space) (t : ℝ) :
    NavierStokes.ProblemStatement.pressureGradient (fun z => p z - z.1 ^ 2) t x =
      NavierStokes.ProblemStatement.pressureGradient p t x :=
  pressureGradient_sub_timeConstant p (fun s => s ^ 2) t x
