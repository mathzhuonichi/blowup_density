import Bindings.ForceCellIntegral

/-! Each declaration below must print exactly the standard three axioms.
The probes use the actual R42 record at positive admissible scale and interior
time, not a zero velocity field (which cannot satisfy its blowup field).
-/
noncomputable section
open Set MeasureTheory
open BlowupDensity.Contracts.V1 BlowupDensity.Contracts.V1.Data
open BlowupDensity.Bindings

#print axioms insertion_reference_smooth
#print axioms velocityDifference_slice_smooth
#print axioms velocityDifference_slice_compact
#print axioms velocityDifference_cell_integral_zero_component
#print axioms velocityDifference_cell_integral_zero
#print axioms insertion_momentum_difference
#print axioms forceDifference_initial_zero
#print axioms velocityDifference_timeDerivative_integral_zero
#print axioms forceDifference_cell_integral_zero
#print axioms continuous_integrableOn_grid_cell
#print axioms forceDifference_slice_support
#print axioms velocity_gridObservation_eq
#print axioms force_gridObservation_eq
#print axioms force_gridObservation_initial_eq

-- The scale and time hypotheses are inhabited for every actual R42 family.
example {ν : ℝ} {P : PacketAPI ν} (A : InsertionFamilyAPI ν P)
    (grid : Grid) (k : Fin 3 → ℤ) (hB : A.ball ⊆ grid.cell k) :
    ∃ ε ∈ Ioc 0 A.ε₀, ∃ t ∈ Ioo 0 A.T,
      (∫ x in grid.cell k, (A.velocity ε (t,x) - A.v (t,x))) = 0 := by
  have hT : 0 < A.T := A.scaling.correction.time_pos
  refine ⟨A.ε₀, ⟨A.eps_pos, le_rfl⟩, A.T / 2, ⟨by linarith, by linarith⟩, ?_⟩
  exact velocityDifference_cell_integral_zero A ⟨A.eps_pos, le_rfl⟩
    ⟨by linarith, by linarith⟩ grid k hB

-- At zero even grids not containing the insertion ball see identical forces.
example {ν : ℝ} {P : PacketAPI ν} (A : InsertionFamilyAPI ν P) (grid : Grid) :
    gridObservation grid (fun x => A.force A.ε₀ (0,x)) =
      gridObservation grid (fun x => A.g (0,x)) :=
  force_gridObservation_initial_eq A ⟨A.eps_pos, le_rfl⟩ grid

-- Integrability is genuine on a nonzero field, independent of PDE assumptions.
example (grid : Grid) (k : Fin 3 → ℤ) (c : Space) :
    IntegrableOn (fun _ : Space => c) (grid.cell k) :=
  continuous_integrableOn_grid_cell grid k continuous_const

-- The temporal term also fires at a strictly interior, positive time.
example {ν : ℝ} {P : PacketAPI ν} (A : InsertionFamilyAPI ν P) :
    (∫ x : Space, deriv (fun s => A.velocity A.ε₀ (s,x) - A.v (s,x)) (A.T / 2)) = 0 := by
  have hT : 0 < A.T := A.scaling.correction.time_pos
  exact velocityDifference_timeDerivative_integral_zero A ⟨A.eps_pos, le_rfl⟩
    ⟨by linarith, by linarith⟩
