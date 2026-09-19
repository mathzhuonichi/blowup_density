import NSFormalization.Section3.T23.NoSlipUniqueness

open Set MeasureTheory
open NSFormalization.Section3.T23
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)

noncomputable section

private def Ω₀ : Set Space :=
  {x : Space | ∀ i : Fin 3, (0 : ℝ) < x i ∧ x i < 1}

private theorem Ω₀_isBox : IsBoxDomain Ω₀ := by
  exact ⟨(fun _ => 0), (fun _ => 1), (fun _ => zero_lt_one), rfl⟩

private theorem zero_initial (Ω : Set Space) :
    (0 : SpatialField) ∈ initialClassOmega Ω := by
  refine ⟨contDiffOn_const, ?_, ?_⟩
  · intro x hx
    simp [spatialDivergence, spatialDerivative]
  · intro x hx
    rfl

private theorem zero_force (Ω : Set Space) :
    (0 : SpaceTimeField) ∈ forceClassOmega Ω := by
  refine ⟨?_, ⟨∅, isCompact_empty, empty_subset _, ?_⟩⟩
  · intro T
    exact ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  · simp

private def zeroSolution (ν T : ℝ) (hT : 0 < T) :
    ClassicalSolutionOmega ν Ω₀ 0 0 T where
  velocity := 0
  pressure := 0
  horizon_pos := hT
  velocity_smooth := ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  pressure_smooth := ⟨univ, isOpen_univ, subset_univ _, contDiffOn_const⟩
  initial := fun _ _ => rfl
  divergence := by
    intro t ht x hx
    simp [spatialDivergence, spatialDerivative]
  momentum := by
    intro t ht x hx
    simp [NavierStokesR3.ProblemStatement.navierStokesResidual, temporalDerivative,
      advection, spatialDerivative, spatialLaplacian, pressureGradient]
  no_slip := by
    intro t ht x hx
    rfl
  pressure_gauge := by
    intro t ht
    simp

-- A genuine application at the concrete box `(0,1)^3`, with inhabited data
-- and solution records rather than only an abstract specialization.
example :
    (zeroSolution 1 1 zero_lt_one).velocity
        ((1 / 2 : ℝ), WithLp.toLp 2 (fun _ : Fin 3 => (1 / 2 : ℝ))) =
      (zeroSolution 1 1 zero_lt_one).velocity
        ((1 / 2 : ℝ), WithLp.toLp 2 (fun _ : Fin 3 => (1 / 2 : ℝ))) := by
  apply noSlip_uniqueness_box 1 one_pos Ω₀ Ω₀_isBox 0 (zero_initial Ω₀)
    0 (zero_force Ω₀) 1 1 (zeroSolution 1 1 zero_lt_one)
    (zeroSolution 1 1 zero_lt_one)
  · constructor <;> norm_num
  · intro i
    constructor <;> norm_num
