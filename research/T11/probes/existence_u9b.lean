import NSFormalization.Section3.T11.LocalExistence

noncomputable section
namespace NSFormalization.Section3.T11.U9bProbe
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ENNReal NNReal ContDiff

local instance u9bProbeNormedGroup : NormedAddCommGroup (PeriodicSobolev 3) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance u9bProbeNormedSpace : NormedSpace ℝ (PeriodicSobolev 3) :=
  realPeriodicSubmodule.normedSpace

-- Completeness does not assume any analytic residue.
example : CompleteSpace (PeriodicSobolev 3) := inferInstance

-- Zero-data instance of the exact forced solver.
example (C : TorusTwoSpaceContract 1) :
    let T := torusKernelTime 1 (torusPicardThreshold ‖C.analytic.bilinear‖ 0)
    0 < T ∧ ∃ u : ℝ → PeriodicSobolev 3,
      TorusForcedMildOn C 0 (fun _ ↦ 0) T u ∧ ∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ 1 := by
  obtain ⟨ht, _, u, hu, hb, _⟩ := torusForcedPicard_quantitative (by norm_num) C
    0 (fun _ ↦ 0) 0 le_rfl continuousOn_const (by simp)
  simp only [norm_zero, add_zero, zero_add] at ht hu hb
  exact ⟨ht, u, hu, hb⟩

-- A nonzero single Fourier mode: the real constant velocity e₁.
example : torusConstantDatum 3 (coordinateVector 0) ≠ 0 := by
  intro h
  have hc := congrArg (fun A : PeriodicSobolev 3 ↦ A.1 0 (0 : PeriodicFrequency)) h
  norm_num [torusConstantDatum, coordinateVector] at hc

-- A nonzero datum AND nonzero forcing in the coefficient solver.
example (C : TorusTwoSpaceContract 1) :
    let A := torusConstantDatum 3 (coordinateVector 0)
    let T := torusKernelTime 1 (torusPicardThreshold ‖C.analytic.bilinear‖ (‖A‖+‖A‖))
    0 < T ∧ ∃ u : ℝ → PeriodicSobolev 3,
      TorusForcedMildOn C A (fun _ ↦ A) T u ∧
      ∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ ‖A‖+‖A‖+1 := by
  let A := torusConstantDatum 3 (coordinateVector 0)
  obtain ⟨ht, _, u, hu, hb, _⟩ := torusForcedPicard_quantitative (by norm_num) C
    A (fun _ ↦ A) ‖A‖ (norm_nonneg _) continuousOn_const (fun _ _ ↦ le_rfl)
  exact ⟨ht, u, hu, hb⟩

-- The actual convolution is absolutely convergent even without its boundedness input.
example (A B : PeriodicSobolev 3) (i j : Fin 3) (k : PeriodicFrequency) :
    Summable (fun l : PeriodicFrequency ↦
      ‖(((periodicFrequencyWeight l) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * A.1 j l *
        (((periodicFrequencyWeight (k-l)) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * B.1 i (k-l)‖) :=
  torusConvolution_summable A B i j k

example (i : Fin 3) (k : PeriodicFrequency) :
    torusProjectedConvectionSymbol (torusConstantDatum 3 (coordinateVector 0))
      (torusConstantDatum 3 (coordinateVector 0)) i k = 0 :=
  torusProjectedConvectionSymbol_constants _ _ i k

-- The one residual input supplies the entire contract, including endpoint analysis.
example (H : TorusConvolutionInput) : Nonempty (TorusTwoSpaceContract 1) :=
  torusTwoSpaceContract_nonempty H 1 (by norm_num)

-- Unconditional nonzero physical witness for the amended quantifiers.
example :
    ∃ (K : ℝ≥0∞) (M : ℕ → ℝ≥0∞)
      (a : NSFormalization.Section4.A02.SpatialField)
      (g : NSFormalization.Section4.A02.SpaceTimeField),
      K ≠ ⊤ ∧ (∀ m, M m ≠ ⊤) ∧ a ∈ initialClassT ∧ periodicSobolevENorm 1 a ≤ K ∧
      ContDiff ℝ ∞ g ∧ IsPeriodicOn univ g ∧
      (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ M m) ∧
      ∃ w : ClassicalSolutionT 1 a g 1,
        PeriodicLocalRegularity 1 a g 1 w ∧ w.velocity (0, 0) ≠ 0 ∧ g (0, 0) ≠ 0 :=
  nonzero_forced_witness'

end NSFormalization.Section3.T11.U9bProbe
