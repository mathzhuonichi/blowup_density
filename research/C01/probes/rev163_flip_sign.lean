import NSFormalization.Section4.C01.Enstrophy

noncomputable section

open Set MeasureTheory
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open NSFormalization.Source.OrdinaryViscousStability
open NavierStokes.ProblemStatement
open scoped RealInnerProductSpace

namespace NSFormalization.Section4.C01

open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)

variable {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {T : ℝ}

-- Negative mutation: flip the main theorem's Laplacian coefficient from `-2` to `+2`.
example (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun s : ℝ => ∫ x, ∑ i : Fin 3,
        ‖fderiv ℝ (fun y : Space => w.velocity (s, y)) x (axis i)‖ ^ 2)
      (2 * (@inner ℝ _ _
        (laplacianField (velocitySliceField w (Ioo_subset_Ico_self ht))).toLp
        (temporalSliceField w hf ht).toLp))
      t := by
  exact enstrophyDerivative_classical_unconditional w hf ht

end NSFormalization.Section4.C01
