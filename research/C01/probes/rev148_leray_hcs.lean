import NSFormalization.Section4.C01.PressureJetPath

/-!
Reviewer probe 2 for lane 148.
(a) M3' — is `D01.Leray.lerayComplement` definitionally the identity?  (EXPECTED TO FAIL.)
(b) N5 — is `hcS : c ≤ S` removable from `pressureGradientPath_jetLp_continuous`?
    The lane's own proof script, verbatim, with the `hcS` binder deleted.  (EXPECTED TO SUCCEED.)
-/

noncomputable section

open Set MeasureTheory Filter Topology
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open NavierStokes.ProblemStatement
  (temporalDerivative advection spatialLaplacian pressureGradient coordinateVector Space)

namespace NSFormalization.Section4
open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)
open NSFormalization.Paper3 (RealVectorSobolev)

variable {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {c S T : ℝ}

set_option maxHeartbeats 100000 in
example (s : ℝ) (h : RealVectorSobolev s) : D01.Leray.lerayComplement s h = h := rfl

theorem pressureGradientPath_jetLp_continuous_noHcS
    (w : ClassicalSolutionR ν a f T) (hf : MemForceR f) (hc : 0 < c)
    (hST : S < T) (n : ℕ) :
    Continuous (fun t : Icc c S =>
      (C01.pressureGradientField w hf (C01.mem_Ioo_of_mem_Icc hc hST t.2)).jetLp n) := by
  have hn : n ≤ n := le_refl n
  have hdatum : Continuous (fun t : Icc c S =>
      D01.smoothAngularDatum n (n : ℝ) (le_refl _) (C01.residualPathIcc w hf hc hST t)) :=
    C01.smoothAngularDatum_path_continuous (C01.residualPathIcc w hf hc hST)
      (C01.residualPathIcc_jetLp_continuous w hf hc hST) n
  have hleray : Continuous (fun t : Icc c S =>
      D01.Leray.lerayComplement (n : ℝ)
        (D01.smoothAngularDatum n (n : ℝ) (le_refl _) (C01.residualPathIcc w hf hc hST t))) :=
    (D01.Leray.lerayComplement (n : ℝ)).continuous.comp hdatum
  have hisdat : ∀ t : Icc c S,
      D01.IsSobolevDatum (n : ℝ) (fun x => pressureGradient w.pressure t.1 x)
        (D01.Leray.lerayComplement (n : ℝ)
          (D01.smoothAngularDatum n (n : ℝ) (le_refl _) (C01.residualPathIcc w hf hc hST t))) := by
    intro t
    refine D01.isSobolevDatum_pressureGradient_lerayComplement w hf
      (C01.mem_Ioo_of_mem_Icc hc hST t.2) ?_
    have hfield : (C01.residualPathIcc w hf hc hST t).field
        = fun x => f (t.1, x) - advection w.velocity t.1 x + ν • spatialLaplacian w.velocity t.1 x :=
      funext (fun x => C01.residualPathIcc_field w hf hc hST t x)
    have hd := D01.smoothAngularDatum_isSobolevDatum n (n : ℝ) (le_refl _)
      (C01.residualPathIcc w hf hc hST t)
    rwa [hfield] at hd
  have hkey : (fun t : Icc c S =>
        (C01.pressureGradientField w hf (C01.mem_Ioo_of_mem_Icc hc hST t.2)).jetLp n)
      = fun t : Icc c S => D01.jetOfDatum n n hn
          (D01.Leray.lerayComplement (n : ℝ)
            (D01.smoothAngularDatum n (n : ℝ) (le_refl _) (C01.residualPathIcc w hf hc hST t))) := by
    funext t
    apply Lp.ext
    exact (((C01.pressureGradientField w hf (C01.mem_Ioo_of_mem_Icc hc hST t.2)).integrable n).coeFn_toLp).trans
      (D01.jetOfDatum_ae hn (C01.pressureGradientField w hf (C01.mem_Ioo_of_mem_Icc hc hST t.2)).smooth
        (hisdat t)).symm
  rw [hkey]
  exact (C01.jetOfDatum_continuous n n hn).comp hleray

end NSFormalization.Section4
