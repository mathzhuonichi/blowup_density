import NSFormalization.Section4.C01.PressureJetPath

/-!
Reviewer probe for lane 148 (row E4b).  Three substantive mutations of
`Section4/C01/PressureJetPath.lean`, each run against the lane's own proof script.
Every `example` below is EXPECTED TO FAIL; the errors are transcribed into
`research/C01/REVIEW_E4B.md`.
-/

noncomputable section

open Set MeasureTheory Filter Topology
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open NavierStokes.ProblemStatement
  (temporalDerivative advection spatialLaplacian pressureGradient coordinateVector Space)

namespace NSFormalization.Section4
open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)

variable {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {c S T : ℝ}

/-! ### M1a — constant `16^m` weakened to `4^m`, lane's proof verbatim -/

example (m : ℕ) (A B : SmoothL2Field Space) :
    ‖D01.smoothAngularDatum m (m : ℝ) (le_refl _) A
        - D01.smoothAngularDatum m (m : ℝ) (le_refl _) B‖ ^ 2
      ≤ (4 : ℝ) ^ m * ∑ k ∈ Finset.range (m + 1), ‖A.jetLp k - B.jetLp k‖ ^ 2 := by
  set M : ℝ := ∑ k ∈ Finset.range (m + 1), ‖A.jetLp k - B.jetLp k‖ ^ 2 with hMdef
  have hsub : D01.IsSobolevDatum (m : ℝ) (A.field - B.field)
      (D01.smoothAngularDatum m (m : ℝ) (le_refl _) A
        - D01.smoothAngularDatum m (m : ℝ) (le_refl _) B) :=
    D01.isSobolevDatum_sub
      (D01.schwartzPairable_of_memLp (fun i => D01.memLp_component A.memLp i))
      (D01.schwartzPairable_of_memLp (fun i => D01.memLp_component B.memLp i))
      (D01.smoothAngularDatum_isSobolevDatum m (m : ℝ) (le_refl _) A)
      (D01.smoothAngularDatum_isSobolevDatum m (m : ℝ) (le_refl _) B)
  have hbnd : D01.HasWeakDerivsL2Bound (A.field - B.field) M m := by
    have h0 : D01.HasWeakDerivsL2Bound (fieldSub A B).field M m :=
      C01.hasWeakDerivsL2Bound_of_jetLp_sq_le m (fieldSub A B) M (fun k hk => by
        rw [jetLp_fieldSub, hMdef]
        exact Finset.single_le_sum (f := fun j => ‖A.jetLp j - B.jetLp j‖ ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
    have hfe : (fieldSub A B).field = A.field - B.field :=
      funext (fun x => (fieldSub_field A B x).trans (Pi.sub_apply _ _ _).symm)
    rwa [hfe] at h0
  exact D01.norm_isSobolevDatum_le_of_memLp_derivs m (A.field - B.field) M hbnd _ hsub

/-! ### M1b — hardened: can the TRUE lemma be pushed down to `4^m` by arithmetic? -/

example (m : ℕ) (A B : SmoothL2Field Space) :
    ‖D01.smoothAngularDatum m (m : ℝ) (le_refl _) A
        - D01.smoothAngularDatum m (m : ℝ) (le_refl _) B‖ ^ 2
      ≤ (4 : ℝ) ^ m * ∑ k ∈ Finset.range (m + 1), ‖A.jetLp k - B.jetLp k‖ ^ 2 := by
  have h := C01.norm_smoothAngularDatum_sub_sq_le m A B
  have hS : (0:ℝ) ≤ (Finset.range (m + 1)).sum (fun k => ‖A.jetLp k - B.jetLp k‖ ^ 2) :=
    Finset.sum_nonneg (fun k _ => sq_nonneg _)
  nlinarith [h, hS, pow_pos (by norm_num : (0:ℝ) < 4) m, pow_pos (by norm_num : (0:ℝ) < 16) m]

/-! ### M2 — the window is pushed onto the endpoint `c = 0` -/

example (w : ClassicalSolutionR ν a f T) (hf : MemForceR f) (hST : S < T) (n : ℕ) :
    Continuous (fun t : Icc (0 : ℝ) S =>
      (C01.pressureGradientField w hf
        (C01.mem_Ioo_of_mem_Icc (c := (0 : ℝ)) (by norm_num) hST t.2)).jetLp n) :=
  C01.pressureGradientPath_jetLp_continuous w hf (by norm_num) (by norm_num) hST n

/-! ### M3 — the Leray complement replaced by the identity in the pin step -/

set_option maxHeartbeats 1000000 in
example (w : ClassicalSolutionR ν a f T) (hf : MemForceR f) (hc : 0 < c) (hST : S < T)
    (n : ℕ) (t : Icc c S) :
    D01.IsSobolevDatum (n : ℝ) (fun x => pressureGradient w.pressure t.1 x)
      (D01.smoothAngularDatum n (n : ℝ) (le_refl _) (C01.residualPathIcc w hf hc hST t)) := by
  refine D01.isSobolevDatum_pressureGradient_lerayComplement w hf
    (C01.mem_Ioo_of_mem_Icc hc hST t.2) ?_
  have hfield : (C01.residualPathIcc w hf hc hST t).field
      = fun x => f (t.1, x) - advection w.velocity t.1 x + ν • spatialLaplacian w.velocity t.1 x :=
    funext (fun x => C01.residualPathIcc_field w hf hc hST t x)
  have hd := D01.smoothAngularDatum_isSobolevDatum n (n : ℝ) (le_refl _)
    (C01.residualPathIcc w hf hc hST t)
  rwa [hfield] at hd

/-! ### M4 — glue (a) order bookkeeping: order-`m` jet control must not give an order-`m+1` bound -/

example (m : ℕ) (Z : SmoothL2Field Space) (M : ℝ) (h : ∀ k, k ≤ m → ‖Z.jetLp k‖ ^ 2 ≤ M) :
    D01.HasWeakDerivsL2Bound Z.field M (m + 1) :=
  C01.hasWeakDerivsL2Bound_of_jetLp_sq_le (m + 1) Z M h

end NSFormalization.Section4
