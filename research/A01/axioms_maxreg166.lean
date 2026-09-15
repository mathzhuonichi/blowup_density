import NSFormalization.Section4.A01.ForcedMaximalRegularity

noncomputable section
open Set MeasureTheory EulerLpTranslation EulerSmoothLimit EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerTimeLp EulerVolterraConvolution
open NSFormalization.Section4
open A01.ForcedMaximalRegularity
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Actual MemForceR and the original physical initial-data hypotheses, at q = 6.
The ordinary carrier retains its initial value; the H8 path restricts to the H7 path only a.e. -/
theorem actual_force_order_eight {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    {f : A02.SpaceTimeField} (hf : A02.MemForceR f) :
    ∃ (T : ℝ) (hT : 0 < T), T ≤ S ∧
      ∃ (u : C(Icc (0 : ℝ) T, SobolevSpace 1 7))
        (U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
        (W : TimeLp T (SobolevSpace 1 8)),
        (∀ t : Icc (0 : ℝ) S, (C01.forcePath hf t).field = fun x => f (t.1, x)) ∧
        U ⟨0, le_rfl, hT.le⟩ = a.toLp ∧
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        ((fun t => restrictOperator 1 (by omega : 7 ≤ 8) (W t))
          =ᵐ[timeMeasure T] extendPath T hT.le u) ∧
        Integrable (fun t => ‖W t‖ ^ 2) (timeMeasure T) := by
  obtain ⟨T, hT, hTS, u, U, W, hfSlice, _, _, hi, hU, _, _, _, hW, hWi⟩ :=
    exists_local_of_memForce (q := 6) (by omega) hν hS a ha hf
  exact ⟨T, hT, hTS, u, U, W, hfSlice, hi, hU, hW, hWi⟩

#print axioms nonlinearSource
#print axioms forced_mild_maximal_regularity
#print axioms exists_local_of_memForce
#print axioms actual_force_order_eight
#print axioms higher_value_ae
