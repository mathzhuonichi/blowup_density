import NSFormalization.Source.OrdinaryForcedLocal
import NSFormalization.Section4.C01.JetPaths
import Euler.SobolevMaximalRegularity

/-! Same-horizon maximal regularity of the actual forced nonlinear mild witness. -/
noncomputable section
namespace NSFormalization.Section4.A01.ForcedMaximalRegularity
open Set MeasureTheory EulerLpTranslation EulerSmoothLimit EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource EulerVolterraConvolution EulerTimeLp
open NSFormalization.Source.ForcedCylinderLocal
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

private def coefficientPath {q : ℕ} {S T : ℝ} (hTS : T ≤ S)
    (C : Coefficients (Icc (0 : ℝ) S) (SobolevSpace 1 (q + 1)) (SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1))) :
    C(Icc (0 : ℝ) T, SobolevSpace 1 q) :=
  ⟨fun t => C.apply (timeInclusion hTS t) (u t),
    C.continuous.comp ((timeInclusion hTS).continuous.prodMk u.continuous)⟩

/-- Evaluate the genuine forced quadratic coefficients along the existing mild path. -/
def nonlinearSource {q : ℕ} (hq : 6 ≤ q) {S T : ℝ} (hTS : T ≤ S)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1))) :
    C(Icc (0 : ℝ) T, SobolevSpace 1 q) :=
  coefficientPath hTS (coefficients 1 hq f) u

/-- One additional spatial order in Bochner L² time, without shortening the horizon.
The higher path restricts to the given mild solution, and its squared norm is integrable. -/
theorem forced_mild_maximal_regularity {q : ℕ} (hq : 6 ≤ q) {ν S T : ℝ}
    (hν : 0 < ν) (hT : 0 ≤ T) (hTS : T ≤ S)
    (u₀ : SobolevSpace 1 (q + 1)) (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
    (hsol : ∀ t, u t = quadraticDuhamel 1 ν hν hT hTS (coefficients 1 hq f) u₀ u t) :
    ∃ W : TimeLp T (SobolevSpace 1 (2 + q)),
      ((fun t => restrictOperator 1 (by omega : q + 1 ≤ 2 + q) (W t))
        =ᵐ[timeMeasure T] extendPath T hT u) ∧
      Integrable (fun t => ‖W t‖ ^ 2) (timeMeasure T) := by
  obtain ⟨W, hW, _⟩ := EulerSobolevMaximalRegularity.viscous_mild_maximal_regularity
    1 ν hν T hT u₀ (nonlinearSource hq hTS f u) u hsol
  exact ⟨W, hW, (memLp_two_iff_integrable_sq_norm (Lp.memLp W).aestronglyMeasurable).mp
    (Lp.memLp W)⟩

/-- The constructed higher realization has the same ordinary L² velocity almost everywhere. -/
theorem higher_value_ae {q : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (W : TimeLp T (SobolevSpace 1 (2 + q)))
    (hW : (fun t => restrictOperator 1 (by omega : q + 1 ≤ 2 + q) (W t))
      =ᵐ[timeMeasure T] extendPath T hT u) :
    (fun t => value 1 (W t)) =ᵐ[timeMeasure T]
      (fun t => ordinaryLift (extendPath T hT U t)) := by
  filter_upwards [hW] with t ht
  have hv := congrArg (value 1) ht
  exact hv.trans (hU (projIcc 0 T hT t)).symm

set_option maxHeartbeats 800000 in
/-- The original local existence hypotheses, with the actual physical force, supply
both the ordinary solution and the compatible higher path on the same local horizon. -/
theorem exists_local_of_memForce {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    {f : A02.SpaceTimeField} (hf : A02.MemForceR f) :
    ∃ (T : ℝ) (hT : 0 < T) (hTS : T ≤ S),
      ∃ (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
        (U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
        (W : TimeLp T (SobolevSpace 1 (2 + q))),
        (∀ t : Icc (0 : ℝ) S, (C01.forcePath hf t).field = fun x => f (t.1, x)) ∧
        ‖u‖ ≤ ‖ordinarySobolev (q + 1) a.toLp a.translation_contDiff‖ + 1 ∧
        u ⟨0, le_rfl, hT.le⟩ = ordinarySobolev (q + 1) a.toLp a.translation_contDiff ∧
        U ⟨0, le_rfl, hT.le⟩ = a.toLp ∧
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
        (∀ t, u t = quadraticDuhamel 1 ν hν hT.le hTS
          (coefficients 1 hq (sobolevPath (C01.forcePath hf)
            (C01.forcePath_jetLp_continuous hf) q))
          (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) ∧
        (∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
        ((fun t => restrictOperator 1 (by omega : q + 1 ≤ 2 + q) (W t))
          =ᵐ[timeMeasure T] extendPath T hT.le u) ∧
        Integrable (fun t => ‖W t‖ ^ 2) (timeMeasure T) := by
  obtain ⟨T, hT, hTS, u, U, hb, hi, hUi, hU, hd, hm, hinv⟩ :=
    NSFormalization.Source.OrdinaryForcedLocal.exists_local hq hν hS a ha
      (C01.forcePath hf) (C01.forcePath_jetLp_continuous hf)
  obtain ⟨W, hW, hWi⟩ := forced_mild_maximal_regularity hq hν hT.le hTS
    (ordinarySobolev (q + 1) a.toLp a.translation_contDiff)
    (sobolevPath (C01.forcePath hf) (C01.forcePath_jetLp_continuous hf) q) u hm
  exact ⟨T, hT, hTS, u, U, W, C01.forcePath_field hf, hb, hi, hUi, hU, hd, hm,
    hinv, hW, hWi⟩

end NSFormalization.Section4.A01.ForcedMaximalRegularity
