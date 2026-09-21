import NSFormalization.Section4.A01.ForcedMaximalRegularity
import Euler.TimeCorrectionSource

/-! The actual forced source gains one Bochner-time spatial order along the constructed mild path. -/
noncomputable section
namespace NSFormalization.Section4.A01.ForcedSourceUpgrade
open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
open EulerQuadraticSource EulerVolterraConvolution EulerTimeLp EulerSmoothFieldSobolevTime
open EulerTimeSobolevTransport EulerTimeCorrectionSource EulerAsymmetricTransport EulerSobolevTransport
open EulerMeanOrdinaryLift EulerMeanSmoothRepresentative EulerLpTranslation EulerSmoothLimit
open NSFormalization.Source.ForcedCylinderLocal
open NSFormalization.Section4.A01.ForcedMaximalRegularity
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The actual spatial Leray map is the same operator at adjacent Sobolev orders. -/
theorem truncate_leray (q : ℕ) (v : SobolevSpace 1 (q + 1)) :
    truncateOperator 1 q (leray 1 (q + 1) v) = leray 1 q (truncateOperator 1 q v) := by
  apply value_injective 1
  rw [value_truncateOperator, leray_value, leray_value, value_truncateOperator]

/-- The higher source is P(f - advection(u,W)), with the actual force and velocity. -/
def sourceTime {q : ℕ} (hq : 6 ≤ q) {S T : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
    (W : TimeLp T (SobolevSpace 1 ((q + 1) + 1))) :
    TimeLp T (SobolevSpace 1 (q + 1)) :=
  (leray 1 (q + 1)).compLpL 2 (timeMeasure T)
    (pathLp T hT (f.comp (timeInclusion hTS)) -
      transportTime 1 (by omega : 6 ≤ q + 1) (velocityComponents 1 0)
        (velocityComponents_norm 1 0 (by norm_num) (by simp)) T hT u W)

/-- Its representative is the actual projected asymmetric transport residual a.e. -/
theorem sourceTime_ae {q : ℕ} (hq : 6 ≤ q) {S T : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
    (W : TimeLp T (SobolevSpace 1 ((q + 1) + 1))) :
    (sourceTime hq hT hTS f u W : ℝ → SobolevSpace 1 (q + 1)) =ᵐ[timeMeasure T]
      fun t => leray 1 (q + 1)
        (extendPath T hT (f.comp (timeInclusion hTS)) t -
          asymmetricTransport 1 (by omega : 6 ≤ q + 1) (velocityComponents 1 0)
            (velocityComponents_norm 1 0 (by norm_num) (by simp)) (extendPath T hT u t) (W t)) := by
  let A := transportTime 1 (by omega : 6 ≤ q + 1) (velocityComponents 1 0)
    (velocityComponents_norm 1 0 (by norm_num) (by simp)) T hT u W
  let F := pathLp T hT (f.comp (timeInclusion hTS))
  filter_upwards [(leray 1 (q + 1)).coeFn_compLpL (F - A), Lp.coeFn_sub F A,
    pathLp_ae T hT (f.comp (timeInclusion hTS)),
    transportTime_ae 1 (by omega : 6 ≤ q + 1) (velocityComponents 1 0)
      (velocityComponents_norm 1 0 (by norm_num) (by simp)) T hT u W] with t hp hs hf ha
  exact hp.trans (congrArg (leray 1 (q + 1)) (hs.trans (congrArg₂ (fun x y => x - y) hf ha)))

set_option maxHeartbeats 800000 in
/-- Compatibility of W supplied by maximal regularity recovers exactly the original source. -/
theorem sourceTime_restriction {q : ℕ} (hq : 6 ≤ q) {S T : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
    (W : TimeLp T (SobolevSpace 1 ((q + 1) + 1)))
    (hW : (fun t => truncateOperator 1 (q + 1) (W t)) =ᵐ[timeMeasure T] extendPath T hT u) :
    (fun t => truncateOperator 1 q (sourceTime hq hT hTS f u W t)) =ᵐ[timeMeasure T]
      extendPath T hT (nonlinearSource hq hTS
        ((truncateOperator 1 q).compLeftContinuous ℝ (Icc (0 : ℝ) S) f) u) := by
  filter_upwards [sourceTime_ae hq hT hTS f u W, hW] with t hs hw
  rw [hs, truncate_leray, map_sub,
    restrict_transport_state 1 hq (velocityComponents 1 0)
      (velocityComponents_norm 1 0 (by norm_num) (by simp)) _ _ _ hw]
  exact (source_eq 1 hq ((truncateOperator 1 q).compLeftContinuous ℝ (Icc (0 : ℝ) S) f)
    (timeInclusion hTS (projIcc 0 T hT t)) (u (projIcc 0 T hT t))).symm

/-- The higher source has a genuinely integrable squared H(q+1) norm. -/
theorem sourceTime_integrable_sq {q : ℕ} (hq : 6 ≤ q) {S T : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
    (W : TimeLp T (SobolevSpace 1 ((q + 1) + 1))) :
    Integrable (fun t => ‖sourceTime hq hT hTS f u W t‖ ^ 2) (timeMeasure T) :=
  (memLp_two_iff_integrable_sq_norm (Lp.memLp _).aestronglyMeasurable).mp (Lp.memLp _)

/-- Smooth physical force paths commute with adjacent Sobolev restriction. -/
theorem truncate_forcePath {f : A02.SpaceTimeField} (hf : A02.MemForceR f) (S : ℝ) (q : ℕ) :
    (truncateOperator 1 q).compLeftContinuous ℝ (Icc (0 : ℝ) S)
      (sobolevPath (C01.forcePath hf) (C01.forcePath_jetLp_continuous hf) (q + 1)) =
    sobolevPath (C01.forcePath hf) (C01.forcePath_jetLp_continuous hf) q := by
  apply ContinuousMap.ext
  intro t
  exact restrict_sobolev (by omega : q ≤ q + 1) (C01.forcePath hf t)

set_option maxHeartbeats 800000 in
/-- From the actual lane-166 local existence output, construct a higher source on precisely
its horizon. Neither W nor the higher source is assumed continuous or given an endpoint trace. -/
theorem exists_local_source_of_memForce {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    {f : A02.SpaceTimeField} (hf : A02.MemForceR f) :
    ∃ (T : ℝ) (hT : 0 < T) (hTS : T ≤ S),
      ∃ (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
        (U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
        (W : TimeLp T (SobolevSpace 1 ((q + 1) + 1)))
        (G : TimeLp T (SobolevSpace 1 (q + 1))),
        (∀ t : Icc (0 : ℝ) S, (C01.forcePath hf t).field = fun x => f (t.1, x)) ∧
        u ⟨0, le_rfl, hT.le⟩ = ordinarySobolev (q + 1) a.toLp a.translation_contDiff ∧
        U ⟨0, le_rfl, hT.le⟩ = a.toLp ∧
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        (∀ t, u t = quadraticDuhamel 1 ν hν hT.le hTS
          (coefficients 1 hq (sobolevPath (C01.forcePath hf)
            (C01.forcePath_jetLp_continuous hf) q))
          (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) ∧
        ((fun t => truncateOperator 1 (q + 1) (W t)) =ᵐ[timeMeasure T] extendPath T hT.le u) ∧
        G = sourceTime hq hT.le hTS
          (sobolevPath (C01.forcePath hf) (C01.forcePath_jetLp_continuous hf) (q + 1)) u W ∧
        ((fun t => truncateOperator 1 q (G t)) =ᵐ[timeMeasure T]
          extendPath T hT.le (nonlinearSource hq hTS
            (sobolevPath (C01.forcePath hf) (C01.forcePath_jetLp_continuous hf) q) u)) ∧
        Integrable (fun t => ‖G t‖ ^ 2) (timeMeasure T) := by
  obtain ⟨T, hT, hTS, u, U, W₀, hfield, _, hi, hUi, hU, _, hm, _, hW₀, _⟩ :=
    exists_local_of_memForce hq hν hS a ha hf
  let R := restrictOperator 1 (by omega : (q + 1) + 1 ≤ 2 + q)
  let W : TimeLp T (SobolevSpace 1 ((q + 1) + 1)) := R.compLpL 2 (timeMeasure T) W₀
  have hW : (fun t => truncateOperator 1 (q + 1) (W t)) =ᵐ[timeMeasure T]
      extendPath T hT.le u := by
    filter_upwards [R.coeFn_compLpL W₀, hW₀] with t hr ht
    change truncateOperator 1 (q + 1) ((R.compLpL 2 (timeMeasure T) W₀) t) = _
    rw [hr]
    change restrictOperator 1 (by omega : q + 1 ≤ (q + 1) + 1)
      (restrictOperator 1 (by omega : (q + 1) + 1 ≤ 2 + q) (W₀ t)) = _
    rw [restrictOperator_comp]
    exact ht
  let F : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)) :=
    sobolevPath (C01.forcePath hf) (C01.forcePath_jetLp_continuous hf) (q + 1)
  let G := sourceTime hq hT.le hTS F u W
  have hG := sourceTime_restriction hq hT.le hTS F u W hW
  change (fun t => truncateOperator 1 q (G t)) =ᵐ[timeMeasure T]
    extendPath T hT.le (nonlinearSource hq hTS
      ((truncateOperator 1 q).compLeftContinuous ℝ (Icc (0 : ℝ) S)
        (sobolevPath (C01.forcePath hf) (C01.forcePath_jetLp_continuous hf) (q + 1))) u) at hG
  rw [truncate_forcePath hf S q] at hG
  exact ⟨T, hT, hTS, u, U, W, G, hfield, hi, hUi, hU, hm, hW, rfl, hG,
    sourceTime_integrable_sq hq hT.le hTS F u W⟩

end NSFormalization.Section4.A01.ForcedSourceUpgrade
