import NSFormalization.Section4.A01.SignedPassage

/-! The unabsorbed signed energy inequality for the maximal-approximation limit.
The varying inverse-root weight acts continuously on time L². Dissipation is
retained as the squared norm of the complete derivative-word family. -/
noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
  EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerSmoothFieldSobolevTime EulerQuadraticSource EulerVolterraConvolution
  EulerQuadraticSourceLimit EulerTimeLp EulerRegularizedTopBlocks
  EulerRegularizedWordEquation EulerRegularizedWordTime EulerRegularizedForcingWord
  EulerRegularizedEnergyFamily EulerFiniteMetricEnergy EulerMetricPathConvergence
  EulerTransportL2Time EulerRegularizedMetricPaths EulerWeightedCylinderEnergy
  EulerSpatialSobolevInverse EulerSobolevMetricTransport EulerSobolevEnergyPaths
  ForcedMaximalRegularity EulerWeightedForcingTime EulerMildTopWord
  EulerSobolevWordValueIdentity
open NSFormalization.Source.ForcedCylinderLocal
open scoped Topology InnerProductSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

theorem rev204_doubled_dissipation {q : ℕ} (hq : 6 ≤ q) (n : ℕ)
    {ν S T : ℝ} (hν : 0 < ν) (hT : 0 ≤ T) (hTS : T ≤ S)
    (D : Coefficients (Icc (0 : ℝ) S) (SobolevSpace 1 (q+1)) (SobolevSpace 1 q))
    (u₀ : SobolevSpace 1 (q+1)) (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν hT hTS D u₀ u t)
    (hdiv : ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0)
    (p : C(Icc (0 : ℝ) T, SobolevSpace 1 q))
    (hp : ∀ t, value 1 (p t) ∈ gradientSpace 1 1 0) {ε : ℝ} (hε : 0 < ε) :
    let r := extendPath T hT (signedApproximationRoot n u)
    let z := extendPath T hT (signedApproximationForcing hq n u
      (sourcePath (D.comp (timeInclusion hTS)) u) p)
    let d := extendPath T hT (signedApproximationDissipation n u)
    ∀ t ∈ Icc (0 : ℝ) T,
      IntervalIntegrable (fun s => (r s*z s-(2*ν)*d s)/Real.sqrt ((r s)^2+ε^2)) volume 0 t ∧
      Real.sqrt ((r t)^2+ε^2) ≤ Real.sqrt ((r 0)^2+ε^2) +
        ∫ s in (0 : ℝ)..t, (r s*z s-(2*ν)*d s)/Real.sqrt ((r s)^2+ε^2) := by
  let e := fun (W : SobolevWord (q+1)) s => value 1 (extendPath T hT (signedWordPath n u W) s)
  let f := fun (W : SobolevWord (q+1)) s => extendPath T hT
    (sourceWordPath 1 (Nat.le_of_lt_succ W.1.isLt) n W.2 T
      (sourcePath (D.comp (timeInclusion hTS)) u)) s
  let x := fun s => familyEnergy (ContinuousLinearMap.id ℝ (LiftL2 1)) (fun W => e W s)
  let b := fun s => ∑ W, ⟪e W s, f W s⟫_ℝ
  have he (W) : Continuous (e W) :=
    (valueOperator 1 2).continuous.comp (extendPath_continuous T hT (signedWordPath n u W))
  have hf (W) : Continuous (f W) := extendPath_continuous T hT _
  have hx : Continuous x := continuous_finsetSum _ (fun W _ => (he W).inner (he W))
  have hb : Continuous b := continuous_finsetSum _ (fun W _ => (he W).inner (hf W))
  have hx0 (s) : 0 ≤ x s := by
    dsimp [x, familyEnergy]
    simp only [real_inner_self_eq_norm_sq]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsq (s) : (extendPath T hT (signedApproximationRoot n u) s)^2 = x s := by
    change (signedApproximationRoot n u _)^2 = _
    rw [signedApproximationRoot_apply, familyNorm_sq]
    simp only [x, familyEnergy, ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq]
    rfl
  have hroot (s) : Real.sqrt (x s) = extendPath T hT (signedApproximationRoot n u) s := by
    rw [← hsq, Real.sqrt_sq]
    exact Real.sqrt_nonneg _
  have hder (s) (hs : s ∈ Ioo 0 T) : HasDerivAt x
      (2*b s-2*ν*extendPath T hT (signedApproximationDissipation n u) s) s := by
    have hh := regularized_full_energy_hasDerivAt n hν hT hTS D u₀ u hu s hs
    convert hh using 1
    · rfl
    · dsimp only [b, e, f, signedApproximationDissipation, extendPath, ContinuousMap.coe_mk]
      simp only [toJet_word 1 _ (by norm_num : 1 ≤ 2)]
      rfl
  have hbound (s) (_hs : s ∈ Icc 0 T) : b s ≤ Real.sqrt (x s) *
      extendPath T hT (signedApproximationForcing hq n u
        (sourcePath (D.comp (timeInclusion hTS)) u) p) s := by
    rw [hroot]
    exact signed_source_pairing_le hq n u _ p hdiv hp _
  have H := signed_scalar_integral hT hε x b
    (extendPath T hT (signedApproximationDissipation n u))
    (extendPath T hT (signedApproximationForcing hq n u
      (sourcePath (D.comp (timeInclusion hTS)) u) p)) hx hb
    (extendPath_continuous T hT _) (extendPath_continuous T hT _) hx0 hder hbound
  simpa only [hsq, hroot] using H

end NSFormalization.Section4.A01
