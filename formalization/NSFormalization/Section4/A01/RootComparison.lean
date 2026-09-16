import NSFormalization.Section4.A01.MildEnergyEnvelope

/-! Scalar comparison, including closed endpoints. The dissipative signed limit
is retained as an explicit analytic premise; the forcing bound alone does not
include the necessary normalization of the initial energy. -/
noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
  EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerSmoothFieldSobolevTime EulerQuadraticSource EulerVolterraConvolution
open NSFormalization.Source.ForcedCylinderLocal EulerQuadraticSourceLimit
  EulerTimeLp EulerRegularizedTopBlocks
open scoped Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Integrating-factor comparison uses only interior derivatives and closed-interval continuity. -/
theorem scalar_differential_comparison {T : ℝ} (hT : 0 ≤ T)
    {α w d : ℝ → ℝ} (hα : Continuous α) (hw : ContinuousOn w (Icc 0 T))
    (hd : ∀ t ∈ Ioo 0 T, HasDerivAt w (d t) t)
    (hle : ∀ t ∈ Ioo 0 T, d t ≤ α t * w t) (hzero : w 0 ≤ 0) :
    ∀ t ∈ Icc 0 T, w t ≤ 0 := by
  let P := fun t => ∫ s in (0 : ℝ)..t, α s
  have hP (t : ℝ) : HasDerivAt P (α t) t :=
    intervalIntegral.integral_hasDerivAt_right (hα.intervalIntegrable _ _)
      hα.aestronglyMeasurable.stronglyMeasurableAtFilter hα.continuousAt
  have hcP : Continuous P := continuous_iff_continuousAt.mpr fun t => (hP t).continuousAt
  let z := fun t => w t * Real.exp (-P t)
  have hz (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt z ((d t - α t * w t) * Real.exp (-P t)) t := by
    convert (hd t ht).mul (hP t).neg.exp using 1 <;> first | rfl | (dsimp; ring)
  have ha : AntitoneOn z (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
      (hw.mul (Real.continuous_exp.comp hcP.neg).continuousOn)
    · intro t ht
      rw [interior_Icc] at ht
      exact (hz t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      change deriv z t ≤ 0
      rw [(hz t ht).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hle t ht))
        (Real.exp_pos _).le
  intro t ht
  have hh := ha ⟨le_rfl, hT⟩ ht ht.1
  have hz0 : z 0 = w 0 := by simp [z, P]
  rw [hz0] at hh
  have hm : w t * Real.exp (-P t) ≤ 0 * Real.exp (-P t) := by
    simpa only [zero_mul] using hh.trans hzero
  exact (mul_le_mul_iff_left₀ (Real.exp_pos (-P t))).mp hm

/-- Bellman comparison with a nonnegative variable coefficient. No derivative of
`r` and no strictly positive root is required. -/
theorem scalar_integral_comparison {T b c : ℝ} (hT : 0 ≤ T)
    {α r : ℝ → ℝ} (hα : Continuous α) (hr : Continuous r)
    (hα0 : ∀ t ∈ Icc 0 T, 0 ≤ α t)
    (hint : ∀ t ∈ Icc 0 T, r t ≤ c + ∫ s in (0 : ℝ)..t, (α s * r s + b)) :
    ∀ t ∈ Icc 0 T, r t ≤ energyComparison α b c t := by
  let z := fun t => c + ∫ s in (0 : ℝ)..t, (α s * r s + b)
  have hc : Continuous (fun s => α s * r s + b) := (hα.mul hr).add continuous_const
  have hz (t : ℝ) : HasDerivAt z (α t * r t + b) t :=
    (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add c
  have hy := energyComparison_hasDerivAt hα b c
  have hd := fun t => (hz t).sub (hy t)
  have hh := scalar_differential_comparison hT hα
    ((continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt).continuousOn)
    (fun t _ => hd t) (fun t ht => ?_) (by simp [z, energyComparison_zero])
  · intro t ht
    exact (hint t ht).trans (sub_nonpos.mp (hh t ht))
  · have hm := mul_le_mul_of_nonneg_left (hint t ⟨ht.1.le, ht.2.le⟩)
      (hα0 t ⟨ht.1.le, ht.2.le⟩)
    dsimp [z] at *
    linarith

/-- Uniqueness of the scalar comparison ODE on the closed horizon. -/
theorem energyComparison_unique_on_Icc {T b c : ℝ} (hT : 0 ≤ T)
    {α y : ℝ → ℝ} (hα : Continuous α) (hy : ContinuousOn y (Icc 0 T))
    (hy0 : y 0 = c)
    (hyd : ∀ t ∈ Ioo 0 T, HasDerivAt y (α t * y t + b) t) :
    ∀ t ∈ Icc 0 T, y t = energyComparison α b c t := by
  have hc : Continuous (energyComparison α b c) :=
    continuous_iff_continuousAt.mpr fun t => (energyComparison_hasDerivAt hα b c t).continuousAt
  have h₁ := scalar_differential_comparison hT hα (hy.sub hc.continuousOn)
    (fun t ht => (hyd t ht).sub (energyComparison_hasDerivAt hα b c t))
    (fun t _ => by dsimp; ring_nf; exact le_rfl)
    (by simp [hy0, energyComparison_zero])
  have h₂ := scalar_differential_comparison hT hα (hc.continuousOn.sub hy)
    (fun t ht => (energyComparison_hasDerivAt hα b c t).sub (hyd t ht))
    (fun t _ => by dsimp; ring_nf; exact le_rfl)
    (by simp [hy0, energyComparison_zero])
  exact fun t ht => le_antisymm (sub_nonpos.mp (h₁ t ht)) (sub_nonpos.mp (h₂ t ht))

/-- Young absorption for a positive regularized root, with exactly k²/(4ν). -/
theorem positive_root_absorption {ν k r g b d : ℝ} (hν : 0 < ν) (hr : 0 < r)
    (h : r*d + ν*g^2 ≤ k*r*g + b*r) : d ≤ k^2/(4*ν)*r+b := by
  have hh := A04.young_high_real (C := k) (a := 1) (n := r) (d := 2*r*d) hν
    (by nlinarith [h] : (1/2 : ℝ)*(2*r*d)+ν*g^2 ≤ k*1*r*g+b*r)
  have hm : r*d ≤ r*(k^2/(4*ν)*r+b) := by nlinarith [hh]
  exact (mul_le_mul_iff_right₀ hr).mp hm

/-- Remove a positive square-root regularization, including r=0 and c=0.
The comparison coefficient and time are fixed; no positive initial energy is used. -/
theorem regularized_root_comparison_limit (α : ℝ → ℝ) {b c r t : ℝ}
    (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hreg : ∀ ε : ℝ, 0 < ε → Real.sqrt (r^2+ε^2) ≤
      energyComparison α b (Real.sqrt (c^2+ε^2)) t) :
    r ≤ energyComparison α b c t := by
  have hl : Continuous (fun ε : ℝ => Real.sqrt (r^2+ε^2)) := by fun_prop
  have hu : Continuous (fun ε : ℝ => energyComparison α b (Real.sqrt (c^2+ε^2)) t) := by
    unfold energyComparison
    fun_prop
  have hleft : Filter.Tendsto (fun ε : ℝ => Real.sqrt (r^2+ε^2))
      (nhdsWithin 0 (Ioi 0)) (𝓝 r) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, Real.sqrt_sq hr] using
      hl.continuousAt.continuousWithinAt.tendsto (s := Ioi 0) (x := 0)
  have hright : Filter.Tendsto (fun ε : ℝ => energyComparison α b (Real.sqrt (c^2+ε^2)) t)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (energyComparison α b c t)) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, Real.sqrt_sq hc] using
      hu.continuousAt.continuousWithinAt.tendsto (s := Ioi 0) (x := 0)
  exact le_of_tendsto_of_tendsto hleft hright
    (Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => hreg ε hε)

/-- The one unresolved analytic input: a substantive absorbed integrated bound
on the root along the SAME maximal-approximation limit and forcing bound. This
is not a generic limit-continuity lemma or lane 198's dissipation-free estimate;
proving it for solenoidal data is the target of lane 203. -/
def CylinderSignedRootLimit {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) (E A : ℝ) : Prop :=
  let _solenoidal := ha
  ∀ (T : ℝ) (hT : 0 ≤ T) (hTS : T ≤ S)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1))),
    (∀ t, u t = quadraticDuhamel 1 ν hν hT hTS
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t) →
    ∀ U : TimeLp T (SobolevSpace 1 (2+q)),
      Filter.Tendsto (fun n => pathLp T hT
        (maximalApproximation 1 q T n u)) Filter.atTop (𝓝 U) →
      (∀ᵐ r ∂timeMeasure T,
        extendPath T hT (energyRootPath u) r * cylinderEnergyForcing hq hT hTS F hF u U r ≤
          A * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq) (extendPath T hT u r)‖) *
            extendPath T hT (energyRootPath u) r * energyGradientNorm U r +
          (E * ‖sobolevPath F hF (q+1)‖) * extendPath T hT (energyRootPath u) r) →
      ∀ t ∈ Icc (0 : ℝ) T,
        extendPath T hT (energyRootPath u) t ≤ energyRootPath u ⟨0, le_rfl, hT⟩ +
          ∫ s in (0 : ℝ)..t,
            ((cylinderEnvelopeDriver hq hT A u s)^2/(4*ν) *
              extendPath T hT (energyRootPath u) s + E * ‖sobolevPath F hF (q+1)‖)

/-- Conditional assembly. The normalization is independent of the forcing bound:
for zero force the latter places no restriction on E. -/
theorem cylinderRootComparison_of_forcingBound {q : ℕ} (hq : 6 ≤ q)
    {ν S : ℝ} (hν : 0 < ν) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) {E A : ℝ}
    (hE : mildNormConstant q ≤ E)
    (hlimit : CylinderSignedRootLimit hq hν a ha F hF E A)
    (hFB : ForcingFamilyBound hq hν a F hF E A) :
    CylinderRootComparison hq hν a F hF E A := by
  intro T hT hTS u hu t
  obtain ⟨U, hU⟩ := energy_maximal_limit hq hν hT hTS _ _ u hu
  have hint := hlimit T hT hTS u hu U hU (hFB T hT hTS u hu U hU)
  have hzero : u ⟨0, le_rfl, hT⟩ =
      ordinarySobolev (q+1) a.toLp a.translation_contDiff := by
    simpa [quadraticDuhamel, EulerSobolevHeat.heatOperator_zero] using hu ⟨0, le_rfl, hT⟩
  have hi : energyRootPath u ⟨0, le_rfl, hT⟩ ≤
      E * ‖ordinarySobolev (q+1) a.toLp a.translation_contDiff‖ := by
    rw [energyRootPath_apply, hzero]
    exact (euclideanWordNorm_bounds _).2.trans
      (mul_le_mul_of_nonneg_right hE (norm_nonneg _))
  have hh := scalar_integral_comparison hT
    ((cylinderEnvelopeDriver_continuous hq hT A u).pow 2 |>.div_const (4*ν))
    (extendPath_continuous T hT (energyRootPath u))
    (fun s _ => div_nonneg (sq_nonneg _) (by positivity))
    (fun s hs => (hint s hs).trans (add_le_add hi le_rfl)) t t.property
  simpa only [extendPath, projIcc_of_mem hT t.property, Pi.pow_apply] using hh

/-- Lane 199's finite-energy conclusion, conditional on the single signed limit. -/
theorem finiteMildEnergy_of_forcingBound {q : ℕ} (hq : 6 ≤ q)
    {ν S : ℝ} (hν : 0 < ν) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) {E A : ℝ}
    (hE : mildNormConstant q ≤ E)
    (hlimit : CylinderSignedRootLimit hq hν a ha F hF E A)
    (hFB : ForcingFamilyBound hq hν a F hF E A) :
    FiniteMildEnergy hq hν a ha F hF E A :=
  finiteMildEnergy_of_rootComparison hq hν a ha F hF
    ((mildNormConstant_nonneg q).trans hE)
    (cylinderRootComparison_of_forcingBound hq hν a ha F hF hE hlimit hFB)

end NSFormalization.Section4.A01
