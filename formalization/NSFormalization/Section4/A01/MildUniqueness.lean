import NSFormalization.Section4.A01.CommonHorizon

/-! Whole-interval uniqueness by finite propagation of a short-window contraction. -/
noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory EulerQuadraticSource EulerVolterraConvolution
open EulerCylinderSobolevSpace EulerSobolevHeat
open EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift EulerMeanSmoothRepresentative
open EulerLiftedGradientSpace EulerSmoothFieldSobolevTime
open NSFormalization.Source.ForcedCylinderLocal NSFormalization.Source.OrdinaryCylinderDescent
open scoped Topology ContDiff NNReal

section Windows
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {S : ℝ} (hS : 0 ≤ S) (K : ℝ → Y →L[ℝ] X) (k : ℝ → ℝ)
  (hK : ContinuousOn (fun p : ℝ × Y => K p.1 p.2) (Ioi 0 ×ˢ (univ : Set Y)))
  (hk : IntegrableOn k (Ioc 0 S)) (hk0 : ∀ r ∈ Ioc 0 S, 0 ≤ k r)
  (hbound : ∀ r ∈ Ioc 0 S, ∀ y, ‖K r y‖ ≤ k r * ‖y‖)

/-- If a Volterra difference vanishes through `a`, its prefix through `b ≤ a+δ`
is controlled by the mass on `[0,δ]`, not by the mass on the full horizon. -/
theorem volterra_window_bound (d : C(Icc (0 : ℝ) S, X))
    (f : C(Icc (0 : ℝ) S, Y)) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ t, ‖f t‖ ≤ L * ‖d t‖)
    (hd : d = convolution S hS K k hK hk hk0 hbound f)
    {a b δ : ℝ} (_hb : 0 ≤ b) (hbS : b ≤ S) (hδS : δ ≤ S)
    (hbδ : b ≤ a + δ) (hpast : ∀ t : Icc (0 : ℝ) S, t.val ≤ a → d t = 0) :
    ‖d.comp (timeInclusion hbS)‖ ≤
      (kernelMass δ k * L) * ‖d.comp (timeInclusion hbS)‖ := by
  let D := d.comp (timeInclusion hbS)
  have hN : 0 ≤ L * ‖D‖ := mul_nonneg hL (norm_nonneg _)
  have hmass : 0 ≤ kernelMass δ k := kernelMass_nonneg δ k
    (fun r hr => hk0 r ⟨hr.1, hr.2.trans hδS⟩)
  apply (ContinuousMap.norm_le _ (mul_nonneg (mul_nonneg hmass hL) (norm_nonneg _))).mpr
  intro t
  let t' : Icc (0 : ℝ) S := timeInclusion hbS t
  have hi := causalIntegrand_integrable S hS K k hK hk hk0 hbound f t'
  have hm := (hk.mul_const (L * ‖D‖)).indicator (measurableSet_Iic (a := δ))
  have hpoint : ∀ r ∈ Ioc 0 S,
      ‖causalIntegrand S hS K f t' r‖ ≤
        (Iic δ).indicator (fun r => k r * (L * ‖D‖)) r := by
    intro r hr
    by_cases hrt : r ≤ t.val
    · have htr : 0 ≤ t.val - r := sub_nonneg.mpr hrt
      have htrb : t.val - r ≤ b := by linarith [t.property.2, hr.1]
      have htrs : t.val - r ≤ S := htrb.trans hbS
      have he : projIcc 0 S hS (t.val-r) = ⟨t.val-r, htr, htrs⟩ :=
        projIcc_of_mem _ ⟨htr, htrs⟩
      have hc : causalIntegrand S hS K f t' r =
          K r (f ⟨t.val-r, htr, htrs⟩) := by
        simp only [causalIntegrand, t', timeInclusion, ContinuousMap.coe_mk,
          mem_Iic, hrt, indicator_of_mem, extendPath, he]
      rw [hc]
      by_cases hrδ : r ≤ δ
      · rw [indicator_of_mem (show r ∈ Iic δ from hrδ)]
        apply (hbound r hr _).trans
        apply mul_le_mul_of_nonneg_left _ (hk0 r hr)
        apply (hf _).trans
        apply mul_le_mul_of_nonneg_left _ hL
        exact D.norm_coe_le_norm ⟨t.val-r, htr, htrb⟩
      · rw [indicator_of_notMem (show r ∉ Iic δ from hrδ)]
        have hz := hpast ⟨t.val-r, htr, htrs⟩ (by dsimp; linarith [t.property.2])
        have hfz : f ⟨t.val-r, htr, htrs⟩ = 0 := by
          apply norm_eq_zero.mp
          have hh := hf ⟨t.val-r, htr, htrs⟩
          rw [hz, norm_zero, mul_zero] at hh
          exact le_antisymm hh (norm_nonneg _)
        simp only [hfz, map_zero, norm_zero, le_refl]
    · have hc : causalIntegrand S hS K f t' r = 0 := by
        exact indicator_of_notMem (show r ∉ Iic t'.val from hrt) _
      rw [hc, norm_zero]
      by_cases hrδ : r ≤ δ
      · simpa only [indicator_of_mem (show r ∈ Iic δ from hrδ)] using mul_nonneg (hk0 r hr) hN
      · simp only [indicator_of_notMem (show r ∉ Iic δ from hrδ), le_refl]
  have hset : Iic δ ∩ Ioc (0 : ℝ) S = Ioc 0 δ := by
    ext r
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    constructor
    · exact fun h => ⟨h.2.1, h.1⟩
    · exact fun h => ⟨h.2, h.1, h.2.trans hδS⟩
  have heval : D t = convolution S hS K k hK hk hk0 hbound f t' :=
    congrArg (fun z : C(Icc (0 : ℝ) S, X) => z t') hd
  change ‖D t‖ ≤ _
  rw [heval]
  change ‖∫ r in Ioc 0 S, causalIntegrand S hS K f t' r‖ ≤ _
  calc
    _ ≤ ∫ r in Ioc 0 S, ‖causalIntegrand S hS K f t' r‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ r in Ioc 0 S, (Iic δ).indicator (fun r => k r * (L * ‖D‖)) r :=
      integral_mono_ae hi.norm hm (by
        filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with r hr
        exact hpoint r hr)
    _ = (kernelMass δ k * L) * ‖D‖ := by
      rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
        hset, integral_mul_const]
      exact (mul_assoc _ _ _).symm

/-- A short-window contraction propagates zero across any finite horizon. -/
theorem volterra_eq_zero (d : C(Icc (0 : ℝ) S, X))
    (f : C(Icc (0 : ℝ) S, Y)) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ t, ‖f t‖ ≤ L * ‖d t‖)
    (hd : d = convolution S hS K k hK hk hk0 hbound f)
    {δ : ℝ} (hδ : 0 < δ) (hδS : δ ≤ S)
    (hsmall : kernelMass δ k * L < 1) : d = 0 := by
  have hind (n : ℕ) : ∀ t : Icc (0 : ℝ) S, t.val ≤ (n : ℝ) * δ → d t = 0 := by
    induction n with
    | zero =>
      intro t ht
      have ht0 : t.val = 0 := le_antisymm (by simpa using ht) t.property.1
      have he := congrArg (fun z : C(Icc (0 : ℝ) S, X) => z t) hd
      rw [convolution_eq_interval S hS K k hK hk hk0 hbound, ht0,
        intervalIntegral.integral_same] at he
      exact he
    | succ n ih =>
      intro t ht
      let b := min (((n : ℝ) + 1) * δ) S
      have hb : 0 ≤ b := le_min (mul_nonneg (by positivity) hδ.le) hS
      have hbS : b ≤ S := min_le_right _ _
      have hbδ : b ≤ (n : ℝ) * δ + δ := by
        calc
          b ≤ ((n : ℝ) + 1) * δ := min_le_left _ _
          _ = (n : ℝ) * δ + δ := by ring
      have he := volterra_window_bound hS K k hK hk hk0 hbound d f L hL hf hd
        hb hbS hδS hbδ ih
      have hz : d.comp (timeInclusion hbS) = 0 := by
        apply norm_eq_zero.mp
        have hn := norm_nonneg (d.comp (timeInclusion hbS))
        nlinarith
      have htb : t.val ≤ b := le_min (by simpa only [Nat.cast_succ] using ht) t.property.2
      exact congrArg (fun z : C(Icc (0 : ℝ) b, X) => z ⟨t.val, t.property.1, htb⟩) hz
  obtain ⟨n, hn⟩ := exists_nat_gt (S / δ)
  have hnS : S < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp hn
  apply ContinuousMap.ext
  intro t
  exact hind n t (t.property.2.trans hnS.le)

end Windows
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
private local instance uniquenessSobolevGroup (q : ℕ) : NormedAddCommGroup (SobolevSpace 1 q) := inferInstance
private local instance uniquenessSobolevSpace (q : ℕ) : NormedSpace ℝ (SobolevSpace 1 q) := inferInstance

/-- Arbitrary continuous quadratic coefficients have at most one mild path on
any prescribed positive horizon. The radius bounds both competing paths. -/
theorem quadratic_mild_unique {q : ℕ} {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (C : Coefficients (Icc (0 : ℝ) S) (SobolevSpace 1 (q+1)) (SobolevSpace 1 q))
    (a : SobolevSpace 1 (q+1)) (u v : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1)))
    (hu : ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl C a u t)
    (hv : ∀ t, v t = quadraticDuhamel 1 ν hν hS.le le_rfl C a v t) : u = v := by
  let R := max ‖u‖ ‖v‖
  have hR : 0 ≤ R := (norm_nonneg u).trans (le_max_left _ _)
  let L := C.ballLipschitz R
  have hL : 0 ≤ L := C.ballLipschitz_nonneg R hR
  let K := heatKernel 1 q ν hν
  let k := parabolicKernelBound ν
  have hK := heatKernel_joint_continuous 1 q ν hν
  have hk := parabolicKernelBound_integrable ν S hS.le
  have hk0 : ∀ r ∈ Ioc 0 S, 0 ≤ k r := fun r hr => parabolicKernelBound_nonneg ν r hr.1
  have hbound : ∀ r ∈ Ioc 0 S, ∀ y, ‖K r y‖ ≤ k r * ‖y‖ :=
    fun r hr y => heatKernel_bound 1 q ν hν r hr.1 y
  let f := commonSource C u - commonSource C v
  have hf : ∀ t, ‖f t‖ ≤ L * ‖(u-v) t‖ := by
    intro t
    exact C.apply_sub_bound R hR t (u t) (v t)
      ((u.norm_coe_le_norm t).trans (le_max_left _ _))
      ((v.norm_coe_le_norm t).trans (le_max_right _ _))
  have he (z : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1))) (t : Icc (0 : ℝ) S) :
      quadraticDuhamel 1 ν hν hS.le le_rfl C a z t =
        heatOperator 1 (q+1) (2*ν*t.val).toNNReal a +
          convolution S hS.le K k hK hk hk0 hbound (commonSource C z) t := by
    rw [convolution_eq_interval S hS.le K k hK hk hk0 hbound]
    rfl
  have hd : u-v = convolution S hS.le K k hK hk hk0 hbound f := by
    rw [show f = commonSource C u - commonSource C v from rfl,
      convolution_sub S hS.le K k hK hk hk0 hbound]
    apply ContinuousMap.ext
    intro t
    change u t - v t = _
    rw [hu t, hv t, he u t, he v t]
    exact add_sub_add_left_eq_sub _ _ _
  obtain ⟨δ, hδ, hδS, _, hsmall⟩ := exists_positive_time_budget ν 0 L 1 S (by norm_num) hS
  have hs : kernelMass δ k * L < 1 := by
    simpa only [kernelMass, k, parabolicKernelBound_integral ν δ hδ.le] using hsmall
  exact sub_eq_zero.mp (volterra_eq_zero hS.le K k hK hk hk0 hbound (u-v) f L hL hf hd hδ hδS hs)

/-- The fixed-order uniqueness input of the common-horizon construction. -/
theorem mildUniqueness : MildUniqueness := by
  intro ν S hν hS a f u v hu hv
  exact quadratic_mild_unique hν hS _ a u v hu hv

/-- Common carriers with whole-interval mild uniqueness discharged. -/
theorem compatible_carriers_of_boundsInv'
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (R : ℕ → ℝ) (hb : ∀ q (hq : 6 ≤ q), HasAprioriBoundInv hq hν a F hF (R q))
    (hfs : ∀ q (_hq : 6 ≤ q),
      ContDiffOn ℝ ∞ (extendPath S hS.le (sobolevPath F hF q)) (Icc (0 : ℝ) S)) :
    ∃ U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
      ∀ (q : ℕ) (hq : 6 ≤ q),
        ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1)),
          ContDiffOn ℝ ∞ (extendPath S hS.le (sobolevPath F hF q)) (Icc (0 : ℝ) S) ∧
          (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
          (∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q+1) (0, θ) (u t) = u t) ∧
          ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
            (coefficients 1 hq (sobolevPath F hF q))
            (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t :=
  compatible_carriers_of_boundsInv mildUniqueness hν hS a ha F hF R hb hfs

/-- Common carriers with whole-interval mild uniqueness discharged. -/
theorem compatible_carriers_of_bounds'
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (R : ℕ → ℝ) (hb : ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν a F hF (R q))
    (hfs : ∀ q (_hq : 6 ≤ q),
      ContDiffOn ℝ ∞ (extendPath S hS.le (sobolevPath F hF q)) (Icc (0 : ℝ) S)) :
    ∃ U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
      ∀ (q : ℕ) (hq : 6 ≤ q),
        ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1)),
          ContDiffOn ℝ ∞ (extendPath S hS.le (sobolevPath F hF q)) (Icc (0 : ℝ) S) ∧
          (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
          (∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q+1) (0, θ) (u t) = u t) ∧
          ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
            (coefficients 1 hq (sobolevPath F hF q))
            (ordinarySobolev (q+1) a.toLp a.translation_contDiff) u t :=
  compatible_carriers_of_bounds mildUniqueness hν hS a ha F hF R hb hfs

/-- Common carriers with whole-interval mild uniqueness discharged. -/
theorem compatible_carriers_hall'
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (R : ℕ → ℝ) (hb : ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν a F hF (R q))
    (hfs : ∀ q (_hq : 6 ≤ q),
      ContDiffOn ℝ ∞ (extendPath S hS.le (sobolevPath F hF q)) (Icc (0 : ℝ) S)) :
    ∃ U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
      ∀ (q : ℕ) (hq : 6 ≤ q),
        ∃ (u₀ : SobolevSpace 1 (q + 1))
          (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
          (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))),
          ContDiffOn ℝ ∞ (extendPath S hS.le f) (Icc (0 : ℝ) S) ∧
          (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
          (∀ (θ : AddCircle (1 : ℝ)) t,
            sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
          ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
            (coefficients 1 hq f) u₀ u t :=
  compatible_carriers_hall mildUniqueness hν hS a ha F hF R hb hfs

end NSFormalization.Section4.A01
