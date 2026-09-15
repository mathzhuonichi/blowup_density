import NSFormalization.Section4.C01.SobolevTwo

/-! Uniform H² time bounds up to and including the terminal lifespan.
Only strictly earlier velocity slices are used. -/

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace NSFormalization.Section4.C01

theorem forceSq_continuousOn {f : A02.SpaceTimeField} (hf : A02.MemForceR f) :
    ContinuousOn (fun s => l2Sq (slice f s)) (Ici (0 : ℝ)) := by
  exact ((forceTimeRegularity f hf).2.pow 2).congr
    (fun s _ => l2Sq_eq_sq_l2Norm (slice f s))

theorem forceSq_intervalIntegrable {f : A02.SpaceTimeField} (hf : A02.MemForceR f)
    {S : ℝ} (hS : 0 ≤ S) :
    IntervalIntegrable (fun s => l2Sq (slice f s)) volume 0 S := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hS]
  exact (forceSq_continuousOn hf).mono (fun _ hs => hs.1)

theorem energyBudget_mono {a : A02.SpatialField} {f : A02.SpaceTimeField}
    (hf : A02.MemForceR f) {s S : ℝ} (hs : 0 ≤ s) (hsS : s ≤ S) :
    energyBudget a f s ≤ energyBudget a f S := by
  have hi : IntervalIntegrable (fun r => l2Norm (slice f r)) volume 0 S := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (hs.trans hsS)]
    exact (forceTimeRegularity f hf).2.mono (fun _ hr => hr.1)
  have hm := intervalIntegral.integral_mono_interval le_rfl hs hsS
    (Filter.Eventually.of_forall (fun _ => Real.sqrt_nonneg _)) hi
  exact add_le_add le_rfl hm

theorem h2TimeIntegral_Ioc {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField}
    {T S t : ℝ} (hν : 0 < ν) (w : A02.ClassicalSolutionR ν a f T)
    (hf : A02.MemForceR f) (ht : t ∈ Ico (0 : ℝ) T) (htS : t ≤ S)
    (hsmall : ∀ s ∈ Ico (0 : ℝ) S,
      ENNReal.ofReal A05.gradientL6Const * criticalL3 (slice w.velocity s) ≤
        ENNReal.ofReal (ν / 4)) :
    ∫⁻ s in Ioc (0 : ℝ) t, D01.sobolevENorm 2 (slice w.velocity s) ^ (2 : ℝ) ≤
      ENNReal.ofReal (32 * S * energyBudget a f S ^ 2 +
        32 * ν⁻¹ * gradientSq a +
        32 * (ν⁻¹) ^ 2 * ∫ s in (0 : ℝ)..S, l2Sq (slice f s)) := by
  have hS : 0 ≤ S := ht.1.trans htS
  have hUc : ContinuousOn (fun s => l2Sq (slice w.velocity s)) (Icc (0 : ℝ) t) :=
    (velocityL2Sq_continuousOn w).mono (fun _ hs => ⟨hs.1, hs.2.trans_lt ht.2⟩)
  have hUi : IntervalIntegrable (fun s => l2Sq (slice w.velocity s)) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le ht.1] using hUc
  have hLi := intervalIntegrable_laplacianSq w ht
  have hFi := forceSq_intervalIntegrable hf hS
  have hUm : (∫ s in (0 : ℝ)..t, l2Sq (slice w.velocity s)) ≤
      S * energyBudget a f S ^ 2 := by
    have hm := intervalIntegral.integral_mono_on ht.1 hUi
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => energyBudget a f S ^ 2) volume 0 t)
      (fun s hs => show l2Sq (slice w.velocity s) ≤ energyBudget a f S ^ 2 from by
        have hb := (l2Bound w hf hν ⟨hs.1, hs.2.trans_lt ht.2⟩).trans
          (energyBudget_mono hf hs.1 (hs.2.trans htS))
        rw [l2Sq_eq_sq_l2Norm]
        exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hb 2)
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hm
    exact hm.trans (mul_le_mul_of_nonneg_right htS (sq_nonneg _))
  have hFm : (∫ s in (0 : ℝ)..t, l2Sq (slice f s)) ≤
      ∫ s in (0 : ℝ)..S, l2Sq (slice f s) :=
    intervalIntegral.integral_mono_interval le_rfl ht.1 htS
      (Filter.Eventually.of_forall (fun _ => integral_nonneg (fun _ => sq_nonneg _))) hFi
  have he := (enstrophyIntegralBound hν w hf ht
    (fun s hs => hsmall s ⟨hs.1, hs.2.trans_le htS⟩)).2
  have hLm : (∫ s in (0 : ℝ)..t, laplacianSq (slice w.velocity s)) ≤
      ν⁻¹ * gradientSq a + 2 * (ν⁻¹) ^ 2 * ∫ s in (0 : ℝ)..S, l2Sq (slice f s) := by
    have he' : ν * (∫ s in (0 : ℝ)..t, laplacianSq (slice w.velocity s)) ≤
        gradientSq a + 2 * ν⁻¹ * ∫ s in (0 : ℝ)..t, l2Sq (slice f s) := by
      linarith [gradientSq_nonneg (slice w.velocity t)]
    have hm := mul_le_mul_of_nonneg_left he' (inv_nonneg.mpr hν.le)
    rw [← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul] at hm
    have hright : ν⁻¹ * (gradientSq a + 2 * ν⁻¹ * ∫ s in (0 : ℝ)..t, l2Sq (slice f s)) ≤
        ν⁻¹ * gradientSq a + 2 * (ν⁻¹) ^ 2 * ∫ s in (0 : ℝ)..S, l2Sq (slice f s) := by
      nlinarith [mul_le_mul_of_nonneg_left hFm (by positivity : 0 ≤ 2 * (ν⁻¹) ^ 2)]
    exact hm.trans hright
  have hdom : (∫⁻ s in Ioc (0 : ℝ) t, D01.sobolevENorm 2 (slice w.velocity s) ^ (2 : ℝ)) ≤
      ∫⁻ s in Ioc (0 : ℝ) t, ENNReal.ofReal (16 *
        (l2Sq (slice w.velocity s) + laplacianSq (slice w.velocity s))) := by
    apply setLIntegral_mono' measurableSet_Ioc
    intro s hs
    exact sobolevTwoFourier _ (velocity_slice_memHInfty w ⟨hs.1.le, hs.2.trans_lt ht.2⟩)
  have hval : (∫⁻ s in Ioc (0 : ℝ) t, ENNReal.ofReal (16 *
        (l2Sq (slice w.velocity s) + laplacianSq (slice w.velocity s)))) =
      ENNReal.ofReal (16 * ((∫ s in (0 : ℝ)..t, l2Sq (slice w.velocity s)) +
        ∫ s in (0 : ℝ)..t, laplacianSq (slice w.velocity s))) := by
    rw [← ofReal_integral_eq_lintegral_ofReal ((hUi.add hLi).const_mul 16).1
      (Filter.Eventually.of_forall (fun s => by
        apply mul_nonneg (by norm_num)
        exact add_nonneg (integral_nonneg (fun _ => sq_nonneg _))
          (integral_nonneg (fun _ => sq_nonneg _))))]
    congr 1
    rw [← intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hUi hLi]
  rw [hval] at hdom
  apply hdom.trans
  apply ENNReal.ofReal_le_ofReal
  nlinarith [mul_nonneg hS (sq_nonneg (energyBudget a f S)),
    mul_nonneg (inv_nonneg.mpr hν.le) (gradientSq_nonneg a)]

/-- A uniform bound on strictly earlier closed-right intervals controls the
open terminal interval. Rational endpoints make this a countable directed
union, so no terminal value or measurability assumption on the integrand is
needed for the lower integral. -/
theorem lintegral_Ioo_le_of_Ioc {S : ℝ} {g : ℝ → ℝ≥0∞} {B : ℝ≥0∞}
    (hbound : ∀ t : ℝ, 0 < t → t < S → ∫⁻ s in Ioc (0 : ℝ) t, g s ≤ B) :
    ∫⁻ s in Ioo (0 : ℝ) S, g s ≤ B := by
  let R := {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < S}
  let J : R → Set ℝ := fun q => Ioc (0 : ℝ) (q.1 : ℝ)
  have hdir : Directed (· ⊆ ·) J := by
    intro q r
    rcases le_total q.1 r.1 with h | h
    · exact ⟨r, Ioc_subset_Ioc le_rfl (by exact_mod_cast h), Subset.rfl⟩
    · exact ⟨q, Subset.rfl, Ioc_subset_Ioc le_rfl (by exact_mod_cast h)⟩
  have hset : (⋃ q : R, J q) = Ioo (0 : ℝ) S := by
    ext x
    constructor
    · intro hx
      obtain ⟨q, hq⟩ := mem_iUnion.mp hx
      exact ⟨hq.1, hq.2.trans_lt q.2.2⟩
    · intro hx
      obtain ⟨q, hxq, hqS⟩ := exists_rat_btwn hx.2
      exact mem_iUnion.mpr ⟨⟨q, hx.1.trans hxq, hqS⟩, hx.1, hxq.le⟩
  rw [← hset, setLIntegral_iUnion_of_directed g hdir]
  exact iSup_le (fun q => hbound q.1 q.2.1 q.2.2)

/-- The exact H² assembly, including `S = T`, with universal constant 32. -/
theorem h2TimeIntegral {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField}
    {T S : ℝ} (hν : 0 < ν) (w : A02.ClassicalSolutionR ν a f T)
    (hf : A02.MemForceR f) (_hS : 0 < S) (hST : S ≤ T)
    (hsmall : ∀ t ∈ Ico (0 : ℝ) S,
      ENNReal.ofReal A05.gradientL6Const * criticalL3 (slice w.velocity t) ≤
        ENNReal.ofReal (ν / 4)) :
    ∫⁻ t in Ioo (0 : ℝ) S, D01.sobolevENorm 2 (slice w.velocity t) ^ (2 : ℝ) ≤
      ENNReal.ofReal (32 * S * energyBudget a f S ^ 2 +
        32 * ν⁻¹ * gradientSq a +
        32 * (ν⁻¹) ^ 2 * ∫ s in (0 : ℝ)..S, l2Sq (slice f s)) := by
  apply lintegral_Ioo_le_of_Ioc
  intro t ht0 htS
  exact h2TimeIntegral_Ioc hν w hf ⟨ht0.le, htS.trans_le hST⟩ htS.le hsmall

/-- The zero-datum assembly uses the same universal constant. -/
theorem h2TimeIntegralZeroDatum {ν : ℝ} {f : A02.SpaceTimeField} {T S : ℝ}
    (hν : 0 < ν) (w : A02.ClassicalSolutionR ν (fun _ => 0) f T)
    (hf : A02.MemForceR f) (hS : 0 < S) (hST : S ≤ T)
    (hsmall : ∀ t ∈ Ico (0 : ℝ) S,
      ENNReal.ofReal A05.gradientL6Const * criticalL3 (slice w.velocity t) ≤
        ENNReal.ofReal (ν / 4)) :
    ∫⁻ t in Ioo (0 : ℝ) S, D01.sobolevENorm 2 (slice w.velocity t) ^ (2 : ℝ) ≤
      ENNReal.ofReal (32 * S * forcePrimitive f S ^ 2 +
        32 * (ν⁻¹) ^ 2 * ∫ s in (0 : ℝ)..S, l2Sq (slice f s)) := by
  simpa [energyBudget, l2Norm, l2Sq, gradientSq] using
    h2TimeIntegral hν w hf hS hST hsmall

end NSFormalization.Section4.C01
