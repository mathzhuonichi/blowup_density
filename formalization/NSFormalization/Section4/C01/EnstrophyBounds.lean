import NSFormalization.Section4.C01.EnstrophyIdentity

/-! Absorption of the nonlinear work and the forcing term in the ordinary
enstrophy identity. The resulting constant is explicitly `2`. -/

noncomputable section

open Set MeasureTheory
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open NSFormalization.Source.OrdinaryViscousStability
open scoped RealInnerProductSpace ENNReal

namespace NSFormalization.Section4.C01

/-- The registered extended-real trilinear estimate gives the real absorbed
work bound, including its finiteness, under the exact critical-smallness test. -/
theorem advectionWork_abs_le (z : A02.SpatialField) (hz : A05.SmoothL2 z)
    {ν : ℝ} (hν : 0 < ν)
    (hsmall : ENNReal.ofReal A05.gradientL6Const * criticalL3 z ≤
      ENNReal.ofReal (ν / 4)) :
    |advectionWork z| ≤ ν / 4 * laplacianSq z := by
  have hb := trilinearAbsorbed z hz
  rw [laplacianSqENorm z hz] at hb
  have hm := hb.trans (mul_le_mul' hsmall (le_refl (ENNReal.ofReal (laplacianSq z))))
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ ν / 4)] at hm
  exact (ENNReal.ofReal_le_ofReal_iff (by
    apply mul_nonneg (by positivity)
    exact integral_nonneg (fun _ => sq_nonneg _))).mp hm

/-- Testing against `-Δu`, absorbing a quarter of the viscosity in each of
the nonlinear and forcing terms, gives the manuscript's differential bound. -/
theorem enstrophyDifferentialBound {ν : ℝ} {a : A02.SpatialField}
    {f : A02.SpaceTimeField} {T : ℝ} (hν : 0 < ν)
    (w : A02.ClassicalSolutionR ν a f T) (hf : A02.MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    (hsmall : ENNReal.ofReal A05.gradientL6Const * criticalL3 (slice w.velocity t) ≤
      ENNReal.ofReal (ν / 4))
    {E' : ℝ} (hd : HasDerivAt (fun s => gradientSq (slice w.velocity s)) E' t) :
    E' + ν * laplacianSq (slice w.velocity t) ≤ 2 * ν⁻¹ * l2Sq (slice f t) := by
  let U := velocitySliceField w (Ioo_subset_Ico_self ht)
  let L := laplacianField U
  let F := forceSliceField hf ht.1.le
  have hL : ‖L.toLp‖ ^ 2 = laplacianSq (slice w.velocity t) := by
    rw [norm_toLp_sq_eq_l2Sq, laplacianField_eq_lap]
    rfl
  have hF : ‖F.toLp‖ ^ 2 = l2Sq (slice f t) := norm_toLp_sq_eq_l2Sq F
  have hp : pairing (slice f t) (A05.lap (slice w.velocity t)) = ⟪F.toLp, L.toLp⟫ := by
    rw [field_inner, laplacianField_eq_lap]
    rfl
  have hwork := advectionWork_abs_le (slice w.velocity t)
    (velocity_slice_smoothL2 w (Ioo_subset_Ico_self ht)) hν hsmall
  have hforce : -pairing (slice f t) (A05.lap (slice w.velocity t)) ≤
      ν / 4 * laplacianSq (slice w.velocity t) + ν⁻¹ * l2Sq (slice f t) := by
    have hyoung : ‖F.toLp‖ * ‖L.toLp‖ ≤
        ν / 4 * ‖L.toLp‖ ^ 2 + ν⁻¹ * ‖F.toLp‖ ^ 2 := by
      apply (mul_le_mul_iff_right₀ hν).mp
      simp only [mul_add, ← mul_assoc, mul_inv_cancel₀ hν.ne', one_mul]
      nlinarith [sq_nonneg (ν * ‖L.toLp‖ - 2 * ‖F.toLp‖)]
    rw [hp, ← hL, ← hF]
    exact (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans hyoung)
  have he := hd.unique (enstrophyIdentity w hf ht)
  have hwle := le_abs_self (advectionWork (slice w.velocity t))
  nlinarith

/-- The squared Laplacian norm is continuous on every closed solution slab,
including the initial time. This supplies honest interval integrability. -/
theorem laplacianSq_continuousOn {ν : ℝ} {a : A02.SpatialField}
    {f : A02.SpaceTimeField} {T S : ℝ}
    (w : A02.ClassicalSolutionR ν a f T) (hST : S < T) :
    ContinuousOn (fun s => laplacianSq (slice w.velocity s)) (Icc (0 : ℝ) S) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc := (continuous_toLp (laplacianPath w hST)
    (laplacianPath_jetLp_continuous w hST 0)).norm.pow 2
  refine hc.congr (fun s => ?_)
  change ‖(laplacianField (velocityField w hST s)).toLp‖ ^ 2 = _
  rw [norm_toLp_sq_eq_l2Sq, laplacianField_eq_lap]
  rfl

/-- The ordinary gradient energy is continuous on each closed solution slab;
it is the finite sum of squared norms of the actual first derivative paths. -/
theorem gradientSq_continuousOn {ν : ℝ} {a : A02.SpatialField}
    {f : A02.SpaceTimeField} {T S : ℝ}
    (w : A02.ClassicalSolutionR ν a f T) (hST : S < T) :
    ContinuousOn (fun s => gradientSq (slice w.velocity s)) (Icc (0 : ℝ) S) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous (fun s : Icc (0 : ℝ) S =>
      ∑ i : Fin 3, ‖((velocityField w hST s).directionalField (axis i)).toLp‖ ^ 2) := by
    apply continuous_finsetSum
    intro i _
    have hpath := (ordinaryWordPath (velocityField w hST)
      (velocityField_jetLp_continuous w hST) (fun _ : Fin 1 => i)).continuous
    have hdir : Continuous (fun s : Icc (0 : ℝ) S =>
        ((velocityField w hST s).directionalField (axis i)).toLp) := by
      exact hpath.congr (fun s => by simp only [ordinaryWordPath_apply, wordField])
    exact hdir.norm.pow 2
  refine hc.congr (fun s => ?_)
  exact gradientSq_eq_sum (velocityField w hST s)

theorem intervalIntegrable_laplacianSq {ν : ℝ} {a : A02.SpatialField}
    {f : A02.SpaceTimeField} {T t : ℝ}
    (w : A02.ClassicalSolutionR ν a f T) (ht : t ∈ Ico (0 : ℝ) T) :
    IntervalIntegrable (fun s => laplacianSq (slice w.velocity s)) volume 0 t := by
  have hc : ContinuousOn (fun s => laplacianSq (slice w.velocity s)) (uIcc (0 : ℝ) t) := by
    simpa only [uIcc_of_le ht.1] using laplacianSq_continuousOn w ht.2
  exact hc.intervalIntegrable

/-- The integrated ordinary enstrophy estimate, including its genuine
Laplacian integrability conclusion and the initial datum term. -/
theorem enstrophyIntegralBound {ν : ℝ} {a : A02.SpatialField}
    {f : A02.SpaceTimeField} {T t : ℝ} (hν : 0 < ν)
    (w : A02.ClassicalSolutionR ν a f T) (hf : A02.MemForceR f)
    (ht : t ∈ Ico (0 : ℝ) T)
    (hsmall : ∀ s ∈ Ico (0 : ℝ) t,
      ENNReal.ofReal A05.gradientL6Const * criticalL3 (slice w.velocity s) ≤
        ENNReal.ofReal (ν / 4)) :
    IntervalIntegrable (fun s => laplacianSq (slice w.velocity s)) volume 0 t ∧
      gradientSq (slice w.velocity t) +
        ν * ∫ s in (0 : ℝ)..t, laplacianSq (slice w.velocity s) ≤
      gradientSq a + 2 * ν⁻¹ * ∫ s in (0 : ℝ)..t, l2Sq (slice f s) := by
  have hLc := laplacianSq_continuousOn w ht.2
  have hLi := intervalIntegrable_laplacianSq w ht
  have hFc : ContinuousOn (fun s => l2Sq (slice f s)) (Icc (0 : ℝ) t) := by
    have hc := ((forceTimeRegularity f hf).2.mono
      (show Icc (0 : ℝ) t ⊆ Ici (0 : ℝ) from fun _ hs => hs.1)).pow 2
    exact hc.congr (fun s _ => l2Sq_eq_sq_l2Norm (slice f s))
  have hFi : IntervalIntegrable (fun s => l2Sq (slice f s)) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le ht.1] using hFc
  let Ederiv := fun s => 2 * advectionWork (slice w.velocity s) -
    2 * ν * laplacianSq (slice w.velocity s) -
    2 * pairing (slice f s) (A05.lap (slice w.velocity s))
  have hd (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) t) :
      HasDerivAt (fun r => gradientSq (slice w.velocity r)) (Ederiv s) s :=
    enstrophyIdentity w hf ⟨hs.1, hs.2.trans ht.2⟩
  have hbound := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le ht.1
    (gradientSq_continuousOn w ht.2)
    (fun s hs => (hd s hs).hasDerivWithinAt)
    (((hFc.const_mul (2 * ν⁻¹)).sub (hLc.const_mul ν)).integrableOn_Icc)
    (fun s hs => show Ederiv s ≤
        2 * ν⁻¹ * l2Sq (slice f s) - ν * laplacianSq (slice w.velocity s) from by
      have hb := enstrophyDifferentialBound hν w hf ⟨hs.1, hs.2.trans ht.2⟩
        (hsmall s (Ioo_subset_Ico_self hs)) (hd s hs)
      linarith)
  simp only [Pi.sub_apply] at hbound
  rw [intervalIntegral.integral_sub (hFi.const_mul _) (hLi.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hbound
  have hzero : slice w.velocity 0 = a := funext w.initial
  rw [hzero] at hbound
  exact ⟨hLi, by linarith⟩

end NSFormalization.Section4.C01
