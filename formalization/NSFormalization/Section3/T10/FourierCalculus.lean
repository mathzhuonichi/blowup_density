import NSFormalization.Section3.T11.LocalTheory
import NSFormalization.Section3.T10.PhysicalBridge
import NSFormalization.Section3.T10.DatumBasics
import NSFormalization.Section3.T10.Parseval
import NSFormalization.Paper1.PeriodicH2Uniform
import NSFormalization.Paper1.PeriodicSmoothSobolev

/-! Fourier calculus in the canonical T10 convention. The derivative proof uses
`Paper1.PeriodicFourierDerivative`'s cube integration by parts. -/
noncomputable section
namespace NSFormalization.Section3.T10
open MeasureTheory NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration (spatialPartial)
open scoped BigOperators ContDiff

 theorem periodicFourierCoeff_fderiv {f : Space → ℂ} (hf : IsPeriodicSpatial f)
    (hs : ContDiff ℝ 1 f) (j : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ fderiv ℝ f x (coordinateVector j)) k =
      periodicDerivativeSymbol j k * periodicFourierCoeff f k :=
  NSFormalization.Paper1.periodicFourierCoeff_spatialPartial hs hf j k

 theorem periodicFourierCoeff_secondPartial {f : Space → ℂ} (hf : IsPeriodicSpatial f)
    (hs : ContDiff ℝ 2 f) (i j : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff (spatialPartial j (spatialPartial i f)) k =
      periodicDerivativeSymbol j k * periodicDerivativeSymbol i k * periodicFourierCoeff f k := by
  change NSFormalization.Paper1.periodicFourierCoeff _ _ = _
  rw [NSFormalization.Paper1.periodicFourierCoeff_spatialPartial
    (NSFormalization.Paper1.spatialPartial_contDiff_one_of_two hs i)
    (NavierStokes.PeriodicUniqueness.spatial_partial_periodic hf i),
    NSFormalization.Paper1.periodicFourierCoeff_spatialPartial (hs.of_le (by norm_num)) hf]
  exact (mul_assoc _ _ _).symm

 theorem norm_periodicFourierCoeff_le (f : Space → ℂ) (k : PeriodicFrequency) :
    ‖periodicFourierCoeff f k‖ ≤ ∫ y, ‖torusLift f y‖ ∂periodicTorusMeasure := by
  change ‖∫ y : PeriodicTorus, UnitAddTorus.mFourier (-k) y • torusLift f y ∂periodicTorusMeasure‖ ≤ _
  have hn (y : PeriodicTorus) : ‖UnitAddTorus.mFourier (-k) y‖ = 1 := by
    change ‖∏ i, fourier ((-k) i) (y i)‖ = 1
    simp only [norm_prod, fourier_apply, Circle.norm_coe, Finset.prod_const_one]
  simpa only [norm_smul, hn, one_mul] using
    norm_integral_le_integral_norm (fun y : PeriodicTorus ↦
      UnitAddTorus.mFourier (-k) y • torusLift f y) (μ := periodicTorusMeasure)

 theorem summable_periodicFourierCoeff_of_h2 {f : Space → ℂ}
    (hf : IsPeriodicSpatial f) (hs : ContDiff ℝ 2 f) :
    Summable (periodicFourierCoeff f) :=
  NSFormalization.Paper1.summable_periodicFourierCoeff_of_h2_actual hs hf

 theorem summable_periodicFourierCoeff_of_smooth {f : Space → ℂ}
    (hf : IsPeriodicSpatial f) (hs : ContDiff ℝ ∞ f) :
    Summable (periodicFourierCoeff f) :=
  summable_periodicFourierCoeff_of_h2 hf (hs.of_le (by simp))

 theorem periodic_eq_tsum_mFourier {f : Space → ℂ} (hf : IsPeriodicSpatial f)
    (hs : Continuous f) (hc : Summable (periodicFourierCoeff f)) (x : Space) :
    f x = ∑' k, periodicFourierCoeff f k *
      Complex.exp ((2 * Real.pi * Complex.I : ℂ) * ∑ i, (k i : ℂ) * (x i : ℂ)) := by
  simpa only [NSFormalization.Paper1.periodicCharacter,
    NSFormalization.Paper1.periodicPhase_apply, mul_comm] using
    (NSFormalization.Paper1.periodicFourier_tsum_eq hs hf hc x).symm

 theorem norm_le_tsum_norm_periodicFourierCoeff {f : Space → ℂ}
    (hf : IsPeriodicSpatial f) (hs : Continuous f)
    (hc : Summable (periodicFourierCoeff f)) (x : Space) :
    ‖f x‖ ≤ ∑' k, ‖periodicFourierCoeff f k‖ :=
  NSFormalization.Paper1.norm_le_tsum_periodicFourierCoeff hs hf hc x

 theorem periodicFrequencyWeight_eq_paper1 (k : PeriodicFrequency) :
    periodicFrequencyWeight k = NSFormalization.Paper1.periodicFrequencyWeight k := by
  unfold periodicFrequencyWeight NSFormalization.Paper1.periodicFrequencyWeight
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [norm_mul, mul_pow, Complex.norm_I, mul_one,
    Complex.norm_intCast, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    sq_abs]
  ring

 theorem summable_weighted_periodicFourierCoeff {f : Space → ℂ}
    (hf : IsPeriodicSpatial f) (hs : ContDiff ℝ ∞ f) (s : ℝ) :
    Summable (fun k ↦ periodicFrequencyWeight k ^ s * ‖periodicFourierCoeff f k‖ ^ 2) := by
  simp_rw [periodicFrequencyWeight_eq_paper1]
  exact NSFormalization.Paper1.summable_periodicSobolev_smooth s hs hf

/-- Rapid decay, with an explicit finite energy constant at order `2*N`. -/
theorem periodicFourierCoeff_rapid_decay {f : Space → ℂ}
    (hf : IsPeriodicSpatial f) (hs : ContDiff ℝ ∞ f) (N : ℕ) :
    ∃ C : ℝ, ∀ k, periodicFrequencyWeight k ^ N * ‖periodicFourierCoeff f k‖ ≤ C := by
  let E := ∑' k, periodicFrequencyWeight k ^ (2 * N) * ‖periodicFourierCoeff f k‖ ^ 2
  refine ⟨Real.sqrt E, fun k ↦ ?_⟩
  have hW (k : PeriodicFrequency) : 0 ≤ periodicFrequencyWeight k := by
    rw [periodicFrequencyWeight_eq_paper1]
    exact zero_le_one.trans (NSFormalization.Paper1.one_le_periodicFrequencyWeight k)
  have hsum : Summable (fun k ↦ periodicFrequencyWeight k ^ (2 * N) *
      ‖periodicFourierCoeff f k‖ ^ 2) := by
    simpa only [Real.rpow_natCast] using
      summable_weighted_periodicFourierCoeff hf hs ((2 * N : ℕ) : ℝ)
  have ht := hsum.le_tsum k (fun k _ ↦ mul_nonneg (pow_nonneg (hW k) _) (sq_nonneg _))
  apply (Real.le_sqrt (mul_nonneg (pow_nonneg (hW k) _) (norm_nonneg _))
    (tsum_nonneg (fun k ↦ mul_nonneg (pow_nonneg (hW k) _) (sq_nonneg _)))).mpr
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm N 2] using ht

 theorem summable_inverse_periodicFrequencyWeight :
    Summable (fun k : PeriodicFrequency ↦ (periodicFrequencyWeight k ^ 2)⁻¹) := by
  simpa only [periodicFrequencyWeight_eq_paper1,
    NSFormalization.Paper1.periodicH2InverseWeight,
    NSFormalization.Paper1.periodicH2Weight, Real.rpow_two] using
    NSFormalization.Paper1.summable_periodicH2InverseWeight

 theorem tsum_norm_periodicFourierCoeff_le {f : Space → ℂ}
    (hE : Summable (fun k ↦ periodicFrequencyWeight k ^ 2 * ‖periodicFourierCoeff f k‖ ^ 2)) :
    (∑' k, ‖periodicFourierCoeff f k‖) ≤
      Real.sqrt (∑' k, (periodicFrequencyWeight k ^ 2)⁻¹) *
      Real.sqrt (∑' k, periodicFrequencyWeight k ^ 2 * ‖periodicFourierCoeff f k‖ ^ 2) := by
  have hW : Summable (fun k ↦ NSFormalization.Paper1.periodicH2Weight k *
      ‖periodicFourierCoeff f k‖ ^ 2) := by
    simpa only [periodicFrequencyWeight_eq_paper1,
      NSFormalization.Paper1.periodicH2Weight, Real.rpow_two] using hE
  have hc := NSFormalization.Paper1.summable_norm_of_periodicH2_weighted _ hW
    NSFormalization.Paper1.summable_periodicH2InverseWeight
  apply le_of_tendsto' hc.hasSum
  intro S
  have hb := NSFormalization.Paper1.finite_fourier_sum_h2_bound_of_summable_inverse
    (fun k ↦ (‖periodicFourierCoeff f k‖ : ℂ)) S
    (E := Real.sqrt (∑' k, NSFormalization.Paper1.periodicH2Weight k *
      ‖periodicFourierCoeff f k‖ ^ 2))
  have hn (k) : ‖(‖periodicFourierCoeff f k‖ : ℂ)‖ = ‖periodicFourierCoeff f k‖ := by simp
  have he := hW.sum_le_tsum S (fun k _ ↦ mul_nonneg
    (NSFormalization.Paper1.periodicH2Weight_pos k).le (sq_nonneg _))
  have hp : 0 ≤ ∑' k, NSFormalization.Paper1.periodicH2Weight k *
      ‖periodicFourierCoeff f k‖ ^ 2 := tsum_nonneg (fun k ↦ mul_nonneg
    (NSFormalization.Paper1.periodicH2Weight_pos k).le (sq_nonneg _))
  have hb' := hb (by simpa only [hn, Real.sq_sqrt hp] using he)
    (Real.sqrt_nonneg _) NSFormalization.Paper1.summable_periodicH2InverseWeight
  simpa [← Complex.ofReal_sum, Real.norm_eq_abs, abs_of_nonneg,
    Finset.sum_nonneg, periodicFrequencyWeight_eq_paper1,
    NSFormalization.Paper1.periodicH2Weight, NSFormalization.Paper1.periodicH2InverseWeight,
    mul_comm] using hb'

theorem periodicFourierCoeff_iteratedFDeriv {f : Space → ℂ}
    (hf : IsPeriodicSpatial f) (hs : ContDiff ℝ ∞ f) (j : Fin 3) (m : ℕ)
    (k : PeriodicFrequency) :
    periodicFourierCoeff ((spatialPartial j)^[m] f) k =
      periodicDerivativeSymbol j k ^ m * periodicFourierCoeff f k := by
  induction m generalizing f with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    have hd : ContDiff ℝ ∞ (spatialPartial j f) :=
      (hs.fderiv_right (by simp)).clm_apply contDiff_const
    rw [ih (NavierStokes.PeriodicUniqueness.spatial_partial_periodic hf j) hd]
    change _ * NSFormalization.Paper1.periodicFourierCoeff (spatialPartial j f) k = _
    rw [NSFormalization.Paper1.periodicFourierCoeff_spatialPartial (hs.of_le (by simp)) hf]
    simp only [pow_succ, periodicDerivativeSymbol, mul_assoc]

theorem norm_periodicFourierCoeff_iterated_le {f : Space → ℂ}
    (hf : IsPeriodicSpatial f) (hs : ContDiff ℝ ∞ f) (j : Fin 3) (m : ℕ)
    (k : PeriodicFrequency) :
    ‖periodicDerivativeSymbol j k ^ m * periodicFourierCoeff f k‖ ≤
      ∫ y, ‖torusLift ((spatialPartial j)^[m] f) y‖ ∂periodicTorusMeasure := by
  rw [← periodicFourierCoeff_iteratedFDeriv hf hs]
  exact norm_periodicFourierCoeff_le _ _

/-- Componentwise inversion for physical vector fields. -/
theorem periodic_component_eq_tsum {v : NSFormalization.Section4.A02.SpatialField}
    (hp : IsPeriodicSpatial v) (hs : Continuous v)
    (hc : ∀ i, Summable (periodicFourierCoeff (fun x ↦ (v x i : ℂ))))
    (i : Fin 3) (x : Space) :
    (v x i : ℂ) = ∑' k, periodicFourierCoeff (fun y ↦ (v y i : ℂ)) k *
      Complex.exp ((2 * Real.pi * Complex.I : ℂ) * ∑ j, (k j : ℂ) * (x j : ℂ)) := by
  apply periodic_eq_tsum_mFourier (fun x j ↦ by dsimp; rw [hp x j])
    (Complex.continuous_ofReal.comp ((PiLp.continuous_apply 2 _ i).comp hs)) (hc i)

/-- Scalar complex Laplacian, using the same coordinate derivatives as T11. -/
theorem periodicFourierCoeff_laplacian {f : Space → ℂ}
    (hp : IsPeriodicSpatial f) (hs : ContDiff ℝ 2 f) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ ∑ j : Fin 3, spatialPartial j (spatialPartial j f) x) k =
      (-(4 * Real.pi ^ 2 * ∑ j : Fin 3, (k j : ℝ) ^ 2) : ℂ) *
        periodicFourierCoeff f k := by
  have hadd : periodicFourierCoeff
      (fun x ↦ ∑ j : Fin 3, spatialPartial j (spatialPartial j f) x) k =
      ∑ j : Fin 3, periodicFourierCoeff (spatialPartial j (spatialPartial j f)) k := by
    simp only [periodicFourierCoeff, NSFormalization.Paper1.periodicFourierCoeff_eq_cube,
      Finset.mul_sum, NavierStokes.PeriodicIntegration.cubeIntegral]
    apply integral_finsetSum
    intro j _
    exact NavierStokes.PeriodicIntegration.integrable_cube
      ((NSFormalization.Paper1.periodicCharacter_smooth (-k)).continuous.mul
        (NavierStokes.PeriodicIntegration.continuous_partial
          (NSFormalization.Paper1.spatialPartial_contDiff_one_of_two hs j) j))
  rw [hadd]
  simp_rw [periodicFourierCoeff_secondPartial hp hs]
  rw [← Finset.sum_mul]
  congr 1
  simp only [periodicDerivativeSymbol,
    Complex.ofReal_pow, Complex.ofReal_sum, Complex.ofReal_intCast,
    Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = (4 * (Real.pi : ℂ) ^ 2 * (k j : ℂ) ^ 2) * Complex.I ^ 2 := by ring
    _ = _ := by rw [Complex.I_sq]; ring

/-- Identification of T11's real scalar Laplacian with coordinate partials. -/
theorem scalarSpatialLaplacianT_eq (f : Space → ℝ) (t : ℝ) (x : Space) :
    NSFormalization.Section3.T11.scalarSpatialLaplacianT (fun z ↦ f z.2) t x =
      ∑ j : Fin 3, spatialPartial j (spatialPartial j f) x := by
  classical
  rfl

theorem summable_periodicFourierCoeff_component_of_smooth
    {v : NSFormalization.Section4.A02.SpatialField} (hp : IsPeriodicSpatial v)
    (hs : ContDiff ℝ ∞ v) (i : Fin 3) :
    Summable (periodicFourierCoeff (fun x ↦ (v x i : ℂ))) := by
  apply summable_periodicFourierCoeff_of_smooth (fun x j ↦ by dsimp; rw [hp x j])
  exact Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hs)

theorem spatialPartial_complexify {f : Space → ℝ} (hs : ContDiff ℝ 1 f)
    (j : Fin 3) :
    spatialPartial j (fun x ↦ (f x : ℂ)) = fun x ↦ ((spatialPartial j f x : ℝ) : ℂ) := by
  funext x
  unfold spatialPartial
  change fderiv ℝ (Complex.ofRealCLM ∘ f) x _ = _
  rw [(Complex.ofRealCLM.hasFDerivAt.comp x
    ((hs.differentiable (by norm_num) x).hasFDerivAt)).fderiv]
  rfl

theorem periodicFourierCoeff_scalarSpatialLaplacianT {f : Space → ℝ}
    (hp : IsPeriodicSpatial f) (hs : ContDiff ℝ 2 f) (t : ℝ)
    (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦
      (NSFormalization.Section3.T11.scalarSpatialLaplacianT (fun z ↦ f z.2) t x : ℂ)) k =
      (-(4 * Real.pi ^ 2 * ∑ j : Fin 3, (k j : ℝ) ^ 2) : ℂ) *
        periodicFourierCoeff (fun x ↦ (f x : ℂ)) k := by
  have he (j : Fin 3) : spatialPartial j (spatialPartial j (fun x ↦ (f x : ℂ))) =
      fun x ↦ ((spatialPartial j (spatialPartial j f) x : ℝ) : ℂ) := by
    rw [spatialPartial_complexify (hs.of_le (by norm_num))]
    exact spatialPartial_complexify
      ((hs.fderiv_right (by norm_num)).clm_apply contDiff_const) j
  have h := periodicFourierCoeff_laplacian
    (f := fun x ↦ (f x : ℂ)) (fun x j ↦ by dsimp; rw [hp x j])
    (Complex.ofRealCLM.contDiff.comp hs) k
  simpa only [he, scalarSpatialLaplacianT_eq, Complex.ofReal_sum] using h

theorem norm_periodicFourierCoeff_coordinate_decay {f : Space → ℂ}
    (hf : IsPeriodicSpatial f) (hs : ContDiff ℝ ∞ f) (j : Fin 3) (m : ℕ)
    (k : PeriodicFrequency) :
    ‖(2 * Real.pi * (k j : ℝ)) ^ m‖ * ‖periodicFourierCoeff f k‖ ≤
      ∫ y, ‖torusLift ((spatialPartial j)^[m] f) y‖ ∂periodicTorusMeasure := by
  have hn : ‖periodicDerivativeSymbol j k‖ = ‖2 * Real.pi * (k j : ℝ)‖ := by
    simp [periodicDerivativeSymbol, norm_mul, mul_assoc]
  simpa only [norm_mul, norm_pow, hn] using
    norm_periodicFourierCoeff_iterated_le hf hs j m k

theorem norm_component_le_tsum_norm_periodicFourierCoeff
    {v : NSFormalization.Section4.A02.SpatialField} (hp : IsPeriodicSpatial v)
    (hs : ContDiff ℝ ∞ v) (i : Fin 3) (x : Space) :
    ‖v x i‖ ≤ ∑' k, ‖periodicFourierCoeff (fun y ↦ (v y i : ℂ)) k‖ := by
  have hc : ContDiff ℝ ∞ (fun x ↦ (v x i : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hs)
  simpa only [Complex.norm_real] using norm_le_tsum_norm_periodicFourierCoeff
    (f := fun x ↦ (v x i : ℂ)) (fun x j ↦ by dsimp; rw [hp x j]) hc.continuous
    (summable_periodicFourierCoeff_component_of_smooth hp hs i) x

theorem periodicFourierCoeff_gradient_sq {f : Space → ℂ}
    (hp : IsPeriodicSpatial f) (hs : ContDiff ℝ 1 f) (k : PeriodicFrequency) :
    (∑ j : Fin 3, ‖periodicFourierCoeff (spatialPartial j f) k‖ ^ 2) =
      (4 * Real.pi ^ 2 * ∑ j : Fin 3, (k j : ℝ) ^ 2) * ‖periodicFourierCoeff f k‖ ^ 2 := by
  change (∑ j, ‖NSFormalization.Paper1.periodicFourierCoeff (spatialPartial j f) k‖ ^ 2) = _
  simp_rw [NSFormalization.Paper1.periodicFourierCoeff_spatialPartial hs hp,
    norm_mul, mul_pow]
  rw [← Finset.sum_mul]
  congr 1
  have hw := periodicFrequencyWeight_eq_paper1 k
  unfold periodicFrequencyWeight NSFormalization.Paper1.periodicFrequencyWeight at hw
  simpa only [norm_mul, mul_pow] using (add_left_cancel hw).symm

example (c : ℂ) : Summable (periodicFourierCoeff (fun _ : Space ↦ c)) :=
  summable_periodicFourierCoeff_of_smooth (fun _ _ ↦ rfl) contDiff_const

example (k : PeriodicFrequency) :
    Summable (periodicFourierCoeff (NSFormalization.Paper1.periodicCharacter k)) :=
  summable_periodicFourierCoeff_of_smooth
    (NSFormalization.Paper1.periodicCharacter_periodic k)
    (NSFormalization.Paper1.periodicCharacter_smooth k)

end NSFormalization.Section3.T10
