import NSFormalization.Section3.T20.YBound
import NSFormalization.Section3.T20.H1Trilinear

/-!
# T20 unit U10b — the `H¹` energy inequality (`eq:H1energy`, `03-torus.tex:467-484`)

For the zero initial datum and a force `g ∈ F_T` with `ρ < c ν`, the mean-free
velocity `v = u - m(t)` of a classical torus solution satisfies, at every
interior time,

`(‖∇v‖²₂)' + ν ‖Δv‖²₂ ≤ CH1 · ν⁻¹ · ‖h‖²₂`,  `CH1 = 2`,

with an actual derivative witness for `(‖∇v‖²₂)'`.  This is the `hOneEnergy`
field of `CriticalRegularityTAPI` verbatim, at
`c = criticalSmallnessH1 = min criticalSmallness (1/(8·h1TrilinearConst))`.

## Route

* §1 Weight arithmetic: `|2πk|^2` is the order-`1` homogeneous weight
  (`homogeneousDatumWeight 1 k ^ 2`), it is the order-`2` homogeneous weight
  itself (`homogeneousDatumWeight 2 k`), and it is dominated by the order-`1`
  inhomogeneous Bessel weight, which is what makes T11's majorant apply.
* §2 A constant spatial shift changes neither `∇` nor `Δ`, so the mean-free
  slice `v(r,·) = u(r,·) - m(r)` has the gradient and Laplacian of `u(r,·)`.
* §3 **Order-`2` Parseval for the Laplacian**: `‖Δz‖_{L²(T³)} = ‖z - ∫z‖_{Ḣ²}`.
  The order-`0` datum of `Δz` is the negative of the order-`2` homogeneous
  datum of the mean-free part of `z`, frequency by frequency
  (`T10.periodicFourierCoeff_vector_laplacian`), so the two `ℓ²` norms agree.
  This is the order-`2` analogue of T10's `gradient_eq_homogeneousENorm`.
* §4 The order-`1` homogeneous frequency energy `h1FreqEnergy` and its termwise
  time derivative, differentiated under the sum exactly as U8's
  `hasDerivAt_tsum_critFreqEnergy` and T11's `hasDerivAt_torusSobolevNormAt_sq`.
* §5 `‖∇v(r)‖²₂ = ∑ₖ |2πk|²∑ᵢ|û_i(k,r)|²` and `‖Δv(t)‖²₂ = ∑ₖ |2πk|⁴∑ᵢ|û_i(k,t)|²`.
* §6 Pairing against `−Δv` on the Fourier side: for smooth periodic `v, z`,
  `∑ₖ |2πk|² Re∑ᵢ conj(v̂ᵢ)ẑᵢ = −⟪Δv, z⟫_{L²(T³)}`.
* §7 Assembly.  The pressure term has already dropped in U8's
  `rawEnergyDeriv_split`; the mean transport drops by U8's
  `re_sum_conj_fderiv_dir_zero`; dissipation gives `−2ν‖Δv‖²₂`; the force term is
  Cauchy–Schwarz on the coefficient side (`T11.torusRealPairing_le`, pairing the
  order-`2` homogeneous velocity datum against the order-`0` force datum) and is
  absorbed by Young; the convection term is U10a's `h1Trilinear_slice` and is
  absorbed using U9's `yBound_of_le`.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `maxHeartbeats`
override, no named goal input.
-/

noncomputable section

namespace NSFormalization.Section3.T20

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section3.T12
open scoped ContDiff ENNReal BigOperators ComplexConjugate

/-! ## §1  The order-one homogeneous weight -/

/-- `|2πk|^{2·(1/2)·2} = |2πk|² = 4π²|k|²`. -/
theorem homogeneousDatumWeight_one_sq (k : PeriodicFrequency) :
    homogeneousDatumWeight 1 k ^ 2 = periodicAngularFrequencySq k := by
  rw [homogeneousDatumWeight_one, Real.sq_sqrt (angularFrequencySq_nonneg k)]

/-- The order-`2` homogeneous weight is `|2πk|² = 4π²|k|²` itself. -/
theorem homogeneousDatumWeight_two_eq (k : PeriodicFrequency) :
    homogeneousDatumWeight 2 k = periodicAngularFrequencySq k := by
  unfold homogeneousDatumWeight
  split_ifs with hk
  · subst hk
    simp [periodicAngularFrequencySq]
  · rw [show (2 : ℝ) / 2 = 1 by norm_num]
    exact Real.rpow_one _

/-- `4π²|k|² ≤ 1 + 4π²|k|²`: the homogeneous order-`1` weight is dominated by
the inhomogeneous order-`1` weight, so T11's order-`1` majorant applies. -/
theorem angularFrequencySq_le_periodicFrequencyWeight (k : PeriodicFrequency) :
    periodicAngularFrequencySq k ≤ periodicFrequencyWeight k := by
  have h := angularFrequencySq_nonneg k
  show periodicAngularFrequencySq k ≤ 1 + periodicAngularFrequencySq k
  linarith

/-! ## §2  A constant spatial shift changes neither `∇` nor `Δ` -/

theorem dirDeriv_sub_const (w : SpatialField) (c : Space) (i : Fin 3) :
    NSFormalization.Section4.A05.dirDeriv i (fun x ↦ w x - c) =
      NSFormalization.Section4.A05.dirDeriv i w := by
  funext x
  show fderiv ℝ (fun y ↦ w y - c) x (coordinateVector i) =
    fderiv ℝ w x (coordinateVector i)
  rw [fderiv_sub_const]

theorem gradientTensor_sub_const (w : SpatialField) (c : Space) :
    gradientTensor (fun x ↦ w x - c) = gradientTensor w := by
  funext x
  simp only [gradientTensor, NSFormalization.Section4.A05.gradTensor,
    dirDeriv_sub_const w c]

theorem laplacian_sub_const (w : SpatialField) (c : Space) :
    laplacian (fun x ↦ w x - c) = laplacian w := by
  funext x
  simp only [laplacian, NSFormalization.Section4.A05.lap, dirDeriv_sub_const w c]

/-- `03-torus.tex:395-401`: `∇v = ∇u` for `v = u - m(t)`. -/
theorem gradientTensor_meanFreeVelocity (g u : SpaceTimeField) (r : ℝ) :
    gradientTensor (fun x ↦ meanFreeVelocity g u (r, x)) =
      gradientTensor (fun x ↦ u (r, x)) :=
  gradientTensor_sub_const (fun x ↦ u (r, x)) (meanPathT g r)

/-- `03-torus.tex:395-401`: `Δv = Δu` for `v = u - m(t)`. -/
theorem laplacian_meanFreeVelocity (g u : SpaceTimeField) (r : ℝ) :
    laplacian (fun x ↦ meanFreeVelocity g u (r, x)) =
      laplacian (fun x ↦ u (r, x)) :=
  laplacian_sub_const (fun x ↦ u (r, x)) (meanPathT g r)

/-! ## §3  Order-`2` Parseval for the Laplacian -/

/-- **`‖Δz‖_{L²(T³)} = ‖z − ∫z‖_{Ḣ²(T³)}`** for smooth periodic `z`.  The
order-`0` datum of `Δz` is the negative of the order-`2` homogeneous datum of the
mean-free part of `z`.  This is the order-`2` analogue of T10's
`gradient_eq_homogeneousENorm`. -/
theorem periodicLpENorm_two_laplacian_eq_homogeneous {z : SpatialField}
    (hs : ContDiff ℝ ∞ z) (hp : IsPeriodicSpatial z) :
    periodicLpENorm 2 (laplacian z) = periodicHomogeneousENorm 2 (meanZeroPartT z) := by
  have hlapS : ContDiff ℝ ∞ (laplacian z) := contDiff_laplacian hs
  have hlapP : IsPeriodicSpatial (laplacian z) := isPeriodicSpatial_laplacian hp
  obtain ⟨B, hB⟩ := smooth_periodic_datum (0 : ℝ) hlapS hlapP
  obtain ⟨A, hA, -⟩ := NSFormalization.Section3.T13.exists_homogeneous_datum
    (show (0 : ℝ) < 2 by norm_num) hp hs
  have hentry : ∀ (i : Fin 3) (k : PeriodicFrequency), B.1 i k = -(A.1 i k) := by
    intro i k
    have hBk : B.1 i k =
        periodicFourierCoeff (fun x ↦ ((laplacian z x i : ℝ) : ℂ)) k := by
      rw [hB.2.2 i k]
      norm_num
    have hAk : A.1 i k = ((homogeneousDatumWeight 2 k : ℝ) : ℂ) *
        periodicFourierCoeff (fun x ↦ ((meanZeroPartT z x i : ℝ) : ℂ)) k := by
      rw [hA.2.2.2 i k, smul_eq_mul]
    rw [hBk, hAk, periodicFourierCoeff_vector_laplacian hp hs i k,
      homogeneousDatumWeight_two_eq]
    by_cases hk : k = 0
    · subst hk
      have h0 : periodicAngularFrequencySq (0 : PeriodicFrequency) = 0 := by
        simp [periodicAngularFrequencySq]
      rw [h0]
      simp
    · rw [NSFormalization.Section3.T13.periodicFourierCoeff_meanZeroPart hs.continuous i hk]
      push_cast
      ring
  have hBA : B = -A := by
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    funext i
    ext k
    exact hentry i k
  have h1 : periodicLpENorm 2 (laplacian z) = ‖B‖ₑ :=
    (parseval_forward (laplacian z) B hB
      (memLp_torusLift_vector hlapS.continuous 2)).symm
  have h2 : periodicHomogeneousENorm 2 (meanZeroPartT z) = ‖A‖ₑ :=
    homENorm_eq_enorm_of_datum hA
  rw [h1, h2, hBA, enorm_neg]

/-! ## §4  The `H¹` frequency energy and its time derivative -/

/-- The order-`1` homogeneous energy of one frequency of a velocity slice. -/
def h1FreqEnergy (u : SpaceTimeField) (k : PeriodicFrequency) (r : ℝ) : ℝ :=
  periodicAngularFrequencySq k * ∑ i : Fin 3, ‖velocityCoeffT u i k r‖ ^ 2

/-- The time derivative of `h1FreqEnergy`. -/
def h1FreqEnergyDeriv (u : SpaceTimeField) (k : PeriodicFrequency) (r : ℝ) : ℝ :=
  periodicAngularFrequencySq k *
    ∑ i : Fin 3, 2 * (conj (velocityCoeffT u i k r) * velocityDerivCoeffT u i k r).re

theorem hasDerivAt_h1FreqEnergy {u : SpaceTimeField} {I : Set ℝ} (hI : IsOpen I)
    (hu : ContDiffOn ℝ ∞ u (I ×ˢ (univ : Set Space))) {t : ℝ} (ht : t ∈ I)
    (k : PeriodicFrequency) :
    HasDerivAt (h1FreqEnergy u k) (h1FreqEnergyDeriv u k t) t := by
  have h : HasDerivAt (fun r ↦ ∑ i : Fin 3, ‖velocityCoeffT u i k r‖ ^ 2)
      (∑ i : Fin 3,
        2 * (conj (velocityCoeffT u i k t) * velocityDerivCoeffT u i k t).re) t :=
    HasDerivAt.fun_sum fun i _ ↦
      hasDerivAt_norm_sq_complex (hasDerivAt_velocityCoeffT hI hu ht i k)
  exact h.const_mul _

theorem abs_h1FreqEnergyDeriv_le_freq (u : SpaceTimeField) (k : PeriodicFrequency)
    (r : ℝ) :
    |h1FreqEnergyDeriv u k r| ≤ |freqEnergyDerivT ((1 : ℕ) : ℝ) u k r| := by
  have hP : 0 < periodicFrequencyWeight k := periodicFrequencyWeight_pos k
  have hW : (0 : ℝ) ≤ periodicAngularFrequencySq k := angularFrequencySq_nonneg k
  have hone : periodicFrequencyWeight k ^ (((1 : ℕ) : ℝ)) = periodicFrequencyWeight k := by
    rw [Nat.cast_one, Real.rpow_one]
  have hle : periodicAngularFrequencySq k ≤ periodicFrequencyWeight k ^ (((1 : ℕ) : ℝ)) := by
    rw [hone]
    exact angularFrequencySq_le_periodicFrequencyWeight k
  rw [h1FreqEnergyDeriv, freqEnergyDerivT, abs_mul, abs_mul, abs_of_nonneg hW,
    abs_of_nonneg (Real.rpow_nonneg hP.le _)]
  exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)

theorem abs_h1FreqEnergyDeriv_le {u : SpaceTimeField} {r : ℝ}
    {A : PeriodicSobolev ((2 * 1 + 4 : ℕ) : ℝ)}
    (hA : IsPeriodicDatum ((2 * 1 + 4 : ℕ) : ℝ) (fun x ↦ u (r, x)) A)
    {M D : ℝ} (hM : ‖A‖ ≤ M)
    (hD : ∀ (i : Fin 3) (k : PeriodicFrequency), ‖velocityDerivCoeffT u i k r‖ ≤ D)
    (k : PeriodicFrequency) :
    |h1FreqEnergyDeriv u k r| ≤ 6 * M * D * (periodicFrequencyWeight k ^ 2)⁻¹ :=
  (abs_h1FreqEnergyDeriv_le_freq u k r).trans
    (abs_freqEnergyDerivT_le (m := 1) hA hM hD k)

theorem summable_h1FreqEnergy {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) {r : ℝ} (hr : r ∈ Ico (0 : ℝ) T) :
    Summable (fun k : PeriodicFrequency ↦ h1FreqEnergy w.velocity k r) := by
  have hs : ContDiff ℝ ∞ (fun x : Space ↦ w.velocity (r, x)) :=
    classical_velocity_slice_contDiff w hr
  have hp : IsPeriodicSpatial (fun x : Space ↦ w.velocity (r, x)) :=
    w.velocity_periodic r hr
  refine (NSFormalization.Section3.T13.summable_homogeneous_total
    (s := (1 : ℝ)) (by norm_num) hp hs).congr fun k ↦ ?_
  rw [homogeneousDatumWeight_one_sq]
  rfl

/-- **The order-`1` homogeneous energy profile is differentiable at every
interior time**, with derivative the termwise-differentiated Fourier series. -/
theorem hasDerivAt_tsum_h1FreqEnergy {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun r ↦ ∑' k : PeriodicFrequency, h1FreqEnergy w.velocity k r)
      (∑' k : PeriodicFrequency, h1FreqEnergyDeriv w.velocity k t) t := by
  classical
  have hI : IsOpen (Ioo (0 : ℝ) T) := isOpen_Ioo
  have hu : ContDiffOn ℝ ∞ w.velocity (Ioo (0 : ℝ) T ×ˢ (univ : Set Space)) :=
    w.velocity_smooth.mono (Set.prod_mono Ioo_subset_Ico_self Subset.rfl)
  obtain ⟨ht0, htT⟩ := ht
  set α : ℝ := t / 2 with hαdef
  set β : ℝ := (t + T) / 2 with hβdef
  have hα0 : 0 < α := by rw [hαdef]; linarith
  have hαt : α < t := by rw [hαdef]; linarith
  have htβ : t < β := by rw [hβdef]; linarith
  have hβT : β < T := by rw [hβdef]; linarith
  have hJI : Icc α β ⊆ Ioo (0 : ℝ) T := fun x hx ↦
    ⟨lt_of_lt_of_le hα0 hx.1, lt_of_le_of_lt hx.2 hβT⟩
  have hSJ : Ioo α β ⊆ Icc α β := Ioo_subset_Icc_self
  have hSI : Ioo α β ⊆ Ioo (0 : ℝ) T := hSJ.trans hJI
  have htS : t ∈ Ioo α β := ⟨hαt, htβ⟩
  obtain ⟨D, hD0, hD⟩ := exists_velocityDerivCoeffT_bound hI hu isCompact_Icc hJI
  obtain ⟨G, hGc, hGd⟩ := w.sobolev (2 * 1 + 4)
  have hGsub : Icc α β ⊆ Ico (0 : ℝ) T := fun x hx ↦
    ⟨le_of_lt (lt_of_lt_of_le hα0 hx.1), lt_of_le_of_lt hx.2 hβT⟩
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hGc.mono hGsub)
  have hsummable : Summable fun k : PeriodicFrequency ↦
      6 * M * D * (periodicFrequencyWeight k ^ 2)⁻¹ :=
    summable_inverse_periodicFrequencyWeight.mul_left _
  have hg0 : Summable fun k ↦ h1FreqEnergy w.velocity k t :=
    summable_h1FreqEnergy w ⟨le_of_lt ht0, htT⟩
  exact hasDerivAt_tsum_of_isPreconnected (u := fun k : PeriodicFrequency ↦
      6 * M * D * (periodicFrequencyWeight k ^ 2)⁻¹)
    (g := fun k ↦ h1FreqEnergy w.velocity k)
    (g' := fun k r ↦ h1FreqEnergyDeriv w.velocity k r)
    hsummable isOpen_Ioo isPreconnected_Ioo
    (fun k r hr ↦ hasDerivAt_h1FreqEnergy hI hu (hSI hr) k)
    (fun k r hr ↦ by
      rw [Real.norm_eq_abs]
      exact abs_h1FreqEnergyDeriv_le (hGd r (hGsub (hSJ hr))) (hM r (hSJ hr))
        (fun i k' ↦ hD r (hSJ hr) i k') k)
    htS hg0 htS

/-! ## §5  The two `H¹` quantities as Fourier sums -/

/-- `‖∇v(r)‖²₂ = ∑ₖ |2πk|² ∑ᵢ |û_i(k,r)|²`. -/
theorem gradientSqT_meanFreeVelocity_eq_tsum {g u : SpaceTimeField} {r : ℝ}
    (hs : ContDiff ℝ ∞ (fun x ↦ u (r, x))) (hp : IsPeriodicSpatial (fun x ↦ u (r, x))) :
    gradientSqT (fun x ↦ meanFreeVelocity g u (r, x)) =
      ∑' k : PeriodicFrequency, h1FreqEnergy u k r := by
  have h1 : periodicLpENorm 2 (gradientTensor (fun x ↦ meanFreeVelocity g u (r, x))) =
      periodicHomogeneousENorm 1 (meanZeroPartT (fun x ↦ u (r, x))) := by
    rw [gradientTensor_meanFreeVelocity]
    exact gradient_eq_homogeneousENorm hs hp
  show (periodicLpENorm 2
    (gradientTensor (fun x ↦ meanFreeVelocity g u (r, x)))).toReal ^ 2 = _
  rw [h1, homENorm_toReal_sq (by norm_num : (0 : ℝ) < 1) hp hs]
  refine tsum_congr fun k ↦ ?_
  rw [homogeneousDatumWeight_one_sq]
  rfl

/-- `‖Δv(r)‖²₂ = ∑ₖ |2πk|⁴ ∑ᵢ |û_i(k,r)|²`. -/
theorem laplacianSqT_meanFreeVelocity_eq_tsum {g u : SpaceTimeField} {r : ℝ}
    (hs : ContDiff ℝ ∞ (fun x ↦ u (r, x))) (hp : IsPeriodicSpatial (fun x ↦ u (r, x))) :
    laplacianSqT (fun x ↦ meanFreeVelocity g u (r, x)) =
      ∑' k : PeriodicFrequency, periodicAngularFrequencySq k ^ 2 *
        ∑ i : Fin 3, ‖velocityCoeffT u i k r‖ ^ 2 := by
  have h1 : periodicLpENorm 2 (laplacian (fun x ↦ meanFreeVelocity g u (r, x))) =
      periodicHomogeneousENorm 2 (meanZeroPartT (fun x ↦ u (r, x))) := by
    rw [laplacian_meanFreeVelocity]
    exact periodicLpENorm_two_laplacian_eq_homogeneous hs hp
  show (periodicLpENorm 2
    (laplacian (fun x ↦ meanFreeVelocity g u (r, x)))).toReal ^ 2 = _
  rw [h1, homENorm_toReal_sq (by norm_num : (0 : ℝ) < 2) hp hs]
  refine tsum_congr fun k ↦ ?_
  rw [homogeneousDatumWeight_two_eq]
  rfl

theorem summable_laplacianSq_tsum {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) {r : ℝ} (hr : r ∈ Ico (0 : ℝ) T) :
    Summable (fun k : PeriodicFrequency ↦ periodicAngularFrequencySq k ^ 2 *
      ∑ i : Fin 3, ‖velocityCoeffT w.velocity i k r‖ ^ 2) := by
  have hs : ContDiff ℝ ∞ (fun x : Space ↦ w.velocity (r, x)) :=
    classical_velocity_slice_contDiff w hr
  have hp : IsPeriodicSpatial (fun x : Space ↦ w.velocity (r, x)) :=
    w.velocity_periodic r hr
  refine (NSFormalization.Section3.T13.summable_homogeneous_total
    (s := (2 : ℝ)) (by norm_num) hp hs).congr fun k ↦ ?_
  rw [homogeneousDatumWeight_two_eq]
  rfl

/-! ## §6  Pairing against `−Δv` on the Fourier side -/

theorem periodicPairing_comm (a b : SpatialField) :
    periodicPairing a b = periodicPairing b a := by
  show (∫ y : PeriodicTorus,
      (inner ℝ (torusLift a y) (torusLift b y) : ℝ) ∂periodicTorusMeasure) =
    ∫ y : PeriodicTorus,
      (inner ℝ (torusLift b y) (torusLift a y) : ℝ) ∂periodicTorusMeasure
  exact integral_congr_ae (Filter.Eventually.of_forall fun y ↦ real_inner_comm _ _)

/-- **The `|2πk|²`-weighted coefficient pairing is `−⟪Δv, z⟫_{L²(T³)}`.**  This
is the Fourier-side form of "take the inner product of the equation with `−Δv`"
(`03-torus.tex:467-468`). -/
theorem hasSum_angularPairing {v z : SpatialField}
    (hv : SmoothPeriodicT v) (hz : SmoothPeriodicT z) :
    HasSum (fun k : PeriodicFrequency ↦ periodicAngularFrequencySq k *
        (∑ i : Fin 3, conj (periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k) *
          periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k).re)
      (-periodicPairing (laplacian v) z) := by
  have hlap : SmoothPeriodicT (laplacian v) :=
    ⟨contDiff_laplacian hv.1, isPeriodicSpatial_laplacian hv.2⟩
  refine (hasSum_periodicPairing hlap hz).neg.congr_fun fun k ↦ ?_
  have hsum : (∑ i : Fin 3,
      conj (periodicFourierCoeff (fun x ↦ ((laplacian v x i : ℝ) : ℂ)) k) *
        periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k) =
      ((-periodicAngularFrequencySq k : ℝ) : ℂ) *
        ∑ i : Fin 3, conj (periodicFourierCoeff (fun x ↦ ((v x i : ℝ) : ℂ)) k) *
          periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [periodicFourierCoeff_vector_laplacian hv.2 hv.1 i k, map_mul, map_neg,
      Complex.conj_ofReal]
    push_cast
    ring
  rw [hsum, Complex.re_ofReal_mul]
  ring

/-! ## §7  The constant, the smallness radius, and `eq:H1energy` -/

/-- `03-torus.tex:479-484`: the absolute constant of `eq:H1energy` after Young's
inequality.  Both absorbed halves are `ν/4`-sized, so the surviving right-hand
coefficient is `2`. -/
def CH1 : ℝ := 2

theorem CH1_pos : 0 < CH1 := by
  show (0 : ℝ) < 2
  norm_num

/-- `03-torus.tex:457,477`: the universal smallness constant for `eq:H1energy`,
small enough for **both** bootstraps — U9's `c ≤ 1/(2C₀)` and the `H¹`
absorption's `c ≤ 1/(8C₁)`.  The strict shrinkings `c < 1/(4C₀)` and
`c < 1/(4C₁)` are `criticalSmallnessH1_lt_quarter_C₀` and
`criticalSmallnessH1_lt_quarter_C₁`. -/
def criticalSmallnessH1 : ℝ := min criticalSmallness (1 / (8 * h1TrilinearConst))

theorem criticalSmallnessH1_pos : 0 < criticalSmallnessH1 := by
  have h1 := criticalSmallness_pos
  have h2 := h1TrilinearConst_pos
  exact lt_min h1 (div_pos one_pos (by linarith))

theorem criticalSmallnessH1_le_criticalSmallness :
    criticalSmallnessH1 ≤ criticalSmallness := min_le_left _ _

theorem criticalSmallnessH1_le_half :
    criticalSmallnessH1 ≤ 1 / (2 * criticalTrilinearConst) :=
  le_trans criticalSmallnessH1_le_criticalSmallness criticalSmallness_le_half

theorem criticalSmallnessH1_lt_quarter_C₀ :
    criticalSmallnessH1 < 1 / (4 * criticalTrilinearConst) :=
  lt_of_le_of_lt criticalSmallnessH1_le_criticalSmallness criticalSmallness_lt_quarter

theorem criticalSmallnessH1_le_eighth_C₁ :
    criticalSmallnessH1 ≤ 1 / (8 * h1TrilinearConst) := min_le_right _ _

theorem criticalSmallnessH1_lt_quarter_C₁ :
    criticalSmallnessH1 < 1 / (4 * h1TrilinearConst) := by
  have h2 := h1TrilinearConst_pos
  refine lt_of_le_of_lt criticalSmallnessH1_le_eighth_C₁ ?_
  exact one_div_lt_one_div_of_lt (by linarith) (by linarith)

/-- **T20 U10b, `03-torus.tex:467-484` (`eq:H1energy`).**  For the zero initial
datum and `g ∈ F_T` with `ρ < c ν`, at every interior time of the classical
lifespan the squared gradient energy `‖∇v‖²₂` of the untranslated mean-free
velocity has an actual derivative `E'`, and

`E' + ν‖Δv‖²₂ ≤ CH1 · ν⁻¹ · ‖h‖²₂`,  `CH1 = 2`.

This is the `hOneEnergy` field of `CriticalRegularityTAPI` verbatim, at
`c = criticalSmallnessH1`. -/
theorem hOneEnergy : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (criticalSmallnessH1 * ν) →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
          ∀ t ∈ Ioo (0 : ℝ) T,
            ∃ E' : ℝ,
              HasDerivAt
                  (fun s ↦ gradientSqT
                    (fun x ↦ meanFreeVelocity g w.velocity (s, x))) E' t ∧
                E' + ν * laplacianSqT
                    (fun x ↦ meanFreeVelocity g w.velocity (t, x)) ≤
                  CH1 * ν⁻¹ * lTwoSqT
                    (fun x ↦ meanFreeForce g (t, x)) := by
  intro ν hν g hg hsmall T w t ht
  have htI : t ∈ Ico (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  have hgm : MemForceT g := hg
  have hus : ContDiff ℝ ∞ (fun x ↦ w.velocity (t, x)) := classical_velocity_slice_contDiff w htI
  have hup : IsPeriodicSpatial (fun x ↦ w.velocity (t, x)) := w.velocity_periodic t htI
  have hreg := reductionRegular ν hν g hg T w t htI
  have hvSP : SmoothPeriodicT (fun x ↦ meanFreeVelocity g w.velocity (t, x)) := hreg.2.1
  have hvH : MemPeriodicHomogeneous (1 / 2) (fun x ↦ meanFreeVelocity g w.velocity (t, x)) :=
    hreg.2.2.1
  have hhSP : SmoothPeriodicT (fun x ↦ meanFreeForce g (t, x)) :=
    hreg.2.2.2.2.2.2.1
  have hveq : (fun x ↦ meanFreeVelocity g w.velocity (t, x))
      = meanZeroPartT (fun x ↦ w.velocity (t, x)) := meanFreeVelocity_slice_eq hν hg w htI
  -- Off the zero mode the mean-free coefficients are the raw coefficients.
  have hvcoeff : ∀ (i : Fin 3) {k : PeriodicFrequency}, k ≠ 0 →
      periodicFourierCoeff (fun x ↦ ((meanFreeVelocity g w.velocity (t, x) i : ℝ) : ℂ)) k =
        velocityCoeffT w.velocity i k t := by
    intro i k hk
    have hfun : (fun x ↦ ((meanFreeVelocity g w.velocity (t, x) i : ℝ) : ℂ)) =
        (fun x ↦ ((meanZeroPartT (fun y ↦ w.velocity (t, y)) x i : ℝ) : ℂ)) := by
      funext x
      rw [show meanFreeVelocity g w.velocity (t, x) =
        meanZeroPartT (fun y ↦ w.velocity (t, y)) x from congrFun hveq x]
    rw [hfun]
    exact NSFormalization.Section3.T13.periodicFourierCoeff_meanZeroPart hus.continuous i hk
  -- the Fourier data of the velocity (order 2, homogeneous) and of the force (order 0)
  obtain ⟨Av2, hAv2, -⟩ := NSFormalization.Section3.T13.exists_homogeneous_datum
    (show (0 : ℝ) < 2 by norm_num) hup hus
  obtain ⟨Bh0, hBh0⟩ := smooth_periodic_datum (0 : ℝ) hhSP.1 hhSP.2
  -- the two real quantities
  set aL : ℝ := (periodicLpENorm 2
    (laplacian (fun x ↦ meanFreeVelocity g w.velocity (t, x)))).toReal with haL
  set bH : ℝ := (periodicLpENorm 2 (fun x ↦ meanFreeForce g (t, x))).toReal with hbH
  have hLsq : laplacianSqT (fun x ↦ meanFreeVelocity g w.velocity (t, x)) = aL ^ 2 := rfl
  have hHsq : lTwoSqT (fun x ↦ meanFreeForce g (t, x)) = bH ^ 2 := rfl
  have haL0 : 0 ≤ aL := ENNReal.toReal_nonneg
  have hbH0 : 0 ≤ bH := ENNReal.toReal_nonneg
  have hnormA : ‖Av2‖ = aL := by
    rw [haL, laplacian_meanFreeVelocity,
      periodicLpENorm_two_laplacian_eq_homogeneous hus hup,
      homENorm_toReal_eq_norm hAv2]
  have hnormB : ‖Bh0‖ = bH := by
    have h := parseval_forward (fun x ↦ meanFreeForce g (t, x)) Bh0 hBh0
      (memLp_torusLift_vector hhSP.1.continuous 2)
    rw [hbH]
    show _ = (eLpNorm (torusLift (fun x ↦ meanFreeForce g (t, x))) 2 periodicTorusMeasure).toReal
    rw [← h, ← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)]
  -- Dissipation.
  have hdiss : HasSum (fun k : PeriodicFrequency ↦
      periodicAngularFrequencySq k ^ 2 *
        ∑ i : Fin 3, ‖velocityCoeffT w.velocity i k t‖ ^ 2) (aL ^ 2) := by
    rw [← hLsq, laplacianSqT_meanFreeVelocity_eq_tsum (g := g) hus hup]
    exact (summable_laplacianSq_tsum w htI).hasSum
  -- Force pairing, Cauchy–Schwarz on the coefficient side.
  have hforce : HasSum (fun k : PeriodicFrequency ↦
      periodicAngularFrequencySq k *
        (∑ i : Fin 3, conj (velocityCoeffT w.velocity i k t) * velocityCoeffT g i k t).re)
      (torusRealPairing (s := (2 : ℝ)) Av2 Bh0) := by
    refine (hasSum_datum_pair (s := (2 : ℝ)) Av2 Bh0).congr_fun fun k ↦ ?_
    by_cases hk : k = 0
    · subst hk
      have hAv0 : ∀ i : Fin 3, Av2.1 i 0 = 0 := by
        intro i
        rw [hAv2.2.2.2 i 0, NSFormalization.Section3.T13.homogeneousDatumWeight_zero]
        simp
      have h0 : periodicAngularFrequencySq (0 : PeriodicFrequency) = 0 := by
        simp [periodicAngularFrequencySq]
      simp [hAv0, h0]
    · have hcv : ∀ i : Fin 3, Av2.1 i k =
          ((periodicAngularFrequencySq k : ℝ) : ℂ) * velocityCoeffT w.velocity i k t := by
        intro i
        rw [hAv2.2.2.2 i k, smul_eq_mul, homogeneousDatumWeight_two_eq]
        congr 1
        exact NSFormalization.Section3.T13.periodicFourierCoeff_meanZeroPart hus.continuous i hk
      have hch : ∀ i : Fin 3, Bh0.1 i k = velocityCoeffT g i k t := by
        intro i
        rw [hBh0.2.2 i k]
        norm_num
        exact NSFormalization.Section3.T13.periodicFourierCoeff_meanZeroPart
          (hgm.1.comp (contDiff_const.prodMk contDiff_id)).continuous i hk
      have hterm : (∑ i : Fin 3, conj (Av2.1 i k) * Bh0.1 i k) =
          ((periodicAngularFrequencySq k : ℝ) : ℂ) *
            ∑ i : Fin 3, conj (velocityCoeffT w.velocity i k t) * velocityCoeffT g i k t := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hcv i, hch i, map_mul, Complex.conj_ofReal]
        ring
      rw [hterm, Complex.re_ofReal_mul]
  -- Convection pairing, through torus Parseval and the constant-transport drop.
  have hNvS : ContDiff ℝ ∞ (fun x ↦ advection
      (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 x) :=
    @advection_spatial_contDiff (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 hvSP.1
  have hNvP : IsPeriodicSpatial (fun x ↦ advection
      (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 x) :=
    @advection_spatial_periodic (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 hvSP.2
  have hus1 : ContDiff ℝ 1 (fun y ↦ w.velocity (t, y)) := hus.of_le (by simp)
  have hNcoeff : ∀ (i : Fin 3) (k : PeriodicFrequency),
      velocityCoeffT (convectionFieldT w.velocity) i k t =
        periodicFourierCoeff (fun x ↦ ((advection
          (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 x i : ℝ) : ℂ)) k +
          periodicFourierCoeff (fun x ↦ (((fderiv ℝ (fun y ↦ w.velocity (t, y)) x
            (meanPathT g t) : Space) i : ℝ) : ℂ)) k := by
    intro i k
    have hDcont : Continuous
        (fun x ↦ (((fderiv ℝ (fun y ↦ w.velocity (t, y)) x (meanPathT g t) : Space) i :
          ℝ) : ℂ)) := by
      have hrw : (fun x ↦ (((fderiv ℝ (fun y ↦ w.velocity (t, y)) x (meanPathT g t) :
            Space) i : ℝ) : ℂ))
          = fun x ↦ ∑ j : Fin 3, ((meanPathT g t j : ℝ) : ℂ) *
              (((fderiv ℝ (fun y ↦ w.velocity (t, y)) x (coordinateVector j) : Space) i :
                ℝ) : ℂ) := by
        funext x
        have h0 : (fderiv ℝ (fun y ↦ w.velocity (t, y)) x) (meanPathT g t) =
            ∑ j : Fin 3, meanPathT g t j •
              (fderiv ℝ (fun y ↦ w.velocity (t, y)) x) (coordinateVector j) := by
          conv_lhs => rw [← NavierStokes.PeriodicUniqueness.sum_coordinates (meanPathT g t)]
          simp only [map_sum, map_smul]
        have h1 : (((fderiv ℝ (fun y ↦ w.velocity (t, y)) x (meanPathT g t) : Space) i : ℝ)) =
            ∑ j : Fin 3, meanPathT g t j *
              ((fderiv ℝ (fun y ↦ w.velocity (t, y)) x (coordinateVector j) : Space) i) := by
          have e : ∀ q : Space, (q i : ℝ) = EuclideanSpace.proj (𝕜 := ℝ) i q := fun _ ↦ rfl
          rw [e, h0, map_sum]
          exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul]; rfl
        rw [h1]
        push_cast
        rfl
      rw [hrw]
      exact continuous_finsetSum _ fun j _ ↦ continuous_const.mul
        (Complex.continuous_ofReal.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp
          (NavierStokes.PeriodicIntegration.continuous_partial hus1 j)))
    have hfun : (fun x ↦ ((convectionFieldT w.velocity (t, x) i : ℝ) : ℂ)) =
        (fun x ↦ ((advection (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 x i :
            ℝ) : ℂ)) +
          (fun x ↦ (((fderiv ℝ (fun y ↦ w.velocity (t, y)) x (meanPathT g t) : Space) i :
            ℝ) : ℂ)) := by
      funext x
      show ((convectionFieldT w.velocity (t, x) i : ℝ) : ℂ) =
        ((advection (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 x i : ℝ) : ℂ) +
          (((fderiv ℝ (fun y ↦ w.velocity (t, y)) x (meanPathT g t) : Space) i : ℝ) : ℂ)
      rw [advection_mean_split w t x]
      simp
    show periodicFourierCoeff (fun x ↦ ((convectionFieldT w.velocity (t, x) i : ℝ) : ℂ)) k = _
    rw [hfun]
    refine NSFormalization.Paper1.periodicFourierCoeff_add ?_ hDcont k
    exact Complex.continuous_ofReal.comp
      ((PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ ℝ) i).comp hNvS.continuous)
  have hconv : HasSum (fun k : PeriodicFrequency ↦
      periodicAngularFrequencySq k *
        (∑ i : Fin 3, conj (velocityCoeffT w.velocity i k t) *
          velocityCoeffT (convectionFieldT w.velocity) i k t).re)
      (-periodicPairing
        (laplacian (fun x ↦ meanFreeVelocity g w.velocity (t, x)))
        (fun x ↦ advection (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 x)) := by
    refine (hasSum_angularPairing hvSP ⟨hNvS, hNvP⟩).congr_fun fun k ↦ ?_
    by_cases hk : k = 0
    · subst hk
      have h0 : periodicAngularFrequencySq (0 : PeriodicFrequency) = 0 := by
        simp [periodicAngularFrequencySq]
      rw [h0]
      ring
    · congr 1
      have hDzero : (∑ i : Fin 3, conj (velocityCoeffT w.velocity i k t) *
          periodicFourierCoeff (fun x ↦ (((fderiv ℝ (fun y ↦ w.velocity (t, y)) x
            (meanPathT g t) : Space) i : ℝ) : ℂ)) k).re = 0 :=
        re_sum_conj_fderiv_dir_zero hus hup (meanPathT g t) k
      have hstep : ∀ i : Fin 3,
          conj (velocityCoeffT w.velocity i k t) *
              velocityCoeffT (convectionFieldT w.velocity) i k t =
            conj (velocityCoeffT w.velocity i k t) *
                periodicFourierCoeff (fun x ↦ ((advection
                  (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 x i : ℝ) : ℂ)) k +
              conj (velocityCoeffT w.velocity i k t) *
                periodicFourierCoeff (fun x ↦ (((fderiv ℝ (fun y ↦ w.velocity (t, y)) x
                  (meanPathT g t) : Space) i : ℝ) : ℂ)) k := by
        intro i
        rw [hNcoeff i k]
        ring
      rw [Finset.sum_congr rfl (fun i _ ↦ hstep i), Finset.sum_add_distrib, Complex.add_re,
        hDzero, add_zero, Complex.re_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hvcoeff i hk]
  -- The differentiated `H¹` energy, summed.
  have hcomb : HasSum (fun k : PeriodicFrequency ↦ h1FreqEnergyDeriv w.velocity k t)
      (-2 * ν * aL ^ 2 + 2 * torusRealPairing (s := (2 : ℝ)) Av2 Bh0 -
        2 * -periodicPairing
          (laplacian (fun x ↦ meanFreeVelocity g w.velocity (t, x)))
          (fun x ↦ advection
            (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 x)) := by
    have hsum := ((hdiss.mul_left (-2 * ν)).add (hforce.mul_left 2)).sub (hconv.mul_left 2)
    refine hsum.congr_fun fun k ↦ ?_
    simp only [h1FreqEnergyDeriv]
    rw [rawEnergyDeriv_split w hgm.1 hgm.2.1 ht k]
    ring
  have hE := hcomb.tsum_eq
  have hderiv := hasDerivAt_tsum_h1FreqEnergy w ht
  have hev : (fun s ↦ gradientSqT (fun x ↦ meanFreeVelocity g w.velocity (s, x)))
      =ᶠ[nhds t] (fun r ↦ ∑' k : PeriodicFrequency, h1FreqEnergy w.velocity k r) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    exact gradientSqT_meanFreeVelocity_eq_tsum (g := g)
      (classical_velocity_slice_contDiff w ⟨hr.1.le, hr.2⟩)
      (w.velocity_periodic r ⟨hr.1.le, hr.2⟩)
  refine ⟨∑' k : PeriodicFrequency, h1FreqEnergyDeriv w.velocity k t,
    hderiv.congr_of_eventuallyEq hev, ?_⟩
  rw [hE, hLsq, hHsq]
  -- force term: Cauchy–Schwarz then Young
  have hPf : torusRealPairing (s := (2 : ℝ)) Av2 Bh0 ≤ aL * bH := by
    have h := torusRealPairing_le (s := (2 : ℝ)) Av2 Bh0
    rwa [hnormA, hnormB] at h
  -- convection term: U10a plus U9's smallness
  have hQ : |periodicPairing
      (laplacian (fun x ↦ meanFreeVelocity g w.velocity (t, x)))
      (fun x ↦ advection (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 x)| ≤
      h1TrilinearConst * (criticalY (meanFreeVelocity g w.velocity) t).toReal *
        aL ^ 2 := by
    have h := h1Trilinear_slice g w.velocity t hvSP hvH
    rw [← hLsq]
    rw [periodicPairing_comm]
    exact h
  have hy : (criticalY (meanFreeVelocity g w.velocity) t).toReal ≤
      criticalSmallnessH1 * ν := by
    have hb := (yBound_of_le criticalSmallnessH1_le_half ν hν g hg hsmall T w t htI).1
    have hb2 := (yBound_of_le criticalSmallnessH1_le_half ν hν g hg hsmall T w t htI).2
    have hle : criticalY (meanFreeVelocity g w.velocity) t < 
        ENNReal.ofReal (criticalSmallnessH1 * ν) := lt_of_le_of_lt (hb.trans hb2) hsmall
    exact (ENNReal.toReal_lt_of_lt_ofReal hle).le
  have hy0 : 0 ≤ (criticalY (meanFreeVelocity g w.velocity) t).toReal := ENNReal.toReal_nonneg
  have hC₁ : 0 < h1TrilinearConst := h1TrilinearConst_pos
  have hcC₁ : h1TrilinearConst * criticalSmallnessH1 ≤ 1 / 8 := by
    have h := criticalSmallnessH1_le_eighth_C₁
    have h2 : h1TrilinearConst * criticalSmallnessH1 ≤
        h1TrilinearConst * (1 / (8 * h1TrilinearConst)) :=
      mul_le_mul_of_nonneg_left h hC₁.le
    have h3 : h1TrilinearConst * (1 / (8 * h1TrilinearConst)) = 1 / 8 := by
      field_simp
    linarith
  have habs : periodicPairing
      (laplacian (fun x ↦ meanFreeVelocity g w.velocity (t, x)))
      (fun x ↦ advection (lift (fun y ↦ meanFreeVelocity g w.velocity (t, y))) 0 x) ≤
      h1TrilinearConst * (criticalY (meanFreeVelocity g w.velocity) t).toReal * aL ^ 2 :=
    (le_abs_self _).trans hQ
  have hconvbound : h1TrilinearConst *
      (criticalY (meanFreeVelocity g w.velocity) t).toReal * aL ^ 2 ≤ ν / 8 * aL ^ 2 := by
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg aL)
    have h1 : h1TrilinearConst * (criticalY (meanFreeVelocity g w.velocity) t).toReal ≤
        h1TrilinearConst * (criticalSmallnessH1 * ν) :=
      mul_le_mul_of_nonneg_left hy hC₁.le
    nlinarith [hν, hcC₁]
  have hyoung : 2 * (aL * bH) ≤ ν / 2 * aL ^ 2 + 2 / ν * bH ^ 2 := by
    have hkey : (0 : ℝ) ≤ (ν * aL - 2 * bH) ^ 2 := sq_nonneg _
    have h2ν : (0 : ℝ) < 2 * ν := by linarith
    have hid : ν / 2 * aL ^ 2 + 2 / ν * bH ^ 2 - 2 * (aL * bH) =
        (ν * aL - 2 * bH) ^ 2 / (2 * ν) := by
      field_simp
      ring
    linarith [hid, div_nonneg hkey h2ν.le]
  have hCH1 : CH1 * ν⁻¹ * bH ^ 2 = 2 / ν * bH ^ 2 := by
    show (2 : ℝ) * ν⁻¹ * bH ^ 2 = 2 / ν * bH ^ 2
    field_simp
  rw [hCH1]
  linarith [hPf, habs, hconvbound, hyoung, mul_nonneg hν.le (sq_nonneg aL)]

end NSFormalization.Section3.T20
