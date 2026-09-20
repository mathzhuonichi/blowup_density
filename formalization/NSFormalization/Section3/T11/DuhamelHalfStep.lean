import NSFormalization.Section3.T11.ConvolutionBoundReal
import NSFormalization.Section3.T11.FractionalSmoothing
import NSFormalization.Section3.T10.ForcePaths
import NSFormalization.Section3.T10.Leray

/-!
# U9d1c: the endpoint Duhamel half-step `TorusHalfStepInput`

Work in progress.
-/

noncomputable section

namespace NSFormalization.Section3.T11

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal NNReal BigOperators Topology

-- Same pinned normed route as `LocalExistence.lean`; explicit instance names
-- (`logs/LESSONS.md`, 2026-09-17).
local instance halfStepNormedGroup : NormedAddCommGroup (PeriodicSobolev 3) :=
  realPeriodicSubmodule.normedAddCommGroup

local instance halfStepNormedSpace : NormedSpace ℝ (PeriodicSobolev 3) :=
  realPeriodicSubmodule.normedSpace

/-! ## 0. Coefficient extensionality and evaluation -/

/-- Two data on the canonical carrier agree as soon as all coefficients agree. -/
theorem torusDatum_ext {s : ℝ} {A B : PeriodicSobolev s}
    (h : ∀ (i : Fin 3) (k : PeriodicFrequency), A.1 i k = B.1 i k) : A = B := by
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  funext i
  ext k
  exact h i k

/-- Every single coefficient is dominated by the Euclidean product norm. -/
theorem torusCoeff_norm_le {s : ℝ} (A : PeriodicSobolev s) (i : Fin 3)
    (k : PeriodicFrequency) : ‖A.1 i k‖ ≤ ‖A‖ := by
  have h1 : ‖A.1 i k‖ ≤ ‖A.1 i‖ := lp.norm_apply_le_norm (by norm_num) (A.1 i) k
  have h2 : ‖A.1 i‖ ≤ ‖A.1‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.single_le_sum
      (f := fun j : Fin 3 ↦ ‖A.1 j‖ ^ 2) (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i)
  exact h1.trans h2

/-- Coefficient evaluation as a real continuous linear functional.  This is what
lets Bochner integrals on the carrier be computed coefficientwise. -/
def torusEvalCLM (s : ℝ) (i : Fin 3) (k : PeriodicFrequency) :
    PeriodicSobolev s →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun A ↦ A.1 i k
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    1 (fun A ↦ by rw [one_mul]; exact torusCoeff_norm_le A i k)

theorem torusEvalCLM_apply (s : ℝ) (i : Fin 3) (k : PeriodicFrequency)
    (A : PeriodicSobolev s) : torusEvalCLM s i k A = A.1 i k := rfl

/-- Coefficientwise evaluation of a Bochner interval integral on the carrier. -/
theorem torusCoeff_intervalIntegral {s a b : ℝ} {f : ℝ → PeriodicSobolev s}
    (hf : IntervalIntegrable f volume a b) (i : Fin 3) (k : PeriodicFrequency) :
    (∫ x in a..b, f x).1 i k = ∫ x in a..b, (f x).1 i k :=
  ((torusEvalCLM s i k).intervalIntegral_comp_comm hf).symm

/-! ## 1. The Leray projector as a bounded operator at every real order -/

/-- The Leray datum of `A` at the same order; unique, by the coefficient formula. -/
def torusLerayDatum (s : ℝ) (A : PeriodicSobolev s) : PeriodicSobolev s :=
  (leray_exists_contraction s A).choose

theorem torusLerayDatum_isDatum (s : ℝ) (A : PeriodicSobolev s) :
    IsPeriodicLerayDatum A (torusLerayDatum s A) :=
  (leray_exists_contraction s A).choose_spec.1

theorem torusLerayDatum_coeff (s : ℝ) (A : PeriodicSobolev s) (i : Fin 3)
    (k : PeriodicFrequency) :
    (torusLerayDatum s A).1 i k = periodicLeray s A i k :=
  (leray_exists_contraction s A).choose_spec.1 i k

theorem torusLerayDatum_norm_le (s : ℝ) (A : PeriodicSobolev s) :
    ‖torusLerayDatum s A‖ ≤ ‖A‖ :=
  (leray_exists_contraction s A).choose_spec.2.1

/-- The Leray symbol is additive at every frequency. -/
theorem periodicLeray_add (s : ℝ) (A B : PeriodicSobolev s) (i : Fin 3)
    (k : PeriodicFrequency) :
    periodicLeray s (A + B) i k = periodicLeray s A i k + periodicLeray s B i k := by
  have hc : ∀ j : Fin 3, (A + B).1 j k = A.1 j k + B.1 j k := fun _ ↦ rfl
  have hsum : (∑ j : Fin 3, (k j : ℂ) * (A + B).1 j k) =
      (∑ j : Fin 3, (k j : ℂ) * A.1 j k) + ∑ j : Fin 3, (k j : ℂ) * B.1 j k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [hc j]; ring
  unfold periodicLeray
  split_ifs with hk
  · exact hc i
  · rw [hc i, hsum]
    ring

/-- The Leray symbol is real-homogeneous at every frequency. -/
theorem periodicLeray_smul (s : ℝ) (c : ℝ) (A : PeriodicSobolev s) (i : Fin 3)
    (k : PeriodicFrequency) :
    periodicLeray s (c • A) i k = (c : ℂ) * periodicLeray s A i k := by
  have hc : ∀ j : Fin 3, (c • A).1 j k = (c : ℂ) * A.1 j k := fun _ ↦ rfl
  have hsum : (∑ j : Fin 3, (k j : ℂ) * (c • A).1 j k) =
      (c : ℂ) * ∑ j : Fin 3, (k j : ℂ) * A.1 j k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [hc j]; ring
  unfold periodicLeray
  split_ifs with hk
  · exact hc i
  · rw [hc i, hsum]
    ring

theorem torusLerayDatum_add (s : ℝ) (A B : PeriodicSobolev s) :
    torusLerayDatum s (A + B) = torusLerayDatum s A + torusLerayDatum s B := by
  refine torusDatum_ext fun i k ↦ ?_
  have hr : (torusLerayDatum s A + torusLerayDatum s B).1 i k =
      (torusLerayDatum s A).1 i k + (torusLerayDatum s B).1 i k := rfl
  rw [torusLerayDatum_coeff, periodicLeray_add, hr, torusLerayDatum_coeff,
    torusLerayDatum_coeff]

theorem torusLerayDatum_smul (s : ℝ) (c : ℝ) (A : PeriodicSobolev s) :
    torusLerayDatum s (c • A) = c • torusLerayDatum s A := by
  refine torusDatum_ext fun i k ↦ ?_
  have hr : (c • torusLerayDatum s A).1 i k = (c : ℂ) * (torusLerayDatum s A).1 i k := rfl
  rw [torusLerayDatum_coeff, periodicLeray_smul, hr, torusLerayDatum_coeff]

/-- The periodic Leray projector as a norm-one continuous linear map at every
real order. -/
def torusLerayCLM (s : ℝ) : PeriodicSobolev s →L[ℝ] PeriodicSobolev s :=
  LinearMap.mkContinuous
    { toFun := torusLerayDatum s
      map_add' := torusLerayDatum_add s
      map_smul' := torusLerayDatum_smul s }
    1 (fun A ↦ by rw [one_mul]; exact torusLerayDatum_norm_le s A)

theorem torusLerayCLM_coeff (s : ℝ) (A : PeriodicSobolev s) (i : Fin 3)
    (k : PeriodicFrequency) :
    (torusLerayCLM s A).1 i k = periodicLeray s A i k :=
  torusLerayDatum_coeff s A i k

/-- The Leray symbol commutes with order transport: it is `ℂ`-linear at each
frequency, and the transport is a scalar there. -/
theorem periodicLeray_reweight {s t : ℝ} {A : PeriodicSobolev s} {B : PeriodicSobolev t}
    (h : IsPeriodicReweight s t A B) (i : Fin 3) (k : PeriodicFrequency) :
    periodicLeray t B i k =
      (periodicFrequencyWeight k ^ ((t - s) / 2) : ℝ) • periodicLeray s A i k := by
  have hsum : (∑ j : Fin 3, (k j : ℂ) * B.1 j k) =
      ((periodicFrequencyWeight k ^ ((t - s) / 2) : ℝ) : ℂ) *
        ∑ j : Fin 3, (k j : ℂ) * A.1 j k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [h j k]
    simp only [Complex.real_smul]
    ring
  unfold periodicLeray
  split_ifs with hk
  · exact h i k
  · rw [h i k, hsum]
    simp only [Complex.real_smul]
    ring

/-- Order transport of Leray data. -/
theorem torusLeray_reweight {s t : ℝ} {A : PeriodicSobolev s} {B : PeriodicSobolev t}
    (h : IsPeriodicReweight s t A B) :
    IsPeriodicReweight s t (torusLerayCLM s A) (torusLerayCLM t B) := by
  intro i k
  rw [torusLerayCLM_coeff, torusLerayCLM_coeff, periodicLeray_reweight h i k]

/-- Leray data are unique, so any witness of `IsPeriodicLerayDatum` is the
bounded projector's value. -/
theorem torusLerayCLM_eq_of_isDatum {s : ℝ} {A B : PeriodicSobolev s}
    (h : IsPeriodicLerayDatum A B) : B = torusLerayCLM s A :=
  torusDatum_ext fun i k ↦ by rw [h i k, torusLerayCLM_coeff]

/-! ## 2. The smooth force at every real order, as a continuous Leray path -/

/-- A smooth space-periodic force has a **continuous** Leray-projected datum
path at every real order, transporting the order-three path of the hypotheses.
Integer-order continuity is `Section3/T10/ForcePaths.lean`; the real order is
reached by the bounded descent `persistenceDown` from the integer ceiling, and
the Leray projector is bounded at every order (§1). -/
theorem exists_continuous_lerayForcePath (σ : ℝ) {g : SpaceTimeField}
    (hg : ContDiff ℝ ∞ g) (hp : IsPeriodicOn univ g)
    {F P : ℝ → PeriodicSobolev 3} (hF : IsPeriodicSobolevPath 3 g F)
    (hP : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t)) :
    ∃ Pσ : ℝ → PeriodicSobolev σ, Continuous Pσ ∧
      ∀ t : ℝ, 0 ≤ t → IsPeriodicReweight 3 σ (P t) (Pσ t) := by
  have hσm : σ ≤ ((⌈σ⌉₊ : ℕ) : ℝ) := Nat.le_ceil σ
  have hgt : ∀ t : ℝ, ContDiff ℝ ∞ (fun x : Space ↦ g (t, x)) :=
    fun t ↦ hg.comp (contDiff_const.prodMk contDiff_id)
  have hpt : ∀ t : ℝ, IsPeriodicSpatial (fun x : Space ↦ g (t, x)) :=
    fun t ↦ hp t (mem_univ t)
  have hex : ∀ t : ℝ, ∃ G : PeriodicSobolev ((⌈σ⌉₊ : ℕ) : ℝ),
      IsPeriodicDatum ((⌈σ⌉₊ : ℕ) : ℝ) (fun x ↦ g (t, x)) G :=
    fun t ↦ exists_periodicDatum_smooth ((⌈σ⌉₊ : ℕ) : ℝ) (hgt t) (hpt t)
  choose G hG using hex
  have hGc : Continuous G := continuous_datum_path ⌈σ⌉₊ hg G hG
  refine ⟨fun t ↦ torusLerayCLM σ (persistenceDown ((⌈σ⌉₊ : ℕ) : ℝ) σ hσm (G t)), ?_, ?_⟩
  · exact (torusLerayCLM σ).continuous.comp
      ((persistenceDown ((⌈σ⌉₊ : ℕ) : ℝ) σ hσm).continuous.comp hGc)
  · intro t ht
    have hGσ : IsPeriodicDatum σ (fun x ↦ g (t, x))
        (persistenceDown ((⌈σ⌉₊ : ℕ) : ℝ) σ hσm (G t)) :=
      persistence_datum_of_reweight (hG t)
        (persistenceDown_reweight ((⌈σ⌉₊ : ℕ) : ℝ) σ hσm (G t))
    have hFσ : IsPeriodicReweight 3 σ (F t)
        (persistenceDown ((⌈σ⌉₊ : ℕ) : ℝ) σ hσm (G t)) :=
      persistence_reweight_of_data (hF t ht) hGσ
    have hPeq : P t = torusLerayCLM 3 (F t) := torusLerayCLM_eq_of_isDatum (hP t ht)
    rw [hPeq]
    exact torusLeray_reweight hFσ

/-! ## 3. The fractional endpoint-safe two-space contract -/

/-- The semigroup law of the `3/2`-gain symbol: the extra elapsed time acts by
the plain heat symbol. -/
theorem torusFracSymbol_add (ν a b : ℝ) (k : PeriodicFrequency) :
    torusFracSymbol ν (a + b) k = torusHeatSymbol ν b k * torusFracSymbol ν a k := by
  unfold torusFracSymbol torusHeatSymbol
  rw [NSFormalization.Paper1.PeriodicHeatMultiplier.heatSymbol_add]
  ring

/-- The scalar majorant of the fractional smoothing, with the window constant
evaluated at the elapsed time itself, so that it is defined for every `τ > 0`. -/
def torusFracMajorant (ν τ : ℝ) : ℝ := torusFracConst ν τ * torusFracKernel ν τ

theorem torusFracMajorant_nonneg {ν : ℝ} (hν : 0 < ν) (τ : ℝ) (hτ : 0 < τ) :
    0 ≤ torusFracMajorant ν τ :=
  mul_nonneg (torusFracConst_nonneg hν hτ le_rfl) (torusFracKernel_pos hν hτ).le

/-- The window constant is monotone in the window. -/
theorem torusFracConst_mono {ν a b : ℝ} (hν : 0 < ν) (ha : 0 ≤ a) (hab : a ≤ b) :
    torusFracConst ν a ≤ torusFracConst ν b := by
  unfold torusFracConst
  refine Real.rpow_le_rpow ?_ ?_ (by norm_num)
  · have : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
    nlinarith
  · nlinarith

theorem torusFracMajorant_measurable (ν : ℝ) : Measurable (torusFracMajorant ν) := by
  unfold torusFracMajorant torusFracConst torusFracKernel
  fun_prop

/-- The majorant is integrable up to the endpoint on every window. -/
theorem torusFracMajorant_intervalIntegrable {ν : ℝ} (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (torusFracMajorant ν) volume 0 T := by
  have hk : IntervalIntegrable (fun τ : ℝ ↦ torusFracKernel ν τ) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr (torusFracKernel_integrableOn hν hT)
  refine (hk.const_mul (torusFracConst ν T)).mono_fun'
    (torusFracMajorant_measurable ν).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with τ hτ
  rw [uIoc_of_le hT] at hτ
  rw [Real.norm_eq_abs, abs_of_nonneg (torusFracMajorant_nonneg hν τ hτ.1)]
  exact mul_le_mul_of_nonneg_right (torusFracConst_mono hν hτ.1.le hτ.2)
    (torusFracKernel_pos hν hτ.1).le

/-- The endpoint-safe two-space Duhamel contract carried by the *fractional*
smoothing: solution space `H^{r+1/2}`, rough space `H^{r-1}`, gain `3/2`,
kernel `(ν τ)^{-3/4}`, and lane 328's real-order projected convolution as the
quadratic source. -/
def torusFracContract (r : ℝ) (hr : 3 ≤ r) {ν : ℝ} (hν : 0 < ν) :
    MNS2.EndpointSafeTwoSpaceDuhamelContract ℝ
      (PeriodicSobolev (r + 1 / 2)) (PeriodicSobolev (r - 1)) where
  linearEvolution := torusHeatCLM hν.le
  linear_zero := by
    apply ContinuousLinearMap.ext
    intro A
    exact torusHeat_zero 3 hν.le A
  linear_add := by
    intro a b
    apply ContinuousLinearMap.ext
    intro A
    exact torusHeat_add 3 hν.le a.2 b.2 A
  continuous_linear_action := torusHeatCLM_continuous hν.le
  positiveSmoothing := fun τ hτ ↦ torusHeatSmoothingCLM_frac (r - 1) hν τ hτ le_rfl
  bilinear := torusConvolutionCLM_real r hr
  smoothingKernel := torusFracMajorant ν
  smoothingKernel_nonneg := fun τ hτ ↦ torusFracMajorant_nonneg hν τ hτ
  norm_positiveSmoothing_apply_le := fun τ hτ y ↦
    torusHeatSmoothingFrac_norm_le (r - 1) hν hτ le_rfl y
  intervalIntegrable_smoothingKernel := torusFracMajorant_intervalIntegrable hν
  smoothing_coherent := by
    intro a ha b
    apply ContinuousLinearMap.ext
    intro A
    refine torusDatum_ext fun i k ↦ ?_
    change ((torusFracSymbol ν (a + (b : ℝ)) k : ℝ) : ℂ) * A.1 i k =
      ((torusHeatSymbol ν (b : ℝ) k : ℝ) : ℂ) *
        (((torusFracSymbol ν a k : ℝ) : ℂ) * A.1 i k)
    rw [torusFracSymbol_add, Complex.ofReal_mul]
    ring

/-! ## 4. The half-step field and its continuity -/

/-- The order-`(r+1/2)` Duhamel field built from the order-`(r+1/2)` datum `A'`
of the smooth initial field, the order-`(r+1/2)` Leray force path `Pσ`, and the
fractional Duhamel integral of the order-`r` realization `v`. -/
def torusHalfStepField {ν : ℝ} (hν : 0 < ν) (C : TorusTwoSpaceContract ν) (r : ℝ) (hr : 3 ≤ r)
    (A' : PeriodicSobolev (r + 1 / 2)) (Pσ : ℝ → PeriodicSobolev (r + 1 / 2))
    (v : ℝ → PeriodicSobolev r) (t : ℝ) : PeriodicSobolev (r + 1 / 2) :=
  C.analytic.linearEvolution (Real.toNNReal t) A' +
    (∫ s in (0 : ℝ)..t, C.analytic.linearEvolution (Real.toNNReal (t - s)) (Pσ s)) -
      (torusFracContract r hr hν).duhamelIntegral v t

/-- Continuity of the fractional Duhamel integral on the half-open window: the
vendor contract gives it on every closed subwindow, and `Ico 0 T` is covered by
those. -/
theorem torusFracDuhamel_continuousOn {ν : ℝ} (hν : 0 < ν) (r : ℝ) (hr : 3 ≤ r)
    {T : ℝ} {v : ℝ → PeriodicSobolev r} (hv : ContinuousOn v (Ico 0 T)) :
    ContinuousOn ((torusFracContract r hr hν).duhamelIntegral v) (Ico 0 T) := by
  intro t₀ ht₀
  have h1 : t₀ < (t₀ + T) / 2 := by have := ht₀.2; linarith
  have h2 : (t₀ + T) / 2 < T := by have := ht₀.2; linarith
  have hT'0 : (0 : ℝ) ≤ (t₀ + T) / 2 := le_trans ht₀.1 h1.le
  have hsub : Icc (0 : ℝ) ((t₀ + T) / 2) ⊆ Ico 0 T :=
    fun x hx ↦ ⟨hx.1, lt_of_le_of_lt hx.2 h2⟩
  have hc := (torusFracContract r hr hν).continuousOn_duhamelIntegral hT'0 (hv.mono hsub)
  refine (hc t₀ ⟨ht₀.1, h1.le⟩).mono_of_mem_nhdsWithin ?_
  exact mem_nhdsWithin.mpr ⟨Iio ((t₀ + T) / 2), isOpen_Iio, h1,
    fun x hx ↦ ⟨hx.2.1, hx.1.le⟩⟩

theorem torusHalfStepField_continuousOn {ν : ℝ} (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    (r : ℝ) (hr : 3 ≤ r) {T : ℝ} (hT : 0 ≤ T) (A' : PeriodicSobolev (r + 1 / 2))
    {Pσ : ℝ → PeriodicSobolev (r + 1 / 2)} (hPσ : Continuous Pσ)
    {v : ℝ → PeriodicSobolev r} (hv : ContinuousOn v (Ico 0 T)) :
    ContinuousOn (torusHalfStepField hν C r hr A' Pσ v) (Ico 0 T) := by
  have hlin : Continuous (fun t : ℝ ↦ C.analytic.linearEvolution (Real.toNNReal t) A') :=
    C.analytic.continuous_linear_action.comp
      (continuous_real_toNNReal.prodMk continuous_const)
  have hforce := torus_forceIntegral_continuousOn C hT Pσ hPσ.continuousOn
  exact (hlin.continuousOn.add (hforce.mono Ico_subset_Icc_self)).sub
    (torusFracDuhamel_continuousOn hν r hr hv)

/-! ## 5. The coefficient identity -/

@[simp]
theorem torusFracContract_positiveSmoothing (r : ℝ) (hr : 3 ≤ r) {ν : ℝ} (hν : 0 < ν)
    (τ : ℝ) (hτ : 0 < τ) :
    (torusFracContract r hr hν).positiveSmoothing τ hτ =
      torusHeatSmoothingCLM_frac (r - 1) hν τ hτ le_rfl := rfl

@[simp]
theorem torusFracContract_bilinear (r : ℝ) (hr : 3 ≤ r) {ν : ℝ} (hν : 0 < ν) :
    (torusFracContract r hr hν).bilinear = torusConvolutionCLM_real r hr := rfl

/-- The exponent bookkeeping of the half-step: gain `3/2` on an order-`(r-1)`
source is the order-`(r+1/2)` transport of gain `1` on an order-two source. -/
theorem torusHalfStep_weight_identity (r : ℝ) (k : PeriodicFrequency) :
    periodicFrequencyWeight k ^ (3 / 4 : ℝ) * periodicFrequencyWeight k ^ ((r - 3) / 2) =
      periodicFrequencyWeight k ^ ((r + 1 / 2 - 3) / 2) *
        Real.sqrt (periodicFrequencyWeight k) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add (persistence_weight_pos k),
    ← Real.rpow_add (persistence_weight_pos k)]
  congr 1
  ring

/-- The order-`r` realization descends to the order-three mild solution. -/
theorem torusHalfStep_down_eq {r T : ℝ} (hr : 3 ≤ r) {u : ℝ → PeriodicSobolev 3}
    {v : ℝ → PeriodicSobolev r}
    (hvu : ∀ t ∈ Ico (0 : ℝ) T, IsPeriodicReweight 3 r (u t) (v t))
    {s : ℝ} (hs : s ∈ Ico (0 : ℝ) T) : persistenceDown r 3 hr (v s) = u s := by
  refine torusDatum_ext fun i k ↦ ?_
  have h := persistence_reweight_trans (hvu s hs) (persistenceDown_reweight r 3 hr (v s)) i k
  simpa using h

/-- Coefficientwise, the fractional Duhamel integrand of the order-`r` path is
the order-`(r+1/2)` transport of the contract's own order-three integrand. -/
theorem torusFracDuhamelIntegrand_coeff {ν : ℝ} (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    (r : ℝ) (hr : 3 ≤ r) {T : ℝ} {u : ℝ → PeriodicSobolev 3} {v : ℝ → PeriodicSobolev r}
    (hvu : ∀ t ∈ Ico (0 : ℝ) T, IsPeriodicReweight 3 r (u t) (v t))
    (t : ℝ) {s : ℝ} (hs : s ∈ Ico (0 : ℝ) T) (i : Fin 3) (k : PeriodicFrequency) :
    ((torusFracContract r hr hν).duhamelIntegrand t v s).1 i k =
      ((periodicFrequencyWeight k ^ ((r + 1 / 2 - 3) / 2) : ℝ) : ℂ) *
        (C.analytic.duhamelIntegrand t u s).1 i k := by
  rcases lt_or_ge s t with hst | hst
  · have hkey : ((periodicFrequencyWeight k ^ (3 / 4 : ℝ) : ℝ) : ℂ) *
        ((periodicFrequencyWeight k ^ ((r - 3) / 2) : ℝ) : ℂ) =
        ((periodicFrequencyWeight k ^ ((r + 1 / 2 - 3) / 2) : ℝ) : ℂ) *
          ((Real.sqrt (periodicFrequencyWeight k) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, torusHalfStep_weight_identity]
    rw [MNS2.EndpointSafeTwoSpaceDuhamelContract.duhamelIntegrand_of_lt _ _ _ hst,
      MNS2.EndpointSafeTwoSpaceDuhamelContract.duhamelIntegrand_of_lt _ _ _ hst,
      torusFracContract_positiveSmoothing, torusFracContract_bilinear,
      torusHeatSmoothingCLM_frac_apply, C.smoothing_symbol, C.bilinear_symbol,
      torusConvolutionCLM_real_coeff_transport r hr (v s) (v s) i k,
      torusHalfStep_down_eq hr hvu hs]
    simp only [torusFracSymbol, Complex.ofReal_mul]
    linear_combination (((torusHeatSymbol ν (t - s) k : ℝ) : ℂ) *
      torusProjectedConvectionSymbol (u s) (u s) i k) * hkey
  · rw [MNS2.EndpointSafeTwoSpaceDuhamelContract.duhamelIntegrand_of_le _ _ _ hst,
      MNS2.EndpointSafeTwoSpaceDuhamelContract.duhamelIntegrand_of_le _ _ _ hst]
    simp

/-- **The half-step coefficient identity.**  At every time of the half-open
window the order-`(r+1/2)` Duhamel field has exactly the order-`(r+1/2)`
transported coefficients of the order-three mild solution. -/
theorem torusHalfStepField_coeff {ν : ℝ} (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    (r : ℝ) (hr : 3 ≤ r) {T : ℝ} {A : PeriodicSobolev 3} {P u : ℝ → PeriodicSobolev 3}
    (hu : TorusForcedMildOn C A P T u)
    {A' : PeriodicSobolev (r + 1 / 2)} (hAA' : IsPeriodicReweight 3 (r + 1 / 2) A A')
    {Pσ : ℝ → PeriodicSobolev (r + 1 / 2)} (hPσc : Continuous Pσ)
    (hPσ : ∀ s : ℝ, 0 ≤ s → IsPeriodicReweight 3 (r + 1 / 2) (P s) (Pσ s))
    {v : ℝ → PeriodicSobolev r} (hv : ContinuousOn v (Ico 0 T))
    (hvu : ∀ t ∈ Ico (0 : ℝ) T, IsPeriodicReweight 3 r (u t) (v t))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (i : Fin 3) (k : PeriodicFrequency) :
    (torusHalfStepField hν C r hr A' Pσ v t).1 i k =
      ((periodicFrequencyWeight k ^ ((r + 1 / 2 - 3) / 2) : ℝ) : ℂ) * (u t).1 i k := by
  have htIcc : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
  have hsub : Icc (0 : ℝ) t ⊆ Ico 0 T := fun x hx ↦ ⟨hx.1, lt_of_le_of_lt hx.2 ht.2⟩
  have huIcc : uIcc (0 : ℝ) t = Icc 0 t := uIcc_of_le ht.1
  -- integrability of the four integrals involved
  have hPint : IntervalIntegrable
      (fun s ↦ C.analytic.linearEvolution (Real.toNNReal (t - s)) (Pσ s)) volume 0 t :=
    torus_forceIntegrable C Pσ hPσc.continuousOn htIcc
  have hPint3 := hu.force_integrable t htIcc
  have hQint : IntervalIntegrable
      ((torusFracContract r hr hν).duhamelIntegrand t v) volume 0 t :=
    (torusFracContract r hr hν).intervalIntegrable_duhamelIntegrand_of_continuousOn ht.1
      (hv.mono hsub)
  have hQint3 := hu.nonlinear_integrable t htIcc
  have hnn : Real.toNNReal t = (⟨t, htIcc.1⟩ : ℝ≥0) := Real.toNNReal_of_nonneg htIcc.1
  -- the order-three mild equation, coefficientwise
  have hueq : (u t).1 i k =
      (C.analytic.linearEvolution ⟨t, htIcc.1⟩ A).1 i k +
        (∫ s in (0 : ℝ)..t, C.analytic.linearEvolution (Real.toNNReal (t - s)) (P s)).1 i k -
        (∫ s in (0 : ℝ)..t, C.analytic.duhamelIntegrand t u s).1 i k := by
    rw [hu.equation t htIcc]; rfl
  -- the linear term
  have hlin : (C.analytic.linearEvolution (Real.toNNReal t) A').1 i k =
      ((periodicFrequencyWeight k ^ ((r + 1 / 2 - 3) / 2) : ℝ) : ℂ) *
        (C.analytic.linearEvolution ⟨t, htIcc.1⟩ A).1 i k := by
    rw [hnn, C.linear_symbol ⟨t, htIcc.1⟩ A' i k, C.linear_symbol ⟨t, htIcc.1⟩ A i k,
      hAA' i k, Complex.real_smul]
    ring
  -- the force term
  have hforce : (∫ s in (0 : ℝ)..t,
        C.analytic.linearEvolution (Real.toNNReal (t - s)) (Pσ s)).1 i k =
      ((periodicFrequencyWeight k ^ ((r + 1 / 2 - 3) / 2) : ℝ) : ℂ) *
        (∫ s in (0 : ℝ)..t,
          C.analytic.linearEvolution (Real.toNNReal (t - s)) (P s)).1 i k := by
    rw [torusCoeff_intervalIntegral hPint, torusCoeff_intervalIntegral hPint3,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    rw [huIcc] at hx
    rw [C.linear_symbol (Real.toNNReal (t - x)) (Pσ x) i k,
      C.linear_symbol (Real.toNNReal (t - x)) (P x) i k, hPσ x hx.1 i k, Complex.real_smul]
    ring
  -- the nonlinear term
  have hnl : ((torusFracContract r hr hν).duhamelIntegral v t).1 i k =
      ((periodicFrequencyWeight k ^ ((r + 1 / 2 - 3) / 2) : ℝ) : ℂ) *
        (∫ s in (0 : ℝ)..t, C.analytic.duhamelIntegrand t u s).1 i k := by
    rw [MNS2.EndpointSafeTwoSpaceDuhamelContract.duhamelIntegral,
      torusCoeff_intervalIntegral hQint, torusCoeff_intervalIntegral hQint3,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    rw [huIcc] at hx
    exact torusFracDuhamelIntegrand_coeff hν C r hr hvu t (hsub hx) i k
  have hsplit : (torusHalfStepField hν C r hr A' Pσ v t).1 i k =
      (C.analytic.linearEvolution (Real.toNNReal t) A').1 i k +
        (∫ s in (0 : ℝ)..t,
          C.analytic.linearEvolution (Real.toNNReal (t - s)) (Pσ s)).1 i k -
        ((torusFracContract r hr hν).duhamelIntegral v t).1 i k := rfl
  rw [hsplit, hlin, hforce, hnl, hueq]
  ring

/-! ## 6. The half-step, unconditionally -/

/-- **The lane's theorem.**  The half-order gain `TorusHalfStepInput` of
`Section3/T11/Persistence.lean` holds outright: no named input, no hypothesis
beyond those of the statement. -/
theorem torusHalfStepInput : TorusHalfStepInput := by
  intro ν hν C a g T ha hg hgp hT A F P u hA hF hP hu r hr v hv hvu
  obtain ⟨A', hA'⟩ := exists_periodicDatum_smooth (r + 1 / 2) ha.1 ha.2.1
  have hAA' : IsPeriodicReweight 3 (r + 1 / 2) A A' := persistence_reweight_of_data hA hA'
  obtain ⟨Pσ, hPσc, hPσ⟩ := exists_continuous_lerayForcePath (r + 1 / 2) hg hgp hF hP
  refine ⟨torusHalfStepField hν C r hr A' Pσ v,
    torusHalfStepField_continuousOn hν C r hr hT.le A' hPσc hv, fun t ht i k ↦ ?_⟩
  have hw : (periodicFrequencyWeight k ^ ((r + 1 / 2 - r) / 2) : ℝ) *
      periodicFrequencyWeight k ^ ((r - 3) / 2) =
      periodicFrequencyWeight k ^ ((r + 1 / 2 - 3) / 2) := by
    rw [← Real.rpow_add (persistence_weight_pos k)]
    congr 1
    ring
  rw [torusHalfStepField_coeff hν C r hr hu hAA' hPσc hPσ hv hvu ht i k,
    hvu t ht i k, smul_smul, hw, Complex.real_smul]

/-- The half-order ladder of `Persistence.lean`, now unconditional. -/
theorem persistence_halfOrder_ladder_unconditional
    (ν : ℝ) (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    (a : SpatialField) (g : SpaceTimeField) (T : ℝ)
    (ha : a ∈ initialClassT) (hg : ContDiff ℝ ∞ g) (hp : IsPeriodicOn univ g)
    (hT : 0 < T) (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3)
    (hA : IsPeriodicDatum 3 a A) (hF : IsPeriodicSobolevPath 3 g F)
    (hP : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hu : TorusForcedMildOn C A P T u) :
    ∀ n : ℕ, ∃ v : ℝ → PeriodicSobolev (3 + (n : ℝ) / 2),
      ContinuousOn v (Ico 0 T) ∧
      ∀ t ∈ Ico 0 T, IsPeriodicReweight 3 (3 + (n : ℝ) / 2) (u t) (v t) :=
  persistence_halfOrder_ladder torusHalfStepInput ν hν C a g T ha hg hp hT A F P u hA hF hP hu

/-- **Unconditional physical-coefficient persistence** at every integer order,
on the original horizon: the conditional theorem of `Persistence.lean` with its
single analytic input discharged. -/
theorem persistence_unconditional
    (ν : ℝ) (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    (a : SpatialField) (g : SpaceTimeField) (T : ℝ)
    (ha : a ∈ initialClassT) (hg : ContDiff ℝ ∞ g) (hp : IsPeriodicOn univ g)
    (hT : 0 < T) (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3)
    (hA : IsPeriodicDatum 3 a A) (hF : IsPeriodicSobolevPath 3 g F)
    (hP : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hu : TorusForcedMildOn C A P T u) :
    ∀ m : ℕ, ∃ u_m : ℝ → PeriodicSobolev m,
      (∀ t ∈ Ico 0 T, IsPeriodicReweight 3 (m : ℝ) (u t) (u_m t)) ∧
      ContinuousOn u_m (Ico 0 T) ∧
      (∀ K : Set ℝ, IsCompact K → K ⊆ Ico 0 T →
        ∃ B : ℝ, ∀ t ∈ K, ‖u_m t‖ ≤ B) :=
  torusForcedMildOn_persistence torusHalfStepInput ν hν C a g T ha hg hp hT A F P u hA hF hP hu

/-! ## 7. Non-vacuity: the constant-datum family -/

/-- A constant vector field is divergence free. -/
theorem isSolenoidal_const (c : Space) :
    NSFormalization.Section4.A02.IsSolenoidal (fun _ : Space ↦ c) := by
  intro x
  simp [NavierStokes.ProblemStatement.spatialDivergence,
    NavierStokes.ProblemStatement.spatialDerivative]

theorem constantDatum_mem_initialClassT (c : Space) :
    (fun _ : Space ↦ c) ∈ initialClassT :=
  ⟨contDiff_const, fun _ _ ↦ rfl, isSolenoidal_const c⟩

/-- Constant modes are already divergence free at the coefficient level. -/
theorem torusConstantDatum_solenoidal (s : ℝ) (c : Space) :
    IsSolenoidalPeriodicDatum (torusConstantDatum s c) := by
  intro k
  by_cases hk : k = 0
  · subst k
    simp [periodicDerivativeSymbol]
  · have hz : ∀ j : Fin 3, (torusConstantDatum s c).1 j k = 0 := by
      intro j
      change (lp.single 2 (0 : PeriodicFrequency) (c j : ℂ) : PeriodicScalarData) k = 0
      simp [lp.single_apply, hk]
    simp [hz]

/-- Hence the constant datum is its own Leray projection. -/
theorem torusConstantDatum_lerayDatum (s : ℝ) (c : Space) :
    IsPeriodicLerayDatum (torusConstantDatum s c) (torusConstantDatum s c) := fun i k ↦
  (periodicLeray_of_solenoidal (torusConstantDatum s c)
    (torusConstantDatum_solenoidal s c) i k).symm

/-- The hypotheses of `persistence_unconditional` are satisfiable by a nonzero,
nonstationary, forced mild solution: the constant-datum family of
`Persistence.lean`.  The conclusion is therefore not vacuous. -/
theorem persistence_unconditional_constant {ν : ℝ} (hν : 0 < ν)
    (C : TorusTwoSpaceContract ν) (c : Space) :
    ∀ m : ℕ, ∃ u_m : ℝ → PeriodicSobolev m,
      (∀ t ∈ Ico (0 : ℝ) 1,
        IsPeriodicReweight 3 (m : ℝ) ((1 + t) • torusConstantDatum 3 c) (u_m t)) ∧
      ContinuousOn u_m (Ico (0 : ℝ) 1) ∧
      (∀ K : Set ℝ, IsCompact K → K ⊆ Ico (0 : ℝ) 1 →
        ∃ B : ℝ, ∀ t ∈ K, ‖u_m t‖ ≤ B) :=
  persistence_unconditional ν hν C (fun _ ↦ c) (fun _ ↦ c) 1
    (constantDatum_mem_initialClassT c) contDiff_const (fun _ _ _ _ ↦ rfl) one_pos
    (torusConstantDatum 3 c) (fun _ ↦ torusConstantDatum 3 c)
    (fun _ ↦ torusConstantDatum 3 c) (fun t ↦ (1 + t) • torusConstantDatum 3 c)
    (torusConstantDatum_isDatum 3 c) (fun _ _ ↦ torusConstantDatum_isDatum 3 c)
    (fun _ _ ↦ torusConstantDatum_lerayDatum 3 c)
    (persistence_constant_mild C zero_le_one c)

end NSFormalization.Section3.T11
