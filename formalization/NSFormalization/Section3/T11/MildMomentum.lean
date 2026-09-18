import NSFormalization.Section3.T11.MildPressure
import Mathlib.Analysis.Calculus.SmoothSeries

/-! # Time differentiation of the mild torus solution and the momentum equation

The Duhamel formula `TorusForcedMildOn` is differentiated in time coefficient by
coefficient: every Fourier coefficient of the mild solution solves the scalar
forced linear ODE `ẏ = -ν|2πk|² y + (P(F - Q))^(k)`.  From that, together with
the locally uniform rapid decay supplied by `PersistenceInput`, the physical
velocity has a genuine time derivative, and the momentum equation holds for any
pressure whose gradient is the Leray complement of the physical source.
-/
noncomputable section
namespace NSFormalization.Section3.T11

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NavierStokes.PeriodicIntegration (spatialPartial)
open NSFormalization.Section3.T10
open scoped BigOperators ContDiff ComplexConjugate NNReal Topology

local instance mildMomentumNormedGroup (s : ℝ) : NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance mildMomentumNormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

/-! ## 1. Coefficient functionals and the heat symbol as an exponential -/

/-- Evaluation of one Fourier coefficient, as a continuous real-linear functional. -/
def torusCoeffCLM (s : ℝ) (i : Fin 3) (k : PeriodicFrequency) :
    PeriodicSobolev s →L[ℝ] ℂ :=
  (lp.evalCLM ℝ (fun _ : PeriodicFrequency ↦ ℂ) 2 k).comp
    ((PiLp.proj 2 (fun _ : Fin 3 ↦ PeriodicScalarData) i).comp
      realPeriodicSubmodule.subtypeL)

@[simp] theorem torusCoeffCLM_apply (s : ℝ) (i : Fin 3) (k : PeriodicFrequency)
    (A : PeriodicSobolev s) : torusCoeffCLM s i k A = A.1 i k := rfl

/-- A single coefficient is dominated by the Sobolev norm of the datum. -/
theorem norm_coeff_le_norm {s : ℝ} (A : PeriodicSobolev s) (i : Fin 3)
    (k : PeriodicFrequency) : ‖A.1 i k‖ ≤ ‖A‖ :=
  (lp.norm_apply_le_norm (by norm_num) (A.1 i) k).trans (PiLp.norm_apply_le A.1 i)

theorem torusLaplaceEigenvalue_eq (k : PeriodicFrequency) :
    NSFormalization.Paper1.PeriodicHeatMultiplier.laplaceEigenvalue k =
      periodicAngularFrequencySq k := by
  unfold NSFormalization.Paper1.PeriodicHeatMultiplier.laplaceEigenvalue
    periodicAngularFrequencySq
  rw [← torus_weight_eq]
  unfold periodicFrequencyWeight
  ring

theorem periodicAngularFrequencySq_nonneg (k : PeriodicFrequency) :
    0 ≤ periodicAngularFrequencySq k := by
  unfold periodicAngularFrequencySq; positivity

/-- The heat symbol is an honest real exponential in the elapsed time. -/
theorem torusHeatSymbol_eq_exp (ν r : ℝ) (k : PeriodicFrequency) :
    torusHeatSymbol ν r k = Real.exp (-(ν * periodicAngularFrequencySq k) * r) := by
  unfold torusHeatSymbol NSFormalization.Paper1.PeriodicHeatMultiplier.heatSymbol
  rw [torusLaplaceEigenvalue_eq]
  ring_nf

theorem torusHeatSymbol_add' (ν r r' : ℝ) (k : PeriodicFrequency) :
    torusHeatSymbol ν (r + r') k = torusHeatSymbol ν r k * torusHeatSymbol ν r' k :=
  NSFormalization.Paper1.PeriodicHeatMultiplier.heatSymbol_add ν r r' k

theorem torusHeatSymbol_zero' (ν : ℝ) (k : PeriodicFrequency) :
    torusHeatSymbol ν 0 k = 1 :=
  NSFormalization.Paper1.PeriodicHeatMultiplier.heatSymbol_zero ν k

/-- The scalar heat factor is differentiable in time with the expected symbol. -/
theorem torusHeatSymbol_hasDerivAt (ν r : ℝ) (k : PeriodicFrequency) :
    HasDerivAt (fun x : ℝ ↦ torusHeatSymbol ν x k)
      (-(ν * periodicAngularFrequencySq k) * torusHeatSymbol ν r k) r := by
  have h : HasDerivAt (fun x : ℝ ↦ Real.exp (-(ν * periodicAngularFrequencySq k) * x))
      (Real.exp (-(ν * periodicAngularFrequencySq k) * r) *
        (-(ν * periodicAngularFrequencySq k))) r := by
    simpa using ((hasDerivAt_id r).const_mul (-(ν * periodicAngularFrequencySq k))).exp
  simp only [torusHeatSymbol_eq_exp]
  simpa only [mul_comm] using h

theorem torusHeatSymbol_continuous (ν : ℝ) (k : PeriodicFrequency) :
    Continuous (fun x : ℝ ↦ torusHeatSymbol ν x k) := by
  simp only [torusHeatSymbol_eq_exp]
  exact Real.continuous_exp.comp (continuous_const.mul continuous_id)


/-! ## 2. The Duhamel formula coefficient by coefficient -/

/-- The quadratic Duhamel source `Q(u,u)` of the mild equation, as an `H²` path. -/
def mildNonlinearDatum {ν : ℝ} (C : TorusTwoSpaceContract ν)
    (u : ℝ → PeriodicSobolev 3) (s : ℝ) : PeriodicSobolev 2 :=
  C.analytic.bilinear (u s) (u s)

theorem mildNonlinearDatum_continuousOn {ν : ℝ} (C : TorusTwoSpaceContract ν)
    {u : ℝ → PeriodicSobolev 3} {I : Set ℝ} (hu : ContinuousOn u I) :
    ContinuousOn (mildNonlinearDatum C u) I := by
  have hp : ContinuousOn (fun s ↦ (u s, u s)) I := hu.prodMk hu
  exact C.analytic.bilinear.continuous₂.comp_continuousOn hp

/-- The Picard value at a nonnegative real time, with the real elapsed time
visible in every integral. -/
theorem torusForcedPicard_real {ν : ℝ} (C : TorusTwoSpaceContract ν)
    (A : PeriodicSobolev 3) (P u : ℝ → PeriodicSobolev 3) {t : ℝ} (ht0 : 0 ≤ t) :
    torusForcedPicard C A P u ⟨t, ht0⟩ =
      (C.analytic.linearEvolution ⟨t, ht0⟩ A +
        ∫ s in (0 : ℝ)..t, C.analytic.linearEvolution (Real.toNNReal (t - s)) (P s)) -
      ∫ s in (0 : ℝ)..t, C.analytic.duhamelIntegrand t u s := rfl

/-- Every Fourier coefficient of the mild solution satisfies the scalar Duhamel
formula, with the endpoint-safe smoothing replaced by the honest heat symbol. -/
theorem mild_coeff_duhamel {ν T : ℝ} {C : TorusTwoSpaceContract ν}
    {A : PeriodicSobolev 3} {P u : ℝ → PeriodicSobolev 3}
    (hu : TorusForcedMildOn C A P T u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (i : Fin 3) (k : PeriodicFrequency) :
    (u t).1 i k = (torusHeatSymbol ν t k : ℂ) * A.1 i k
      + (∫ s in (0 : ℝ)..t, (torusHeatSymbol ν (t - s) k : ℂ) * (P s).1 i k)
      - (Real.sqrt (periodicFrequencyWeight k) : ℂ) *
        ∫ s in (0 : ℝ)..t,
          (torusHeatSymbol ν (t - s) k : ℂ) * (mildNonlinearDatum C u s).1 i k := by
  have hL := hu.equation t ht
  have h : (u t).1 i k = torusCoeffCLM 3 i k (torusForcedPicard C A P u ⟨t, ht.1⟩) :=
    congrArg (torusCoeffCLM 3 i k) hL
  rw [h, torusForcedPicard_real]
  rw [map_sub, map_add,
    ← (torusCoeffCLM 3 i k).intervalIntegral_comp_comm (hu.force_integrable t ht),
    ← (torusCoeffCLM 3 i k).intervalIntegral_comp_comm (hu.nonlinear_integrable t ht)]
  have hlin : torusCoeffCLM 3 i k (C.analytic.linearEvolution ⟨t, ht.1⟩ A) =
      (torusHeatSymbol ν t k : ℂ) * A.1 i k := C.linear_symbol _ A i k
  have hforce : (∫ s in (0 : ℝ)..t, torusCoeffCLM 3 i k
        (C.analytic.linearEvolution (Real.toNNReal (t - s)) (P s))) =
      ∫ s in (0 : ℝ)..t, (torusHeatSymbol ν (t - s) k : ℂ) * (P s).1 i k := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    have hts : ((Real.toNNReal (t - s) : ℝ≥0) : ℝ) = t - s :=
      Real.coe_toNNReal _ (sub_nonneg.mpr hs.2)
    show torusCoeffCLM 3 i k (C.analytic.linearEvolution (Real.toNNReal (t - s)) (P s)) = _
    rw [torusCoeffCLM_apply, C.linear_symbol _ (P s) i k, hts]
  have hnl : (∫ s in (0 : ℝ)..t, torusCoeffCLM 3 i k (C.analytic.duhamelIntegrand t u s)) =
      (Real.sqrt (periodicFrequencyWeight k) : ℂ) *
        ∫ s in (0 : ℝ)..t,
          (torusHeatSymbol ν (t - s) k : ℂ) * (mildNonlinearDatum C u s).1 i k := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_ae
    have hae : ∀ᵐ s : ℝ, s ≠ t := by
      have : (volume {s : ℝ | ¬ s ≠ t}) = 0 := by
        simp
      exact (MeasureTheory.ae_iff).mpr this
    filter_upwards [hae] with s hs hmem
    rw [uIoc_of_le ht.1] at hmem
    have hlt : s < t := lt_of_le_of_ne hmem.2 hs
    show torusCoeffCLM 3 i k (C.analytic.duhamelIntegrand t u s) = _
    rw [C.analytic.duhamelIntegrand_of_lt t u hlt, torusCoeffCLM_apply,
      C.smoothing_symbol (t - s) (sub_pos.mpr hlt) _ i k]
    change ((Real.sqrt (periodicFrequencyWeight k) * torusHeatSymbol ν (t - s) k : ℝ) : ℂ) *
      (mildNonlinearDatum C u s).1 i k = _
    rw [Complex.ofReal_mul, mul_assoc]
  rw [hlin, hforce, hnl]


/-! ## 3. The forced linear scalar ODE -/

/-- Duhamel's integral against the heat symbol solves the forced scalar linear
ODE at every interior time. -/
theorem heat_duhamel_hasDerivAt {ν T : ℝ} (k : PeriodicFrequency)
    {χ : ℝ → ℂ} (hχ : ContinuousOn χ (Icc (0 : ℝ) T)) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun r : ℝ ↦ ∫ s in (0 : ℝ)..r, (torusHeatSymbol ν (r - s) k : ℂ) * χ s)
      ((-(ν * periodicAngularFrequencySq k) : ℝ) *
          (∫ s in (0 : ℝ)..t, (torusHeatSymbol ν (t - s) k : ℂ) * χ s) + χ t) t := by
  have hkey : ∀ r : ℝ, (∫ s in (0 : ℝ)..r, (torusHeatSymbol ν (r - s) k : ℂ) * χ s) =
      (torusHeatSymbol ν r k : ℂ) *
        ∫ s in (0 : ℝ)..r, (torusHeatSymbol ν (-s) k : ℂ) * χ s := by
    intro r
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ ↦ ?_
    rw [show r - s = r + -s by ring, torusHeatSymbol_add', Complex.ofReal_mul, mul_assoc]
  have hcont : ContinuousOn (fun s : ℝ ↦ (torusHeatSymbol ν (-s) k : ℂ) * χ s)
      (Icc (0 : ℝ) T) :=
    (Complex.continuous_ofReal.comp
      ((torusHeatSymbol_continuous ν k).comp continuous_neg)).continuousOn.mul hχ
  have hnhds : Icc (0 : ℝ) T ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have hI : HasDerivAt (fun r : ℝ ↦ ∫ s in (0 : ℝ)..r, (torusHeatSymbol ν (-s) k : ℂ) * χ s)
      ((torusHeatSymbol ν (-t) k : ℂ) * χ t) t := by
    refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ (hcont.continuousAt hnhds)
    · refine (hcont.mono ?_).intervalIntegrable
      rw [uIcc_of_le ht.1.le]
      exact Icc_subset_Icc le_rfl ht.2.le
    · exact (hcont.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo t ht
  have hσ : HasDerivAt (fun r : ℝ ↦ (torusHeatSymbol ν r k : ℂ))
      (((-(ν * periodicAngularFrequencySq k) * torusHeatSymbol ν t k : ℝ)) : ℂ) t :=
    (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (torusHeatSymbol_hasDerivAt ν t k))
  have hmul := hσ.mul hI
  have hone : (torusHeatSymbol ν t k : ℂ) * (torusHeatSymbol ν (-t) k : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← torusHeatSymbol_add', add_neg_cancel, torusHeatSymbol_zero']
    norm_num
  have hD : ((-(ν * periodicAngularFrequencySq k) : ℝ) : ℂ) *
        ((torusHeatSymbol ν t k : ℂ) *
          ∫ s in (0 : ℝ)..t, (torusHeatSymbol ν (-s) k : ℂ) * χ s) + χ t =
      ((-(ν * periodicAngularFrequencySq k) * torusHeatSymbol ν t k : ℝ) : ℂ) *
          (∫ s in (0 : ℝ)..t, (torusHeatSymbol ν (-s) k : ℂ) * χ s) +
        (torusHeatSymbol ν t k : ℂ) * ((torusHeatSymbol ν (-t) k : ℂ) * χ t) := by
    rw [show (torusHeatSymbol ν t k : ℂ) * ((torusHeatSymbol ν (-t) k : ℂ) * χ t) =
        ((torusHeatSymbol ν t k : ℂ) * (torusHeatSymbol ν (-t) k : ℂ)) * χ t by ring, hone,
      one_mul, Complex.ofReal_mul]
    ring
  simp only [hkey]
  rw [hD]
  exact hmul



/-! ## 4. Time differentiability of the mild coefficient paths -/

/-- **(i), weighted form.**  Every order-three Fourier coefficient of a forced
mild solution is differentiable at every interior time, with
`d/dt û(t)(k) = -ν|2πk|² û(t)(k) + (P F)^(t)(k) - √W(k) (P Q(u,u))^(t)(k)`. -/
theorem mild_coeff_hasDerivAt {ν T : ℝ} {C : TorusTwoSpaceContract ν}
    {A : PeriodicSobolev 3} {P u : ℝ → PeriodicSobolev 3}
    (hu : TorusForcedMildOn C A P T u) (hP : ContinuousOn P (Icc (0 : ℝ) T))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (i : Fin 3) (k : PeriodicFrequency) :
    HasDerivAt (fun r : ℝ ↦ (u r).1 i k)
      ((-(ν * periodicAngularFrequencySq k) : ℝ) * (u t).1 i k +
        ((P t).1 i k -
          (Real.sqrt (periodicFrequencyWeight k) : ℂ) *
            (mildNonlinearDatum C u t).1 i k)) t := by
  have hφc : ContinuousOn (fun s : ℝ ↦ (P s).1 i k) (Icc (0 : ℝ) T) :=
    (torusCoeffCLM 3 i k).continuous.comp_continuousOn hP
  have hψc : ContinuousOn (fun s : ℝ ↦ (mildNonlinearDatum C u s).1 i k) (Icc (0 : ℝ) T) :=
    (torusCoeffCLM 2 i k).continuous.comp_continuousOn
      (mildNonlinearDatum_continuousOn C hu.continuous_path)
  have hσ : HasDerivAt (fun r : ℝ ↦ (torusHeatSymbol ν r k : ℂ))
      ((-(ν * periodicAngularFrequencySq k) * torusHeatSymbol ν t k : ℝ) : ℂ) t :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (torusHeatSymbol_hasDerivAt ν t k)
  have hIP := heat_duhamel_hasDerivAt (ν := ν) (T := T) k hφc ht
  have hIQ := heat_duhamel_hasDerivAt (ν := ν) (T := T) k hψc ht
  have hmodel := ((hσ.mul_const (A.1 i k)).add hIP).sub
    ((hIQ.const_mul (Real.sqrt (periodicFrequencyWeight k) : ℂ)))
  have hdu := mild_coeff_duhamel hu (Ioo_subset_Icc_self ht) i k
  have heq : (fun r : ℝ ↦ (u r).1 i k) =ᶠ[𝓝 t]
      fun r : ℝ ↦ (torusHeatSymbol ν r k : ℂ) * A.1 i k +
        (∫ s in (0 : ℝ)..r, (torusHeatSymbol ν (r - s) k : ℂ) * (P s).1 i k) -
        (Real.sqrt (periodicFrequencyWeight k) : ℂ) *
          ∫ s in (0 : ℝ)..r,
            (torusHeatSymbol ν (r - s) k : ℂ) * (mildNonlinearDatum C u s).1 i k := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr using mild_coeff_duhamel hu hr i k
  refine (HasDerivAt.congr_of_eventuallyEq ?_ heq)
  rw [hdu]
  refine hmodel.congr_deriv ?_
  rw [Complex.ofReal_mul]
  ring

/-- **(i), physical form.**  The same identity for the unweighted (physical)
Fourier coefficients: `d/dt v̂(t)(k) = -ν|2πk|² v̂(t)(k) + (P(F - Q))^(t)(k)`. -/
theorem mild_physicalCoeff_hasDerivAt {ν T : ℝ} {C : TorusTwoSpaceContract ν}
    {A : PeriodicSobolev 3} {P u : ℝ → PeriodicSobolev 3}
    (hu : TorusForcedMildOn C A P T u) (hP : ContinuousOn P (Icc (0 : ℝ) T))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (i : Fin 3) (k : PeriodicFrequency) :
    HasDerivAt (fun r : ℝ ↦ torusPhysicalCoeff 3 (u r) i k)
      ((-(ν * periodicAngularFrequencySq k) : ℝ) * torusPhysicalCoeff 3 (u t) i k +
        (torusPhysicalCoeff 3 (P t) i k -
          torusPhysicalCoeff 2 (mildNonlinearDatum C u t) i k)) t := by
  have hw : 0 < periodicFrequencyWeight k := mildPressure_weight_pos k
  have hbase := (mild_coeff_hasDerivAt hu hP ht i k).const_mul
    ((periodicFrequencyWeight k ^ (-(3 : ℝ) / 2) : ℝ) : ℂ)
  have hsq : ((periodicFrequencyWeight k ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) *
      (Real.sqrt (periodicFrequencyWeight k) : ℂ) =
      ((periodicFrequencyWeight k ^ (-(2 : ℝ) / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hw]
    norm_num
  have hgen : ∀ c d e x y z w : ℂ, c * d = e →
      c * (w * x + (y - d * z)) = w * (c * x) + (c * y - e * z) := by
    intro c d e x y z w h
    rw [← h]; ring
  have hgoal : ((periodicFrequencyWeight k ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) *
      ((-(ν * periodicAngularFrequencySq k) : ℝ) * (u t).1 i k +
        ((P t).1 i k -
          (Real.sqrt (periodicFrequencyWeight k) : ℂ) * (mildNonlinearDatum C u t).1 i k)) =
      (-(ν * periodicAngularFrequencySq k) : ℝ) * torusPhysicalCoeff 3 (u t) i k +
        (torusPhysicalCoeff 3 (P t) i k -
          torusPhysicalCoeff 2 (mildNonlinearDatum C u t) i k) := by
    unfold torusPhysicalCoeff
    exact hgen _ _ _ _ _ _ _ hsq
  rw [← hgoal]
  exact hbase



/-! ## 5. Locally uniform rapid decay of the physical coefficients -/

/-- Persistence at order `2N+4` bounds the `N+2`-weighted physical coefficients
by the Sobolev norm of the order-`2N+4` realization. -/
theorem persistence_weight_pow_le {T : ℝ} {u : ℝ → PeriodicSobolev 3}
    (h : PersistenceInput T u) (N : ℕ) :
    ∃ um : ℝ → PeriodicSobolev ((2 * N + 4 : ℕ) : ℝ), ContinuousOn um (Ico (0 : ℝ) T) ∧
      ∀ t ∈ Ico (0 : ℝ) T, ∀ (i : Fin 3) (k : PeriodicFrequency),
        periodicFrequencyWeight k ^ (N + 2) * ‖torusPhysicalCoeff 3 (u t) i k‖ ≤ ‖um t‖ := by
  obtain ⟨um, hc, he⟩ := h (2 * N + 4)
  refine ⟨um, hc, fun t ht i k ↦ ?_⟩
  have hw : 0 < periodicFrequencyWeight k := mildPressure_weight_pos k
  have h1 : torusPhysicalCoeff ((2 * N + 4 : ℕ) : ℝ) (um t) i k =
      torusPhysicalCoeff 3 (u t) i k := he t ht i k
  have h2 : ‖torusPhysicalCoeff 3 (u t) i k‖ =
      periodicFrequencyWeight k ^ (-((2 * N + 4 : ℕ) : ℝ) / 2) * ‖(um t).1 i k‖ := by
    rw [← h1]
    unfold torusPhysicalCoeff
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hw.le _)]
  rw [h2, ← mul_assoc,
    ← Real.rpow_natCast (periodicFrequencyWeight k) (N + 2), ← Real.rpow_add hw,
    show ((N + 2 : ℕ) : ℝ) + -((2 * N + 4 : ℕ) : ℝ) / 2 = 0 by push_cast; ring,
    Real.rpow_zero, one_mul]
  exact norm_coeff_le_norm (um t) i k

/-- On every compact subinterval of the lifespan the physical coefficients decay
faster than any polynomial, with a constant uniform in time. -/
theorem persistence_uniform_decay {T : ℝ} {u : ℝ → PeriodicSobolev 3}
    (h : PersistenceInput T u) (N : ℕ) {a b : ℝ} (hab : Icc a b ⊆ Ico (0 : ℝ) T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc a b, ∀ (i : Fin 3) (k : PeriodicFrequency),
      periodicFrequencyWeight k ^ N * ‖torusPhysicalCoeff 3 (u t) i k‖ ≤
        M * (periodicFrequencyWeight k ^ 2)⁻¹ := by
  obtain ⟨um, hc, hb⟩ := persistence_weight_pow_le h N
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hc.mono hab)
  refine ⟨max M 0, le_max_right _ _, fun t ht i k ↦ ?_⟩
  have hw : 0 < periodicFrequencyWeight k := mildPressure_weight_pos k
  have h1 := hb t (hab ht) i k
  have h2 : ‖um t‖ ≤ max M 0 := (hM t ht).trans (le_max_left _ _)
  have h3 : periodicFrequencyWeight k ^ N * ‖torusPhysicalCoeff 3 (u t) i k‖ =
      (periodicFrequencyWeight k ^ (N + 2) * ‖torusPhysicalCoeff 3 (u t) i k‖) *
        (periodicFrequencyWeight k ^ 2)⁻¹ := by
    rw [pow_add]
    field_simp
  rw [h3]
  exact mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity)



/-! ## 6. The frequency-local Leray symbol on raw coefficient vectors -/

/-- `Section3/T10/PeriodicData.lean`'s `periodicLeray`, read as an operation on a
bare vector of three complex coefficients at one frequency. -/
def lerayAt (k : PeriodicFrequency) (w : Fin 3 → ℂ) (i : Fin 3) : ℂ :=
  if k = 0 then w i
  else w i - ((k i : ℂ) / ((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ) : ℂ)) * ∑ j : Fin 3, (k j : ℂ) * w j

theorem periodicLeray_eq_lerayAt {s : ℝ} (A : PeriodicSobolev s) (i : Fin 3)
    (k : PeriodicFrequency) : periodicLeray s A i k = lerayAt k (fun j ↦ A.1 j k) i := rfl

theorem lerayAt_const_mul (k : PeriodicFrequency) (c : ℂ) (w : Fin 3 → ℂ) (i : Fin 3) :
    lerayAt k (fun j ↦ c * w j) i = c * lerayAt k w i := by
  unfold lerayAt
  split_ifs with hk
  · rfl
  · have h : (∑ j : Fin 3, (k j : ℂ) * (c * w j)) = c * ∑ j : Fin 3, (k j : ℂ) * w j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [h]
    ring

theorem lerayAt_sub (k : PeriodicFrequency) (w v : Fin 3 → ℂ) (i : Fin 3) :
    lerayAt k (fun j ↦ w j - v j) i = lerayAt k w i - lerayAt k v i := by
  unfold lerayAt
  split_ifs with hk
  · rfl
  · have h : (∑ j : Fin 3, (k j : ℂ) * (w j - v j)) =
        (∑ j : Fin 3, (k j : ℂ) * w j) - ∑ j : Fin 3, (k j : ℂ) * v j := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [h]
    ring

/-- The projected physical coefficient of a Leray datum is the Leray symbol of the
physical coefficients. -/
theorem torusPhysicalCoeff_leray {s : ℝ} {A B : PeriodicSobolev s}
    (h : IsPeriodicLerayDatum A B) (i : Fin 3) (k : PeriodicFrequency) :
    torusPhysicalCoeff s B i k = lerayAt k (fun j ↦ torusPhysicalCoeff s A j k) i := by
  have he : (fun j ↦ torusPhysicalCoeff s A j k) =
      fun j ↦ ((periodicFrequencyWeight k ^ (-s / 2) : ℝ) : ℂ) * A.1 j k := rfl
  rw [he, lerayAt_const_mul, torusPhysicalCoeff, h i k, periodicLeray_eq_lerayAt]

/-- A crude but uniform bound on the Leray symbol at a single frequency. -/
theorem norm_lerayAt_le (k : PeriodicFrequency) (w : Fin 3 → ℂ) (i : Fin 3) :
    ‖lerayAt k w i‖ ≤ 2 * ∑ j : Fin 3, ‖w j‖ := by
  have hsum : ‖w i‖ ≤ ∑ j : Fin 3, ‖w j‖ :=
    Finset.single_le_sum (f := fun j : Fin 3 ↦ ‖w j‖) (fun j _ ↦ norm_nonneg _)
      (Finset.mem_univ i)
  have hnn : (0 : ℝ) ≤ ∑ j : Fin 3, ‖w j‖ := Finset.sum_nonneg fun j _ ↦ norm_nonneg _
  unfold lerayAt
  split_ifs with hk
  · linarith
  · have hD1 : 1 ≤ ∑ j : Fin 3, (k j : ℝ) ^ 2 := mildPressure_one_le_sq_sum hk
    have hDpos : 0 < ∑ j : Fin 3, (k j : ℝ) ^ 2 := lt_of_lt_of_le one_pos hD1
    have hprod : ∀ j : Fin 3, |(k i : ℝ)| * |(k j : ℝ)| ≤ ∑ l : Fin 3, (k l : ℝ) ^ 2 := by
      intro j
      have hi : (k i : ℝ) ^ 2 ≤ ∑ l : Fin 3, (k l : ℝ) ^ 2 :=
        Finset.single_le_sum (f := fun l : Fin 3 ↦ (k l : ℝ) ^ 2)
          (fun l _ ↦ sq_nonneg _) (Finset.mem_univ i)
      have hj : (k j : ℝ) ^ 2 ≤ ∑ l : Fin 3, (k l : ℝ) ^ 2 :=
        Finset.single_le_sum (f := fun l : Fin 3 ↦ (k l : ℝ) ^ 2)
          (fun l _ ↦ sq_nonneg _) (Finset.mem_univ j)
      nlinarith [sq_abs ((k i : ℝ)), sq_abs ((k j : ℝ)),
        sq_nonneg (|(k i : ℝ)| - |(k j : ℝ)|), abs_nonneg ((k i : ℝ)), abs_nonneg ((k j : ℝ))]
    have hquot : ‖((k i : ℂ) / ((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ) : ℂ)) *
        ∑ j : Fin 3, (k j : ℂ) * w j‖ ≤ ∑ j : Fin 3, ‖w j‖ := by
      rw [norm_mul, norm_div,
        show ‖((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ) : ℂ)‖ = ∑ j : Fin 3, (k j : ℝ) ^ 2 by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hDpos],
        show ‖(k i : ℂ)‖ = |(k i : ℝ)| by simp [Complex.norm_intCast],
        div_mul_eq_mul_div, div_le_iff₀ hDpos]
      calc |(k i : ℝ)| * ‖∑ j : Fin 3, (k j : ℂ) * w j‖
          ≤ |(k i : ℝ)| * ∑ j : Fin 3, |(k j : ℝ)| * ‖w j‖ := by
            refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
            rw [norm_mul, show ‖(k j : ℂ)‖ = |(k j : ℝ)| by simp [Complex.norm_intCast]]
        _ = ∑ j : Fin 3, (|(k i : ℝ)| * |(k j : ℝ)|) * ‖w j‖ := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ ↦ by ring
        _ ≤ ∑ j : Fin 3, (∑ l : Fin 3, (k l : ℝ) ^ 2) * ‖w j‖ :=
            Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_right (hprod j) (norm_nonneg _)
        _ = (∑ j : Fin 3, ‖w j‖) * ∑ l : Fin 3, (k l : ℝ) ^ 2 := by
            rw [← Finset.mul_sum]
            ring
    calc ‖w i - ((k i : ℂ) / ((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ) : ℂ)) *
            ∑ j : Fin 3, (k j : ℂ) * w j‖
        ≤ ‖w i‖ + ‖((k i : ℂ) / ((∑ j : Fin 3, (k j : ℝ) ^ 2 : ℝ) : ℂ)) *
            ∑ j : Fin 3, (k j : ℂ) * w j‖ := norm_sub_le _ _
      _ ≤ (∑ j : Fin 3, ‖w j‖) + ∑ j : Fin 3, ‖w j‖ := add_le_add hsum hquot
      _ = 2 * ∑ j : Fin 3, ‖w j‖ := by ring


/-! ## 7. The periodic convolution theorem -/

/-- A continuous periodic function with summable Fourier data is its own
Fourier series. -/
theorem eq_torusScalarSeries_of_summable {g : Space → ℂ} (hgc : Continuous g)
    (hpg : IsPeriodicSpatial g) (hgs : Summable (periodicFourierCoeff g)) :
    g = torusScalarSeries (periodicFourierCoeff g) := by
  funext x
  rw [periodic_eq_tsum_mFourier hpg hgc hgs x]
  unfold torusScalarSeries NSFormalization.Paper1.periodicCharacter
  exact tsum_congr fun l ↦ by rw [NSFormalization.Paper1.periodicPhase_apply]

/-- **The periodic convolution theorem.**  The Fourier coefficients of a product
of two continuous periodic functions, one of them with absolutely summable data,
are the discrete convolution of the two coefficient families. -/
theorem periodicFourierCoeff_mul {f g : Space → ℂ}
    (hf : Continuous f) (hpf : IsPeriodicSpatial f)
    (hgc : Continuous g) (hpg : IsPeriodicSpatial g)
    (hgs : Summable (fun l ↦ ‖periodicFourierCoeff g l‖))
    (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ f x * g x) k =
      ∑' l : PeriodicFrequency,
        periodicFourierCoeff g l * periodicFourierCoeff f (k - l) := by
  classical
  have hlf : Continuous (torusLift f) :=
    NSFormalization.Paper1.continuous_torusLift hf (fun x j ↦ hpf x j)
  let F : PeriodicFrequency → PeriodicTorus → ℂ := fun l q ↦
    periodicFourierCoeff g l * (UnitAddTorus.mFourier (l - k) q * torusLift f q)
  have hFi : ∀ l, Integrable (F l) periodicTorusMeasure := by
    intro l
    have hc : Continuous (F l) :=
      continuous_const.mul ((UnitAddTorus.mFourier (l - k)).continuous.mul hlf)
    simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact
      (μ := periodicTorusMeasure) isCompact_univ
  have hFn : ∀ (l : PeriodicFrequency) (q : PeriodicTorus),
      ‖F l q‖ = ‖periodicFourierCoeff g l‖ * ‖torusLift f q‖ := by
    intro l q
    simp only [F, norm_mul, torusMFourier_norm, one_mul]
  have hFs : Summable (fun l ↦ ∫ q, ‖F l q‖ ∂periodicTorusMeasure) := by
    simp only [hFn, integral_const_mul]
    exact hgs.mul_right _
  have hgfun : g = torusScalarSeries (periodicFourierCoeff g) :=
    eq_torusScalarSeries_of_summable hgc hpg hgs.of_norm
  have hpoint : ∀ q : PeriodicTorus,
      UnitAddTorus.mFourier (-k) q • torusLift (fun x ↦ f x * g x) q = ∑' l, F l q := by
    intro q
    have h1 : torusLift (fun x ↦ f x * g x) q = torusLift f q * torusLift g q := rfl
    rw [smul_eq_mul, h1, hgfun, torusScalarSeries_lift, ← tsum_mul_left, ← tsum_mul_left]
    refine tsum_congr fun l ↦ ?_
    simp only [F, sub_eq_add_neg, UnitAddTorus.mFourier_add]
    ring
  change (∫ q, UnitAddTorus.mFourier (-k) q •
    torusLift (fun x ↦ f x * g x) q ∂periodicTorusMeasure) = _
  simp_rw [hpoint]
  rw [← integral_tsum_of_summable_integral_norm hFi hFs]
  refine tsum_congr fun l ↦ ?_
  rw [show (∫ q, F l q ∂periodicTorusMeasure) = periodicFourierCoeff g l *
      ∫ q, UnitAddTorus.mFourier (l - k) q * torusLift f q ∂periodicTorusMeasure from
    integral_const_mul _ _]
  congr 1
  change _ = ∫ q, UnitAddTorus.mFourier (-(k - l)) q • torusLift f q ∂periodicTorusMeasure
  simp only [neg_sub, smul_eq_mul]



/-! ## 8. The convection coefficient is the physical tensor divergence -/

theorem periodicFourierCoeff_finsetSum {ι : Type*} (s : Finset ι) (f : ι → Space → ℂ)
    (hf : ∀ j ∈ s, Continuous (f j)) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ ∑ j ∈ s, f j x) k =
      ∑ j ∈ s, periodicFourierCoeff (f j) k := by
  simp only [periodicFourierCoeff, NSFormalization.Paper1.periodicFourierCoeff_eq_cube,
    Finset.mul_sum, NavierStokes.PeriodicIntegration.cubeIntegral]
  apply integral_finsetSum
  intro j hj
  exact NavierStokes.PeriodicIntegration.integrable_cube
    ((NSFormalization.Paper1.periodicCharacter_smooth (-k)).continuous.mul (hf j hj))

/-- One component of the tensor divergence is the coordinate expression
`∑_j ∂_j (v_j v_i)`. -/
theorem convectionDivergenceT_component {v : SpaceTimeField} {t : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : Space ↦ v (t, x))) (i : Fin 3) (x : Space) :
    convectionDivergenceT v t x i =
      ∑ j : Fin 3, spatialPartial j (fun y : Space ↦ v (t, y) j * v (t, y) i) x := by
  have hproj : convectionDivergenceT v t x i =
      ∑ j : Fin 3,
        (fderiv ℝ (fun y : Space ↦ (v (t, y) j) • v (t, y)) x (coordinateVector j)) i :=
    map_sum (EuclideanSpace.proj (𝕜 := ℝ) i)
      (fun j : Fin 3 ↦ fderiv ℝ (fun y : Space ↦ (v (t, y) j) • v (t, y)) x
        (coordinateVector j)) Finset.univ
  rw [hproj]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hdj : ContDiff ℝ ∞ (fun y : Space ↦ (v (t, y) j) • v (t, y)) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hv).smul hv
  have h : HasFDerivAt (fun y : Space ↦ v (t, y) j * v (t, y) i)
      ((EuclideanSpace.proj (𝕜 := ℝ) i).comp
        (fderiv ℝ (fun y : Space ↦ (v (t, y) j) • v (t, y)) x)) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x
      ((hdj.differentiable (by simp) x).hasFDerivAt)
  show (fderiv ℝ (fun y : Space ↦ (v (t, y) j) • v (t, y)) x (coordinateVector j)) i =
    fderiv ℝ (fun y : Space ↦ v (t, y) j * v (t, y) i) x (coordinateVector j)
  rw [h.fderiv]
  rfl

/-- The Fourier coefficients of the tensor divergence of a smooth periodic
velocity slice are the derivative symbol times the convolution of the component
coefficients. -/
theorem periodicFourierCoeff_convectionDivergenceT {v : SpaceTimeField} {t : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : Space ↦ v (t, x)))
    (hp : IsPeriodicSpatial (fun x : Space ↦ v (t, x)))
    (hs : ∀ j : Fin 3,
      Summable (fun l ↦ ‖periodicFourierCoeff (fun y : Space ↦ ((v (t, y) j : ℝ) : ℂ)) l‖))
    (i : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ ((convectionDivergenceT v t x i : ℝ) : ℂ)) k =
      ∑ j : Fin 3, periodicDerivativeSymbol j k *
        ∑' l : PeriodicFrequency,
          periodicFourierCoeff (fun y : Space ↦ ((v (t, y) j : ℝ) : ℂ)) l *
            periodicFourierCoeff (fun y : Space ↦ ((v (t, y) i : ℝ) : ℂ)) (k - l) := by
  have hcomp : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y : Space ↦ ((v (t, y) j : ℝ) : ℂ)) := fun j ↦
    Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hv)
  have hcompp : ∀ j : Fin 3, IsPeriodicSpatial (fun y : Space ↦ ((v (t, y) j : ℝ) : ℂ)) :=
    fun j x l ↦ congrArg (fun w : Space ↦ ((w j : ℝ) : ℂ)) (hp x l)
  have hprod : ∀ j : Fin 3, ContDiff ℝ ∞ (fun y : Space ↦ v (t, y) j * v (t, y) i) :=
    fun j ↦ ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp hv).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hv)
  have hcplx : ∀ j : Fin 3,
      (fun x : Space ↦ ((spatialPartial j (fun y : Space ↦ v (t, y) j * v (t, y) i) x : ℝ) : ℂ)) =
        spatialPartial j (fun y : Space ↦ ((v (t, y) j : ℝ) : ℂ) * ((v (t, y) i : ℝ) : ℂ)) := by
    intro j
    have he : (fun y : Space ↦ ((v (t, y) j * v (t, y) i : ℝ) : ℂ)) =
        fun y : Space ↦ ((v (t, y) j : ℝ) : ℂ) * ((v (t, y) i : ℝ) : ℂ) := by
      funext y; rw [Complex.ofReal_mul]
    rw [← he, spatialPartial_complexify ((hprod j).of_le (by simp)) j]
  have hstep : (fun x : Space ↦ ((convectionDivergenceT v t x i : ℝ) : ℂ)) =
      fun x : Space ↦ ∑ j : Fin 3,
        spatialPartial j (fun y : Space ↦ ((v (t, y) j : ℝ) : ℂ) * ((v (t, y) i : ℝ) : ℂ)) x := by
    funext x
    rw [convectionDivergenceT_component hv i x, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun j _ ↦ congrFun (hcplx j) x
  rw [hstep]
  rw [periodicFourierCoeff_finsetSum Finset.univ _ (fun j _ ↦ ?_) k]
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hd : ContDiff ℝ 1 (fun y : Space ↦
        ((v (t, y) j : ℝ) : ℂ) * ((v (t, y) i : ℝ) : ℂ)) :=
      ((hcomp j).mul (hcomp i)).of_le (by simp)
    have hpp : IsPeriodicSpatial (fun y : Space ↦
        ((v (t, y) j : ℝ) : ℂ) * ((v (t, y) i : ℝ) : ℂ)) :=
      fun x l ↦ congrArg (fun w : Space ↦ ((w j : ℝ) : ℂ) * ((w i : ℝ) : ℂ)) (hp x l)
    show periodicFourierCoeff (fun x : Space ↦
      fderiv ℝ (fun y : Space ↦ ((v (t, y) j : ℝ) : ℂ) * ((v (t, y) i : ℝ) : ℂ)) x
        (coordinateVector j)) k = _
    rw [periodicFourierCoeff_fderiv hpp hd j k]
    congr 1
    rw [show (fun y : Space ↦ ((v (t, y) j : ℝ) : ℂ) * ((v (t, y) i : ℝ) : ℂ)) =
        fun y : Space ↦ ((v (t, y) i : ℝ) : ℂ) * ((v (t, y) j : ℝ) : ℂ) by
      funext y; ring]
    exact periodicFourierCoeff_mul (hcomp i).continuous (hcompp i)
      (hcomp j).continuous (hcompp j) (hs j) k
  · have hd : ContDiff ℝ ∞ (fun y : Space ↦
        ((v (t, y) j : ℝ) : ℂ) * ((v (t, y) i : ℝ) : ℂ)) := (hcomp j).mul (hcomp i)
    have hds : ContDiff ℝ ∞ (spatialPartial j (fun y : Space ↦
        ((v (t, y) j : ℝ) : ℂ) * ((v (t, y) i : ℝ) : ℂ))) :=
      (hd.fderiv_right (by simp)).clm_apply contDiff_const
    exact hds.continuous



/-- The physical Fourier coefficient of the unprojected tensor divergence
`∇·(A ⊗ B)`, as a discrete convolution of physical coefficients. -/
def torusConvectionCoeff (A B : PeriodicSobolev 3) (i : Fin 3) (k : PeriodicFrequency) : ℂ :=
  ∑ j : Fin 3, periodicDerivativeSymbol j k *
    ∑' l : PeriodicFrequency, torusPhysicalCoeff 3 A j l * torusPhysicalCoeff 3 B i (k - l)

theorem torusPhysicalCoeff_convectionDatum (A B : PeriodicSobolev 3) (i : Fin 3)
    (k : PeriodicFrequency) :
    torusPhysicalCoeff 2 (torusConvectionDatum A B) i k = torusConvectionCoeff A B i k := by
  have hw : 0 < periodicFrequencyWeight k := mildPressure_weight_pos k
  have hW : ((periodicFrequencyWeight k ^ (-(2 : ℝ) / 2) : ℝ) : ℂ) *
      ((periodicFrequencyWeight k : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul,
      show (-(2 : ℝ) / 2) = (-1 : ℝ) by norm_num, Real.rpow_neg_one,
      inv_mul_cancel₀ hw.ne', Complex.ofReal_one]
  rw [torusPhysicalCoeff, torusConvectionDatum_coeff, torusConvectionSymbol,
    torusConvectionCoeff, ← mul_assoc, hW, one_mul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  congr 1
  refine tsum_congr fun l ↦ ?_
  unfold torusPhysicalCoeff
  ring

theorem torusProjectedConvectionSymbol_eq_lerayAt (A B : PeriodicSobolev 3) (i : Fin 3)
    (k : PeriodicFrequency) :
    torusProjectedConvectionSymbol A B i k =
      lerayAt k (fun j ↦ torusConvectionSymbol A B j k) i := rfl

/-- The contract's bilinear map has exactly the Leray projection of the physical
convection coefficients. -/
theorem torusPhysicalCoeff_bilinear {ν : ℝ} (C : TorusTwoSpaceContract ν)
    (A B : PeriodicSobolev 3) (i : Fin 3) (k : PeriodicFrequency) :
    torusPhysicalCoeff 2 (C.analytic.bilinear A B) i k =
      lerayAt k (fun j ↦ torusConvectionCoeff A B j k) i := by
  rw [torusPhysicalCoeff, C.bilinear_symbol, torusProjectedConvectionSymbol_eq_lerayAt,
    ← lerayAt_const_mul]
  congr 1
  funext j
  rw [← torusPhysicalCoeff_convectionDatum, torusPhysicalCoeff, torusConvectionDatum_coeff]

/-- Physical Fourier data of the recovered velocity is the physical coefficient
of the coefficient path. -/
theorem physicalVelocity_coeff (u : ℝ → PeriodicSobolev 3) (t : ℝ) (j : Fin 3)
    (l : PeriodicFrequency) :
    periodicFourierCoeff (fun y : Space ↦ ((torusPhysicalVelocity u (t, y) j : ℝ) : ℂ)) l =
      torusPhysicalCoeff 3 (u t) j l :=
  (torusPhysicalCoeff_eq (torusPhysicalField_datum (u t)) j l).symm

/-- **The convection identity.**  The tensor divergence of the recovered
physical velocity has exactly the contract's convection coefficients. -/
theorem convectionDivergenceT_coeff {T : ℝ} {u : ℝ → PeriodicSobolev 3}
    (h : PersistenceInput T u) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T)
    (i : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff
      (fun x ↦ ((convectionDivergenceT (torusPhysicalVelocity u) t x i : ℝ) : ℂ)) k =
      torusConvectionCoeff (u t) (u t) i k := by
  have hv : ContDiff ℝ ∞ (fun x : Space ↦ torusPhysicalVelocity u (t, x)) :=
    persistence_physical_spatial_smooth h ht
  have hp : IsPeriodicSpatial (fun x : Space ↦ torusPhysicalVelocity u (t, x)) :=
    fun x l ↦ torusPhysicalVelocity_periodic u t (mem_univ t) x l
  have hs : ∀ j : Fin 3, Summable (fun l ↦
      ‖periodicFourierCoeff
        (fun y : Space ↦ ((torusPhysicalVelocity u (t, y) j : ℝ) : ℂ)) l‖) := by
    intro j
    simpa only [physicalVelocity_coeff] using torusPhysicalCoeff_summable (u t) j
  rw [periodicFourierCoeff_convectionDivergenceT hv hp hs i k, torusConvectionCoeff]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  congr 1
  exact tsum_congr fun l ↦ by rw [physicalVelocity_coeff, physicalVelocity_coeff]



/-! ## 9. Weight submultiplicativity and the convolution estimate -/

theorem one_le_periodicFrequencyWeight' (k : PeriodicFrequency) :
    1 ≤ periodicFrequencyWeight k := by
  have hS : (0 : ℝ) ≤ ∑ i : Fin 3, (k i : ℝ) ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  unfold periodicFrequencyWeight
  nlinarith [Real.pi_pos, sq_nonneg Real.pi]

theorem periodicFrequencyWeight_shift_le (k l : PeriodicFrequency) :
    periodicFrequencyWeight k ≤
      2 * (periodicFrequencyWeight l * periodicFrequencyWeight (k - l)) := by
  have hsq : (∑ i : Fin 3, (k i : ℝ) ^ 2) ≤
      2 * (∑ i : Fin 3, (l i : ℝ) ^ 2) + 2 * ∑ i : Fin 3, ((k - l) i : ℝ) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    have h : (k i : ℝ) = (l i : ℝ) + ((k - l) i : ℝ) := by
      have hsub : (k - l) i = k i - l i := rfl
      rw [hsub]
      push_cast
      ring
    rw [h]
    nlinarith [sq_nonneg ((l i : ℝ) - ((k - l) i : ℝ))]
  have hl : (0 : ℝ) ≤ ∑ i : Fin 3, (l i : ℝ) ^ 2 := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hkl : (0 : ℝ) ≤ ∑ i : Fin 3, ((k - l) i : ℝ) ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  unfold periodicFrequencyWeight
  nlinarith [Real.pi_pos, sq_nonneg Real.pi, mul_nonneg hl hkl,
    mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 4 * Real.pi ^ 2) hl)
      (mul_nonneg (by positivity : (0:ℝ) ≤ 4 * Real.pi ^ 2) hkl)]

theorem periodicFrequencyWeight_pow_shift_le (k l : PeriodicFrequency) (n : ℕ) :
    periodicFrequencyWeight k ^ n ≤
      2 ^ n * (periodicFrequencyWeight l ^ n * periodicFrequencyWeight (k - l) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (0 : ℝ) ≤ periodicFrequencyWeight k ^ n :=
      pow_nonneg (mildPressure_weight_pos k).le n
    have h2 := periodicFrequencyWeight_shift_le k l
    have h3 : (0 : ℝ) ≤ 2 ^ n * (periodicFrequencyWeight l ^ n *
        periodicFrequencyWeight (k - l) ^ n) :=
      mul_nonneg (by positivity)
        (mul_nonneg (pow_nonneg (mildPressure_weight_pos l).le n)
          (pow_nonneg (mildPressure_weight_pos (k - l)).le n))
    calc periodicFrequencyWeight k ^ (n + 1)
        = periodicFrequencyWeight k ^ n * periodicFrequencyWeight k := by rw [pow_succ]
      _ ≤ (2 ^ n * (periodicFrequencyWeight l ^ n * periodicFrequencyWeight (k - l) ^ n)) *
            (2 * (periodicFrequencyWeight l * periodicFrequencyWeight (k - l))) :=
          mul_le_mul ih h2 (mildPressure_weight_pos k).le h3
      _ = 2 ^ (n + 1) * (periodicFrequencyWeight l ^ (n + 1) *
            periodicFrequencyWeight (k - l) ^ (n + 1)) := by
          rw [pow_succ, pow_succ, pow_succ]
          ring

theorem inv_pow_weight_shift_le (k l : PeriodicFrequency) (n : ℕ) :
    (periodicFrequencyWeight l ^ n)⁻¹ * (periodicFrequencyWeight (k - l) ^ n)⁻¹ ≤
      2 ^ n * (periodicFrequencyWeight k ^ n)⁻¹ := by
  have hl : (0 : ℝ) < periodicFrequencyWeight l ^ n := by
    exact pow_pos (mildPressure_weight_pos l) n
  have hkl : (0 : ℝ) < periodicFrequencyWeight (k - l) ^ n :=
    pow_pos (mildPressure_weight_pos (k - l)) n
  have hk : (0 : ℝ) < periodicFrequencyWeight k ^ n := pow_pos (mildPressure_weight_pos k) n
  have hprod : (0 : ℝ) < periodicFrequencyWeight l ^ n * periodicFrequencyWeight (k - l) ^ n :=
    mul_pos hl hkl
  have key := periodicFrequencyWeight_pow_shift_le k l n
  rw [← mul_inv, ← sub_nonneg,
    show (2 : ℝ) ^ n * (periodicFrequencyWeight k ^ n)⁻¹ -
        (periodicFrequencyWeight l ^ n * periodicFrequencyWeight (k - l) ^ n)⁻¹ =
      ((2 : ℝ) ^ n * (periodicFrequencyWeight l ^ n * periodicFrequencyWeight (k - l) ^ n) -
        periodicFrequencyWeight k ^ n) /
        (periodicFrequencyWeight k ^ n *
          (periodicFrequencyWeight l ^ n * periodicFrequencyWeight (k - l) ^ n)) by
      field_simp]
  exact div_nonneg (by linarith) (mul_nonneg hk.le hprod.le)

theorem norm_periodicDerivativeSymbol_le (j : Fin 3) (k : PeriodicFrequency) :
    ‖periodicDerivativeSymbol j k‖ ≤ periodicFrequencyWeight k := by
  have hnorm : ‖periodicDerivativeSymbol j k‖ = 2 * Real.pi * |(k j : ℝ)| := by
    unfold periodicDerivativeSymbol
    rw [norm_mul, norm_mul, norm_mul]
    simp [Complex.norm_I, Complex.norm_intCast, abs_of_pos Real.pi_pos]
  have hsq : (2 * Real.pi * |(k j : ℝ)|) ^ 2 ≤ periodicFrequencyWeight k - 1 := by
    have hj : (k j : ℝ) ^ 2 ≤ ∑ i : Fin 3, (k i : ℝ) ^ 2 :=
      Finset.single_le_sum (f := fun i : Fin 3 ↦ (k i : ℝ) ^ 2)
        (fun i _ ↦ sq_nonneg _) (Finset.mem_univ j)
    unfold periodicFrequencyWeight
    nlinarith [sq_abs ((k j : ℝ)), sq_nonneg Real.pi, Real.pi_pos]
  have hW : 1 ≤ periodicFrequencyWeight k := one_le_periodicFrequencyWeight' k
  have hy : (0 : ℝ) ≤ 2 * Real.pi * |(k j : ℝ)| := by positivity
  rw [hnorm]
  nlinarith [hsq, hW, hy]

/-- The discrete convolution of two rapidly decaying coefficient families is
absolutely convergent, with a bound one power better than the inputs. -/
theorem convolution_norm_bound {c d : PeriodicFrequency → ℂ} {M : ℝ} (hM : 0 ≤ M) (n : ℕ)
    (hc : ∀ l, ‖c l‖ ≤ M * (periodicFrequencyWeight l ^ (n + 2))⁻¹)
    (hd : ∀ l, ‖d l‖ ≤ M * (periodicFrequencyWeight l ^ (n + 2))⁻¹)
    (k : PeriodicFrequency) :
    Summable (fun l ↦ ‖c l * d (k - l)‖) ∧
      ∑' l : PeriodicFrequency, ‖c l * d (k - l)‖ ≤
        (2 ^ n * M ^ 2 * ∑' l : PeriodicFrequency, (periodicFrequencyWeight l ^ 2)⁻¹) *
          (periodicFrequencyWeight k ^ n)⁻¹ := by
  have hKs : Summable (fun l : PeriodicFrequency ↦ (periodicFrequencyWeight l ^ 2)⁻¹) :=
    summable_inverse_periodicFrequencyWeight
  set B : ℝ := 2 ^ n * M ^ 2 * (periodicFrequencyWeight k ^ n)⁻¹ with hB
  have hkpow : (0 : ℝ) < periodicFrequencyWeight k ^ n := pow_pos (mildPressure_weight_pos k) n
  have hBnn : 0 ≤ B := by
    rw [hB]
    exact mul_nonneg (mul_nonneg (by positivity) (sq_nonneg M)) (inv_nonneg.mpr hkpow.le)
  have hpoint : ∀ l : PeriodicFrequency,
      ‖c l * d (k - l)‖ ≤ B * (periodicFrequencyWeight l ^ 2)⁻¹ := by
    intro l
    have hwl : (0 : ℝ) < periodicFrequencyWeight l := mildPressure_weight_pos l
    have hwkl : (0 : ℝ) < periodicFrequencyWeight (k - l) := mildPressure_weight_pos (k - l)
    have hstep1 : ‖c l * d (k - l)‖ ≤
        (M * (periodicFrequencyWeight l ^ (n + 2))⁻¹) *
          (M * (periodicFrequencyWeight (k - l) ^ (n + 2))⁻¹) := by
      rw [norm_mul]
      exact mul_le_mul (hc l) (hd (k - l)) (norm_nonneg _) (by positivity)
    have hsplit : (M * (periodicFrequencyWeight l ^ (n + 2))⁻¹) *
        (M * (periodicFrequencyWeight (k - l) ^ (n + 2))⁻¹) =
        M ^ 2 * (((periodicFrequencyWeight l ^ n)⁻¹ *
            (periodicFrequencyWeight (k - l) ^ n)⁻¹) *
          ((periodicFrequencyWeight l ^ 2)⁻¹ * (periodicFrequencyWeight (k - l) ^ 2)⁻¹)) := by
      rw [pow_add, pow_add, mul_inv, mul_inv]
      ring
    have hkl1 : (periodicFrequencyWeight (k - l) ^ 2)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      nlinarith [one_le_periodicFrequencyWeight' (k - l)]
    calc ‖c l * d (k - l)‖
        ≤ M ^ 2 * (((periodicFrequencyWeight l ^ n)⁻¹ *
            (periodicFrequencyWeight (k - l) ^ n)⁻¹) *
          ((periodicFrequencyWeight l ^ 2)⁻¹ *
            (periodicFrequencyWeight (k - l) ^ 2)⁻¹)) := hsplit ▸ hstep1
      _ ≤ M ^ 2 * ((2 ^ n * (periodicFrequencyWeight k ^ n)⁻¹) *
            ((periodicFrequencyWeight l ^ 2)⁻¹ * 1)) := by
          have hp1 : (0 : ℝ) ≤ (periodicFrequencyWeight l ^ 2)⁻¹ :=
            inv_nonneg.mpr (pow_nonneg hwl.le 2)
          have hp2 : (0 : ℝ) ≤ (periodicFrequencyWeight l ^ 2)⁻¹ *
              (periodicFrequencyWeight (k - l) ^ 2)⁻¹ :=
            mul_nonneg hp1 (inv_nonneg.mpr (pow_nonneg hwkl.le 2))
          have hp3 : (0 : ℝ) ≤ 2 ^ n * (periodicFrequencyWeight k ^ n)⁻¹ :=
            mul_nonneg (by positivity)
              (inv_nonneg.mpr (pow_nonneg (mildPressure_weight_pos k).le n))
          exact mul_le_mul_of_nonneg_left (mul_le_mul (inv_pow_weight_shift_le k l n)
            (mul_le_mul_of_nonneg_left hkl1 hp1) hp2 hp3) (sq_nonneg M)
      _ = B * (periodicFrequencyWeight l ^ 2)⁻¹ := by rw [hB]; ring
  have hsum : Summable (fun l ↦ ‖c l * d (k - l)‖) :=
    Summable.of_nonneg_of_le (fun l ↦ norm_nonneg _) hpoint (hKs.mul_left B)
  refine ⟨hsum, ?_⟩
  calc ∑' l : PeriodicFrequency, ‖c l * d (k - l)‖
      ≤ ∑' l : PeriodicFrequency, B * (periodicFrequencyWeight l ^ 2)⁻¹ :=
        hsum.tsum_le_tsum hpoint (hKs.mul_left B)
    _ = B * ∑' l : PeriodicFrequency, (periodicFrequencyWeight l ^ 2)⁻¹ := hKs.tsum_mul_left B
    _ = _ := by rw [hB]; ring



/-! ## 10. Rapid decay of the projected convection coefficients -/

/-- The convolution constant used throughout: the total inverse square weight. -/
def torusWeightMass : ℝ := ∑' l : PeriodicFrequency, (periodicFrequencyWeight l ^ 2)⁻¹

theorem torusWeightMass_nonneg : 0 ≤ torusWeightMass :=
  tsum_nonneg fun l ↦ inv_nonneg.mpr (pow_nonneg (mildPressure_weight_pos l).le 2)

theorem norm_torusConvectionCoeff_le {A B : PeriodicSobolev 3} {M : ℝ} (hM : 0 ≤ M) (n : ℕ)
    (hA : ∀ (j : Fin 3) (l : PeriodicFrequency),
      ‖torusPhysicalCoeff 3 A j l‖ ≤ M * (periodicFrequencyWeight l ^ (n + 3))⁻¹)
    (hB : ∀ (j : Fin 3) (l : PeriodicFrequency),
      ‖torusPhysicalCoeff 3 B j l‖ ≤ M * (periodicFrequencyWeight l ^ (n + 3))⁻¹)
    (i : Fin 3) (k : PeriodicFrequency) :
    ‖torusConvectionCoeff A B i k‖ ≤
      (3 * (2 ^ (n + 1) * M ^ 2 * torusWeightMass)) * (periodicFrequencyWeight k ^ n)⁻¹ := by
  have hwk : (0 : ℝ) < periodicFrequencyWeight k := mildPressure_weight_pos k
  have hcst : (0 : ℝ) ≤ 2 ^ (n + 1) * M ^ 2 * torusWeightMass :=
    mul_nonneg (mul_nonneg (by positivity) (sq_nonneg M)) torusWeightMass_nonneg
  have hterm : ∀ j : Fin 3,
      ‖periodicDerivativeSymbol j k *
        ∑' l : PeriodicFrequency, torusPhysicalCoeff 3 A j l *
          torusPhysicalCoeff 3 B i (k - l)‖ ≤
        (2 ^ (n + 1) * M ^ 2 * torusWeightMass) * (periodicFrequencyWeight k ^ n)⁻¹ := by
    intro j
    obtain ⟨hs, hle⟩ := convolution_norm_bound (c := fun l ↦ torusPhysicalCoeff 3 A j l)
      (d := fun l ↦ torusPhysicalCoeff 3 B i l) hM (n + 1)
      (fun l ↦ hA j l) (fun l ↦ hB i l) k
    have hnt : ‖∑' l : PeriodicFrequency, torusPhysicalCoeff 3 A j l *
        torusPhysicalCoeff 3 B i (k - l)‖ ≤
        (2 ^ (n + 1) * M ^ 2 * torusWeightMass) * (periodicFrequencyWeight k ^ (n + 1))⁻¹ :=
      (norm_tsum_le_tsum_norm hs).trans hle
    rw [norm_mul]
    have hinv : periodicFrequencyWeight k * (periodicFrequencyWeight k ^ (n + 1))⁻¹ =
        (periodicFrequencyWeight k ^ n)⁻¹ := by
      rw [pow_succ, mul_inv]
      field_simp
    calc ‖periodicDerivativeSymbol j k‖ *
          ‖∑' l : PeriodicFrequency, torusPhysicalCoeff 3 A j l *
            torusPhysicalCoeff 3 B i (k - l)‖
        ≤ periodicFrequencyWeight k *
            ((2 ^ (n + 1) * M ^ 2 * torusWeightMass) *
              (periodicFrequencyWeight k ^ (n + 1))⁻¹) :=
          mul_le_mul (norm_periodicDerivativeSymbol_le j k) hnt (norm_nonneg _) hwk.le
      _ = (2 ^ (n + 1) * M ^ 2 * torusWeightMass) *
            (periodicFrequencyWeight k * (periodicFrequencyWeight k ^ (n + 1))⁻¹) := by ring
      _ = _ := by rw [hinv]
  calc ‖torusConvectionCoeff A B i k‖
      ≤ ∑ j : Fin 3, ‖periodicDerivativeSymbol j k *
          ∑' l : PeriodicFrequency, torusPhysicalCoeff 3 A j l *
            torusPhysicalCoeff 3 B i (k - l)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, (2 ^ (n + 1) * M ^ 2 * torusWeightMass) *
          (periodicFrequencyWeight k ^ n)⁻¹ := Finset.sum_le_sum fun j _ ↦ hterm j
    _ = _ := by simp; ring

/-- The projected (contract) nonlinearity inherits the same rapid decay. -/
theorem norm_torusPhysicalCoeff_bilinear_le {ν : ℝ} (C : TorusTwoSpaceContract ν)
    {A B : PeriodicSobolev 3} {M : ℝ} (hM : 0 ≤ M) (n : ℕ)
    (hA : ∀ (j : Fin 3) (l : PeriodicFrequency),
      ‖torusPhysicalCoeff 3 A j l‖ ≤ M * (periodicFrequencyWeight l ^ (n + 3))⁻¹)
    (hB : ∀ (j : Fin 3) (l : PeriodicFrequency),
      ‖torusPhysicalCoeff 3 B j l‖ ≤ M * (periodicFrequencyWeight l ^ (n + 3))⁻¹)
    (i : Fin 3) (k : PeriodicFrequency) :
    ‖torusPhysicalCoeff 2 (C.analytic.bilinear A B) i k‖ ≤
      (6 * (3 * (2 ^ (n + 1) * M ^ 2 * torusWeightMass))) *
        (periodicFrequencyWeight k ^ n)⁻¹ := by
  rw [torusPhysicalCoeff_bilinear]
  refine (norm_lerayAt_le k (fun j ↦ torusConvectionCoeff A B j k) i).trans ?_
  calc 2 * ∑ j : Fin 3, ‖torusConvectionCoeff A B j k‖
      ≤ 2 * ∑ _j : Fin 3, (3 * (2 ^ (n + 1) * M ^ 2 * torusWeightMass)) *
          (periodicFrequencyWeight k ^ n)⁻¹ := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ ↦
          norm_torusConvectionCoeff_le hM n hA hB j k) (by norm_num)
    _ = _ := by simp; ring

/-- Uniform rapid decay of the coefficient nonlinearity on a compact subinterval. -/
theorem persistence_nonlinear_decay {ν T : ℝ} (C : TorusTwoSpaceContract ν)
    {u : ℝ → PeriodicSobolev 3} (h : PersistenceInput T u) (N : ℕ)
    {a b : ℝ} (hab : Icc a b ⊆ Ico (0 : ℝ) T) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Icc a b, ∀ (i : Fin 3) (k : PeriodicFrequency),
      periodicFrequencyWeight k ^ N *
        ‖torusPhysicalCoeff 2 (mildNonlinearDatum C u t) i k‖ ≤
        D * (periodicFrequencyWeight k ^ 2)⁻¹ := by
  obtain ⟨M, hM, hbd⟩ := persistence_uniform_decay h (N + 5) hab
  refine ⟨6 * (3 * (2 ^ (N + 3) * M ^ 2 * torusWeightMass)),
    mul_nonneg (by norm_num) (mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg M)) torusWeightMass_nonneg)), ?_⟩
  intro t ht i k
  have hcoeff : ∀ (j : Fin 3) (l : PeriodicFrequency),
      ‖torusPhysicalCoeff 3 (u t) j l‖ ≤ M * (periodicFrequencyWeight l ^ ((N + 2) + 3))⁻¹ := by
    intro j l
    have hwl : (0 : ℝ) < periodicFrequencyWeight l := mildPressure_weight_pos l
    have h1 := hbd t ht j l
    have h2 : (periodicFrequencyWeight l ^ 2)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      nlinarith [one_le_periodicFrequencyWeight' l]
    have h3 : periodicFrequencyWeight l ^ (N + 5) * ‖torusPhysicalCoeff 3 (u t) j l‖ ≤ M := by
      refine h1.trans ?_
      calc M * (periodicFrequencyWeight l ^ 2)⁻¹ ≤ M * 1 := mul_le_mul_of_nonneg_left h2 hM
        _ = M := mul_one M
    have hp : (0 : ℝ) < periodicFrequencyWeight l ^ (N + 5) := pow_pos hwl _
    rw [show (N + 2) + 3 = N + 5 by ring, ← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
    exact h3
  have hbil := norm_torusPhysicalCoeff_bilinear_le C hM (N + 2) hcoeff hcoeff i k
  have hwk : (0 : ℝ) < periodicFrequencyWeight k := mildPressure_weight_pos k
  have hpow : periodicFrequencyWeight k ^ N * (periodicFrequencyWeight k ^ (N + 2))⁻¹ =
      (periodicFrequencyWeight k ^ 2)⁻¹ := by
    rw [pow_add, mul_inv]
    field_simp
  calc periodicFrequencyWeight k ^ N *
        ‖torusPhysicalCoeff 2 (mildNonlinearDatum C u t) i k‖
      ≤ periodicFrequencyWeight k ^ N *
          ((6 * (3 * (2 ^ (N + 3) * M ^ 2 * torusWeightMass))) *
            (periodicFrequencyWeight k ^ (N + 2))⁻¹) :=
        mul_le_mul_of_nonneg_left hbil (pow_nonneg hwk.le N)
    _ = (6 * (3 * (2 ^ (N + 3) * M ^ 2 * torusWeightMass))) *
          (periodicFrequencyWeight k ^ N * (periodicFrequencyWeight k ^ (N + 2))⁻¹) := by ring
    _ = _ := by rw [hpow]



/-! ## 11. Rapid decay of the whole Duhamel source -/

/-- Uniform rapid decay of the projected force coefficients. -/
theorem persistence_force_decay {T : ℝ} {F P : ℝ → PeriodicSobolev 3}
    (hF : PersistenceInput T F) (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (N : ℕ) {a b : ℝ} (hab : Icc a b ⊆ Ico (0 : ℝ) T) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Icc a b, ∀ (i : Fin 3) (k : PeriodicFrequency),
      periodicFrequencyWeight k ^ N * ‖torusPhysicalCoeff 3 (P t) i k‖ ≤
        D * (periodicFrequencyWeight k ^ 2)⁻¹ := by
  obtain ⟨M, hM, hbd⟩ := persistence_uniform_decay hF N hab
  refine ⟨6 * M, by linarith, fun t ht i k ↦ ?_⟩
  have hwk : (0 : ℝ) < periodicFrequencyWeight k := mildPressure_weight_pos k
  have ht0 : (0 : ℝ) ≤ t := (hab ht).1
  have heq := torusPhysicalCoeff_leray (hPL t ht0) i k
  have hbound : ‖torusPhysicalCoeff 3 (P t) i k‖ ≤
      2 * ∑ j : Fin 3, ‖torusPhysicalCoeff 3 (F t) j k‖ := by
    rw [heq]
    exact norm_lerayAt_le k _ i
  calc periodicFrequencyWeight k ^ N * ‖torusPhysicalCoeff 3 (P t) i k‖
      ≤ periodicFrequencyWeight k ^ N * (2 * ∑ j : Fin 3, ‖torusPhysicalCoeff 3 (F t) j k‖) :=
        mul_le_mul_of_nonneg_left hbound (pow_nonneg hwk.le N)
    _ = 2 * ∑ j : Fin 3, periodicFrequencyWeight k ^ N * ‖torusPhysicalCoeff 3 (F t) j k‖ := by
        rw [← mul_assoc, mul_comm (periodicFrequencyWeight k ^ N) 2, mul_assoc, Finset.mul_sum]
    _ ≤ 2 * ∑ _j : Fin 3, M * (periodicFrequencyWeight k ^ 2)⁻¹ := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ ↦ hbd t ht j k) (by norm_num)
    _ = (6 * M) * (periodicFrequencyWeight k ^ 2)⁻¹ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_ofNat]
        ring

/-- The coefficient family predicted for the time derivative by the Duhamel
formula. -/
def mildDerivCoeff {ν : ℝ} (C : TorusTwoSpaceContract ν) (P u : ℝ → PeriodicSobolev 3)
    (t : ℝ) (i : Fin 3) (k : PeriodicFrequency) : ℂ :=
  (-(ν * periodicAngularFrequencySq k) : ℝ) * torusPhysicalCoeff 3 (u t) i k +
    (torusPhysicalCoeff 3 (P t) i k - torusPhysicalCoeff 2 (mildNonlinearDatum C u t) i k)

theorem mildDerivCoeff_neg {ν : ℝ} (C : TorusTwoSpaceContract ν)
    (P u : ℝ → PeriodicSobolev 3) (t : ℝ) (i : Fin 3) (k : PeriodicFrequency) :
    mildDerivCoeff C P u t i (-k) = star (mildDerivCoeff C P u t i k) := by
  have hang : periodicAngularFrequencySq (-k) = periodicAngularFrequencySq k := by
    unfold periodicAngularFrequencySq
    simp
  unfold mildDerivCoeff
  rw [hang, torusPhysicalCoeff_neg, torusPhysicalCoeff_neg, torusPhysicalCoeff_neg]
  simp only [Complex.star_def, map_add, map_sub, map_mul, Complex.conj_ofReal]

theorem periodicAngularFrequencySq_le (k : PeriodicFrequency) :
    periodicAngularFrequencySq k ≤ periodicFrequencyWeight k := by
  unfold periodicAngularFrequencySq periodicFrequencyWeight
  linarith

/-- Uniform rapid decay of the predicted derivative coefficients on a compact
subinterval of the lifespan. -/
theorem mildDerivCoeff_decay {ν T : ℝ} (C : TorusTwoSpaceContract ν)
    {F P u : ℝ → PeriodicSobolev 3}
    (hu : PersistenceInput T u) (hF : PersistenceInput T F)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (N : ℕ) {a b : ℝ} (hab : Icc a b ⊆ Ico (0 : ℝ) T) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t ∈ Icc a b, ∀ (i : Fin 3) (k : PeriodicFrequency),
      periodicFrequencyWeight k ^ N * ‖mildDerivCoeff C P u t i k‖ ≤
        D * (periodicFrequencyWeight k ^ 2)⁻¹ := by
  obtain ⟨M₁, hM₁, hb₁⟩ := persistence_uniform_decay hu (N + 1) hab
  obtain ⟨M₂, hM₂, hb₂⟩ := persistence_force_decay hF hPL N hab
  obtain ⟨M₃, hM₃, hb₃⟩ := persistence_nonlinear_decay C hu N hab
  refine ⟨|ν| * M₁ + (M₂ + M₃), by positivity, fun t ht i k ↦ ?_⟩
  have hwk : (0 : ℝ) < periodicFrequencyWeight k := mildPressure_weight_pos k
  have hang : (0 : ℝ) ≤ periodicAngularFrequencySq k := periodicAngularFrequencySq_nonneg k
  have hlin : periodicFrequencyWeight k ^ N *
      ‖((-(ν * periodicAngularFrequencySq k) : ℝ) : ℂ) * torusPhysicalCoeff 3 (u t) i k‖ ≤
      (|ν| * M₁) * (periodicFrequencyWeight k ^ 2)⁻¹ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul,
      abs_of_nonneg hang]
    have hstep : periodicFrequencyWeight k ^ N *
        (|ν| * periodicAngularFrequencySq k * ‖torusPhysicalCoeff 3 (u t) i k‖) ≤
        |ν| * (periodicFrequencyWeight k ^ (N + 1) *
          ‖torusPhysicalCoeff 3 (u t) i k‖) := by
      rw [pow_succ]
      have h := mul_le_mul_of_nonneg_right (periodicAngularFrequencySq_le k)
        (norm_nonneg (torusPhysicalCoeff 3 (u t) i k))
      have hc := mul_le_mul_of_nonneg_left h
        (mul_nonneg (abs_nonneg ν) (pow_nonneg hwk.le N))
      calc periodicFrequencyWeight k ^ N *
            (|ν| * periodicAngularFrequencySq k * ‖torusPhysicalCoeff 3 (u t) i k‖)
          = |ν| * periodicFrequencyWeight k ^ N *
            (periodicAngularFrequencySq k * ‖torusPhysicalCoeff 3 (u t) i k‖) := by ring
        _ ≤ |ν| * periodicFrequencyWeight k ^ N *
            (periodicFrequencyWeight k * ‖torusPhysicalCoeff 3 (u t) i k‖) := hc
        _ = |ν| * (periodicFrequencyWeight k ^ N * periodicFrequencyWeight k *
            ‖torusPhysicalCoeff 3 (u t) i k‖) := by ring
    refine hstep.trans ?_
    have := mul_le_mul_of_nonneg_left (hb₁ t ht i k) (abs_nonneg ν)
    calc |ν| * (periodicFrequencyWeight k ^ (N + 1) * ‖torusPhysicalCoeff 3 (u t) i k‖)
        ≤ |ν| * (M₁ * (periodicFrequencyWeight k ^ 2)⁻¹) := this
      _ = (|ν| * M₁) * (periodicFrequencyWeight k ^ 2)⁻¹ := by ring
  have hrest : periodicFrequencyWeight k ^ N *
      ‖torusPhysicalCoeff 3 (P t) i k -
        torusPhysicalCoeff 2 (mildNonlinearDatum C u t) i k‖ ≤
      (M₂ + M₃) * (periodicFrequencyWeight k ^ 2)⁻¹ := by
    have hsub : ‖torusPhysicalCoeff 3 (P t) i k -
        torusPhysicalCoeff 2 (mildNonlinearDatum C u t) i k‖ ≤
        ‖torusPhysicalCoeff 3 (P t) i k‖ +
          ‖torusPhysicalCoeff 2 (mildNonlinearDatum C u t) i k‖ := norm_sub_le _ _
    calc periodicFrequencyWeight k ^ N *
          ‖torusPhysicalCoeff 3 (P t) i k -
            torusPhysicalCoeff 2 (mildNonlinearDatum C u t) i k‖
        ≤ periodicFrequencyWeight k ^ N *
            (‖torusPhysicalCoeff 3 (P t) i k‖ +
              ‖torusPhysicalCoeff 2 (mildNonlinearDatum C u t) i k‖) :=
          mul_le_mul_of_nonneg_left hsub (pow_nonneg hwk.le N)
      _ = periodicFrequencyWeight k ^ N * ‖torusPhysicalCoeff 3 (P t) i k‖ +
            periodicFrequencyWeight k ^ N *
              ‖torusPhysicalCoeff 2 (mildNonlinearDatum C u t) i k‖ := by ring
      _ ≤ M₂ * (periodicFrequencyWeight k ^ 2)⁻¹ + M₃ * (periodicFrequencyWeight k ^ 2)⁻¹ :=
          add_le_add (hb₂ t ht i k) (hb₃ t ht i k)
      _ = (M₂ + M₃) * (periodicFrequencyWeight k ^ 2)⁻¹ := by ring
  calc periodicFrequencyWeight k ^ N * ‖mildDerivCoeff C P u t i k‖
      ≤ periodicFrequencyWeight k ^ N *
          (‖((-(ν * periodicAngularFrequencySq k) : ℝ) : ℂ) *
              torusPhysicalCoeff 3 (u t) i k‖ +
            ‖torusPhysicalCoeff 3 (P t) i k -
              torusPhysicalCoeff 2 (mildNonlinearDatum C u t) i k‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (pow_nonneg hwk.le N)
    _ = periodicFrequencyWeight k ^ N *
          ‖((-(ν * periodicAngularFrequencySq k) : ℝ) : ℂ) *
            torusPhysicalCoeff 3 (u t) i k‖ +
          periodicFrequencyWeight k ^ N *
            ‖torusPhysicalCoeff 3 (P t) i k -
              torusPhysicalCoeff 2 (mildNonlinearDatum C u t) i k‖ := by ring
    _ ≤ (|ν| * M₁) * (periodicFrequencyWeight k ^ 2)⁻¹ +
          (M₂ + M₃) * (periodicFrequencyWeight k ^ 2)⁻¹ := add_le_add hlin hrest
    _ = _ := by ring



/-! ## 12. The time derivative of the recovered physical velocity -/

/-- The physical field predicted for `∂_t u` by the Duhamel formula. -/
def mildTimeDerivative {ν : ℝ} (C : TorusTwoSpaceContract ν) (P u : ℝ → PeriodicSobolev 3)
    (t : ℝ) : SpatialField :=
  fun x ↦ WithLp.toLp 2 fun i ↦
    (torusScalarSeries (fun k ↦ mildDerivCoeff C P u t i k) x).re

theorem mildDerivCoeff_summable {ν T : ℝ} (C : TorusTwoSpaceContract ν)
    {F P u : ℝ → PeriodicSobolev 3}
    (hu : PersistenceInput T u) (hF : PersistenceInput T F)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (i : Fin 3) (N : ℕ) :
    Summable (fun k ↦ periodicFrequencyWeight k ^ N * ‖mildDerivCoeff C P u t i k‖) := by
  obtain ⟨D, hD, hbd⟩ := mildDerivCoeff_decay C hu hF hPL N
    (a := t) (b := t) (by simpa using ht)
  refine Summable.of_nonneg_of_le (fun k ↦ ?_) (fun k ↦ hbd t (by simp) i k)
    (summable_inverse_periodicFrequencyWeight.mul_left D)
  exact mul_nonneg (pow_nonneg (mildPressure_weight_pos k).le N) (norm_nonneg _)

theorem mildTimeDerivative_contDiff {ν T : ℝ} (C : TorusTwoSpaceContract ν)
    {F P u : ℝ → PeriodicSobolev 3}
    (hu : PersistenceInput T u) (hF : PersistenceInput T F)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    ContDiff ℝ ∞ (mildTimeDerivative C P u t) := by
  apply (PiLp.contDiff_toLp (p := 2)).comp
  refine contDiff_pi.mpr fun i ↦ Complex.reCLM.contDiff.comp ?_
  exact torusScalarSeries_contDiff (fun N ↦ mildDerivCoeff_summable C hu hF hPL ht i N)

theorem mildTimeDerivative_periodic {ν : ℝ} (C : TorusTwoSpaceContract ν)
    (P u : ℝ → PeriodicSobolev 3) (t : ℝ) :
    IsPeriodicSpatial (mildTimeDerivative C P u t) := by
  intro x j
  apply WithLp.ofLp_injective 2
  funext i
  exact congrArg Complex.re
    (torusScalarSeries_periodic (fun k ↦ mildDerivCoeff C P u t i k) x j)

theorem mildTimeDerivative_coeff {ν T : ℝ} (C : TorusTwoSpaceContract ν)
    {F P u : ℝ → PeriodicSobolev 3}
    (hu : PersistenceInput T u) (hF : PersistenceInput T F)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (i : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ ((mildTimeDerivative C P u t x i : ℝ) : ℂ)) k =
      mildDerivCoeff C P u t i k := by
  have hsum : Summable (fun l ↦ ‖mildDerivCoeff C P u t i l‖) := by
    simpa using mildDerivCoeff_summable C hu hF hPL ht i 0
  have hreal : (fun x ↦ ((mildTimeDerivative C P u t x i : ℝ) : ℂ)) =
      torusScalarSeries (fun l ↦ mildDerivCoeff C P u t i l) := by
    funext x
    exact Complex.conj_eq_iff_re.mp
      (torusScalarSeries_conj (fun l ↦ mildDerivCoeff_neg C P u t i l) x)
  rw [hreal]
  exact torusScalarSeries_coeff hsum k

/-- **(ii), time derivative.**  The recovered physical velocity is differentiable
in time at every interior time, with the Fourier series of the Duhamel
derivative as its derivative. -/
theorem torusPhysicalVelocity_hasDerivAt {ν T : ℝ} {C : TorusTwoSpaceContract ν}
    {A : PeriodicSobolev 3} {F P u : ℝ → PeriodicSobolev 3}
    (hmild : TorusForcedMildOn C A P T u) (hPc : ContinuousOn P (Icc (0 : ℝ) T))
    (hu : PersistenceInput T u) (hF : PersistenceInput T F)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    {a b t : ℝ} (hab : Icc a b ⊆ Ico (0 : ℝ) T) (hlt : a < b) (ht : t ∈ Ioo a b)
    (x : Space) :
    HasDerivAt (fun r : ℝ ↦ torusPhysicalVelocity u (r, x))
      (mildTimeDerivative C P u t x) t := by
  obtain ⟨D, hD, hbd⟩ := mildDerivCoeff_decay C hu hF hPL 0 hab
  have ha0 : (0 : ℝ) ≤ a := (hab (left_mem_Icc.mpr hlt.le)).1
  have hbT : b < T := (hab (right_mem_Icc.mpr hlt.le)).2
  have hIoo : Ioo a b ⊆ Ioo (0 : ℝ) T := fun r hr ↦
    ⟨lt_of_le_of_lt ha0 hr.1, lt_of_lt_of_le hr.2 hbT.le⟩
  have hcomp : ∀ i : Fin 3, HasDerivAt
      (fun r : ℝ ↦ ∑' k : PeriodicFrequency, torusPhysicalCoeff 3 (u r) i k *
        NSFormalization.Paper1.periodicCharacter k x)
      (∑' k : PeriodicFrequency, mildDerivCoeff C P u t i k *
        NSFormalization.Paper1.periodicCharacter k x) t := by
    intro i
    refine hasDerivAt_tsum_of_isPreconnected
      (u := fun k ↦ D * (periodicFrequencyWeight k ^ 2)⁻¹)
      (g := fun k r ↦ torusPhysicalCoeff 3 (u r) i k *
        NSFormalization.Paper1.periodicCharacter k x)
      (g' := fun k r ↦ mildDerivCoeff C P u r i k *
        NSFormalization.Paper1.periodicCharacter k x)
      (t := Set.Ioo a b) (y₀ := t)
      (summable_inverse_periodicFrequencyWeight.mul_left D) isOpen_Ioo
      isPreconnected_Ioo ?_ ?_ ht ?_ ht
    · intro k r hr
      exact (mild_physicalCoeff_hasDerivAt hmild hPc (hIoo hr) i k).mul_const _
    · intro k r hr
      have h := hbd r (Ioo_subset_Icc_self hr) i k
      rw [pow_zero, one_mul] at h
      rw [norm_mul, torusCharacter_norm, mul_one]
      exact h
    · exact torusPhysicalComponent_summable (u t) i x
  have hre : ∀ i : Fin 3, HasDerivAt
      (fun r : ℝ ↦ (torusPhysicalComponent (u r) i x).re)
      ((torusScalarSeries (fun k ↦ mildDerivCoeff C P u t i k) x).re) t := fun i ↦
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hcomp i)
  have hpi : HasDerivAt
      (fun r : ℝ ↦ (fun i ↦ (torusPhysicalComponent (u r) i x).re : Fin 3 → ℝ))
      (fun i ↦ (torusScalarSeries (fun k ↦ mildDerivCoeff C P u t i k) x).re) t :=
    hasDerivAt_pi.mpr hre
  exact (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 3 ↦ ℝ)).symm.hasFDerivAt.comp_hasDerivAt t hpi

/-- The physical time derivative of the recovered velocity, in the exact
`temporalDerivative` spelling of the problem statement. -/
theorem temporalDerivative_torusPhysicalVelocity {ν T : ℝ} {C : TorusTwoSpaceContract ν}
    {A : PeriodicSobolev 3} {F P u : ℝ → PeriodicSobolev 3}
    (hmild : TorusForcedMildOn C A P T u) (hPc : ContinuousOn P (Icc (0 : ℝ) T))
    (hu : PersistenceInput T u) (hF : PersistenceInput T F)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    {a b t : ℝ} (hab : Icc a b ⊆ Ico (0 : ℝ) T) (hlt : a < b) (ht : t ∈ Ioo a b)
    (x : Space) :
    temporalDerivative (torusPhysicalVelocity u) t x = mildTimeDerivative C P u t x := by
  have h := torusPhysicalVelocity_hasDerivAt hmild hPc hu hF hPL hab hlt ht x
  show fderiv ℝ (fun r : ℝ ↦ torusPhysicalVelocity u (r, x)) t 1 = _
  rw [h.hasFDerivAt.fderiv]
  simp



/-! ## 13. Physical calculus for the momentum equation -/

theorem periodicFourierCoeff_const_mul (c : ℂ) (f : Space → ℂ) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ c * f x) k = c * periodicFourierCoeff f k := by
  change UnitAddTorus.mFourierCoeff (fun q : PeriodicTorus ↦ c * torusLift f q) k =
    c * UnitAddTorus.mFourierCoeff (torusLift f) k
  unfold UnitAddTorus.mFourierCoeff
  rw [show (fun q : PeriodicTorus ↦ UnitAddTorus.mFourier (-k) q • (c * torusLift f q)) =
      fun q : PeriodicTorus ↦ c * (UnitAddTorus.mFourier (-k) q • torusLift f q) from
    funext fun q ↦ by simp only [smul_eq_mul]; ring]
  exact integral_const_mul c _

/-- One component of the vector Laplacian is the scalar Laplacian of that
component. -/
theorem spatialLaplacian_component {v : SpaceTimeField} {t : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : Space ↦ v (t, x))) (i : Fin 3) (x : Space) :
    spatialLaplacian v t x i =
      ∑ j : Fin 3, spatialPartial j (spatialPartial j (fun y : Space ↦ v (t, y) i)) x := by
  have hcomp : ∀ j : Fin 3,
      (fun y : Space ↦ (spatialDerivative v t y (coordinateVector j)) i) =
        spatialPartial j (fun y : Space ↦ v (t, y) i) := by
    intro j
    funext y
    have h : HasFDerivAt (fun z : Space ↦ v (t, z) i)
        ((EuclideanSpace.proj (𝕜 := ℝ) i).comp
          (fderiv ℝ (fun z : Space ↦ v (t, z)) y)) y :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp y
        ((hv.differentiable (by simp) y).hasFDerivAt)
    show (fderiv ℝ (fun z : Space ↦ v (t, z)) y (coordinateVector j)) i =
      fderiv ℝ (fun z : Space ↦ v (t, z) i) y (coordinateVector j)
    rw [h.fderiv]
    rfl
  have hproj : spatialLaplacian v t x i =
      ∑ j : Fin 3, (fderiv ℝ (fun y : Space ↦ spatialDerivative v t y (coordinateVector j)) x
        (coordinateVector j)) i :=
    map_sum (EuclideanSpace.proj (𝕜 := ℝ) i)
      (fun j : Fin 3 ↦ fderiv ℝ (fun y : Space ↦ spatialDerivative v t y (coordinateVector j)) x
        (coordinateVector j)) Finset.univ
  rw [hproj]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have hdj : ContDiff ℝ ∞ (fun y : Space ↦ spatialDerivative v t y (coordinateVector j)) :=
    (hv.fderiv_right (by simp)).clm_apply contDiff_const
  have h : HasFDerivAt (fun y : Space ↦ (spatialDerivative v t y (coordinateVector j)) i)
      ((EuclideanSpace.proj (𝕜 := ℝ) i).comp
        (fderiv ℝ (fun y : Space ↦ spatialDerivative v t y (coordinateVector j)) x)) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x
      ((hdj.differentiable (by simp) x).hasFDerivAt)
  show (fderiv ℝ (fun y : Space ↦ spatialDerivative v t y (coordinateVector j)) x
      (coordinateVector j)) i = _
  rw [show (fderiv ℝ (fun y : Space ↦ spatialDerivative v t y (coordinateVector j)) x
      (coordinateVector j)) i =
      fderiv ℝ (fun y : Space ↦ (spatialDerivative v t y (coordinateVector j)) i) x
        (coordinateVector j) by rw [h.fderiv]; rfl, hcomp j]
  rfl

theorem spatialLaplacian_component_contDiff {v : SpaceTimeField} {t : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : Space ↦ v (t, x))) (i : Fin 3) :
    ContDiff ℝ ∞ (fun x : Space ↦ spatialLaplacian v t x i) := by
  have he : (fun x : Space ↦ spatialLaplacian v t x i) =
      fun x : Space ↦ ∑ j : Fin 3,
        spatialPartial j (spatialPartial j (fun y : Space ↦ v (t, y) i)) x :=
    funext (spatialLaplacian_component hv i)
  rw [he]
  have hc : ContDiff ℝ ∞ (fun y : Space ↦ v (t, y) i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hv
  refine ContDiff.sum fun j _ ↦ ?_
  exact NavierStokes.PeriodicUniqueness.spatial_partial_contDiff
    (NavierStokes.PeriodicUniqueness.spatial_partial_contDiff hc j) j

theorem spatialLaplacian_component_periodic {v : SpaceTimeField} {t : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : Space ↦ v (t, x)))
    (hp : IsPeriodicSpatial (fun x : Space ↦ v (t, x))) (i : Fin 3) :
    IsPeriodicSpatial (fun x : Space ↦ spatialLaplacian v t x i) := by
  have he : (fun x : Space ↦ spatialLaplacian v t x i) =
      fun x : Space ↦ ∑ j : Fin 3,
        spatialPartial j (spatialPartial j (fun y : Space ↦ v (t, y) i)) x :=
    funext (spatialLaplacian_component hv i)
  rw [he]
  have hpi : IsPeriodicSpatial (fun y : Space ↦ v (t, y) i) :=
    fun y l ↦ congrArg (fun w : Space ↦ w i) (hp y l)
  have hup : NavierStokes.PeriodicIntegration.UnitPeriods (fun y : Space ↦ v (t, y) i) :=
    fun y l ↦ hpi y l
  intro y l
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  exact NavierStokes.PeriodicUniqueness.spatial_partial_periodic
    (NavierStokes.PeriodicUniqueness.spatial_partial_periodic hup j) j y l

theorem periodicFourierCoeff_spatialLaplacian {v : SpaceTimeField} {t : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : Space ↦ v (t, x)))
    (hp : IsPeriodicSpatial (fun x : Space ↦ v (t, x)))
    (i : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ ((spatialLaplacian v t x i : ℝ) : ℂ)) k =
      ((-(periodicAngularFrequencySq k) : ℝ) : ℂ) *
        periodicFourierCoeff (fun y : Space ↦ ((v (t, y) i : ℝ) : ℂ)) k := by
  have hreal : ContDiff ℝ ∞ (fun y : Space ↦ v (t, y) i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hv
  have hc : ContDiff ℝ ∞ (fun y : Space ↦ ((v (t, y) i : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hreal
  have hcp : IsPeriodicSpatial (fun y : Space ↦ ((v (t, y) i : ℝ) : ℂ)) :=
    fun y l ↦ congrArg (fun w : Space ↦ ((w i : ℝ) : ℂ)) (hp y l)
  have he : ∀ j : Fin 3,
      spatialPartial j (spatialPartial j (fun y : Space ↦ ((v (t, y) i : ℝ) : ℂ))) =
        fun x : Space ↦
          ((spatialPartial j (spatialPartial j (fun y : Space ↦ v (t, y) i)) x : ℝ) : ℂ) := by
    intro j
    rw [spatialPartial_complexify (hreal.of_le (by norm_num))]
    exact spatialPartial_complexify
      ((hreal.fderiv_right (by norm_num)).clm_apply contDiff_const) j
  have hstep : (fun x : Space ↦ ((spatialLaplacian v t x i : ℝ) : ℂ)) =
      fun x : Space ↦ ∑ j : Fin 3,
        spatialPartial j (spatialPartial j (fun y : Space ↦ ((v (t, y) i : ℝ) : ℂ))) x := by
    funext x
    rw [spatialLaplacian_component hv i x, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun j _ ↦ (congrFun (he j) x).symm
  rw [hstep, periodicFourierCoeff_laplacian hcp (hc.of_le (by simp)) k]
  congr 1
  unfold periodicAngularFrequencySq
  push_cast
  ring

/-- The physical time derivative on the open lifespan, without an auxiliary
compact window. -/
theorem temporalDerivative_torusPhysicalVelocity' {ν T : ℝ} {C : TorusTwoSpaceContract ν}
    {A : PeriodicSobolev 3} {F P u : ℝ → PeriodicSobolev 3}
    (hmild : TorusForcedMildOn C A P T u) (hPc : ContinuousOn P (Icc (0 : ℝ) T))
    (hu : PersistenceInput T u) (hF : PersistenceInput T F)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (x : Space) :
    temporalDerivative (torusPhysicalVelocity u) t x = mildTimeDerivative C P u t x := by
  have hab : Icc (t / 2) ((t + T) / 2) ⊆ Ico (0 : ℝ) T := by
    intro r hr
    exact ⟨le_trans (by linarith [ht.1]) hr.1, lt_of_le_of_lt hr.2 (by linarith [ht.2])⟩
  refine temporalDerivative_torusPhysicalVelocity hmild hPc hu hF hPL hab
    (by linarith [ht.1, ht.2]) ⟨by linarith [ht.1], by linarith [ht.2]⟩ x



/-! ## 14. The momentum equation -/

/-- The physical source coefficient is the force datum minus the convection
coefficient. -/
theorem mildSourceCoeff_eq {T : ℝ} {g : SpaceTimeField} {u F : ℝ → PeriodicSobolev 3}
    (hu : PersistenceInput T u) (hFg : IsPeriodicSobolevPath 3 g F)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (j : Fin 3) (k : PeriodicFrequency) :
    sourceComponentCoeff (fun x ↦ mildPressureSource g u (t, x)) j k =
      torusPhysicalCoeff 3 (F t) j k - torusConvectionCoeff (u t) (u t) j k := by
  rw [mildPressureSourceCoeff_eq_force_sub_convection hu hFg ht j k,
    convectionDivergenceT_coeff hu ht j k]

/-- The Duhamel derivative coefficient is the viscous term plus the Leray
projection of the physical source. -/
theorem mildDerivCoeff_eq_source {ν T : ℝ} (C : TorusTwoSpaceContract ν)
    {F P u : ℝ → PeriodicSobolev 3} {g : SpaceTimeField}
    (hu : PersistenceInput T u) (hFg : IsPeriodicSobolevPath 3 g F)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (i : Fin 3) (k : PeriodicFrequency) :
    mildDerivCoeff C P u t i k =
      ((-(ν * periodicAngularFrequencySq k) : ℝ) : ℂ) * torusPhysicalCoeff 3 (u t) i k +
        lerayAt k
          (fun j ↦ sourceComponentCoeff (fun x ↦ mildPressureSource g u (t, x)) j k) i := by
  unfold mildDerivCoeff
  congr 1
  rw [torusPhysicalCoeff_leray (hPL t ht.1) i k,
    show mildNonlinearDatum C u t = C.analytic.bilinear (u t) (u t) from rfl,
    torusPhysicalCoeff_bilinear C (u t) (u t) i k, ← lerayAt_sub]
  congr 1
  funext j
  rw [mildSourceCoeff_eq hu hFg ht j k]

/-- **(iii).**  For any pressure whose gradient carries the Leray-complement
Fourier data `(I - P)(F - Q)` of the physical source, the recovered physical
velocity and that pressure satisfy the exact `ClassicalSolutionT.momentum`
identity at every interior time. -/
theorem momentum_of_pressure {ν T : ℝ} {C : TorusTwoSpaceContract ν}
    {Ad : PeriodicSobolev 3} {g : SpaceTimeField} {F P u : ℝ → PeriodicSobolev 3}
    {p : SpaceTimeScalar}
    (hmild : TorusForcedMildOn C Ad P T u) (hPc : ContinuousOn P (Icc (0 : ℝ) T))
    (hu : PersistenceInput T u) (hF : PersistenceInput T F)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g)
    (hFg : IsPeriodicSobolevPath 3 g F)
    (hps : ∀ t ∈ Ico (0 : ℝ) T, ContDiff ℝ ∞ (fun x : Space ↦ p (t, x)))
    (hpp : IsPeriodicOn univ p)
    (hpgrad : ∀ t ∈ Ico (0 : ℝ) T, ∀ (i : Fin 3) (k : PeriodicFrequency),
      periodicFourierCoeff (fun x ↦ ((pressureGradient p t x i : ℝ) : ℂ)) k =
        sourceComponentCoeff (fun x ↦ mildPressureSource g u (t, x)) i k -
          lerayAt k
            (fun j ↦ sourceComponentCoeff (fun x ↦ mildPressureSource g u (t, x)) j k) i)
    (hdivfree : ∀ t ∈ Ico (0 : ℝ) T, ∀ y : Space,
      spatialDivergence (torusPhysicalVelocity u) t y = 0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (x : Space) :
    NavierStokesR3.ProblemStatement.navierStokesResidual ν (torusPhysicalVelocity u) p t x =
      g (t, x) := by
  have ht' : t ∈ Ico (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  have hv : ContDiff ℝ ∞ (fun y : Space ↦ torusPhysicalVelocity u (t, y)) :=
    persistence_physical_spatial_smooth hu ht'
  have hvp : IsPeriodicSpatial (fun y : Space ↦ torusPhysicalVelocity u (t, y)) :=
    fun y l ↦ torusPhysicalVelocity_periodic u t (mem_univ t) y l
  have hgt : ContDiff ℝ ∞ (fun y : Space ↦ g (t, y)) :=
    hg.comp (contDiff_const.prodMk contDiff_id)
  have hgtp : IsPeriodicSpatial (fun y : Space ↦ g (t, y)) := fun y l ↦ hgp t (mem_univ t) y l
  have hpt : ContDiff ℝ ∞ (fun y : Space ↦ p (t, y)) := hps t ht'
  have hptp : IsPeriodicSpatial (fun y : Space ↦ p (t, y)) := fun y l ↦ hpp t (mem_univ t) y l
  have hct : ContDiff ℝ ∞ (fun y : Space ↦
      convectionDivergenceT (torusPhysicalVelocity u) t y) :=
    convectionDivergenceT_spatial_contDiff hv
  have hctp : IsPeriodicSpatial (fun y : Space ↦
      convectionDivergenceT (torusPhysicalVelocity u) t y) :=
    convectionDivergenceT_spatial_periodic hvp
  refine (NSFormalization.Section4.A01.navierStokesResidual_eq_iff_projected ν
    (torusPhysicalVelocity u) p t x (g (t, x))
    (hv.differentiable (by simp) x) (hdivfree t ht' x)).mpr ?_
  apply WithLp.ofLp_injective 2
  funext i
  show temporalDerivative (torusPhysicalVelocity u) t x i -
      ν * spatialLaplacian (torusPhysicalVelocity u) t x i =
    (g (t, x) i - convectionDivergenceT (torusPhysicalVelocity u) t x i) -
      pressureGradient p t x i
  have htd : ∀ y : Space, temporalDerivative (torusPhysicalVelocity u) t y i =
      mildTimeDerivative C P u t y i := fun y ↦ congrArg (fun w : Space ↦ w i)
    (temporalDerivative_torusPhysicalVelocity' hmild hPc hu hF hPL ht y)
  rw [htd x]
  -- the two smooth periodic scalar fields
  have hLs : ContDiff ℝ ∞ (fun y : Space ↦
      mildTimeDerivative C P u t y i -
        ν * spatialLaplacian (torusPhysicalVelocity u) t y i) :=
    (((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp
      (mildTimeDerivative_contDiff C hu hF hPL ht'))).sub
      (contDiff_const.mul (spatialLaplacian_component_contDiff hv i))
  have hLp : IsPeriodicSpatial (fun y : Space ↦
      mildTimeDerivative C P u t y i -
        ν * spatialLaplacian (torusPhysicalVelocity u) t y i) := by
    intro y l
    have h1 := congrArg (fun w : Space ↦ w i) (mildTimeDerivative_periodic C P u t y l)
    have h2 := spatialLaplacian_component_periodic hv hvp i y l
    dsimp at h1 h2 ⊢
    rw [h1, h2]
  have hRs : ContDiff ℝ ∞ (fun y : Space ↦
      (g (t, y) i - convectionDivergenceT (torusPhysicalVelocity u) t y i) -
        pressureGradient p t y i) := by
    refine (((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hgt).sub
      ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hct)).sub ?_
    have he : (fun y : Space ↦ pressureGradient p t y i) =
        spatialPartial i (fun z : Space ↦ p (t, z)) := funext fun y ↦
      pressureGradient_component p t y i
    rw [he]
    exact NavierStokes.PeriodicUniqueness.spatial_partial_contDiff hpt i
  have hRp : IsPeriodicSpatial (fun y : Space ↦
      (g (t, y) i - convectionDivergenceT (torusPhysicalVelocity u) t y i) -
        pressureGradient p t y i) := by
    intro y l
    have h1 := congrArg (fun w : Space ↦ w i) (hgtp y l)
    have h2 := congrArg (fun w : Space ↦ w i) (hctp y l)
    have hup : NavierStokes.PeriodicIntegration.UnitPeriods (fun z : Space ↦ p (t, z)) :=
      fun z q ↦ hptp z q
    have h3 : pressureGradient p t (y + coordinateVector l) i = pressureGradient p t y i := by
      rw [pressureGradient_component, pressureGradient_component]
      exact NavierStokes.PeriodicUniqueness.spatial_partial_periodic hup i y l
    dsimp at h1 h2 ⊢
    rw [h1, h2, h3]
  refine congrFun (periodic_eq_of_coeff_eq hLs hLp hRs hRp ?_) x
  intro k
  have hint : ∀ f : Space → ℝ, ContDiff ℝ ∞ f → IsPeriodicSpatial f →
      Integrable (torusLift (fun y ↦ ((f y : ℝ) : ℂ))) periodicTorusMeasure := by
    intro f hf hfp
    exact integrable_torusLift_of_continuous_periodic
      (Complex.ofRealCLM.contDiff.comp hf).continuous
      (fun y l ↦ congrArg (fun r : ℝ ↦ (r : ℂ)) (hfp y l))
  have hcd1 : ContDiff ℝ ∞ (fun y : Space ↦ mildTimeDerivative C P u t y i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp
      (mildTimeDerivative_contDiff C hu hF hPL ht')
  have hpd1 : IsPeriodicSpatial (fun y : Space ↦ mildTimeDerivative C P u t y i) :=
    fun y l ↦ congrArg (fun w : Space ↦ w i) (mildTimeDerivative_periodic C P u t y l)
  have hcd2 : ContDiff ℝ ∞ (fun y : Space ↦
      spatialLaplacian (torusPhysicalVelocity u) t y i) :=
    spatialLaplacian_component_contDiff hv i
  have hpd2 : IsPeriodicSpatial (fun y : Space ↦
      spatialLaplacian (torusPhysicalVelocity u) t y i) :=
    spatialLaplacian_component_periodic hv hvp i
  have hcd3 : ContDiff ℝ ∞ (fun y : Space ↦ g (t, y) i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hgt
  have hpd3 : IsPeriodicSpatial (fun y : Space ↦ g (t, y) i) :=
    fun y l ↦ congrArg (fun w : Space ↦ w i) (hgtp y l)
  have hcd4 : ContDiff ℝ ∞ (fun y : Space ↦
      convectionDivergenceT (torusPhysicalVelocity u) t y i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hct
  have hpd4 : IsPeriodicSpatial (fun y : Space ↦
      convectionDivergenceT (torusPhysicalVelocity u) t y i) :=
    fun y l ↦ congrArg (fun w : Space ↦ w i) (hctp y l)
  have hgradeq : (fun y : Space ↦ pressureGradient p t y i) =
      spatialPartial i (fun z : Space ↦ p (t, z)) :=
    funext fun y ↦ pressureGradient_component p t y i
  have hup : NavierStokes.PeriodicIntegration.UnitPeriods (fun z : Space ↦ p (t, z)) :=
    fun z q ↦ hptp z q
  have hcd5 : ContDiff ℝ ∞ (fun y : Space ↦ pressureGradient p t y i) := by
    rw [hgradeq]
    exact NavierStokes.PeriodicUniqueness.spatial_partial_contDiff hpt i
  have hpd5 : IsPeriodicSpatial (fun y : Space ↦ pressureGradient p t y i) := by
    intro y l
    show pressureGradient p t (y + coordinateVector l) i = pressureGradient p t y i
    rw [pressureGradient_component, pressureGradient_component]
    exact NavierStokes.PeriodicUniqueness.spatial_partial_periodic hup i y l
  have hI1 := hint _ hcd1 hpd1
  have hI2 := hint _ hcd2 hpd2
  have hI3 := hint _ hcd3 hpd3
  have hI4 := hint _ hcd4 hpd4
  have hI5 := hint _ hcd5 hpd5
  have hI34 : Integrable (torusLift (fun y : Space ↦ ((g (t, y) i : ℝ) : ℂ) -
      ((convectionDivergenceT (torusPhysicalVelocity u) t y i : ℝ) : ℂ)))
      periodicTorusMeasure := hI3.sub hI4
  have hI2' : Integrable (torusLift (fun y : Space ↦ (ν : ℂ) *
      ((spatialLaplacian (torusPhysicalVelocity u) t y i : ℝ) : ℂ))) periodicTorusMeasure :=
    hI2.const_mul (ν : ℂ)
  have hLsplit : (fun y : Space ↦ ((mildTimeDerivative C P u t y i -
      ν * spatialLaplacian (torusPhysicalVelocity u) t y i : ℝ) : ℂ)) =
      fun y : Space ↦ ((mildTimeDerivative C P u t y i : ℝ) : ℂ) -
        (ν : ℂ) * ((spatialLaplacian (torusPhysicalVelocity u) t y i : ℝ) : ℂ) := by
    funext y
    push_cast
    ring
  have hRsplit : (fun y : Space ↦ (((g (t, y) i -
      convectionDivergenceT (torusPhysicalVelocity u) t y i) -
        pressureGradient p t y i : ℝ) : ℂ)) =
      fun y : Space ↦ (((g (t, y) i : ℝ) : ℂ) -
        ((convectionDivergenceT (torusPhysicalVelocity u) t y i : ℝ) : ℂ)) -
        ((pressureGradient p t y i : ℝ) : ℂ) := by
    funext y
    push_cast
    ring
  have hsrc : periodicFourierCoeff (fun y : Space ↦ ((g (t, y) i : ℝ) : ℂ) -
      ((convectionDivergenceT (torusPhysicalVelocity u) t y i : ℝ) : ℂ)) k =
      sourceComponentCoeff (fun y ↦ mildPressureSource g u (t, y)) i k := by
    rw [sourceComponentCoeff]
    congr 1
    funext y
    simp only [mildPressureSource, PiLp.sub_apply, Complex.ofReal_sub]
  rw [hLsplit, hRsplit, periodicFourierCoeff_sub hI1 hI2' k,
    periodicFourierCoeff_sub hI34 hI5 k,
    periodicFourierCoeff_const_mul (ν : ℂ) _ k,
    mildTimeDerivative_coeff C hu hF hPL ht' i k,
    periodicFourierCoeff_spatialLaplacian hv hvp i k,
    physicalVelocity_coeff u t i k, hpgrad t ht' i k, hsrc,
    mildDerivCoeff_eq_source C hu hFg hPL ht' i k]
  push_cast
  ring




/-- The `PeriodicLocalRegularity.projected` field, in its exact shape. -/
theorem projected_of_pressure {ν T : ℝ} {C : TorusTwoSpaceContract ν}
    {Ad : PeriodicSobolev 3} {g : SpaceTimeField} {F P u : ℝ → PeriodicSobolev 3}
    {p : SpaceTimeScalar}
    (hmild : TorusForcedMildOn C Ad P T u) (hPc : ContinuousOn P (Icc (0 : ℝ) T))
    (hu : PersistenceInput T u) (hF : PersistenceInput T F)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g)
    (hFg : IsPeriodicSobolevPath 3 g F)
    (hps : ∀ t ∈ Ico (0 : ℝ) T, ContDiff ℝ ∞ (fun x : Space ↦ p (t, x)))
    (hpp : IsPeriodicOn univ p)
    (hpgrad : ∀ t ∈ Ico (0 : ℝ) T, ∀ (i : Fin 3) (k : PeriodicFrequency),
      periodicFourierCoeff (fun x ↦ ((pressureGradient p t x i : ℝ) : ℂ)) k =
        sourceComponentCoeff (fun x ↦ mildPressureSource g u (t, x)) i k -
          lerayAt k
            (fun j ↦ sourceComponentCoeff (fun x ↦ mildPressureSource g u (t, x)) j k) i)
    (hdivfree : ∀ t ∈ Ico (0 : ℝ) T, ∀ y : Space,
      spatialDivergence (torusPhysicalVelocity u) t y = 0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (x : Space) :
    temporalDerivative (torusPhysicalVelocity u) t x -
        ν • spatialLaplacian (torusPhysicalVelocity u) t x =
      (g (t, x) - convectionDivergenceT (torusPhysicalVelocity u) t x) -
        pressureGradient p t x := by
  have ht' : t ∈ Ico (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
  have hv : ContDiff ℝ ∞ (fun y : Space ↦ torusPhysicalVelocity u (t, y)) :=
    persistence_physical_spatial_smooth hu ht'
  exact (NSFormalization.Section4.A01.navierStokesResidual_eq_iff_projected ν
    (torusPhysicalVelocity u) p t x (g (t, x))
    (hv.differentiable (by simp) x) (hdivfree t ht' x)).mp
    (momentum_of_pressure hmild hPc hu hF hPL hg hgp hFg hps hpp hpgrad hdivfree ht x)

/-! ## 15. Lane 326's pressure instantiates the momentum theorem -/

/-- The constructed pressure of `MildPressure.lean` has exactly the
Leray-complement gradient data required by `momentum_of_pressure`. -/
theorem mildPressure_gradient_source_coeff {T : ℝ} {g : SpaceTimeField}
    {u : ℝ → PeriodicSobolev 3}
    (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g) (hu : PersistenceInput T u)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (i : Fin 3) (k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ ((pressureGradient (mildPressure g u) t x i : ℝ) : ℂ)) k =
      sourceComponentCoeff (fun x ↦ mildPressureSource g u (t, x)) i k -
        lerayAt k
          (fun j ↦ sourceComponentCoeff (fun x ↦ mildPressureSource g u (t, x)) j k) i := by
  have hS := mildPressureSource_contDiff hg hu ht
  have hSp := mildPressureSource_periodic u hgp t
  rw [mildPressure_gradient_coeff hg hgp hu ht i k, mildPressureCoeff]
  by_cases hk : k = 0
  · subst hk
    rw [lerayPotentialCoeff_zero, mul_zero]
    simp [lerayAt]
  · obtain ⟨B, hB⟩ := exists_periodicDatum_smooth 3 hS hSp
    rw [lerayPotentialCoeff_leray_complement hB hk i, torusPhysicalCoeff_eq hB i k]
    congr 1
    rw [periodicLeray_eq_lerayAt, ← lerayAt_const_mul]
    congr 1
    funext j
    exact (torusPhysicalCoeff_eq hB j k)

/-- **The momentum equation for the constructed pressure.**  Lane 326's
`mildPressure` instantiates `momentum_of_pressure`. -/
theorem momentum_of_mildPressure {ν T : ℝ} {C : TorusTwoSpaceContract ν}
    {Ad : PeriodicSobolev 3} {g : SpaceTimeField} {F P u : ℝ → PeriodicSobolev 3}
    (hmild : TorusForcedMildOn C Ad P T u) (hPc : ContinuousOn P (Icc (0 : ℝ) T))
    (hu : PersistenceInput T u) (hF : PersistenceInput T F)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g)
    (hFg : IsPeriodicSobolevPath 3 g F)
    (hdivfree : ∀ t ∈ Ico (0 : ℝ) T, ∀ y : Space,
      spatialDivergence (torusPhysicalVelocity u) t y = 0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (x : Space) :
    NavierStokesR3.ProblemStatement.navierStokesResidual ν (torusPhysicalVelocity u)
      (mildPressure g u) t x = g (t, x) :=
  momentum_of_pressure hmild hPc hu hF hPL hg hgp hFg
    (fun _ hs ↦ mildPressure_spatial_contDiff hg hgp hu hs)
    (mildPressure_periodic g u)
    (fun _ hs i k ↦ mildPressure_gradient_source_coeff hg hgp hu hs i k)
    hdivfree ht x


/-- The `PeriodicLocalRegularity.projected` field for the constructed pressure. -/
theorem projected_of_mildPressure {ν T : ℝ} {C : TorusTwoSpaceContract ν}
    {Ad : PeriodicSobolev 3} {g : SpaceTimeField} {F P u : ℝ → PeriodicSobolev 3}
    (hmild : TorusForcedMildOn C Ad P T u) (hPc : ContinuousOn P (Icc (0 : ℝ) T))
    (hu : PersistenceInput T u) (hF : PersistenceInput T F)
    (hPL : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hg : ContDiff ℝ ∞ g) (hgp : IsPeriodicOn univ g)
    (hFg : IsPeriodicSobolevPath 3 g F)
    (hdivfree : ∀ t ∈ Ico (0 : ℝ) T, ∀ y : Space,
      spatialDivergence (torusPhysicalVelocity u) t y = 0)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (x : Space) :
    temporalDerivative (torusPhysicalVelocity u) t x -
        ν • spatialLaplacian (torusPhysicalVelocity u) t x =
      (g (t, x) - convectionDivergenceT (torusPhysicalVelocity u) t x) -
        pressureGradient (mildPressure g u) t x :=
  projected_of_pressure hmild hPc hu hF hPL hg hgp hFg
    (fun _ hs ↦ mildPressure_spatial_contDiff hg hgp hu hs)
    (mildPressure_periodic g u)
    (fun _ hs i k ↦ mildPressure_gradient_source_coeff hg hgp hu hs i k)
    hdivfree ht x

/-! ## 16. Non-vacuity -/

/-- The convolution theorem applies to a genuine nonzero smooth periodic pair. -/
example (m k : PeriodicFrequency) :
    periodicFourierCoeff (fun x ↦ NSFormalization.Paper1.periodicCharacter m x *
        NSFormalization.Paper1.periodicCharacter m x) k =
      ∑' l : PeriodicFrequency,
        periodicFourierCoeff (NSFormalization.Paper1.periodicCharacter m) l *
          periodicFourierCoeff (NSFormalization.Paper1.periodicCharacter m) (k - l) :=
  periodicFourierCoeff_mul
    (NSFormalization.Paper1.periodicCharacter_smooth m).continuous
    (NSFormalization.Paper1.periodicCharacter_periodic m)
    (NSFormalization.Paper1.periodicCharacter_smooth m).continuous
    (NSFormalization.Paper1.periodicCharacter_periodic m)
    (by
      simpa using summable_weight_pow_mul_coeff
        (NSFormalization.Paper1.periodicCharacter_periodic m)
        (NSFormalization.Paper1.periodicCharacter_smooth m) 0) k

/-- Non-vacuity of the Duhamel differentiation: a genuinely nonconstant forced
mild solution on a nonzero constant mode, with the exact derivative formula. -/
theorem mildMomentum_nonzero_instance :
    ∃ (C : TorusTwoSpaceContract 1) (u : ℝ → PeriodicSobolev 3),
      TorusForcedMildOn C (torusConstantDatum 3 (coordinateVector 0))
        (fun _ ↦ torusConstantDatum 3 (coordinateVector 0)) 1 u ∧
      PersistenceInput 1 u ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, ∀ (i : Fin 3) (k : PeriodicFrequency),
        HasDerivAt (fun r : ℝ ↦ (u r).1 i k)
          ((-(1 * periodicAngularFrequencySq k) : ℝ) * (u t).1 i k +
            ((torusConstantDatum 3 (coordinateVector 0)).1 i k -
              (Real.sqrt (periodicFrequencyWeight k) : ℂ) *
                (mildNonlinearDatum C u t).1 i k)) t) ∧
      u 0 ≠ 0 := by
  obtain ⟨C⟩ := torusTwoSpaceContract_nonempty' 1 (by norm_num)
  refine ⟨C, fun t ↦ (1 + t) • torusConstantDatum 3 (coordinateVector 0),
    torusForcedMildOn_affine_constant C _ (by norm_num),
    persistence_affine_constant 1 _, ?_, ?_⟩
  · intro t ht i k
    exact mild_coeff_hasDerivAt (torusForcedMildOn_affine_constant C _ (by norm_num))
      continuousOn_const ht i k
  · intro h
    change ((1 : ℝ) + 0) • (torusConstantDatum 3 (coordinateVector 0)) = 0 at h
    have hval : (torusConstantDatum 3 (coordinateVector 0)).1 0 0 = 1 := by
      change (lp.single 2 (0 : PeriodicFrequency)
        (((coordinateVector 0 : Space) 0 : ℝ) : ℂ) : PeriodicScalarData) 0 = 1
      simp [coordinateVector]
    have hzero : ((1 : ℝ) + 0) • (torusConstantDatum 3 (coordinateVector 0)) =
        torusConstantDatum 3 (coordinateVector 0) := by
      rw [add_zero, one_smul]
    rw [hzero] at h
    have hc2 := congrArg (fun B : PeriodicSobolev 3 ↦ B.1 0 0) h
    rw [hval] at hc2
    exact one_ne_zero hc2

example : ∃ (C : TorusTwoSpaceContract 1) (u : ℝ → PeriodicSobolev 3),
    TorusForcedMildOn C (torusConstantDatum 3 (coordinateVector 0))
      (fun _ ↦ torusConstantDatum 3 (coordinateVector 0)) 1 u ∧
    PersistenceInput 1 u ∧
    (∀ t ∈ Ioo (0 : ℝ) 1, ∀ (i : Fin 3) (k : PeriodicFrequency),
      HasDerivAt (fun r : ℝ ↦ (u r).1 i k)
        ((-(1 * periodicAngularFrequencySq k) : ℝ) * (u t).1 i k +
          ((torusConstantDatum 3 (coordinateVector 0)).1 i k -
            (Real.sqrt (periodicFrequencyWeight k) : ℂ) *
              (mildNonlinearDatum C u t).1 i k)) t) ∧
    u 0 ≠ 0 :=
  mildMomentum_nonzero_instance


end NSFormalization.Section3.T11
