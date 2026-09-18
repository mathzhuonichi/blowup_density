import NSFormalization.Section3.T11.Persistence

/-!
# U9d1b: the `σ = 3/2` fractional heat smoothing estimate on the torus

The coefficient heat semigroup of `Section3/T11/LocalExistenceProbe.lean`
(`torusHeatSymbol`, `torusHeat`, `torusHeatCLM`) gains one derivative with the
kernel `(1 + 1/(νt))^{1/2}` (`torusHeatSmoothing_norm_le`).  The Duhamel term of
the periodic local-existence route needs the *fractional* gain `H^s → H^{s+3/2}`
with the integrable endpoint kernel `(νt)^{-3/4}`.

Everything here is unconditional.  The analytic core is the one-variable
maximization `y^{3/4} e^{-y} ≤ (3/4)^{3/4} e^{-3/4}`, kept in the combined form
`a (1+x) e^{-4ax/3} ≤ a + (3/4) e^{-1}`, which produces the explicit constant

  `torusFracConst ν T = (ν T + (3/4) e^{-1})^{3/4}`,

valid on the whole window `0 < t ≤ T`; the summand `ν T` is exactly how the `1`
in `W(k) = 1 + 4π²|k|²` is paid for.  The order shift `s ↦ s + 3/2` is the
canonical `IsPeriodicReweight` relation of `Section3/T10/PeriodicData.lean`
applied to the heat image, not a re-indexing of the same weighted sequence.

Contents.
* `torusFracSymbol_le` — the symbol bound `W(k)^{3/4} e^{-νt·4π²|k|²} ≤ C_T (νt)^{-3/4}`.
* `torusHeatSmoothingFrac` / `torusHeatSmoothingCLM_frac` — the order-`(s+3/2)`
  datum and its bounded linear realization, with the coefficient identity and
  the operator-norm bound.
* `torusHeatSmoothingFrac_reweight` — `IsPeriodicReweight s (s+3/2)` of the heat image.
* `torusFracKernel_integrableOn`, `torusFracKernel_integral` — endpoint kernel
  integrability on `Ioc 0 t` and the exact Duhamel mass `4 t^{1/4} ν^{-3/4}`.
* `torusFracPath_continuousOn`, `torusHeatSmoothingCLM_frac_continuousOn` —
  strong continuity of `t ↦ e^{νtΔ}A` at order `s + 3/2` on `Ioc 0 T`.
-/

noncomputable section

namespace NSFormalization.Section3.T11

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal NNReal BigOperators Topology

-- The same pinned normed route through the submodule as `LocalExistence.lean`;
-- every instance in this shared namespace carries an explicit name
-- (`logs/LESSONS.md`, 2026-09-17).
local instance fracSmoothingNormedGroup : NormedAddCommGroup (PeriodicSobolev 3) :=
  realPeriodicSubmodule.normedAddCommGroup

local instance fracSmoothingNormedSpace : NormedSpace ℝ (PeriodicSobolev 3) :=
  realPeriodicSubmodule.normedSpace

/-! ## 1. The one-variable maximization -/

/-- The maximum of `y ↦ y^{3/4} e^{-y}` on `[0,∞)`, attained at `y = 3/4`.
This is the scalar content of the `3/2`-derivative heat gain. -/
theorem rpow_three_quarters_mul_exp_neg_le {y : ℝ} (hy : 0 ≤ y) :
    y ^ (3 / 4 : ℝ) * Real.exp (-y) ≤ (3 / 4 : ℝ) ^ (3 / 4 : ℝ) * Real.exp (-(3 / 4 : ℝ)) := by
  have hkey : y * Real.exp (-(4 * y / 3)) ≤ 3 / 4 * Real.exp (-1) := by
    have h := Real.mul_exp_neg_le_exp_neg_one (4 * y / 3)
    nlinarith [Real.exp_pos (-(4 * y / 3))]
  have hexp : Real.exp (-(4 * y / 3)) ^ (3 / 4 : ℝ) = Real.exp (-y) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  have hexp1 : Real.exp (-1 : ℝ) ^ (3 / 4 : ℝ) = Real.exp (-(3 / 4 : ℝ)) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  calc y ^ (3 / 4 : ℝ) * Real.exp (-y)
      = (y * Real.exp (-(4 * y / 3))) ^ (3 / 4 : ℝ) := by
        rw [Real.mul_rpow hy (Real.exp_nonneg _), hexp]
    _ ≤ (3 / 4 * Real.exp (-1)) ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hkey (by norm_num)
    _ = (3 / 4 : ℝ) ^ (3 / 4 : ℝ) * Real.exp (-(3 / 4 : ℝ)) := by
        rw [Real.mul_rpow (by norm_num) (Real.exp_nonneg _), hexp1]

/-! ## 2. The `3/2`-smoothing symbol, its constant and its kernel -/

/-- The explicit smoothing constant on the window `0 < t ≤ T`.  The summand
`ν T` pays for the `1` in `W(k) = 1 + 4π²|k|²`; the summand `(3/4) e^{-1}` is the
maximum of `y ↦ y e^{-4y/3}`, whose `3/4`-power is `(3/4)^{3/4} e^{-3/4}`. -/
def torusFracConst (ν T : ℝ) : ℝ := (ν * T + 3 / 4 * Real.exp (-1)) ^ (3 / 4 : ℝ)

/-- The integrable endpoint kernel `(ν t)^{-3/4}` of the `3/2`-derivative gain. -/
def torusFracKernel (ν t : ℝ) : ℝ := (ν * t) ^ (-(3 / 4) : ℝ)

/-- The `H^s → H^{s+3/2}` heat multiplier symbol: the reweighting factor
`W(k)^{3/4}` of `IsPeriodicReweight s (s+3/2)` times the heat symbol. -/
def torusFracSymbol (ν t : ℝ) (k : PeriodicFrequency) : ℝ :=
  periodicFrequencyWeight k ^ (3 / 4 : ℝ) * torusHeatSymbol ν t k

/-- The `σ = 3/2` symbol bound `W(k)^{3/4} e^{-νt·4π²|k|²} ≤ C_T (νt)^{-3/4}`,
uniform in the lattice frequency and with an explicit constant. -/
theorem torusFracSymbol_le {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t) (htT : t ≤ T)
    (k : PeriodicFrequency) :
    torusFracSymbol ν t k ≤ torusFracConst ν T * torusFracKernel ν t := by
  have hx : 0 ≤ NSFormalization.Paper1.PeriodicHeatMultiplier.laplaceEigenvalue k :=
    NSFormalization.Paper1.PeriodicHeatMultiplier.laplaceEigenvalue_nonneg k
  have hw : periodicFrequencyWeight k
      = 1 + NSFormalization.Paper1.PeriodicHeatMultiplier.laplaceEigenvalue k := by
    rw [torus_weight_eq]
    unfold NSFormalization.Paper1.PeriodicHeatMultiplier.laplaceEigenvalue
    ring
  have hsym : torusHeatSymbol ν t k
      = Real.exp (-(ν * t *
          NSFormalization.Paper1.PeriodicHeatMultiplier.laplaceEigenvalue k)) := by
    rw [torusHeatSymbol, NSFormalization.Paper1.PeriodicHeatMultiplier.heatSymbol]
    congr 1
    ring
  simp only [torusFracSymbol, torusFracConst, torusFracKernel, hw, hsym]
  set x := NSFormalization.Paper1.PeriodicHeatMultiplier.laplaceEigenvalue k
  set a := ν * t with ha_def
  have ha : 0 < a := by rw [ha_def]; exact mul_pos hν ht
  have haT : a ≤ ν * T := by rw [ha_def]; exact mul_le_mul_of_nonneg_left htT hν.le
  set E := Real.exp (-(4 * (a * x) / 3)) with hE_def
  have hEpos : (0 : ℝ) < E := Real.exp_pos _
  have hEle : E ≤ 1 := by
    rw [hE_def]
    apply Real.exp_le_one_iff.mpr
    nlinarith
  have hstep : a * ((1 + x) * E) ≤ ν * T + 3 / 4 * Real.exp (-1) := by
    have hmain := Real.mul_exp_neg_le_exp_neg_one (4 * (a * x) / 3)
    rw [← hE_def] at hmain
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hEle)]
  have hEfrac : E ^ (3 / 4 : ℝ) = Real.exp (-(a * x)) := by
    rw [hE_def, ← Real.exp_mul]
    congr 1
    ring
  have hinv : a ^ (3 / 4 : ℝ) * a ^ (-(3 / 4) : ℝ) = 1 := by
    rw [← Real.rpow_add ha]
    norm_num
  have hkey : (1 + x) ^ (3 / 4 : ℝ) * Real.exp (-(a * x))
      = (a * ((1 + x) * E)) ^ (3 / 4 : ℝ) * a ^ (-(3 / 4) : ℝ) := by
    rw [Real.mul_rpow ha.le (by positivity), Real.mul_rpow (by positivity) hEpos.le, hEfrac]
    have hrw : a ^ (3 / 4 : ℝ) * ((1 + x) ^ (3 / 4 : ℝ) * Real.exp (-(a * x))) *
        a ^ (-(3 / 4) : ℝ) =
        ((1 + x) ^ (3 / 4 : ℝ) * Real.exp (-(a * x))) *
          (a ^ (3 / 4 : ℝ) * a ^ (-(3 / 4) : ℝ)) := by ring
    rw [hrw, hinv, mul_one]
  rw [hkey]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (by positivity) hstep (by norm_num)) (Real.rpow_nonneg ha.le _)

/-- The symbol is nonnegative at every frequency and every time. -/
theorem torusFracSymbol_nonneg (ν t : ℝ) (k : PeriodicFrequency) :
    0 ≤ torusFracSymbol ν t k :=
  mul_nonneg (Real.rpow_nonneg (persistence_weight_pos k).le _)
    (NSFormalization.Paper1.PeriodicHeatMultiplier.heatSymbol_nonneg ν t k)

/-- Evenness: the symbol preserves the conjugate-reflection real subspace. -/
theorem torusFracSymbol_neg (ν t : ℝ) (k : PeriodicFrequency) :
    torusFracSymbol ν t (-k) = torusFracSymbol ν t k := by
  rw [torusFracSymbol, torusFracSymbol, torus_weight_neg, torusHeatSymbol_neg]

/-- The constant mode is fixed: `W(0) = 1` and the heat symbol is one there. -/
theorem torusFracSymbol_zero (ν t : ℝ) : torusFracSymbol ν t 0 = 1 := by
  have hw : periodicFrequencyWeight (0 : PeriodicFrequency) = 1 := by
    simp [periodicFrequencyWeight]
  have hlam : NSFormalization.Paper1.PeriodicHeatMultiplier.laplaceEigenvalue
      (0 : PeriodicFrequency) = 0 := by
    unfold NSFormalization.Paper1.PeriodicHeatMultiplier.laplaceEigenvalue
    rw [← torus_weight_eq, hw]
    ring
  rw [torusFracSymbol, hw, Real.one_rpow, one_mul, torusHeatSymbol,
    NSFormalization.Paper1.PeriodicHeatMultiplier.heatSymbol, hlam]
  simp

/-- Splitting the symbol along the semigroup law: the time `t` symbol is the
heat symbol of the increment times the symbol at the earlier time. -/
theorem torusFracSymbol_sub (ν t δ : ℝ) (k : PeriodicFrequency) :
    torusFracSymbol ν t k = torusHeatSymbol ν (t - δ) k * torusFracSymbol ν δ k := by
  have hadd : torusHeatSymbol ν (t - δ) k * torusHeatSymbol ν δ k = torusHeatSymbol ν t k := by
    simp only [torusHeatSymbol]
    rw [← NSFormalization.Paper1.PeriodicHeatMultiplier.heatSymbol_add]
    congr 1
    ring
  rw [torusFracSymbol, torusFracSymbol, ← hadd]
  ring

/-- Positivity of the constant on the window. -/
theorem torusFracConst_nonneg {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t) (htT : t ≤ T) :
    0 ≤ torusFracConst ν T := by
  have h1 : 0 < ν * t := mul_pos hν ht
  have h2 : ν * t ≤ ν * T := mul_le_mul_of_nonneg_left htT hν.le
  have h3 : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
  have hbase : 0 ≤ ν * T + 3 / 4 * Real.exp (-1) := by nlinarith
  exact Real.rpow_nonneg hbase _

/-- The endpoint kernel is positive at positive times. -/
theorem torusFracKernel_pos {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) :
    0 < torusFracKernel ν t :=
  Real.rpow_pos_of_pos (mul_pos hν ht) _

/-! ## 3. The order-`(s + 3/2)` smoothing datum and its bounded realization -/

/-- The `3/2`-derivative heat image of an order-`s` datum, as an order-`(s+3/2)`
datum on the same complete real vector carrier. -/
def torusHeatSmoothingFrac (s : ℝ) {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t) (htT : t ≤ T)
    (A : PeriodicSobolev s) : PeriodicSobolev (s + 3 / 2) :=
  torusMultiplier s (s + 3 / 2) (torusFracSymbol ν t)
    (torusFracConst ν T * torusFracKernel ν t)
    (mul_nonneg (torusFracConst_nonneg hν ht htT) (torusFracKernel_pos hν ht).le)
    (fun k => by
      rw [abs_of_nonneg (torusFracSymbol_nonneg ν t k)]
      exact torusFracSymbol_le hν ht htT k)
    (torusFracSymbol_neg ν t) A

/-- The coefficient identity fixing the order conversion. -/
theorem torusHeatSmoothingFrac_apply (s : ℝ) {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t) (htT : t ≤ T)
    (A : PeriodicSobolev s) (i : Fin 3) (k : PeriodicFrequency) :
    (torusHeatSmoothingFrac s hν ht htT A).1 i k =
      ((torusFracSymbol ν t k : ℝ) : ℂ) * A.1 i k := rfl

/-- The `σ = 3/2` smoothing estimate `‖e^{νtΔ}A‖_{s+3/2} ≤ C_T (νt)^{-3/4} ‖A‖_s`
on the whole real vector carrier, with the Euclidean product norm. -/
theorem torusHeatSmoothingFrac_norm_le (s : ℝ) {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t) (htT : t ≤ T)
    (A : PeriodicSobolev s) :
    ‖torusHeatSmoothingFrac s hν ht htT A‖ ≤
      torusFracConst ν T * torusFracKernel ν t * ‖A‖ :=
  torusMultiplier_norm_le _ _ _ _ _ _ _ A

/-- The image really is the order-`(s+3/2)` reweighting of the *heat image* at
order `s`: the canonical `IsPeriodicReweight` relation, not an index erasure. -/
theorem torusHeatSmoothingFrac_reweight (s : ℝ) {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (htT : t ≤ T) (A : PeriodicSobolev s) :
    IsPeriodicReweight s (s + 3 / 2) (torusHeat s hν.le ht.le A)
      (torusHeatSmoothingFrac s hν ht htT A) := by
  intro i k
  have hexp : (s + 3 / 2 - s) / 2 = (3 / 4 : ℝ) := by ring
  change ((torusFracSymbol ν t k : ℝ) : ℂ) * A.1 i k
      = (periodicFrequencyWeight k ^ ((s + 3 / 2 - s) / 2) : ℝ) •
        (((torusHeatSymbol ν t k : ℝ) : ℂ) * A.1 i k)
  rw [hexp, Complex.real_smul, torusFracSymbol, Complex.ofReal_mul, mul_assoc]

/-- Multiplication by a scalar frequency symbol preserves incompressibility. -/
theorem torusHeatSmoothingFrac_solenoidal (s : ℝ) {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (htT : t ≤ T) (A : PeriodicSobolev s) (hA : IsSolenoidalPeriodicDatum A) :
    IsSolenoidalPeriodicDatum (torusHeatSmoothingFrac s hν ht htT A) := by
  intro k
  change ∑ j : Fin 3, periodicDerivativeSymbol j k *
    (((torusFracSymbol ν t k : ℝ) : ℂ) * A.1 j k) = 0
  calc
    _ = ((torusFracSymbol ν t k : ℝ) : ℂ) *
        ∑ j : Fin 3, periodicDerivativeSymbol j k * A.1 j k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    _ = 0 := by rw [hA k, mul_zero]

/-- The bounded linear realization `H^s →L H^{s+3/2}` of the `3/2`-smoothing. -/
def torusHeatSmoothingCLM_frac (s : ℝ) {ν T : ℝ} (hν : 0 < ν) (t : ℝ) (ht : 0 < t) (htT : t ≤ T) :
    PeriodicSobolev s →L[ℝ] PeriodicSobolev (s + 3 / 2) :=
  torusMultiplierCLM s (s + 3 / 2) (torusFracSymbol ν t)
    (torusFracConst ν T * torusFracKernel ν t)
    (mul_nonneg (torusFracConst_nonneg hν ht htT) (torusFracKernel_pos hν ht).le)
    (fun k => by
      rw [abs_of_nonneg (torusFracSymbol_nonneg ν t k)]
      exact torusFracSymbol_le hν ht htT k)
    (torusFracSymbol_neg ν t)

/-- The continuous linear map is exactly the datum-level construction. -/
theorem torusHeatSmoothingCLM_frac_eq (s : ℝ) {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t) (htT : t ≤ T)
    (A : PeriodicSobolev s) :
    torusHeatSmoothingCLM_frac s hν t ht htT A = torusHeatSmoothingFrac s hν ht htT A := rfl

/-- Coefficients of the bounded realization. -/
theorem torusHeatSmoothingCLM_frac_apply (s : ℝ) {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (htT : t ≤ T) (A : PeriodicSobolev s) (i : Fin 3) (k : PeriodicFrequency) :
    (torusHeatSmoothingCLM_frac s hν t ht htT A).1 i k =
      ((torusFracSymbol ν t k : ℝ) : ℂ) * A.1 i k := rfl

/-- The pointwise smoothing estimate for the bounded realization. -/
theorem torusHeatSmoothingCLM_frac_norm_le (s : ℝ) {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (htT : t ≤ T) (A : PeriodicSobolev s) :
    ‖torusHeatSmoothingCLM_frac s hν t ht htT A‖ ≤
      torusFracConst ν T * torusFracKernel ν t * ‖A‖ :=
  torusHeatSmoothingFrac_norm_le s hν ht htT A

/-- The operator norm obeys the same explicit endpoint bound. -/
theorem torusHeatSmoothingCLM_frac_opNorm_le (s : ℝ) {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (htT : t ≤ T) :
    ‖torusHeatSmoothingCLM_frac s hν t ht htT‖ ≤ torusFracConst ν T * torusFracKernel ν t :=
  ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (torusFracConst_nonneg hν ht htT) (torusFracKernel_pos hν ht).le)
    (fun A => torusHeatSmoothingCLM_frac_norm_le s hν ht htT A)

/-! ## 4. The endpoint kernel: integrability and the exact Duhamel mass -/

/-- The kernel factorizes at nonnegative arguments. -/
theorem torusFracKernel_eq {ν τ : ℝ} (hν : 0 ≤ ν) (hτ : 0 ≤ τ) :
    torusFracKernel ν τ = ν ^ (-(3 / 4) : ℝ) * τ ^ (-(3 / 4) : ℝ) :=
  Real.mul_rpow hν hτ

/-- The endpoint singularity `(ντ)^{-3/4}` is integrable on `Ioc 0 t`. -/
theorem torusFracKernel_integrableOn {ν t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) :
    IntegrableOn (fun τ : ℝ => torusFracKernel ν τ) (Ioc 0 t) volume := by
  have hbase : IntegrableOn (fun τ : ℝ => τ ^ (-(3 / 4) : ℝ)) (Ioc 0 t) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mp
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
  have hmul : IntegrableOn (fun τ : ℝ => ν ^ (-(3 / 4) : ℝ) * τ ^ (-(3 / 4) : ℝ))
      (Ioc 0 t) volume := hbase.const_mul _
  refine IntegrableOn.congr_fun hmul ?_ measurableSet_Ioc
  intro τ hτ
  exact (torusFracKernel_eq hν.le hτ.1.le).symm

/-- The time-reversed kernel of the Duhamel term is interval integrable. -/
theorem torusFracKernel_intervalIntegrable {ν t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) :
    IntervalIntegrable (fun τ : ℝ => torusFracKernel ν (t - τ)) volume 0 t := by
  have hb : IntervalIntegrable (fun τ : ℝ => torusFracKernel ν τ) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr (torusFracKernel_integrableOn hν ht)
  simpa using (hb.comp_sub_left t).symm

/-- The exact mass of the endpoint kernel: `∫₀ᵗ (ν(t-τ))^{-3/4} dτ = 4 t^{1/4} ν^{-3/4}`. -/
theorem torusFracKernel_integral {ν t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) :
    (∫ τ in (0 : ℝ)..t, torusFracKernel ν (t - τ)) =
      4 * t ^ (1 / 4 : ℝ) * ν ^ (-(3 / 4) : ℝ) := by
  have hcongr : Set.EqOn (fun τ : ℝ => torusFracKernel ν (t - τ))
      (fun τ : ℝ => ν ^ (-(3 / 4) : ℝ) * (t - τ) ^ (-(3 / 4) : ℝ)) (Set.uIcc 0 t) := by
    intro τ hτ
    rw [Set.uIcc_of_le ht] at hτ
    exact torusFracKernel_eq hν.le (by linarith [hτ.2])
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => x ^ (-(3 / 4) : ℝ)) t]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(3 / 4)))]
  have he : (-(3 / 4 : ℝ) + 1) = 1 / 4 := by norm_num
  rw [he, Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0)]
  ring

/-! ## 5. Strong continuity on `Ioc 0 T` -/

/-- The canonical positive-time path of the fractional smoothing applied to a
fixed order-`s` datum.  Off the window `Ioc 0 T` the value is irrelevant; only
values on `Ioc 0 T` enter `ContinuousOn`. -/
def torusFracPath (s : ℝ) {ν : ℝ} (hν : 0 < ν) (T : ℝ) (A : PeriodicSobolev s) (t : ℝ) :
    PeriodicSobolev (s + 3 / 2) :=
  if h : 0 < t ∧ t ≤ T then torusHeatSmoothingFrac s hν h.1 h.2 A else 0

/-- On the window the path is the bounded realization applied to `A`. -/
theorem torusFracPath_eq (s : ℝ) {ν T : ℝ} (hν : 0 < ν) (A : PeriodicSobolev s)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    torusFracPath s hν T A t = torusHeatSmoothingCLM_frac s hν t ht htT A := by
  rw [torusFracPath, dite_eq_left (⟨ht, htT⟩ : 0 < t ∧ t ≤ T)]
  rfl

/-- Strong continuity: `t ↦ e^{νtΔ}A` is continuous into `H^{s+3/2}` on `Ioc 0 T`.
The proof factors the symbol at `t` through the symbol at `t₀/2` and the heat
semigroup of the increment, so it uses the existing joint heat continuity. -/
theorem torusFracPath_continuousOn (s : ℝ) {ν T : ℝ} (hν : 0 < ν) (A : PeriodicSobolev s) :
    ContinuousOn (torusFracPath s hν T A) (Ioc 0 T) := by
  intro t₀ ht₀
  have hδ : 0 < t₀ / 2 := by linarith [ht₀.1]
  have hδt : t₀ / 2 < t₀ := by linarith [ht₀.1]
  have hδT : t₀ / 2 ≤ T := le_trans hδt.le ht₀.2
  set A' := torusHeatSmoothingFrac s hν hδ hδT A with hA'
  have hkey : Set.EqOn (torusFracPath s hν T A)
      (fun t : ℝ => torusHeatCLM hν.le (Real.toNNReal (t - t₀ / 2)) A') (Icc (t₀ / 2) T) := by
    intro t ht
    have h0t : 0 < t := lt_of_lt_of_le hδ ht.1
    rw [torusFracPath, dite_eq_left (⟨h0t, ht.2⟩ : 0 < t ∧ t ≤ T)]
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    funext i
    ext k
    change ((torusFracSymbol ν t k : ℝ) : ℂ) * A.1 i k =
      ((torusHeatSymbol ν ((Real.toNNReal (t - t₀ / 2) : ℝ≥0) : ℝ) k : ℝ) : ℂ) *
        (((torusFracSymbol ν (t₀ / 2) k : ℝ) : ℂ) * A.1 i k)
    rw [Real.coe_toNNReal _ (by linarith [ht.1] : (0 : ℝ) ≤ t - t₀ / 2), ← mul_assoc,
      ← Complex.ofReal_mul, ← torusFracSymbol_sub]
  have hcont : Continuous
      (fun t : ℝ => torusHeatCLM hν.le (Real.toNNReal (t - t₀ / 2)) A') := by
    have h1 : Continuous
        (fun t : ℝ => ((Real.toNNReal (t - t₀ / 2), A') : ℝ≥0 × PeriodicSobolev 3)) :=
      (continuous_real_toNNReal.comp (continuous_id.sub continuous_const)).prodMk
        continuous_const
    exact (torusHeatCLM_continuous hν.le).comp h1
  have hIcc : ContinuousOn (torusFracPath s hν T A) (Icc (t₀ / 2) T) :=
    hcont.continuousOn.congr hkey
  refine ContinuousWithinAt.mono_of_mem_nhdsWithin (hIcc t₀ ⟨hδt.le, ht₀.2⟩) ?_
  exact Filter.mem_of_superset
    (inter_mem_nhdsWithin (Ioc 0 T) (Ioi_mem_nhds hδt))
    (fun x hx => ⟨hx.2.le, hx.1.2⟩)

/-- Consumer form of strong continuity: any path whose values on `Ioc 0 T` are
the fractional smoothing of a fixed datum is continuous there. -/
theorem torusHeatSmoothingCLM_frac_continuousOn (s : ℝ) {ν T : ℝ} (hν : 0 < ν)
    (A : PeriodicSobolev s) {u : ℝ → PeriodicSobolev (s + 3 / 2)}
    (hu : ∀ t : ℝ, ∀ ht : 0 < t, ∀ htT : t ≤ T,
      u t = torusHeatSmoothingCLM_frac s hν t ht htT A) :
    ContinuousOn u (Ioc 0 T) := by
  refine (torusFracPath_continuousOn s hν A).congr ?_
  intro t ht
  rw [hu t ht.1 ht.2, torusFracPath_eq s hν A ht.1 ht.2]

/-! ## 6. Non-vacuity -/

/-- The constant (zero) mode is fixed by the fractional smoothing at every
positive time: the estimate is not about a trivial operator. -/
theorem torusHeatSmoothingFrac_constant (s : ℝ) {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (htT : t ≤ T) (c : Space) :
    torusHeatSmoothingFrac s hν ht htT (torusConstantDatum s c)
      = torusConstantDatum (s + 3 / 2) c := by
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  funext i
  ext k
  change ((torusFracSymbol ν t k : ℝ) : ℂ) *
      (lp.single 2 (0 : PeriodicFrequency) (c i : ℂ) : PeriodicScalarData) k =
    (lp.single 2 (0 : PeriodicFrequency) (c i : ℂ) : PeriodicScalarData) k
  by_cases hk : k = 0
  · subst k
    rw [torusFracSymbol_zero]
    simp
  · simp [lp.single_apply, hk]

/-- Non-vacuity: a genuine nonzero single-mode datum has a nonzero image. -/
example {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t) (htT : t ≤ T) (c : Space) (i : Fin 3)
    (hc : c i ≠ 0) :
    torusHeatSmoothingFrac 3 hν ht htT (torusConstantDatum 3 c) ≠ 0 := by
  rw [torusHeatSmoothingFrac_constant]
  intro h
  apply hc
  have hcoeff := congrArg (fun B : PeriodicSobolev (3 + 3 / 2) =>
    B.1 i (0 : PeriodicFrequency)) h
  simp only at hcoeff
  change (lp.single 2 (0 : PeriodicFrequency) (c i : ℂ) : PeriodicScalarData) 0 = 0 at hcoeff
  simpa using hcoeff

end NSFormalization.Section3.T11
