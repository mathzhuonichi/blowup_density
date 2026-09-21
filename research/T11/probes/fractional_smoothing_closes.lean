import NSFormalization.Section3.T11.FractionalSmoothing

/-!
Probe for lane 329 (T11 U9d1b).  Every target of the brief is instantiated at
`s = 3` and shown to close from `Section3/T11/FractionalSmoothing.lean`, on a
genuine single lattice mode: the conjugate pair `{k₀, -k₀}` with `k₀ = (1,0,0)`,
which is the smallest datum in the real subspace carrying a nonzero frequency
(a single `k₀ ≠ 0` alone violates `A i (-k) = star (A i k)`).
-/

noncomputable section

namespace NSFormalization.Section3.T11.FractionalSmoothingProbe

open Set MeasureTheory
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ENNReal NNReal BigOperators

local instance fracProbeNormedGroup : NormedAddCommGroup (PeriodicSobolev 3) :=
  realPeriodicSubmodule.normedAddCommGroup

local instance fracProbeNormedSpace : NormedSpace ℝ (PeriodicSobolev 3) :=
  realPeriodicSubmodule.normedSpace

/-! ## The single-mode datum -/

/-- The real single-mode datum at the conjugate pair `{k₀, -k₀}`, amplitude `c`. -/
def singleMode (s : ℝ) (k₀ : PeriodicFrequency) (c : ℝ) : PeriodicSobolev s := by
  refine ⟨WithLp.toLp 2 (fun _ : Fin 3 =>
    (lp.single 2 k₀ ((c : ℝ) : ℂ) + lp.single 2 (-k₀) ((c : ℝ) : ℂ) :
      PeriodicScalarData)), ?_⟩
  intro i k
  change (lp.single 2 k₀ ((c : ℝ) : ℂ) + lp.single 2 (-k₀) ((c : ℝ) : ℂ) :
      PeriodicScalarData) (-k)
    = star ((lp.single 2 k₀ ((c : ℝ) : ℂ) + lp.single 2 (-k₀) ((c : ℝ) : ℂ) :
      PeriodicScalarData) k)
  simp only [lp.coeFn_add, Pi.add_apply, lp.single_apply, Pi.single_apply, star_add,
    apply_ite (star : ℂ → ℂ), star_zero, Complex.star_def, Complex.conj_ofReal,
    neg_eq_iff_eq_neg, neg_neg]
  exact add_comm _ _

theorem singleMode_apply (s : ℝ) (k₀ : PeriodicFrequency) (c : ℝ) (i : Fin 3)
    (k : PeriodicFrequency) :
    (singleMode s k₀ c).1 i k =
      (if k = k₀ then ((c : ℝ) : ℂ) else 0) + (if k = -k₀ then ((c : ℝ) : ℂ) else 0) := by
  change (lp.single 2 k₀ ((c : ℝ) : ℂ) + lp.single 2 (-k₀) ((c : ℝ) : ℂ) :
      PeriodicScalarData) k = _
  simp [lp.single_apply, Pi.single_apply]

/-- The chosen concrete mode `(1,0,0)`. -/
def probeFrequency : PeriodicFrequency := ![1, 0, 0]

theorem probeFrequency_ne_neg : probeFrequency ≠ -probeFrequency := by
  intro h
  have h0 := congrFun h 0
  simp [probeFrequency] at h0

/-! ## 1. Non-vacuity: the image of a genuine nonzero mode is nonzero -/

theorem singleMode_frac_apply {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t) (htT : t ≤ T)
    (c : ℝ) (i : Fin 3) :
    (torusHeatSmoothingFrac 3 hν ht htT (singleMode 3 probeFrequency c)).1 i probeFrequency
      = ((torusFracSymbol ν t probeFrequency * c : ℝ) : ℂ) := by
  rw [torusHeatSmoothingFrac_apply, singleMode_apply, ite_eq_left rfl,
    ite_eq_right (fun h => probeFrequency_ne_neg h), add_zero, Complex.ofReal_mul]

example {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t) (htT : t ≤ T) {c : ℝ} (hc : c ≠ 0) :
    torusHeatSmoothingFrac 3 hν ht htT (singleMode 3 probeFrequency c) ≠ 0 := by
  intro hzero
  have hsym : 0 < torusFracSymbol ν t probeFrequency :=
    mul_pos (Real.rpow_pos_of_pos (persistence_weight_pos _) _)
      (Real.exp_pos _)
  have hcoeff := singleMode_frac_apply hν ht htT c 0
  rw [hzero] at hcoeff
  have : (0 : ℂ) = ((torusFracSymbol ν t probeFrequency * c : ℝ) : ℂ) := by
    simpa using hcoeff
  have hreal : torusFracSymbol ν t probeFrequency * c = 0 := by
    exact_mod_cast this.symm
  rcases mul_eq_zero.mp hreal with h | h
  · exact absurd h hsym.ne'
  · exact hc h

/-! ## 2. The symbol bound with the explicit constant -/

example {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t) (htT : t ≤ T) (k : PeriodicFrequency) :
    periodicFrequencyWeight k ^ (3 / 4 : ℝ) * torusHeatSymbol ν t k ≤
      (ν * T + 3 / 4 * Real.exp (-1)) ^ (3 / 4 : ℝ) * (ν * t) ^ (-(3 / 4) : ℝ) :=
  torusFracSymbol_le hν ht htT k

/-! ## 3. The order-`(s+3/2)` datum: reweight compatibility and the estimate -/

example {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t) (htT : t ≤ T) (A : PeriodicSobolev 3) :
    IsPeriodicReweight 3 (3 + 3 / 2) (torusHeat 3 hν.le ht.le A)
      (torusHeatSmoothingFrac 3 hν ht htT A) :=
  torusHeatSmoothingFrac_reweight 3 hν ht htT A

example {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t) (htT : t ≤ T) (A : PeriodicSobolev 3) :
    ‖torusHeatSmoothingFrac 3 hν ht htT A‖ ≤
      (ν * T + 3 / 4 * Real.exp (-1)) ^ (3 / 4 : ℝ) * (ν * t) ^ (-(3 / 4) : ℝ) * ‖A‖ :=
  torusHeatSmoothingFrac_norm_le 3 hν ht htT A

example {ν t T : ℝ} (hν : 0 < ν) (ht : 0 < t) (htT : t ≤ T) (A : PeriodicSobolev 3)
    (hA : IsSolenoidalPeriodicDatum A) :
    IsSolenoidalPeriodicDatum (torusHeatSmoothingFrac 3 hν ht htT A) :=
  torusHeatSmoothingFrac_solenoidal 3 hν ht htT A hA

/-! ## 4. The bounded linear map `H³ →L H^{9/2}` -/

example {ν T : ℝ} (hν : 0 < ν) (t : ℝ) (ht : 0 < t) (htT : t ≤ T) :
    PeriodicSobolev 3 →L[ℝ] PeriodicSobolev (3 + 3 / 2) :=
  torusHeatSmoothingCLM_frac 3 hν t ht htT

example {ν T : ℝ} (hν : 0 < ν) (t : ℝ) (ht : 0 < t) (htT : t ≤ T) :
    ‖torusHeatSmoothingCLM_frac 3 hν t ht htT‖ ≤
      torusFracConst ν T * torusFracKernel ν t :=
  torusHeatSmoothingCLM_frac_opNorm_le 3 hν ht htT

example {ν T : ℝ} (hν : 0 < ν) (t : ℝ) (ht : 0 < t) (htT : t ≤ T) (A : PeriodicSobolev 3)
    (i : Fin 3) (k : PeriodicFrequency) :
    (torusHeatSmoothingCLM_frac 3 hν t ht htT A).1 i k =
      ((torusFracSymbol ν t k : ℝ) : ℂ) * A.1 i k :=
  torusHeatSmoothingCLM_frac_apply 3 hν ht htT A i k

/-! ## 5. The endpoint kernel -/

example {ν t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) :
    IntegrableOn (fun τ : ℝ => (ν * τ) ^ (-(3 / 4) : ℝ)) (Ioc 0 t) volume :=
  torusFracKernel_integrableOn hν ht

example {ν t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) :
    (∫ τ in (0 : ℝ)..t, (ν * (t - τ)) ^ (-(3 / 4) : ℝ)) =
      4 * t ^ (1 / 4 : ℝ) * ν ^ (-(3 / 4) : ℝ) :=
  torusFracKernel_integral hν ht

example {ν t : ℝ} (hν : 0 < ν) (ht : 0 ≤ t) :
    IntervalIntegrable (fun τ : ℝ => (ν * (t - τ)) ^ (-(3 / 4) : ℝ)) volume 0 t :=
  torusFracKernel_intervalIntegrable hν ht

/-! ## 6. Strong continuity on `Ioc 0 T` -/

example {ν T : ℝ} (hν : 0 < ν) (A : PeriodicSobolev 3)
    (u : ℝ → PeriodicSobolev (3 + 3 / 2))
    (hu : ∀ t : ℝ, ∀ ht : 0 < t, ∀ htT : t ≤ T,
      u t = torusHeatSmoothingCLM_frac 3 hν t ht htT A) :
    ContinuousOn u (Ioc 0 T) :=
  torusHeatSmoothingCLM_frac_continuousOn 3 hν A hu

example {ν T : ℝ} (hν : 0 < ν) (A : PeriodicSobolev 3) :
    ContinuousOn (torusFracPath 3 hν T A) (Ioc 0 T) :=
  torusFracPath_continuousOn 3 hν A

/-! ## 7. The scalar maximization of the brief -/

example {y : ℝ} (hy : 0 ≤ y) :
    y ^ (3 / 4 : ℝ) * Real.exp (-y) ≤ (3 / 4 : ℝ) ^ (3 / 4 : ℝ) * Real.exp (-(3 / 4 : ℝ)) :=
  rpow_three_quarters_mul_exp_neg_le hy


/-! ## 8. Exact axiom audit of the probe's own declarations -/

/-- info: 'NSFormalization.Section3.T11.FractionalSmoothingProbe.fracProbeNormedGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.FractionalSmoothingProbe.fracProbeNormedGroup

/-- info: 'NSFormalization.Section3.T11.FractionalSmoothingProbe.fracProbeNormedSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.FractionalSmoothingProbe.fracProbeNormedSpace

/-- info: 'NSFormalization.Section3.T11.FractionalSmoothingProbe.singleMode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.FractionalSmoothingProbe.singleMode

/-- info: 'NSFormalization.Section3.T11.FractionalSmoothingProbe.singleMode_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.FractionalSmoothingProbe.singleMode_apply

/-- info: 'NSFormalization.Section3.T11.FractionalSmoothingProbe.probeFrequency' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.FractionalSmoothingProbe.probeFrequency

/-- info: 'NSFormalization.Section3.T11.FractionalSmoothingProbe.probeFrequency_ne_neg' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.FractionalSmoothingProbe.probeFrequency_ne_neg

/-- info: 'NSFormalization.Section3.T11.FractionalSmoothingProbe.singleMode_frac_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NSFormalization.Section3.T11.FractionalSmoothingProbe.singleMode_frac_apply

end NSFormalization.Section3.T11.FractionalSmoothingProbe
