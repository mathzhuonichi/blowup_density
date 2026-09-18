import NSFormalization.Section3.T20.CriticalEnergy
import NSFormalization.Section3.T20.BIntegral
import NSFormalization.Section3.T10.ForcePaths
import NSFormalization.Section3.T11.LocalExistence
import NSFormalization.Paper1.ScalarEnergy

/-!
# T20 unit U9 — the critical bootstrap `eq:ybound` (`03-torus.tex:446-458`)

For the zero initial datum and a force `g ∈ F_T` whose critical size `ρ` obeys
the smallness hypothesis `ρ < c·ν`, the mean-free velocity of a classical torus
solution satisfies

`y(t) ≤ ∫₀ᵗ b(s) ds ≤ ρ`  for every `t ∈ [0,T)`,

with `y(t) = ‖v(t)‖_{Ḣ^{1/2}}`, `b(t) = ‖h(t)‖_{Ḣ^{1/2}}`.  This is the
`yBound` field of `CriticalRegularityTAPI` verbatim, at the explicit constant
`criticalSmallness = 1/(8·criticalTrilinearConst)`.

## Route

* §1 The bounded even symbol `|2πk|^{1/2}/(1+4π²|k|²)^{1/2}` turns an order-one
  inhomogeneous datum of a periodic field into the order-`1/2` **homogeneous**
  datum of its mean-free part.  Packaged as the contraction
  `critLower : PeriodicSobolev 1 →L[ℝ] PeriodicSobolev (1/2)`; this is the torus
  copy of `Section4/R43/ForcePath.lean`'s Bessel-to-homogeneous map.
* §2 The critical force profile `b` and its primitive `N(t) = ∫₀ᵗ b`.  Lane 312's
  `force_coefficient_path` supplies a globally continuous order-one datum path of
  `g`, so `b` is continuous, `N` is everywhere differentiable with `N' = b`, and
  `∫⁻_{(0,t]} b = ENNReal.ofReal (N t) ≤ ρ` by U3 `bIntegral`.
* §3 The critical velocity profile `y`.  `w.sobolev 1` supplies a datum path
  continuous on the lifespan, so `y` is continuous there and `y(0) = 0`.
* §4 The scalar bootstrap.  `Paper1.critical_norm_bound` applied to the clamped
  profile with `K = ν/(2·C₀)` gives `y ≤ ρ` on `[0,t]`; feeding that back into
  `Paper1.sqrt_energy_le_primitive` upgrades it to the paper's `y(t) ≤ N(t)`.
-/

noncomputable section

namespace NSFormalization.Section3.T20

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02
  (SpatialField SpaceTimeField SpaceTimeScalar forceTimeMeasure)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section3.T12
open scoped ContDiff ENNReal BigOperators

/-! ## 1. Order one to homogeneous order one half -/

/-- `03-torus.tex:414-418`: the bounded even symbol
`|2πk|^{1/2}/(1+4π²|k|²)^{1/2}` that converts an order-one inhomogeneous datum
into the order-`1/2` homogeneous datum of the mean-free part. -/
def critSymbol (k : PeriodicFrequency) : ℝ :=
  homogeneousDatumWeight (1 / 2) k / periodicFrequencyWeight k ^ ((1 : ℝ) / 2)

theorem critSymbol_nonneg (k : PeriodicFrequency) : 0 ≤ critSymbol k := by
  refine div_nonneg ?_ (Real.rpow_nonneg (periodicFrequencyWeight_pos k).le _)
  by_cases hk : k = 0
  · simp [homogeneousDatumWeight, hk]
  · simp only [homogeneousDatumWeight, hk, ↓reduceIte]
    exact Real.rpow_nonneg (by unfold periodicAngularFrequencySq; positivity) _

theorem one_le_periodicFrequencyWeight' (k : PeriodicFrequency) :
    1 ≤ periodicFrequencyWeight k := by
  unfold periodicFrequencyWeight
  have h : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * ∑ i : Fin 3, (k i : ℝ) ^ 2 := by positivity
  linarith

theorem critSymbol_abs_le_one (k : PeriodicFrequency) : |critSymbol k| ≤ 1 := by
  rw [abs_of_nonneg (critSymbol_nonneg k)]
  refine (div_le_one₀ (Real.rpow_pos_of_pos (periodicFrequencyWeight_pos k) _)).2 ?_
  refine le_trans (homogeneousDatumWeight_le_periodicFrequencyWeight_rpow (1 / 2)
    (by norm_num) k) ?_
  exact Real.rpow_le_rpow_of_exponent_le
    (one_le_periodicFrequencyWeight' k) (by norm_num)

theorem critSymbol_even (k : PeriodicFrequency) : critSymbol (-k) = critSymbol k := by
  unfold critSymbol homogeneousDatumWeight periodicFrequencyWeight periodicAngularFrequencySq
  simp [neg_eq_zero]

/-- The contractive order-one to homogeneous order-`1/2` datum map.  Torus copy
of `Section4/R43/ForcePath.lean`'s `ofSobolevVectorL ∘ lowerVectorL`. -/
def critLower : PeriodicSobolev 1 →L[ℝ] PeriodicSobolev (1 / 2) :=
  torusMultiplierCLM 1 (1 / 2) critSymbol 1 zero_le_one critSymbol_abs_le_one
    critSymbol_even

theorem critLower_apply (A : PeriodicSobolev 1) (i : Fin 3) (k : PeriodicFrequency) :
    (critLower A).1 i k = (critSymbol k : ℂ) * A.1 i k := rfl

/-- **The order-one datum of a periodic field is the order-`1/2` homogeneous
datum of its mean-free part.**  The zero mode is killed by the homogeneous
weight, and away from it the mean-free part has the same Fourier coefficients. -/
theorem critLower_isHomogeneousDatum {z : SpatialField} {A : PeriodicSobolev 1}
    (hA : IsPeriodicDatum 1 z A) :
    IsPeriodicHomogeneousDatum (1 / 2) (meanZeroPartT z) (critLower A) := by
  have hint : Integrable (torusLift z) periodicTorusMeasure := hA.2.1
  have hi : ∀ i : Fin 3,
      Integrable (torusLift (fun x ↦ ((z x i : ℝ) : ℂ))) periodicTorusMeasure :=
    fun i ↦ hA.integrable_component i
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x j
    exact congrArg (· - meanT z) (hA.1 x j)
  · exact hint.sub (integrable_const (meanT z))
  · change meanT (fun x ↦ z x - meanT z) = 0
    rw [NSFormalization.Section3.T11.MeanIdentity.meanT_sub_const hint (meanT z)]
    exact sub_eq_zero.mpr rfl
  · intro i k
    show (critSymbol k : ℂ) * A.1 i k =
      (homogeneousDatumWeight (1 / 2) k : ℂ) •
        periodicFourierCoeff (fun x ↦ ((meanZeroPartT z x i : ℝ) : ℂ)) k
    by_cases hk : k = 0
    · subst hk
      have h0 : critSymbol 0 = 0 := by
        simp [critSymbol, homogeneousDatumWeight]
      rw [h0]
      simp [homogeneousDatumWeight]
    · rw [hA.2.2 i k]
      have hcoeff :
          periodicFourierCoeff (fun x ↦ ((meanZeroPartT z x i : ℝ) : ℂ)) k =
            periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k := by
        have hsplit : (fun x ↦ ((meanZeroPartT z x i : ℝ) : ℂ)) =
            (fun x ↦ ((z x i : ℝ) : ℂ) - ((meanT z i : ℝ) : ℂ)) := by
          funext x
          rw [show (meanZeroPartT z x) i = z x i - meanT z i from rfl,
            Complex.ofReal_sub]
        rw [hsplit, periodicFourierCoeff_sub (hi i) (integrable_const _),
          periodicFourierCoeff_const]
        simp [hk]
      rw [hcoeff]
      have hp : periodicFrequencyWeight k ^ ((1 : ℝ) / 2) ≠ 0 :=
        (Real.rpow_pos_of_pos (periodicFrequencyWeight_pos k) _).ne'
      change
        ((homogeneousDatumWeight (1 / 2) k /
              periodicFrequencyWeight k ^ ((1 : ℝ) / 2) : ℝ) : ℂ) *
            (((periodicFrequencyWeight k ^ ((1 : ℝ) / 2) : ℝ) : ℂ) *
              periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k) =
          ((homogeneousDatumWeight (1 / 2) k : ℝ) : ℂ) *
            periodicFourierCoeff (fun x ↦ ((z x i : ℝ) : ℂ)) k
      rw [← mul_assoc, ← Complex.ofReal_mul, div_mul_cancel₀ _ hp]


/-! ## 2. The critical force profile and its primitive -/

/-- `03-torus.tex:414-418`: `b(t)=‖h(t)‖_{Ḣ^{1/2}}` as a real number. -/
def criticalForceProfileT (g : SpaceTimeField) (t : ℝ) : ℝ :=
  (criticalB (meanFreeForce g) t).toReal

/-- `03-torus.tex:446-458`: the forcing primitive `N(t)=∫₀ᵗ b(s)ds`. -/
def criticalForcePrimitiveT (g : SpaceTimeField) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, criticalForceProfileT g s

theorem criticalForceProfileT_nonneg (g : SpaceTimeField) (t : ℝ) :
    0 ≤ criticalForceProfileT g t := ENNReal.toReal_nonneg

/-- **The mean-free force has a globally continuous homogeneous order-`1/2`
datum path.**  Torus copy of `R43.criticalForceHalf_continuousOn`; lane 312's
`force_coefficient_path` supplies the order-one path, §1 lowers it. -/
theorem exists_criticalForcePath {g : SpaceTimeField} (hg : g ∈ forceClassT) :
    ∃ H : ℝ → PeriodicSobolev (1 / 2), Continuous H ∧
      ∀ t : ℝ, criticalB (meanFreeForce g) t = ‖H t‖ₑ := by
  obtain ⟨G, hG, hc, _hcs, _hm, _hp, _hq⟩ := force_coefficient_path hg 1
  have hcast : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
  refine ⟨fun t ↦ critLower (G t), critLower.continuous.comp hc, fun t ↦ ?_⟩
  have hdat := hG t
  rw [hcast] at hdat
  show periodicHomogeneousENorm (1 / 2) (fun x ↦ meanFreeForce g (t, x)) = _
  rw [meanFreeForce_slice_eq g t]
  exact homENorm_eq_enorm_of_datum (critLower_isHomogeneousDatum hdat)

theorem criticalB_ne_top {g : SpaceTimeField} (hg : g ∈ forceClassT) (t : ℝ) :
    criticalB (meanFreeForce g) t ≠ ⊤ := by
  obtain ⟨H, _, hHeq⟩ := exists_criticalForcePath hg
  rw [hHeq t]
  exact enorm_ne_top

theorem criticalB_eq_ofReal {g : SpaceTimeField} (hg : g ∈ forceClassT) (t : ℝ) :
    criticalB (meanFreeForce g) t = ENNReal.ofReal (criticalForceProfileT g t) :=
  (ENNReal.ofReal_toReal (criticalB_ne_top hg t)).symm

theorem criticalForceProfileT_continuous {g : SpaceTimeField} (hg : g ∈ forceClassT) :
    Continuous (criticalForceProfileT g) := by
  obtain ⟨H, hHc, hHeq⟩ := exists_criticalForcePath hg
  have heq : criticalForceProfileT g = fun t ↦ ‖H t‖ := by
    funext t
    show (criticalB (meanFreeForce g) t).toReal = _
    rw [hHeq t, ← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)]
  rw [heq]
  exact hHc.norm

/-- FTC for the critical force primitive (`03-torus.tex:452-456`). -/
theorem criticalForcePrimitiveT_hasDerivAt {g : SpaceTimeField} (hg : g ∈ forceClassT)
    (t : ℝ) :
    HasDerivAt (criticalForcePrimitiveT g) (criticalForceProfileT g t) t := by
  have hc := criticalForceProfileT_continuous hg
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

theorem criticalForcePrimitiveT_continuous {g : SpaceTimeField} (hg : g ∈ forceClassT) :
    Continuous (criticalForcePrimitiveT g) :=
  continuous_iff_continuousAt.2 fun t ↦
    (criticalForcePrimitiveT_hasDerivAt hg t).continuousAt

@[simp] theorem criticalForcePrimitiveT_zero (g : SpaceTimeField) :
    criticalForcePrimitiveT g 0 = 0 := by
  simp [criticalForcePrimitiveT]

theorem criticalForcePrimitiveT_nonneg (g : SpaceTimeField) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ criticalForcePrimitiveT g t :=
  intervalIntegral.integral_nonneg ht fun s _ ↦ criticalForceProfileT_nonneg g s

/-- The extended running force integral is the `ofReal` of the primitive. -/
theorem lintegral_criticalB_eq {g : SpaceTimeField} (hg : g ∈ forceClassT) {t : ℝ}
    (ht : 0 ≤ t) :
    (∫⁻ s in Ioc (0 : ℝ) t, criticalB (meanFreeForce g) s) =
      ENNReal.ofReal (criticalForcePrimitiveT g t) := by
  have hc := criticalForceProfileT_continuous hg
  have hInt : IntegrableOn (criticalForceProfileT g) (Ioc (0 : ℝ) t) volume :=
    hc.integrableOn_Ioc
  calc (∫⁻ s in Ioc (0 : ℝ) t, criticalB (meanFreeForce g) s)
      = ∫⁻ s in Ioc (0 : ℝ) t, ENNReal.ofReal (criticalForceProfileT g s) :=
        lintegral_congr fun s ↦ criticalB_eq_ofReal hg s
    _ = ENNReal.ofReal (∫ s in Ioc (0 : ℝ) t, criticalForceProfileT g s) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt
          (Filter.Eventually.of_forall fun s ↦ criticalForceProfileT_nonneg g s)).symm
    _ = ENNReal.ofReal (criticalForcePrimitiveT g t) := by
        rw [criticalForcePrimitiveT, intervalIntegral.integral_of_le ht]

/-- `03-torus.tex:441-458`: the running force integral never exceeds `ρ`; this
is U3 `bIntegral` restricted to `(0,t]`. -/
theorem criticalForcePrimitiveT_le_rho {g : SpaceTimeField} (hg : g ∈ forceClassT) {t : ℝ}
    (ht : 0 ≤ t) :
    ENNReal.ofReal (criticalForcePrimitiveT g t) ≤ criticalRho g := by
  rw [← lintegral_criticalB_eq hg ht]
  refine le_trans ?_ (bIntegral g hg)
  show (∫⁻ s in Ioc (0 : ℝ) t, criticalB (meanFreeForce g) s) ≤
    ∫⁻ s in Ioi (0 : ℝ), criticalB (meanFreeForce g) s
  exact lintegral_mono_set Ioc_subset_Ioi_self

/-! ## 3. The critical velocity profile -/

/-- `03-torus.tex:414-418`: `y(t)=‖v(t)‖_{Ḣ^{1/2}}` as a real number. -/
def criticalYProfileT (g u : SpaceTimeField) (t : ℝ) : ℝ :=
  (criticalY (meanFreeVelocity g u) t).toReal

theorem criticalYProfileT_nonneg (g u : SpaceTimeField) (t : ℝ) :
    0 ≤ criticalYProfileT g u t := ENNReal.toReal_nonneg

/-- The classical solution's order-one datum path, at the real order `1`. -/
theorem exists_velocityOrderOnePath {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) :
    ∃ G : ℝ → PeriodicSobolev 1, ContinuousOn G (Ico (0 : ℝ) T) ∧
      ∀ t ∈ Ico (0 : ℝ) T, IsPeriodicDatum 1 (fun x ↦ w.velocity (t, x)) (G t) := by
  obtain ⟨G, hc, hd⟩ := w.sobolev 1
  have hcast : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
  refine ⟨G, hc, fun t ht ↦ ?_⟩
  have hdat := hd t ht
  rw [hcast] at hdat
  exact hdat

theorem criticalY_eq_enorm {ν T : ℝ} (hν : 0 < ν) {g : SpaceTimeField}
    (hg : g ∈ forceClassT) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T)
    {G : ℝ → PeriodicSobolev 1}
    (hd : ∀ t ∈ Ico (0 : ℝ) T, IsPeriodicDatum 1 (fun x ↦ w.velocity (t, x)) (G t))
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    criticalY (meanFreeVelocity g w.velocity) t = ‖critLower (G t)‖ₑ := by
  show periodicHomogeneousENorm (1 / 2)
    (fun x ↦ meanFreeVelocity g w.velocity (t, x)) = _
  rw [meanFreeVelocity_slice_eq hν hg w ht]
  exact homENorm_eq_enorm_of_datum (critLower_isHomogeneousDatum (hd t ht))

theorem criticalY_ne_top {ν T : ℝ} (hν : 0 < ν) {g : SpaceTimeField}
    (hg : g ∈ forceClassT) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    criticalY (meanFreeVelocity g w.velocity) t ≠ ⊤ := by
  obtain ⟨G, _, hGd⟩ := exists_velocityOrderOnePath w
  rw [criticalY_eq_enorm hν hg w hGd ht]
  exact enorm_ne_top

theorem criticalY_eq_ofReal {ν T : ℝ} (hν : 0 < ν) {g : SpaceTimeField}
    (hg : g ∈ forceClassT) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    criticalY (meanFreeVelocity g w.velocity) t =
      ENNReal.ofReal (criticalYProfileT g w.velocity t) :=
  (ENNReal.ofReal_toReal (criticalY_ne_top hν hg w ht)).symm

/-- **Continuity of `t ↦ y(t)` on the lifespan** (`03-torus.tex:446-458`, the
continuity argument).  Order-`1/2` homogeneous transport of T11's
`continuousOn_torusSobolevNormAt_velocity`. -/
theorem continuousOn_criticalYProfileT {ν T : ℝ} (hν : 0 < ν) {g : SpaceTimeField}
    (hg : g ∈ forceClassT) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T) :
    ContinuousOn (criticalYProfileT g w.velocity) (Ico (0 : ℝ) T) := by
  obtain ⟨G, hGc, hGd⟩ := exists_velocityOrderOnePath w
  have heq : ∀ s ∈ Ico (0 : ℝ) T,
      criticalYProfileT g w.velocity s = ‖critLower (G s)‖ := by
    intro s hs
    show (criticalY (meanFreeVelocity g w.velocity) s).toReal = _
    rw [criticalY_eq_enorm hν hg w hGd hs, ← ofReal_norm,
      ENNReal.toReal_ofReal (norm_nonneg _)]
  exact ((critLower.continuous.comp_continuousOn hGc).norm).congr heq

theorem homENorm_zero (s : ℝ) :
    periodicHomogeneousENorm s (fun _ : Space ↦ (0 : Space)) = 0 := by
  have hdat : IsPeriodicHomogeneousDatum s (fun _ : Space ↦ (0 : Space)) 0 := by
    refine ⟨fun x j ↦ rfl, ?_, ?_, fun i k ↦ ?_⟩
    · exact integrable_zero _ _ _
    · show meanT (fun _ : Space ↦ (0 : Space)) = 0
      simp [meanT, NSFormalization.Paper1.torusLift]
    · have hz : (fun x : Space ↦ (((0 : Space) i : ℝ) : ℂ)) = fun _ : Space ↦ (0 : ℂ) := by
        funext x
        norm_num
      rw [hz, periodicFourierCoeff_const]
      simp
  rw [homENorm_eq_enorm_of_datum hdat, ← ofReal_norm, norm_zero, ENNReal.ofReal_zero]

/-- `y(0)=0`: the solution starts from rest, so the mean-free slice vanishes. -/
theorem criticalYProfileT_zero {ν T : ℝ} (hν : 0 < ν) {g : SpaceTimeField}
    (hg : g ∈ forceClassT) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T) :
    criticalYProfileT g w.velocity 0 = 0 := by
  have hslice : (fun x ↦ meanFreeVelocity g w.velocity (0, x)) =
      fun _ : Space ↦ (0 : Space) := by
    rw [meanFreeVelocity_slice_eq hν hg w ⟨le_rfl, w.horizon_pos⟩]
    have hzero : (fun x ↦ w.velocity (0, x)) = fun _ : Space ↦ (0 : Space) := by
      funext x
      exact w.initial x
    rw [hzero]
    funext x
    show (0 : Space) - meanT (fun _ : Space ↦ (0 : Space)) = 0
    rw [show meanT (fun _ : Space ↦ (0 : Space)) = 0 by
      simp [meanT, NSFormalization.Paper1.torusLift]]
    simp
  show (criticalY (meanFreeVelocity g w.velocity) 0).toReal = 0
  show (periodicHomogeneousENorm (1 / 2)
    (fun x ↦ meanFreeVelocity g w.velocity (0, x))).toReal = 0
  rw [hslice, homENorm_zero]
  rfl


/-! ## 4. The continuity bootstrap -/

/-- `03-torus.tex:457` "Choose `c < 1/(4C₀)`": the universal smallness constant,
taken to be `1/(8·C₀)` with `C₀ = criticalTrilinearConst` (lane 413's explicit
constant, the one U8 installs).  The strict shrinking
`criticalSmallness < 1/(4·criticalTrilinearConst)` is `criticalSmallness_lt_quarter`
below, so the structure field `c_lt_C₀` is available to U13. -/
def criticalSmallness : ℝ := 1 / (8 * criticalTrilinearConst)

theorem criticalSmallness_pos : 0 < criticalSmallness := by
  have hC := criticalTrilinearConst_pos
  show 0 < 1 / (8 * criticalTrilinearConst)
  exact div_pos one_pos (by linarith)

theorem criticalSmallness_lt_quarter :
    criticalSmallness < 1 / (4 * criticalTrilinearConst) := by
  have hC := criticalTrilinearConst_pos
  show 1 / (8 * criticalTrilinearConst) < 1 / (4 * criticalTrilinearConst)
  exact one_div_lt_one_div_of_lt (by linarith) (by linarith)

theorem criticalSmallness_le_half :
    criticalSmallness ≤ 1 / (2 * criticalTrilinearConst) := by
  have hC := criticalTrilinearConst_pos
  show 1 / (8 * criticalTrilinearConst) ≤ 1 / (2 * criticalTrilinearConst)
  exact (one_div_lt_one_div_of_lt (by linarith) (by linarith)).le

/-- **`03-torus.tex:446-458`, `eq:ybound`, for any smallness constant below the
bootstrap level `1/(2C₀)`.**  `yBound` below is the instance at
`criticalSmallness`. -/
theorem yBound_of_le {c : ℝ} (hc : c ≤ 1 / (2 * criticalTrilinearConst)) :
    ∀ (ν : ℝ), 0 < ν →
      ∀ (g : SpaceTimeField), g ∈ forceClassT →
        criticalRho g < ENNReal.ofReal (c * ν) →
          ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
            ∀ t ∈ Ico (0 : ℝ) T,
              criticalY (meanFreeVelocity g w.velocity) t ≤
                  ∫⁻ s in Ioc (0 : ℝ) t, criticalB (meanFreeForce g) s ∧
                (∫⁻ s in Ioc (0 : ℝ) t, criticalB (meanFreeForce g) s) ≤
                  criticalRho g := by
  intro ν hν g hg hsmall T w t ht
  have hC₀ : 0 < criticalTrilinearConst := criticalTrilinearConst_pos
  have hρtop : criticalRho g ≠ ⊤ := ne_top_of_lt hsmall
  have hρ0 : 0 ≤ (criticalRho g).toReal := ENNReal.toReal_nonneg
  have hρreal : (criticalRho g).toReal < c * ν :=
    ENNReal.toReal_lt_of_lt_ofReal hsmall
  have hK : criticalTrilinearConst * (ν / (2 * criticalTrilinearConst)) = ν / 2 := by
    field_simp
  have hρK : (criticalRho g).toReal < ν / (2 * criticalTrilinearConst) := by
    have h1 : c * ν ≤ 1 / (2 * criticalTrilinearConst) * ν :=
      mul_le_mul_of_nonneg_right hc hν.le
    have h2 : 1 / (2 * criticalTrilinearConst) * ν = ν / (2 * criticalTrilinearConst) := by
      field_simp
    linarith
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have hsub : Icc (0 : ℝ) t ⊆ Ico (0 : ℝ) T := fun x hx ↦ ⟨hx.1, lt_of_le_of_lt hx.2 ht.2⟩
  have hsub' : Ioo (0 : ℝ) t ⊆ Ioo (0 : ℝ) T := fun x hx ↦ ⟨hx.1, hx.2.trans ht.2⟩
  -- the clamped critical profile, continuous on all of `ℝ`
  have hyIcc : ContinuousOn (criticalYProfileT g w.velocity) (Icc (0 : ℝ) t) :=
    (continuousOn_criticalYProfileT hν hg w).mono hsub
  have hclampc : Continuous (fun s : ℝ ↦ min (max s 0) t) :=
    (continuous_id.max continuous_const).min continuous_const
  have hclampmem : ∀ s : ℝ, min (max s 0) t ∈ Icc (0 : ℝ) t :=
    fun s ↦ ⟨le_min (le_max_right _ _) ht0, min_le_right _ _⟩
  have hYcont :
      Continuous (fun s : ℝ ↦ criticalYProfileT g w.velocity (min (max s 0) t)) :=
    hyIcc.comp_continuous hclampc hclampmem
  have hclampid : ∀ s ∈ Icc (0 : ℝ) t, min (max s 0) t = s := by
    intro s hs
    rw [max_eq_left hs.1, min_eq_left hs.2]
  have hYeq : ∀ s ∈ Icc (0 : ℝ) t,
      criticalYProfileT g w.velocity (min (max s 0) t) =
        criticalYProfileT g w.velocity s := by
    intro s hs
    rw [hclampid s hs]
  -- U8, with a chosen derivative witness
  have hEex : ∀ s : ℝ, ∃ e : ℝ, s ∈ Ioo (0 : ℝ) T →
      HasDerivAt (fun r ↦ criticalYProfileT g w.velocity r ^ 2) e s ∧
        e / 2 + (ν - criticalTrilinearConst * criticalYProfileT g w.velocity s) *
            (criticalZ (meanFreeVelocity g w.velocity) s).toReal ^ 2 ≤
          criticalForceProfileT g s * criticalYProfileT g w.velocity s := by
    intro s
    by_cases hs : s ∈ Ioo (0 : ℝ) T
    · obtain ⟨e, he⟩ := criticalEnergy ν hν g hg T w s hs
      exact ⟨e, fun _ ↦ he⟩
    · exact ⟨0, fun h ↦ absurd h hs⟩
  choose E' hE' using hEex
  have hdE : ∀ s ∈ Ioo (0 : ℝ) t,
      HasDerivAt
        (fun x ↦ criticalYProfileT g w.velocity (min (max x 0) t) ^ 2) (E' s) s := by
    intro s hs
    refine (hE' s (hsub' hs)).1.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioo.mem_nhds hs] with x hx
    rw [hclampid x ⟨hx.1.le, hx.2.le⟩]
  have henergy : ∀ s ∈ Ioo (0 : ℝ) t,
      E' s / 2 + (ν - criticalTrilinearConst *
            criticalYProfileT g w.velocity (min (max s 0) t)) *
            (criticalZ (meanFreeVelocity g w.velocity) s).toReal ^ 2 ≤
        criticalForceProfileT g s *
          criticalYProfileT g w.velocity (min (max s 0) t) := by
    intro s hs
    rw [hYeq s ⟨hs.1.le, hs.2.le⟩]
    exact (hE' s (hsub' hs)).2
  -- the forcing primitive
  have hNcont : ContinuousOn (criticalForcePrimitiveT g) (Icc (0 : ℝ) t) :=
    (criticalForcePrimitiveT_continuous hg).continuousOn
  have hNbound : ∀ s ∈ Icc (0 : ℝ) t,
      criticalForcePrimitiveT g s ≤ (criticalRho g).toReal := by
    intro s hs
    calc criticalForcePrimitiveT g s
        = (ENNReal.ofReal (criticalForcePrimitiveT g s)).toReal :=
          (ENNReal.toReal_ofReal (criticalForcePrimitiveT_nonneg g hs.1)).symm
      _ ≤ (criticalRho g).toReal :=
          ENNReal.toReal_mono hρtop (criticalForcePrimitiveT_le_rho hg hs.1)
  have hdN : ∀ s ∈ Ioo (0 : ℝ) t,
      HasDerivAt (criticalForcePrimitiveT g) (criticalForceProfileT g s) s :=
    fun s _ ↦ criticalForcePrimitiveT_hasDerivAt hg s
  have hY0 : criticalYProfileT g w.velocity (min (max (0 : ℝ) 0) t) = 0 := by
    rw [hYeq 0 ⟨le_rfl, ht0⟩]
    exact criticalYProfileT_zero hν hg w
  -- Step 1: the level-crossing bootstrap gives `y ≤ ρ` on `[0,t]`
  have hstage1 : ∀ s ∈ Icc (0 : ℝ) t,
      criticalYProfileT g w.velocity (min (max s 0) t) ≤ (criticalRho g).toReal :=
    NSFormalization.Paper1.critical_norm_bound hν.le hC₀.le hρ0 hρK hK.le hYcont hY0
      (fun s _ ↦ criticalYProfileT_nonneg _ _ _) hNcont
      (criticalForcePrimitiveT_zero g) hNbound
      (fun s _ ↦ criticalForceProfileT_nonneg g s) hdE hdN henergy
  -- Step 2: with `C₀ y ≤ ν/2` the dissipation absorbs and the primitive bounds `y`
  have habsorb : ∀ s ∈ Ioo (0 : ℝ) t,
      criticalTrilinearConst *
        criticalYProfileT g w.velocity (min (max s 0) t) ≤ ν / 2 := by
    intro s hs
    have h2 : criticalYProfileT g w.velocity (min (max s 0) t) ≤
        ν / (2 * criticalTrilinearConst) :=
      le_trans (hstage1 s ⟨hs.1.le, hs.2.le⟩) hρK.le
    calc criticalTrilinearConst * criticalYProfileT g w.velocity (min (max s 0) t)
        ≤ criticalTrilinearConst * (ν / (2 * criticalTrilinearConst)) :=
          mul_le_mul_of_nonneg_left h2 hC₀.le
      _ = ν / 2 := hK
  have hineq : ∀ s ∈ Ioo (0 : ℝ) t,
      E' s ≤ 2 * criticalForceProfileT g s *
        Real.sqrt (criticalYProfileT g w.velocity (min (max s 0) t) ^ 2) := by
    intro s hs
    have hd := NSFormalization.Paper1.critical_squared_derivative_bound hν.le
      (NSFormalization.Paper1.critical_energy_absorption (habsorb s hs) (henergy s hs))
    rwa [Real.sqrt_sq (criticalYProfileT_nonneg _ _ _)]
  have hprim : ∀ s ∈ Icc (0 : ℝ) t,
      Real.sqrt (criticalYProfileT g w.velocity (min (max s 0) t) ^ 2) ≤
        criticalForcePrimitiveT g s :=
    NSFormalization.Paper1.sqrt_energy_le_primitive ht0 (hYcont.pow 2).continuousOn hNcont
      (by rw [hY0]; ring) (criticalForcePrimitiveT_zero g) (fun s _ ↦ sq_nonneg _)
      (fun s _ ↦ criticalForceProfileT_nonneg g s) hdE hdN hineq
  have hyt : criticalYProfileT g w.velocity t ≤ criticalForcePrimitiveT g t := by
    have h := hprim t ⟨ht0, le_rfl⟩
    rwa [Real.sqrt_sq (criticalYProfileT_nonneg _ _ _), hYeq t ⟨ht0, le_rfl⟩] at h
  refine ⟨?_, ?_⟩
  · rw [criticalY_eq_ofReal hν hg w ht, lintegral_criticalB_eq hg ht0]
    exact ENNReal.ofReal_le_ofReal hyt
  · rw [lintegral_criticalB_eq hg ht0]
    exact criticalForcePrimitiveT_le_rho hg ht0

/-- `03-torus.tex:446-458`, `eq:ybound`: the `yBound` field of
`CriticalRegularityTAPI`, verbatim, at `c = criticalSmallness`. -/
theorem yBound : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (criticalSmallness * ν) →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν (fun _ : Space ↦ 0) g T),
          ∀ t ∈ Ico (0 : ℝ) T,
            criticalY (meanFreeVelocity g w.velocity) t ≤
                ∫⁻ s in Ioc (0 : ℝ) t, criticalB (meanFreeForce g) s ∧
              (∫⁻ s in Ioc (0 : ℝ) t, criticalB (meanFreeForce g) s) ≤
                criticalRho g :=
  yBound_of_le criticalSmallness_le_half

end NSFormalization.Section3.T20
