import NSFormalization.Section3.T11.Persistence
import NSFormalization.Section3.T10.ForcePaths
import NSFormalization.Section4.A01.Propagation
import NSFormalization.Section4.A04.Regularized

/-!
# T11 unit U12 — the periodic higher-order bound (`eq:Rhigh` + Grönwall)

`paper/sections/appendix-a-local-theory.tex:127-147`.  The target is the
`higherOrderBound` field of `PeriodicContinuationAPI`
(`research/T11/probes/api_on_canonical.lean:112-121`): a finite squared `H²`
time integral bounds **every** integer Sobolev order uniformly on `[0,S)`.

This module delivers the whole chain **after** the energy inequality, together
with the coefficient-level pieces of the energy inequality that the torus
carrier settles outright, and states the exact residual.

## What is proved unconditionally

* `periodicSobolevENorm_mono_order` — the order-descent inequality
  `‖z‖_{H^r} ≤ ‖z‖_{H^s}` for `r ≤ s` on the torus (the weight
  `1 + 4π²|k|²` is `≥ 1`, so the descending multiplier has norm `≤ 1`).
  This is what reduces the target's `∀ m : ℕ` to the orders `m ≥ 3` on which
  `eq:Rhigh` is stated.
* `running_hTwo_integral_le` — the `ℝ≥0∞` continuation criterion
  `squaredHTwoIntegralT S u ≠ ⊤` caps **every** running real integral
  `∫₀ᵗ ‖u(r)‖²_{H²} dr` by the single constant `(squaredHTwoIntegralT S u).toReal`,
  uniformly in the horizon of the local solution carrying `u`.  No value at the
  terminal time `S` is used.
* `force_hm_profile_cap` — for `f ∈ F_T` the profile `s ↦ ‖f(s)‖_{H^m}` is
  continuous on all of `ℝ` and its running integral is capped by one constant
  (compact positive-time support, lane 312's `force_coefficient_path`).
* `torusPressureDrop` — **the pressure term of `eq:Rhigh` vanishes** for a
  solenoidal velocity datum, as the manuscript's "the pressure term vanishes by
  solenoidality" (`appendix-a-local-theory.tex:141`).  On the torus this is an
  exact coefficient computation, not an integration by parts: conjugating
  `∑ⱼ 2πi kⱼ ûⱼ(k) = 0` kills every frequency of `⟪u, ∇p⟫_{H^m}`.
  `research/T11/probes/high_order_closes.lean` exhibits it at a **nonzero**
  velocity datum and a **nonzero** pressure-gradient datum (the shear mode
  `2 e₁ cos(2π x₀)` and the gradient of the companion scalar mode); the witness
  lives in the probe because its frequency arithmetic prints a strict subset of
  the three standard axioms.
* `torusLaplacianPairing` / `torusLaplacianPairing_nonpos` — the dissipation
  term has the right sign at every frequency, with the exact value
  `−|2πk|² ∑ᵢ |û ᵢ(k)|²`.
* `torusRealPairing_le` — the Cauchy–Schwarz step used for the force term
  `⟪f, u⟫_{H^m} ≤ ‖f‖_{H^m}‖u‖_{H^m}`.
* `torusYoungAbsorb` — Young's absorption of the cross term into the
  dissipation, fixing `C_{m,ν} = C_m²/(4ν)` (the same arithmetic as
  `Section4.A04.young_high_real`, reproved here so that Section 3 does not
  depend on the whole-space energy chain).
* `torusGronwallChain` — `eq:Rhigh → eq:highcontinuation → Grönwall` on the
  real profiles: the `ζ↓0` integral form is `Section4.A04.sqrt_le_primitive_linear`
  and the variable-coefficient Grönwall bound is
  `Section4.A01.gronwall_bddAbove_Ico` (both pure real analysis, Mathlib-only
  imports).

## The exact residual

`higherOrderBound_of_energyInequality` proves the target field **verbatim** from
one hypothesis, `hRhigh`, written out in full in its binder: the periodic
`eq:Rhigh` on a `ClassicalSolutionT`.  Nothing else is assumed.

`hRhigh` is *not* the target restated: it is a differential inequality at each
interior time of one local solution, whereas the target is a uniform bound over
the whole of `[0,S)` for the glued field of `SolvesBelowT`; the passage between
them is the content of this module.  It is the exact torus analogue of Section 4's
`energyIdentityHigh` (`Section4/A04/EnergyIdentityHigh.lean`), which needed the
sub-lanes SL0–SL8 of `research/A04/G1_SPLIT.md` on the whole-space carrier.

Two facts are missing on the torus for `hRhigh`, and they are recorded, not
papered over (`research/T11/ATTEMPTS_HIGH_ORDER.md`):

1. **Time differentiability of the coefficient path.**  `ClassicalSolutionT.sobolev`
   supplies only `ContinuousOn G (Ico 0 T)`; `PeriodicLocalRegularity.sobolev_smooth`
   supplies `ContDiffOn ℝ ∞ G`, but `SolvesBelowT` does not carry the regularity
   predicate.  Section 4 closed the same gap with
   `A04.classical_hasSmoothSobolevPath`, which routes through the local-existence
   carrier and uniqueness; the torus analogue is blocked on the still-open
   `PeriodicQuantitativeLocalInput'` (lanes 311/313/321).
2. **The torus tame product** at the pairing level, i.e.
   `|⟪(u·∇)u, u⟫_{H^m}| ≤ C_m ‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m}`.  T12's
   `tameProduct` field is a *scalar physical-field* bound
   (`periodicScalarSobolevENorm`), so it is an input to that estimate rather
   than the estimate itself; Section 4 needed the whole `research/A04/SL5_SPLIT.md`
   campaign for the corresponding step.

Because two independent facts are missing, no single named `def … : Prop` input
would be honest here, and none is introduced: the residual is exactly the
`hRhigh` binder.

## Shape note on the dissipation

`eq:Rhigh`'s dissipation term `ν‖∇u‖²_{H^m}` appears in `hRhigh` as `ν * g ^ 2`
with `g` existentially quantified and nonnegative.  The torus vocabulary has no
fixed spelling of `‖∇u‖_{H^m}` (T10's `periodicHomogeneousENorm` is defined only
for mean-zero fields), and quantifying `g` existentially makes the hypothesis
*weaker*, hence easier to discharge: instantiating `g := ‖∇u(t)‖_{H^m}` recovers
`eq:Rhigh` literally.  Young's absorption is valid for every `g ≥ 0`.
-/

noncomputable section

namespace NSFormalization.Section3.T11

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal BigOperators ComplexConjugate

-- Named, so that the two normed structures on the datum carrier never collide
-- with the ones another module of this namespace installs (`logs/LESSONS.md`,
-- 2026-09-17).
local instance highOrderNormedGroup (s : ℝ) : NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup

local instance highOrderNormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

/-! ## 1. The real Sobolev profile of a space-time field -/

/-- `‖z(t)‖_{H^s}` as a real number; `⊤` becomes `0`, so the profile is total.
The torus analogue of `Section4.A04.sobolevNormAt`. -/
def torusSobolevNormAt (s : ℝ) (u : SpaceTimeField) (t : ℝ) : ℝ :=
  (periodicSobolevENorm s (fun x ↦ u (t, x))).toReal

theorem torusSobolevNormAt_nonneg (s : ℝ) (u : SpaceTimeField) (t : ℝ) :
    0 ≤ torusSobolevNormAt s u t := ENNReal.toReal_nonneg

/-- At a time carrying a datum the profile is that datum's norm. -/
theorem torusSobolevNormAt_eq {s : ℝ} {u : SpaceTimeField} {t : ℝ}
    {A : PeriodicSobolev s} (hA : IsPeriodicDatum s (fun x ↦ u (t, x)) A) :
    torusSobolevNormAt s u t = ‖A‖ := by
  rw [torusSobolevNormAt, periodicSobolevENorm_eq_datum hA, toReal_enorm]

/-- A represented slice has finite extended norm. -/
theorem periodicSobolevENorm_ne_top_of_datum {s : ℝ} {z : SpatialField}
    {A : PeriodicSobolev s} (hA : IsPeriodicDatum s z A) :
    periodicSobolevENorm s z ≠ ⊤ := by
  rw [periodicSobolevENorm_eq_datum hA]
  exact enorm_ne_top

/-- On the lifespan the profile is `‖G ·‖` for the solution's datum path, hence
continuous. -/
theorem continuousOn_torusSobolevNormAt_velocity {ν T : ℝ} {a : SpatialField}
    {f : SpaceTimeField} (w : ClassicalSolutionT ν a f T) (m : ℕ) :
    ContinuousOn (fun t ↦ torusSobolevNormAt (m : ℝ) w.velocity t) (Ico (0 : ℝ) T) := by
  obtain ⟨G, hG, hd⟩ := w.sobolev m
  exact hG.norm.congr fun t ht ↦ torusSobolevNormAt_eq (hd t ht)

/-! ## 2. Order descent on the torus -/

/-- The descending multiplier `W(k)^((r−s)/2)` applied to an order-`s` datum.
`persistenceDown` is the same map packaged as a continuous linear map; the bare
function is used here because only the pointwise bound of
`torusMultiplier_norm_le` is needed. -/
def torusOrderDown (s r : ℝ) (h : r ≤ s) (A : PeriodicSobolev s) : PeriodicSobolev r :=
  torusMultiplier s r (fun k ↦ periodicFrequencyWeight k ^ ((r - s) / 2)) 1 zero_le_one
    (persistence_down_weight_le h) (fun k ↦ by rw [torus_weight_neg]) A

theorem torusOrderDown_reweight (s r : ℝ) (h : r ≤ s) (A : PeriodicSobolev s) :
    IsPeriodicReweight s r A (torusOrderDown s r h A) := by
  intro i k
  rfl

/-- Descending in order never increases the datum norm: the inhomogeneous weight
is `≥ 1`, so the multiplier is bounded by one. -/
theorem torusOrderDown_norm_le (s r : ℝ) (h : r ≤ s) (A : PeriodicSobolev s) :
    ‖torusOrderDown s r h A‖ ≤ ‖A‖ := by
  have hb := torusMultiplier_norm_le s r
    (fun k ↦ periodicFrequencyWeight k ^ ((r - s) / 2)) 1 zero_le_one
    (persistence_down_weight_le h) (fun k ↦ by rw [torus_weight_neg]) A
  rwa [one_mul] at hb

/-- **Order descent for the physical extended norm.**  For `r ≤ s`,
`‖z‖_{H^r} ≤ ‖z‖_{H^s}`; the `⊤` case is covered because the infimum over an
empty set of representing data is `⊤`. -/
theorem periodicSobolevENorm_mono_order {s r : ℝ} (h : r ≤ s) (z : SpatialField) :
    periodicSobolevENorm r z ≤ periodicSobolevENorm s z := by
  apply le_iInf
  intro A
  have hB : IsPeriodicDatum r z (torusOrderDown s r h A.1) :=
    persistence_datum_of_reweight A.2 (torusOrderDown_reweight s r h A.1)
  calc periodicSobolevENorm r z ≤ ‖torusOrderDown s r h A.1‖ₑ := iInf_le_of_le ⟨_, hB⟩ le_rfl
    _ ≤ ‖A.1‖ₑ := by
        rw [← ofReal_norm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (torusOrderDown_norm_le s r h A.1)

/-! ## 3. The running `H²` integral cap -/

/-- **The finite `ℝ≥0∞` criterion caps every running real `H²` integral.**
The horizon `T` of the local solution is arbitrary below `S`, and the cap
`(squaredHTwoIntegralT S u).toReal` does not depend on it — which is exactly
what makes the Grönwall bound uniform over the exhaustion of `[0,S)`.
Torus analogue of `Section4.A04.running_hTwo_integral_le`. -/
theorem running_hTwo_integral_le {ν T S : ℝ} {a : SpatialField} {f u : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) (hwu : w.velocity = u) (hTS : T ≤ S)
    (hfin : squaredHTwoIntegralT S u ≠ ⊤) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    (∫ r in (0 : ℝ)..t, torusSobolevNormAt 2 u r ^ 2) ≤ (squaredHTwoIntegralT S u).toReal := by
  have hc : ContinuousOn (fun r ↦ torusSobolevNormAt 2 u r ^ 2) (Icc (0 : ℝ) t) := by
    rw [← hwu]
    exact ((continuousOn_torusSobolevNormAt_velocity w 2).mono
      fun r hr ↦ ⟨hr.1, hr.2.trans_lt ht.2⟩).pow 2
  have hint : IntegrableOn (fun r ↦ torusSobolevNormAt 2 u r ^ 2) (Ioo (0 : ℝ) t) :=
    hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hle : ENNReal.ofReal (∫ r in (0 : ℝ)..t, torusSobolevNormAt 2 u r ^ 2) ≤
      squaredHTwoIntegralT S u := by
    rw [intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo,
      ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun r ↦ sq_nonneg _)]
    calc
      _ = ∫⁻ r in Ioo (0 : ℝ) t, periodicSobolevENorm 2 (fun x ↦ u (r, x)) ^ 2 := by
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro r hr
        obtain ⟨G, _, hd⟩ := w.sobolev 2
        have hn : periodicSobolevENorm 2 (fun x ↦ u (r, x)) ≠ ⊤ := by
          rw [← hwu]
          exact periodicSobolevENorm_ne_top_of_datum (hd r ⟨hr.1.le, hr.2.trans ht.2⟩)
        change ENNReal.ofReal (torusSobolevNormAt 2 u r ^ 2) = _
        rw [torusSobolevNormAt, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hn]
      _ ≤ squaredHTwoIntegralT S u :=
        lintegral_mono' (Measure.restrict_mono
          (Ioo_subset_Ioo le_rfl (ht.2.le.trans hTS)) le_rfl) le_rfl
  have hnn : 0 ≤ ∫ r in (0 : ℝ)..t, torusSobolevNormAt 2 u r ^ 2 :=
    intervalIntegral.integral_nonneg ht.1 fun r _ ↦ sq_nonneg _
  simpa only [ENNReal.toReal_ofReal hnn] using ENNReal.toReal_mono hfin hle

/-! ## 4. The forcing cap -/

/-- **Continuity and one `L¹_t H^m` cap for a torus test force.**  Lane 312's
`force_coefficient_path` supplies a continuous, compactly supported datum path at
every integer order, so the `H^m` profile of `f` is continuous on all of `ℝ` and
its running integral never exceeds the total mass. -/
theorem force_hm_profile_cap {f : SpaceTimeField} (hf : MemForceT f) (m : ℕ) :
    Continuous (fun s ↦ torusSobolevNormAt (m : ℝ) f s) ∧
      ∃ B : ℝ, 0 ≤ B ∧
        ∀ t : ℝ, 0 ≤ t → (∫ s in (0 : ℝ)..t, torusSobolevNormAt (m : ℝ) f s) ≤ B := by
  obtain ⟨G, hG, hc, hcs, _, _, _⟩ := force_coefficient_path hf m
  have heq : (fun s ↦ torusSobolevNormAt (m : ℝ) f s) = fun s ↦ ‖G s‖ := by
    funext s
    exact torusSobolevNormAt_eq (hG s)
  have hcn : Continuous fun s ↦ ‖G s‖ := hc.norm
  have hint : Integrable (fun s ↦ ‖G s‖) volume :=
    hcn.integrable_of_hasCompactSupport hcs.norm
  refine ⟨heq ▸ hcn, ∫ s, ‖G s‖, integral_nonneg fun s ↦ norm_nonneg _, ?_⟩
  intro t ht
  rw [heq, intervalIntegral.integral_of_le ht]
  exact setIntegral_le_integral hint (Filter.Eventually.of_forall fun s ↦ norm_nonneg _)

/-! ## 5. Coefficient-level pieces of `eq:Rhigh` -/

/-- The real pairing of two order-`s` data, read off the ambient complex `ℓ²`
inner product.  This is the `⟪·,·⟫_{H^s}` in which `eq:Rhigh` pairs the momentum
equation against `u`. -/
def torusRealPairing {s : ℝ} (A B : PeriodicSobolev s) : ℝ :=
  (inner ℂ A.1 B.1 : ℂ).re

/-- **The force term of `eq:Rhigh`, Cauchy–Schwarz.** -/
theorem torusRealPairing_le {s : ℝ} (A B : PeriodicSobolev s) :
    torusRealPairing A B ≤ ‖A‖ * ‖B‖ := by
  have h := re_inner_le_norm (𝕜 := ℂ) A.1 B.1
  have hre : RCLike.re (inner ℂ A.1 B.1 : ℂ) = (inner ℂ A.1 B.1 : ℂ).re := rfl
  have hA : ‖A‖ = ‖A.1‖ := rfl
  have hB : ‖B‖ = ‖B.1‖ := rfl
  rw [torusRealPairing, hA, hB, ← hre]
  exact h

/-- The unit-period derivative symbol `2πi kᵢ` is purely imaginary. -/
theorem periodicDerivativeSymbol_conj (i : Fin 3) (k : PeriodicFrequency) :
    conj (periodicDerivativeSymbol i k) = -periodicDerivativeSymbol i k := by
  simp [periodicDerivativeSymbol, Complex.ext_iff]

/-- The derivative symbol is odd in the frequency. -/
theorem periodicDerivativeSymbol_neg (i : Fin 3) (k : PeriodicFrequency) :
    periodicDerivativeSymbol i (-k) = -periodicDerivativeSymbol i k := by
  simp [periodicDerivativeSymbol]

/-- **The pressure term of `eq:Rhigh` drops, frequency by frequency.**
`appendix-a-local-theory.tex:141` "The pressure term vanishes by solenoidality".
No integration by parts: conjugating the coefficient-side solenoidality
`∑ⱼ 2πi kⱼ Â ⱼ(k) = 0` gives `∑ⱼ 2πi kⱼ conj(Â ⱼ(k)) = 0`, and the gradient datum
is exactly `2πi kᵢ q̂(k)`. -/
theorem torusPressureSymbol_drop {s : ℝ} {A : PeriodicSobolev s}
    (hA : IsSolenoidalPeriodicDatum A) (q : ℂ) (k : PeriodicFrequency) :
    ∑ i : Fin 3, conj (A.1 i k) * (periodicDerivativeSymbol i k * q) = 0 := by
  have hconj : ∀ j : Fin 3,
      conj (periodicDerivativeSymbol j k) = -periodicDerivativeSymbol j k :=
    fun j ↦ periodicDerivativeSymbol_conj j k
  have hs : ∑ j : Fin 3, periodicDerivativeSymbol j k * A.1 j k = 0 := hA k
  have hc : ∑ j : Fin 3, periodicDerivativeSymbol j k * conj (A.1 j k) = 0 := by
    have h0 : conj (∑ j : Fin 3, periodicDerivativeSymbol j k * A.1 j k) = 0 := by
      rw [hs, map_zero]
    rw [map_sum] at h0
    have h1 : ∑ j : Fin 3, conj (periodicDerivativeSymbol j k * A.1 j k) =
        -∑ j : Fin 3, periodicDerivativeSymbol j k * conj (A.1 j k) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [map_mul, hconj j]
      ring
    rw [h1] at h0
    exact neg_eq_zero.mp h0
  calc ∑ i : Fin 3, conj (A.1 i k) * (periodicDerivativeSymbol i k * q)
      = q * ∑ i : Fin 3, periodicDerivativeSymbol i k * conj (A.1 i k) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ = 0 := by rw [hc, mul_zero]

/-- **The pressure term of `eq:Rhigh` drops.**  `A` is the order-`s` datum of a
solenoidal velocity slice and `P` the order-`s` datum of a gradient with scalar
symbol `q`; then the `H^s` pairing is zero. -/
theorem torusPressureDrop {s : ℝ} {A P : PeriodicSobolev s}
    (hA : IsSolenoidalPeriodicDatum A) (q : PeriodicFrequency → ℂ)
    (hP : ∀ (i : Fin 3) (k : PeriodicFrequency),
      P.1 i k = periodicDerivativeSymbol i k * q k) :
    torusRealPairing A P = 0 := by
  have hcomp : ∀ i : Fin 3,
      (inner ℂ (A.1 i) (P.1 i) : ℂ) = ∑' k, conj (A.1 i k) * P.1 i k := by
    intro i
    rw [lp.inner_eq_tsum]
    exact tsum_congr fun k ↦ RCLike.inner_apply' _ _
  have hsum : ∀ i : Fin 3, Summable fun k ↦ conj (A.1 i k) * P.1 i k := by
    intro i
    have hsi := lp.summable_inner (𝕜 := ℂ) (A.1 i) (P.1 i)
    refine hsi.congr fun k ↦ ?_
    exact RCLike.inner_apply' _ _
  have hzero : (inner ℂ A.1 P.1 : ℂ) = 0 := by
    rw [PiLp.inner_apply]
    have : ∑ i : Fin 3, (inner ℂ (A.1 i) (P.1 i) : ℂ) =
        ∑' k : PeriodicFrequency, ∑ i : Fin 3, conj (A.1 i k) * P.1 i k := by
      rw [Summable.tsum_finsetSum fun i _ ↦ hsum i]
      exact Finset.sum_congr rfl fun i _ ↦ hcomp i
    rw [this]
    have hk : ∀ k : PeriodicFrequency, ∑ i : Fin 3, conj (A.1 i k) * P.1 i k = 0 := by
      intro k
      have := torusPressureSymbol_drop hA (q k) k
      refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) this
      rw [hP i k]
    simp [hk]
  rw [torusRealPairing, hzero, Complex.zero_re]

/-- **The dissipation term of `eq:Rhigh`, frequency by frequency.**  If `L` is
the order-`s` datum of `Δu` — coefficient symbol `−|2πk|²` — then the pairing
against the velocity datum is `−|2πk|² ∑ᵢ |û ᵢ(k)|²` at every frequency. -/
theorem torusLaplacianSymbol_pairing {s : ℝ} (A L : PeriodicSobolev s)
    (hL : ∀ (i : Fin 3) (k : PeriodicFrequency),
      L.1 i k = -(periodicAngularFrequencySq k : ℂ) * A.1 i k)
    (k : PeriodicFrequency) :
    (∑ i : Fin 3, conj (A.1 i k) * L.1 i k) =
      ((-(periodicAngularFrequencySq k) * ∑ i : Fin 3, ‖A.1 i k‖ ^ 2 : ℝ) : ℂ) := by
  have hterm : ∀ i : Fin 3, conj (A.1 i k) * L.1 i k =
      ((-(periodicAngularFrequencySq k) * ‖A.1 i k‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [hL i k]
    have hmc : conj (A.1 i k) * A.1 i k = ((‖A.1 i k‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.conj_mul']
      norm_cast
    calc conj (A.1 i k) * (-(periodicAngularFrequencySq k : ℂ) * A.1 i k)
        = -(periodicAngularFrequencySq k : ℂ) * (conj (A.1 i k) * A.1 i k) := by ring
      _ = ((-(periodicAngularFrequencySq k) * ‖A.1 i k‖ ^ 2 : ℝ) : ℂ) := by
          rw [hmc]; push_cast; ring
  rw [Finset.sum_congr rfl fun i _ ↦ hterm i]
  push_cast
  rw [Finset.mul_sum]

/-- The dissipation pairing is nonpositive at every frequency. -/
theorem torusLaplacianSymbol_nonpos {s : ℝ} (A L : PeriodicSobolev s)
    (hL : ∀ (i : Fin 3) (k : PeriodicFrequency),
      L.1 i k = -(periodicAngularFrequencySq k : ℂ) * A.1 i k)
    (k : PeriodicFrequency) :
    (∑ i : Fin 3, conj (A.1 i k) * L.1 i k).re ≤ 0 := by
  rw [torusLaplacianSymbol_pairing A L hL k, Complex.ofReal_re]
  have h1 : 0 ≤ periodicAngularFrequencySq k := angularFrequencySq_nonneg k
  have h2 : 0 ≤ ∑ i : Fin 3, ‖A.1 i k‖ ^ 2 :=
    Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  nlinarith

/-! ## 6. Young's absorption and the Grönwall chain -/

/-- **Young's absorption**, pure real arithmetic
(`appendix-a-local-theory.tex:139-140`).  From
`½ d + ν g² ≤ C · a · n · g + F · n` absorb the cross term into the dissipation:
`½ d ≤ (C²/(4ν)) a² n² + F · n`.  The nonnegativity of `(2νg − Can)²/(4ν)` is the
whole content.  Same statement as `Section4.A04.young_high_real`, reproved so
that Section 3 does not import the whole-space energy chain. -/
theorem torusYoungAbsorb {d g a n F ν C : ℝ} (hν : 0 < ν)
    (h : (1 / 2) * d + ν * g ^ 2 ≤ C * a * n * g + F * n) :
    (1 / 2) * d ≤ C ^ 2 / (4 * ν) * a ^ 2 * n ^ 2 + F * n := by
  have h4ν : (0 : ℝ) < 4 * ν := by linarith
  have key : 0 ≤ ν * g ^ 2 + C ^ 2 / (4 * ν) * a ^ 2 * n ^ 2 - C * a * n * g := by
    have expand : ν * g ^ 2 + C ^ 2 / (4 * ν) * a ^ 2 * n ^ 2 - C * a * n * g
        = (2 * ν * g - C * a * n) ^ 2 / (4 * ν) := by
      field_simp
      ring
    rw [expand]
    exact div_nonneg (sq_nonneg _) h4ν.le
  linarith

/-- **`eq:Rhigh → eq:highcontinuation → Grönwall`, on the real profiles.**

`y` is `‖u(·)‖_{H^m}`, `a` is `‖u(·)‖_{H²}`, `b` is `‖f(·)‖_{H^m}`.  From the
differential inequality `hR` at interior times, Young's absorption
(`torusYoungAbsorb`) gives `½(y²)' ≤ C_{m,ν} a² y² + b y`; the `ζ↓0` integral
form `Section4.A04.sqrt_le_primitive_linear` turns that into
`y t ≤ y 0 + ∫₀ᵗ (C_{m,ν} a² y + b)` — the step that survives the limit even
where `y` vanishes — and the variable-coefficient Grönwall bound
`Section4.A01.gronwall_bddAbove_Ico` closes with the two uniform caps. -/
theorem torusGronwallChain {T₀ C ν Kbnd Bbnd : ℝ} {y a b : ℝ → ℝ} (hν : 0 < ν)
    (hy : ContinuousOn y (Ico 0 T₀)) (hynn : ∀ t, 0 ≤ y t)
    (ha : ContinuousOn a (Ico 0 T₀)) (hb : ContinuousOn b (Ico 0 T₀))
    (hbnn : ∀ t, 0 ≤ b t)
    (hkbnd : ∀ t ∈ Ico 0 T₀, (∫ s in (0 : ℝ)..t, a s ^ 2) ≤ Kbnd)
    (hbbnd : ∀ t ∈ Ico 0 T₀, (∫ s in (0 : ℝ)..t, b s) ≤ Bbnd)
    (hR : ∀ t ∈ Ioo (0 : ℝ) T₀, ∃ d g : ℝ, 0 ≤ g ∧
      HasDerivAt (fun r ↦ y r ^ 2) d t ∧
      (1 / 2) * d + ν * g ^ 2 ≤ C * a t * y t * g + b t * y t) :
    ∀ t ∈ Ico (0 : ℝ) T₀, y t ≤ (y 0 + Bbnd) * Real.exp (C ^ 2 / (4 * ν) * Kbnd) := by
  set Cg : ℝ := C ^ 2 / (4 * ν) with hCg
  have hCgnn : 0 ≤ Cg := by
    rw [hCg]
    positivity
  have hR' : ∀ t : ℝ, ∃ d : ℝ, t ∈ Ioo (0 : ℝ) T₀ →
      HasDerivAt (fun r ↦ y r ^ 2) d t ∧
        (1 / 2) * d ≤ Cg * a t ^ 2 * y t ^ 2 + b t * y t := by
    intro t
    by_cases ht : t ∈ Ioo (0 : ℝ) T₀
    · obtain ⟨d, g, _, hdd, hineq⟩ := hR t ht
      exact ⟨d, fun _ ↦ ⟨hdd, torusYoungAbsorb hν hineq⟩⟩
    · exact ⟨0, fun h ↦ absurd h ht⟩
  choose E' hE' using hR'
  have hstep : ∀ t ∈ Ico (0 : ℝ) T₀,
      y t ≤ y 0 + ∫ s in (0 : ℝ)..t, (Cg * a s ^ 2 * y s + b s) := by
    intro t ht
    have hsub : Icc (0 : ℝ) t ⊆ Ico (0 : ℝ) T₀ := fun x hx ↦ ⟨hx.1, hx.2.trans_lt ht.2⟩
    have hsubo : Ioo (0 : ℝ) t ⊆ Ioo (0 : ℝ) T₀ := fun x hx ↦ ⟨hx.1, hx.2.trans ht.2⟩
    have hmain := NSFormalization.Section4.A04.sqrt_le_primitive_linear
      (E := fun r ↦ y r ^ 2) (E' := E') (K := fun s ↦ Cg * a s ^ 2) (b := b)
      ht.1 ((hy.mono hsub).pow 2)
      (continuousOn_const.mul ((ha.mono hsub).pow 2)) (hb.mono hsub)
      (fun r _ ↦ sq_nonneg _)
      (fun r _ ↦ mul_nonneg hCgnn (sq_nonneg _)) (fun r _ ↦ hbnn r)
      (fun r hr ↦ (hE' r (hsubo hr)).1)
      (fun r hr ↦ by
        have h2 := (hE' r (hsubo hr)).2
        rw [Real.sqrt_sq (hynn r)]
        nlinarith [h2])
      t ⟨ht.1, le_rfl⟩
    rw [Real.sqrt_sq (hynn 0), Real.sqrt_sq (hynn t)] at hmain
    calc y t ≤ y 0 + ∫ s in (0 : ℝ)..t, (Cg * a s ^ 2 * Real.sqrt (y s ^ 2) + b s) := hmain
      _ = y 0 + ∫ s in (0 : ℝ)..t, (Cg * a s ^ 2 * y s + b s) := by
          congr 1
          refine intervalIntegral.integral_congr fun s _ ↦ ?_
          simp [Real.sqrt_sq (hynn s)]
  exact NSFormalization.Section4.A01.gronwall_bddAbove_Ico
    (Cgron := Cg) (Kbnd := Kbnd) (Bbnd := Bbnd) (y := y) (k := fun s ↦ a s ^ 2) (b := b)
    hCgnn (hynn 0) hy (ha.pow 2) hb (fun _ _ ↦ sq_nonneg _) (fun t _ ↦ hbnn t)
    hkbnd hbbnd hstep

/-! ## 7. The target field, from the periodic `eq:Rhigh` -/

/-- **`PeriodicContinuationAPI.higherOrderBound`, verbatim, from the periodic
`eq:Rhigh`.**

The conclusion is the field of `research/T11/probes/api_on_canonical.lean:112-121`
token for token.  The single hypothesis `hRhigh` is the manuscript's
`eq:Rhigh` (`appendix-a-local-theory.tex:127-138`) on one
`ClassicalSolutionT`, with the dissipation norm `‖∇u(t)‖_{H^m}` carried by the
existentially quantified nonnegative `g` (module docstring, "Shape note").
`Chigh m` is the manuscript's `C_m`; the Grönwall constant it produces is
`C_{m,ν} = C_m²/(4ν)` (`torusYoungAbsorb`), as in Section 4.

Everything between `hRhigh` and the conclusion is proved here: Young's
absorption, the `ζ↓0` integral form, the variable-coefficient Grönwall bound,
the uniform `H²` cap extracted from `squaredHTwoIntegralT S u ≠ ⊤`, the uniform
`L¹_t H^m` forcing cap, and the order descent that covers `m < 3`.

The bound is uniform over the exhaustion of `[0,S)`: the local solution
`w` produced by `SolvesBelowT` at each time depends on `t`, but the three
constants `‖u(0)‖_{H^n}`, the forcing cap and `(squaredHTwoIntegralT S u).toReal`
do not. -/
theorem higherOrderBound_of_energyInequality
    (Chigh : ℕ → ℝ)
    (hRhigh : ∀ (ν : ℝ), 0 < ν → ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T) (m : ℕ), 3 ≤ m →
          ∀ t ∈ Ioo (0 : ℝ) T, ∃ d g : ℝ, 0 ≤ g ∧
            HasDerivAt (fun r ↦ torusSobolevNormAt (m : ℝ) w.velocity r ^ 2) d t ∧
            (1 / 2) * d + ν * g ^ 2 ≤
              Chigh m * torusSobolevNormAt 2 w.velocity t *
                  torusSobolevNormAt (m : ℝ) w.velocity t * g +
                torusSobolevNormAt (m : ℝ) f t * torusSobolevNormAt (m : ℝ) w.velocity t) :
    ∀ (ν : ℝ), 0 < ν →
      ∀ (a : SpatialField), a ∈ initialClassT →
        ∀ (f : SpaceTimeField), f ∈ forceClassT →
          ∀ (S : ℝ), 0 < S →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
                ∀ m : ℕ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
                  ∀ t ∈ Ico (0 : ℝ) S,
                    periodicSobolevENorm (m : ℝ) (fun x ↦ u (t, x)) ≤ M := by
  intro ν hν a ha f hf S _hS u p hu hfin m
  set n : ℕ := max m 3 with hnd
  have h3n : 3 ≤ n := le_max_right m 3
  have hmn : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_max_left m 3
  obtain ⟨hfc, B, _hB0, hBcap⟩ := force_hm_profile_cap (hf : MemForceT f) n
  refine ⟨ENNReal.ofReal ((torusSobolevNormAt (n : ℝ) u 0 + B) *
      Real.exp (Chigh n ^ 2 / (4 * ν) * (squaredHTwoIntegralT S u).toReal)),
    ENNReal.ofReal_ne_top, ?_⟩
  intro t ht
  obtain ⟨w, hwv, _⟩ := hu ((t + S) / 2) (by linarith [ht.1]) (by linarith [ht.2])
  have htb : t ∈ Ico (0 : ℝ) ((t + S) / 2) := ⟨ht.1, by linarith [ht.2]⟩
  have hbS : (t + S) / 2 ≤ S := by linarith [ht.2]
  have hchain := torusGronwallChain (T₀ := (t + S) / 2) (C := Chigh n) (ν := ν)
    (Kbnd := (squaredHTwoIntegralT S u).toReal) (Bbnd := B)
    (y := fun r ↦ torusSobolevNormAt (n : ℝ) w.velocity r)
    (a := fun r ↦ torusSobolevNormAt 2 w.velocity r)
    (b := fun r ↦ torusSobolevNormAt (n : ℝ) f r)
    hν
    (continuousOn_torusSobolevNormAt_velocity w n)
    (fun r ↦ torusSobolevNormAt_nonneg _ _ _)
    (continuousOn_torusSobolevNormAt_velocity w 2)
    hfc.continuousOn
    (fun r ↦ torusSobolevNormAt_nonneg _ _ _)
    (fun r hr ↦ by
      have hrun := running_hTwo_integral_le w hwv hbS hfin hr
      rw [hwv]
      exact hrun)
    (fun r hr ↦ hBcap r hr.1)
    (fun r hr ↦ hRhigh ν hν a ha f hf ((t + S) / 2) w n h3n r hr)
    t htb
  obtain ⟨G, _, hd⟩ := w.sobolev n
  have hdat : IsPeriodicDatum (n : ℝ) (fun x ↦ u (t, x)) (G t) := by
    rw [← hwv]
    exact hd t htb
  calc periodicSobolevENorm (m : ℝ) (fun x ↦ u (t, x))
      ≤ periodicSobolevENorm (n : ℝ) (fun x ↦ u (t, x)) :=
        periodicSobolevENorm_mono_order hmn _
    _ = ENNReal.ofReal (torusSobolevNormAt (n : ℝ) u t) := by
        rw [torusSobolevNormAt,
          ENNReal.ofReal_toReal (periodicSobolevENorm_ne_top_of_datum hdat)]
    _ ≤ ENNReal.ofReal ((torusSobolevNormAt (n : ℝ) u 0 + B) *
          Real.exp (Chigh n ^ 2 / (4 * ν) * (squaredHTwoIntegralT S u).toReal)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hwv] at hchain
        exact hchain

/-! ## 8. Non-vacuity -/

/-- The order-descent inequality is not vacuous: at a nonzero constant field both
sides are finite and the inequality is a genuine comparison of two finite
numbers. -/
example (c : Space) :
    periodicSobolevENorm 1 (fun _ ↦ c) ≤ periodicSobolevENorm 5 (fun _ ↦ c) ∧
      periodicSobolevENorm 5 (fun _ ↦ c) ≠ ⊤ :=
  ⟨periodicSobolevENorm_mono_order (by norm_num) _,
    periodicSobolevENorm_ne_top_smooth 5 contDiff_const fun _ _ ↦ rfl⟩

/-- The Grönwall chain is not vacuous at a nowhere-vanishing profile: `y = exp`,
zero `H²` driver, forcing `exp`, `ν = 1`, `C = 0` satisfies `eq:Rhigh` with
`g = 0` at every interior time and the chain returns a finite bound. -/
example {T₀ : ℝ} (hT : 0 < T₀) :
    (0 : ℝ) ∈ Ico (0 : ℝ) T₀ ∧
      ∀ t ∈ Ico (0 : ℝ) T₀,
        Real.exp t ≤ (Real.exp 0 + Real.exp T₀) *
          Real.exp ((0 : ℝ) ^ 2 / (4 * 1) * 0) := by
  refine ⟨⟨le_rfl, hT⟩, ?_⟩
  refine torusGronwallChain (T₀ := T₀) (C := 0) (ν := 1) (Kbnd := 0)
    (Bbnd := Real.exp T₀) (y := Real.exp) (a := fun _ ↦ 0) (b := Real.exp)
    one_pos Real.continuous_exp.continuousOn (fun t ↦ (Real.exp_pos t).le)
    continuousOn_const Real.continuous_exp.continuousOn (fun t ↦ (Real.exp_pos t).le)
    (fun r _ ↦ by simp) (fun r hr ↦ ?_) (fun r hr ↦ ?_)
  · rw [integral_exp]
    have h1 : Real.exp r ≤ Real.exp T₀ := Real.exp_le_exp.mpr hr.2.le
    have h2 : (0 : ℝ) < Real.exp 0 := Real.exp_pos 0
    linarith
  · refine ⟨2 * Real.exp r ^ 1 * Real.exp r, 0, le_rfl,
      (Real.hasDerivAt_exp r).pow 2, ?_⟩
    have : Real.exp r ^ 1 = Real.exp r := pow_one _
    rw [this]
    ring_nf
    linarith [Real.exp_pos r]

end NSFormalization.Section3.T11
