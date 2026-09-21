import NSFormalization.Section3.T15.Convergence
import NSFormalization.Section3.T15.Mixed
import NSFormalization.Section3.T18.SobolevRate
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! # Negative-order Fourier estimates for T15 U14b

The canonical `q = 2` limit holds for every order below `-1/2`.
Sharp lattice summability gives an `L¹` spatial bound below `-3/2`;
Fourier and time Hölder interpolation combine its positive scaling with
Parseval's order-zero scaling. The final theorem includes both canonical
values of the time exponent.
-/
noncomputable section
namespace NSFormalization.Section3.T15
open NSFormalization.Section3.T10
open Set Filter MeasureTheory
open NSFormalization.Section4.A02 (forceTimeMeasure)
open NavierStokes.ProblemStatement
open scoped ContDiff ENNReal Topology
open scoped BigOperators

/-- The one-dimensional Bessel weight is summable below order `-1/2`. -/
theorem summable_coordinate_rpow {a : ℝ} (ha : a < -(1 : ℝ) / 2) :
    Summable (fun n : ℤ ↦ (1 + (n : ℝ)^2) ^ a) := by
  have hp := Real.summable_abs_int_rpow (by linarith : 1 < -(2 * a))
  have hz : Summable (fun n : ℤ ↦ if n = 0 then (1 : ℝ) else 0) :=
    (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  apply (hz.add hp).of_nonneg_of_le
  · intro n
    positivity
  · intro n
    by_cases hn : n = 0
    · subst n
      simp only [Int.cast_zero, sq, mul_zero, add_zero, Real.one_rpow, ite_true, abs_zero, neg_neg]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (by norm_num) _)
    · simp only [ite_eq_right hn, zero_add, neg_neg]
      have habs : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
      calc
        (1 + (n : ℝ)^2) ^ a ≤ ((n : ℝ)^2) ^ a :=
          Real.rpow_le_rpow_of_nonpos (sq_pos_of_ne_zero (by exact_mod_cast hn))
            (by linarith) (by linarith)
        _ = |(n : ℝ)| ^ (2 * a) := by
          rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul habs.le]
          norm_num

/-- Every coordinate Bessel weight is bounded by the three-dimensional weight. -/
theorem coordinate_weight_le_periodic (k : PeriodicFrequency) (i : Fin 3) :
    1 + (k i : ℝ)^2 ≤ periodicFrequencyWeight k := by
  have hsum := Finset.single_le_sum (f := fun j : Fin 3 ↦ (k j : ℝ)^2)
    (fun j _ ↦ sq_nonneg _) (Finset.mem_univ i)
  have hn : 0 ≤ ∑ j : Fin 3, (k j : ℝ)^2 :=
    Finset.sum_nonneg fun j _ ↦ sq_nonneg _
  unfold periodicFrequencyWeight
  have hp : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
  nlinarith [mul_nonneg (sub_nonneg.mpr hp) hn]

/-- Sharp summability of negative powers of the canonical torus weight. -/
theorem summable_periodicWeight_rpow {s : ℝ} (hs : s < -(3 : ℝ) / 2) :
    Summable (fun k : PeriodicFrequency ↦ periodicFrequencyWeight k ^ s) := by
  have ha := summable_coordinate_rpow (show s / 3 < -(1 : ℝ) / 2 by linarith)
  have hn : ∀ n : ℤ, 0 ≤ (1 + (n : ℝ)^2) ^ (s / 3) := fun n ↦ by positivity
  have hab := ha.mul_of_nonneg ha hn hn
  have habc := hab.mul_of_nonneg ha (fun n ↦ mul_nonneg (hn n.1) (hn n.2)) hn
  have hi : Function.Injective (fun k : PeriodicFrequency ↦ ((k 0, k 1), k 2)) := by
    intro k l h
    have h0 := congrArg (fun p : (ℤ × ℤ) × ℤ ↦ p.1.1) h
    have h1 := congrArg (fun p : (ℤ × ℤ) × ℤ ↦ p.1.2) h
    have h2 := congrArg (fun p : (ℤ × ℤ) × ℤ ↦ p.2) h
    funext i
    fin_cases i <;> assumption
  apply (habc.comp_injective hi).of_nonneg_of_le
  · intro k
    exact Real.rpow_nonneg (by
      have := coordinate_weight_le_periodic k 0
      nlinarith [sq_nonneg (k 0 : ℝ)]) _
  · intro k
    have hw : 0 < periodicFrequencyWeight k := by
      have := coordinate_weight_le_periodic k 0
      nlinarith [sq_nonneg (k 0 : ℝ)]
    have hb (i : Fin 3) : periodicFrequencyWeight k ^ (s / 3) ≤
        (1 + (k i : ℝ)^2) ^ (s / 3) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (coordinate_weight_le_periodic k i)
        (by linarith)
    calc
      periodicFrequencyWeight k ^ s =
          periodicFrequencyWeight k ^ (s / 3) * periodicFrequencyWeight k ^ (s / 3) *
            periodicFrequencyWeight k ^ (s / 3) := by
        rw [← Real.rpow_add hw, ← Real.rpow_add hw]
        congr 1
        ring
      _ ≤ _ := mul_le_mul (mul_le_mul (hb 0) (hb 1) (by positivity) (by positivity))
        (hb 2) (by positivity) (by positivity)

/-- The negative-order Fourier energy is controlled by the square of the spatial
`L¹` norm, with a finite scale-independent weight sum. -/
theorem negative_fourier_energy_le {s : ℝ} (hs : s < -(3 : ℝ) / 2)
    (g : NavierStokes.ProblemStatement.Space → ℂ) :
    (∑' k : PeriodicFrequency, periodicFrequencyWeight k ^ s *
      ‖periodicFourierCoeff g k‖ ^ 2) ≤
    (∑' k : PeriodicFrequency, periodicFrequencyWeight k ^ s) *
      (∫ y, ‖torusLift g y‖ ∂periodicTorusMeasure) ^ 2 := by
  have hw (k : PeriodicFrequency) : 0 ≤ periodicFrequencyWeight k ^ s := by
    have h := coordinate_weight_le_periodic k 0
    exact Real.rpow_nonneg (by nlinarith [sq_nonneg (k 0 : ℝ)]) _
  have hb (k : PeriodicFrequency) : periodicFrequencyWeight k ^ s *
      ‖periodicFourierCoeff g k‖ ^ 2 ≤ periodicFrequencyWeight k ^ s *
        (∫ y, ‖torusLift g y‖ ∂periodicTorusMeasure) ^ 2 :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_periodicFourierCoeff_le g k) 2) (hw k)
  have hmajor := (summable_periodicWeight_rpow hs).mul_right
    ((∫ y, ‖torusLift g y‖ ∂periodicTorusMeasure) ^ 2)
  have hminor := hmajor.of_nonneg_of_le
    (fun k ↦ mul_nonneg (hw k) (sq_nonneg _)) hb
  exact (hminor.tsum_le_tsum hb hmajor).trans_eq (tsum_mul_right)

/-- Hölder interpolation of two summable nonnegative coefficient energies. -/
theorem tsum_energy_interpolation {ι : Type*} {a b : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hsa : Summable a) (hsb : Summable b)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    (∑' i, (a i) ^ θ * (b i) ^ (1 - θ)) ≤
      (∑' i, a i) ^ θ * (∑' i, b i) ^ (1 - θ) := by
  have heqa (i : ι) : (a i ^ θ) ^ θ⁻¹ = a i := by
    rw [← Real.rpow_mul (ha i), mul_inv_cancel₀ hθ.ne', Real.rpow_one]
  have heqb (i : ι) : (b i ^ (1 - θ)) ^ (1 - θ)⁻¹ = b i := by
    rw [← Real.rpow_mul (hb i), mul_inv_cancel₀ (by linarith : 1 - θ ≠ 0),
      Real.rpow_one]
  have H := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg
    (Real.HolderConjugate.inv_one_sub_inv hθ hθ1)
    (fun i ↦ Real.rpow_nonneg (ha i) θ)
    (fun i ↦ Real.rpow_nonneg (hb i) (1 - θ))
    (hsa.congr fun i ↦ (heqa i).symm) (hsb.congr fun i ↦ (heqb i).symm)
  simpa only [heqa, heqb, one_div, inv_inv] using H

/-- Smooth torus data at sufficiently negative order are bounded by their
physical `L¹` norm. The factor `3` only accounts for the three components. -/
theorem norm_datum_le_L1 {s : ℝ} (hs : s < -(3 : ℝ) / 2)
    {z : Space → Space} (hz : ContDiff ℝ ∞ z)
    {A : PeriodicSobolev s} (hA : IsPeriodicDatum s z A) :
    ‖A‖ ≤ Real.sqrt (3 * ∑' k : PeriodicFrequency, periodicFrequencyWeight k ^ s) *
      (∫ y, ‖torusLift z y‖ ∂periodicTorusMeasure) := by
  let L := ∫ y, ‖torusLift z y‖ ∂periodicTorusMeasure
  let C := ∑' k : PeriodicFrequency, periodicFrequencyWeight k ^ s
  have hL : 0 ≤ L := integral_nonneg fun _ ↦ norm_nonneg _
  have hC : 0 ≤ C := tsum_nonneg fun k ↦ Real.rpow_nonneg (by
    have := coordinate_weight_le_periodic k 0
    nlinarith [sq_nonneg (k 0 : ℝ)]) _
  have hb (i : Fin 3) :
      NSFormalization.Paper1.periodicSobolevSq s (fun x ↦ (z x i : ℂ)) ≤ C * L ^ 2 := by
    have hi : (∫ y, ‖torusLift (fun x ↦ (z x i : ℂ)) y‖ ∂periodicTorusMeasure) ≤ L := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
        hA.2.1.norm
      exact Filter.Eventually.of_forall fun y ↦ by
        change ‖((torusLift z y) i : ℂ)‖ ≤ ‖torusLift z y‖
        simpa only [Complex.norm_real, Real.norm_eq_abs] using
          NSFormalization.Section3.T13.abs_spaceCoord_le_norm (torusLift z y) i
    have he := negative_fourier_energy_le hs (fun x ↦ (z x i : ℂ))
    have he' : NSFormalization.Paper1.periodicSobolevSq s (fun x ↦ (z x i : ℂ)) ≤
        C * (∫ y, ‖torusLift (fun x ↦ (z x i : ℂ)) y‖ ∂periodicTorusMeasure) ^ 2 := by
      simpa only [C, NSFormalization.Paper1.periodicSobolevSq,
        periodicFrequencyWeight_eq_paper1] using he
    exact he'.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (integral_nonneg fun _ ↦ norm_nonneg _) hi 2) hC)
  change ‖A.1‖ ≤ _
  rw [NSFormalization.Section3.T17.norm_datum_eq_sqrt s hz hA]
  calc
    _ ≤ Real.sqrt (3 * C * L ^ 2) := Real.sqrt_le_sqrt (by
      simpa [Finset.sum_const, mul_assoc] using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3))) (fun i _ ↦ hb i))
    _ = Real.sqrt (3 * C) * L := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hL]

/-- All component Fourier energies form a summable sequence on the product index. -/
theorem summable_vector_energy (r : ℝ) {z : Space → Space}
    (hz : ContDiff ℝ ∞ z) (hp : IsPeriodicSpatial z) :
    Summable (fun j : Fin 3 × PeriodicFrequency ↦ periodicFrequencyWeight j.2 ^ r *
      ‖periodicFourierCoeff (fun x ↦ (z x j.1 : ℂ)) j.2‖ ^ 2) := by
  apply (summable_prod_of_nonneg (fun j ↦ mul_nonneg (Real.rpow_nonneg (by
    have := coordinate_weight_le_periodic j.2 0
    nlinarith [sq_nonneg (j.2 0 : ℝ)]) _) (sq_nonneg _))).2
  constructor
  · intro i
    exact summable_weighted_periodicFourierCoeff
      (fun x j ↦ congrArg (fun v : Space ↦ (v i : ℂ)) (hp x j))
      (Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hz)) r
  · exact (hasSum_fintype _).summable

/-- The canonical datum norm squared is the sum of all component energies. -/
theorem datum_norm_sq_eq_energy {r : ℝ} {z : Space → Space}
    (hz : ContDiff ℝ ∞ z) {A : PeriodicSobolev r} (hA : IsPeriodicDatum r z A) :
    ‖A‖ ^ 2 = ∑' j : Fin 3 × PeriodicFrequency, periodicFrequencyWeight j.2 ^ r *
      ‖periodicFourierCoeff (fun x ↦ (z x j.1 : ℂ)) j.2‖ ^ 2 := by
  rw [(summable_vector_energy r hz hA.1).tsum_prod, tsum_fintype]
  change ‖A.1‖ ^ 2 = _
  rw [NSFormalization.Section3.T17.norm_datum_eq_sqrt r hz hA,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ ↦
      NSFormalization.Section3.T17.periodicSobolevSq_nonneg r _)]
  simp only [NSFormalization.Paper1.periodicSobolevSq, periodicFrequencyWeight_eq_paper1]

/-- Interpolation of genuine Fourier data between a real order and order zero. -/
theorem norm_datum_interpolation {r θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    {z : Space → Space} (hz : ContDiff ℝ ∞ z)
    {A : PeriodicSobolev ((1 - θ) * r)} {B : PeriodicSobolev 0} {D : PeriodicSobolev r}
    (hA : IsPeriodicDatum ((1 - θ) * r) z A)
    (hB : IsPeriodicDatum 0 z B) (hD : IsPeriodicDatum r z D) :
    ‖A‖ ≤ ‖B‖ ^ θ * ‖D‖ ^ (1 - θ) := by
  let e (a : ℝ) (j : Fin 3 × PeriodicFrequency) := periodicFrequencyWeight j.2 ^ a *
    ‖periodicFourierCoeff (fun x ↦ (z x j.1 : ℂ)) j.2‖ ^ 2
  have hn (a : ℝ) (j : Fin 3 × PeriodicFrequency) : 0 ≤ e a j := by
    apply mul_nonneg _ (sq_nonneg _)
    apply Real.rpow_nonneg
    have := coordinate_weight_le_periodic j.2 0
    nlinarith [sq_nonneg (j.2 0 : ℝ)]
  have he (j : Fin 3 × PeriodicFrequency) : e ((1 - θ) * r) j =
      (e 0 j) ^ θ * (e r j) ^ (1 - θ) := by
    have hw : 0 ≤ periodicFrequencyWeight j.2 := by
      have := coordinate_weight_le_periodic j.2 0
      nlinarith [sq_nonneg (j.2 0 : ℝ)]
    dsimp [e]
    rw [Real.rpow_zero, one_mul, Real.mul_rpow (Real.rpow_nonneg hw _) (sq_nonneg _),
      ← Real.rpow_mul hw]
    rw [mul_left_comm, ← Real.rpow_add_of_nonneg (sq_nonneg _) hθ.le (by linarith),
      show θ + (1 - θ) = 1 by ring, Real.rpow_one, mul_comm r (1 - θ)]
  have hi := tsum_energy_interpolation (hn 0) (hn r)
    (summable_vector_energy 0 hz hA.1) (summable_vector_energy r hz hA.1) hθ hθ1
  have hsq : ‖A‖ ^ 2 ≤ (‖B‖ ^ 2) ^ θ * (‖D‖ ^ 2) ^ (1 - θ) := by
    rw [datum_norm_sq_eq_energy hz hA, datum_norm_sq_eq_energy hz hB,
      datum_norm_sq_eq_energy hz hD]
    simpa only [← he] using hi
  have hh := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (by positivity)] at hh
  have heq (x a : ℝ) (hx : 0 ≤ x) : Real.sqrt ((x ^ 2) ^ a) = x ^ a := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx, ← Real.rpow_mul hx]
    congr 1
    push_cast
    ring
  simpa only [heq _ _ (norm_nonneg _)] using hh

/-- Weighted Hölder for the actual `L²` time norm. -/
theorem eLpNorm_two_interpolation {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a b : α → ℝ} (ha : AEMeasurable a μ) (hb : AEMeasurable b μ)
    (ha0 : ∀ t, 0 ≤ a t) (hb0 : ∀ t, 0 ≤ b t)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    eLpNorm (fun t ↦ a t ^ θ * b t ^ (1 - θ)) 2 μ ≤
      eLpNorm a 2 μ ^ θ * eLpNorm b 2 μ ^ (1 - θ) := by
  have hns : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  simp only [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤), ENNReal.toReal_ofNat]
  have hi := ENNReal.lintegral_mul_norm_pow_le
    ((ha.ennreal_ofReal).pow_const 2) ((hb.ennreal_ofReal).pow_const 2)
    hθ hns (by ring : θ + (1 - θ) = 1)
  have hh := ENNReal.rpow_le_rpow hi (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.rpow_mul] at hh
  simp only [Real.enorm_eq_ofReal (mul_nonneg (Real.rpow_nonneg (ha0 _) _)
      (Real.rpow_nonneg (hb0 _) _)),
    ENNReal.ofReal_mul (Real.rpow_nonneg (ha0 _) _),
    ← ENNReal.ofReal_rpow_of_nonneg (ha0 _) hθ,
    ← ENNReal.ofReal_rpow_of_nonneg (hb0 _) hns,
    Real.enorm_eq_ofReal (ha0 _), Real.enorm_eq_ofReal (hb0 _),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), ← ENNReal.rpow_mul]
  simp only [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at hh
  convert hh using 1 <;> congr 1 <;> ring_nf

/-- Interpolation of the canonical infimum-over-paths time norms. -/
theorem forceNorm_interpolation {F : Section4.A02.SpaceTimeField} (hF : MemForceT F)
    {r θ : ℝ} (hr : r ≤ 0) (hθ : 0 < θ) (hθ1 : θ < 1) :
    forceSobolevENormT 2 ((1 - θ) * r) F ≤
      forceSobolevENormT 2 0 F ^ θ * forceSobolevENormT 2 r F ^ (1 - θ) := by
  have hs : (1 - θ) * r ≤ 1 :=
    (mul_nonpos_of_nonneg_of_nonpos (by linarith) hr).trans (by norm_num)
  obtain ⟨A, hA, _, _, hmA, hpA, _⟩ :=
    NSFormalization.Section3.T17.force_coefficient_path_real hF hs
  obtain ⟨B, hB, _, _, hmB, hpB, _⟩ :=
    NSFormalization.Section3.T17.force_coefficient_path_real hF (show (0 : ℝ) ≤ 1 by norm_num)
  obtain ⟨D, hD, _, _, hmD, hpD, _⟩ :=
    NSFormalization.Section3.T17.force_coefficient_path_real hF (hr.trans (by norm_num))
  rw [NSFormalization.Section3.T18.forceSobolevENormT_eq_of_path_local 2 _ hpA hmA.aestronglyMeasurable,
    NSFormalization.Section3.T18.forceSobolevENormT_eq_of_path_local 2 _ hpB hmB.aestronglyMeasurable,
    NSFormalization.Section3.T18.forceSobolevENormT_eq_of_path_local 2 _ hpD hmD.aestronglyMeasurable]
  calc
    _ ≤ eLpNorm (fun t ↦ ‖B t‖ ^ θ * ‖D t‖ ^ (1 - θ)) 2 forceTimeMeasure := by
      apply eLpNorm_mono
      intro t
      exact (norm_datum_interpolation hθ hθ1
        (hF.1.comp (contDiff_const.prodMk contDiff_id)) (hA t) (hB t) (hD t)).trans
        (le_abs_self _)
    _ ≤ _ := by
      simpa only [eLpNorm_norm] using eLpNorm_two_interpolation
        hmB.norm.aemeasurable hmD.norm.aemeasurable
        (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _) hθ.le hθ1.le

/-- Parseval for the packet's order-zero time norm. -/
theorem packet_forceNorm_zero
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hf : ContDiff ℝ ∞ f)
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) place.ε₀) :
    forceSobolevENormT 2 0 (periodizedScaledForce f place.x₀ place.T ε) =
      ENNReal.ofReal (ε ^ (-(1 : ℝ) / 2)) * mixedLebesgueENorm 2 2 f := by
  have hF := force_mem hf hc place ε hε
  have hH := scaledForce_contDiff hf place.x₀ place.T ε
  have hHc := scaledForce_hasCompactSupport hc.1 place.x₀ place.T ε
  obtain ⟨G, hG, _, _, hm, hp, _⟩ :=
    NSFormalization.Section3.T17.force_coefficient_path_real hF (show (0 : ℝ) ≤ 1 by norm_num)
  have hmixed := packetMixedScaling hf hc place 2 2 (by norm_num) ε hε
  norm_num [alphaT, neg_div] at hmixed ⊢
  rw [← hmixed, NSFormalization.Section3.T18.forceSobolevENormT_eq_of_path_local 2 _ hp
    hm.aestronglyMeasurable, mixedLebesgueENormT_eq hH.continuous hHc
      (fun t _ ↦ torusLift_periodizedScaledForce hc place hε t)]
  apply eLpNorm_congr_enorm_ae
  apply Eventually.of_forall
  intro t
  have hmem := memLp_torusLift_vector (continuous_slice hH.continuous t) 2
  rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hmem.2.ne]
  have hz : ContDiff ℝ ∞ (fun x : Space ↦ periodizedScaledForce f place.x₀ place.T ε (t, x)) :=
    hF.1.comp (contDiff_const.prodMk contDiff_id)
  rw [← periodicSobolevENorm_eq (hG t), periodicSobolevENorm_zero_eq _
    ⟨hz, (hG t).1⟩,
    torusLift_periodizedScaledForce hc place hε t]

/-- At orders below `-3/2`, the packet's Sobolev time norm is bounded by
its spatial `L¹` mixed norm, which has a positive scaling exponent. -/
theorem packet_negative_bound
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hf : ContDiff ℝ ∞ f)
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) {s : ℝ} (hs : s < -(3 : ℝ) / 2)
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) place.ε₀) :
    forceSobolevENormT 2 s (periodizedScaledForce f place.x₀ place.T ε) ≤
      ENNReal.ofReal (Real.sqrt (3 * ∑' k : PeriodicFrequency,
        periodicFrequencyWeight k ^ s)) *
      (ENNReal.ofReal ε * mixedLebesgueENorm 2 1 f) := by
  let F := periodizedScaledForce f place.x₀ place.T ε
  let H := scaledForce f place.x₀ place.T ε
  let C := Real.sqrt (3 * ∑' k : PeriodicFrequency, periodicFrequencyWeight k ^ s)
  have hF := force_mem hf hc place ε hε
  have hH := scaledForce_contDiff hf place.x₀ place.T ε
  have hHc := scaledForce_hasCompactSupport hc.1 place.x₀ place.T ε
  obtain ⟨G, hG, _, _, hm, hp, _⟩ :=
    NSFormalization.Section3.T17.force_coefficient_path_real hF (show s ≤ 1 by linarith)
  have hb (t : ℝ) : ‖G t‖ ≤ C *
      (eLpNorm (torusLift (fun x ↦ H (t, x))) 1 periodicTorusMeasure).toReal := by
    have hh := norm_datum_le_L1 hs
      (hF.1.comp (contDiff_const.prodMk contDiff_id)) (hG t)
    change ‖G t‖ ≤ C * (∫ y, ‖torusLift (fun x ↦ F (t, x)) y‖ ∂periodicTorusMeasure) at hh
    rw [integral_norm_eq_lintegral_enorm (hG t).2.1.aestronglyMeasurable,
      torusLift_periodizedScaledForce hc place hε t] at hh
    rw [eLpNorm_one_eq_lintegral_enorm]
    exact hh
  have hmixed := packetMixedScaling hf hc place 1 2 (by norm_num) ε hε
  norm_num [alphaT] at hmixed
  rw [← hmixed]
  change forceSobolevENormT 2 s F ≤ ENNReal.ofReal C * mixedLebesgueENormT 2 1 F
  rw [mixedLebesgueENormT_eq hH.continuous hHc
    (fun t _ ↦ torusLift_periodizedScaledForce hc place hε t)]
  refine (iInf_le_of_le ⟨G, hp, hm.aestronglyMeasurable⟩ le_rfl).trans ?_
  calc
    eLpNorm G 2 forceTimeMeasure ≤ eLpNorm
        (fun t ↦ C * (eLpNorm (torusLift (fun x ↦ H (t, x))) 1
          periodicTorusMeasure).toReal) 2 forceTimeMeasure := by
      apply eLpNorm_mono
      intro t
      exact (hb t).trans (le_abs_self _)
    _ = _ := by
      change eLpNorm (C • (fun t ↦ (eLpNorm (torusLift (fun x ↦ H (t, x))) 1
        periodicTorusMeasure).toReal)) 2 forceTimeMeasure = _
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (show 0 ≤ C from Real.sqrt_nonneg _)]

/-- The two endpoint scalings combine into a positive power exactly when
`θ < 2/3`. -/
theorem packet_interpolated_bound
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hf : ContDiff ℝ ∞ f)
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) {r θ : ℝ} (hr : r < -(3 : ℝ) / 2)
    (hθ : 0 < θ) (hθ1 : θ < 1)
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) place.ε₀) :
    forceSobolevENormT 2 ((1 - θ) * r) (periodizedScaledForce f place.x₀ place.T ε) ≤
      ENNReal.ofReal (ε ^ (1 - 3 * θ / 2)) *
        (mixedLebesgueENorm 2 2 f ^ θ *
          (ENNReal.ofReal (Real.sqrt (3 * ∑' k : PeriodicFrequency, periodicFrequencyWeight k ^ r)) *
            mixedLebesgueENorm 2 1 f) ^ (1 - θ)) := by
  have hi := forceNorm_interpolation (force_mem hf hc place ε hε)
    (show r ≤ 0 by linarith) hθ hθ1
  rw [packet_forceNorm_zero hf hc place hε] at hi
  refine hi.trans ((mul_le_mul' le_rfl (ENNReal.rpow_le_rpow
    (packet_negative_bound hf hc place hr hε) (by linarith))).trans_eq ?_)
  let C := ENNReal.ofReal (Real.sqrt (3 * ∑' k : PeriodicFrequency, periodicFrequencyWeight k ^ r))
  change (ENNReal.ofReal (ε ^ (-(1 : ℝ) / 2)) * mixedLebesgueENorm 2 2 f) ^ θ *
    (C * (ENNReal.ofReal ε * mixedLebesgueENorm 2 1 f)) ^ (1 - θ) = _
  rw [show C * (ENNReal.ofReal ε * mixedLebesgueENorm 2 1 f) =
    ENNReal.ofReal ε * (C * mixedLebesgueENorm 2 1 f) by ac_rfl,
    ENNReal.mul_rpow_of_nonneg _ _ hθ.le,
    ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ 1 - θ),
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hε.1.le _) hθ.le,
    ENNReal.ofReal_rpow_of_nonneg hε.1.le (by linarith : 0 ≤ 1 - θ),
    ← Real.rpow_mul hε.1.le]
  rw [show ENNReal.ofReal (ε ^ (-1 / 2 * θ)) * mixedLebesgueENorm 2 2 f ^ θ *
      (ENNReal.ofReal (ε ^ (1 - θ)) * (C * mixedLebesgueENorm 2 1 f) ^ (1 - θ)) =
      (ENNReal.ofReal (ε ^ (-1 / 2 * θ)) * ENNReal.ofReal (ε ^ (1 - θ))) *
        (mixedLebesgueENorm 2 2 f ^ θ * (C * mixedLebesgueENorm 2 1 f) ^ (1 - θ)) by ac_rfl,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hε.1.le _), ← Real.rpow_add hε.1]
  congr 3
  ring

/-- The `q = 2` convergence conclusion on the direct `L¹`-controlled range. -/
theorem forceConvergence_two_low
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hf : ContDiff ℝ ∞ f)
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ s : ℝ, s < -(3 : ℝ) / 2 →
      Tendsto (fun ε : ℝ ↦ forceSobolevENormT 2 s
        (periodizedScaledForce f place.x₀ place.T ε)) (𝓝[>] 0) (𝓝 0) := by
  intro s hs
  have hfinite : mixedLebesgueENorm 2 1 f ≠ ⊤ := by
    rw [mixedLebesgueENorm_eq hf.continuous hc.1]
    exact ne_top_of_le_ne_top (NSFormalization.Source.compact_mixed_memLp hf hc.1 1 2).2.ne
      (eLpNorm_mono_measure _ Measure.restrict_le_self)
  have he : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using (ENNReal.tendsto_ofReal (tendsto_id : Tendsto (fun ε : ℝ ↦ ε)
      (𝓝 (0 : ℝ)) (𝓝 0))).mono_left nhdsWithin_le_nhds
  have hu := ENNReal.Tendsto.const_mul
    (ENNReal.Tendsto.mul_const he (Or.inr hfinite)) (Or.inr ENNReal.ofReal_ne_top)
      (a := ENNReal.ofReal (Real.sqrt (3 * ∑' k : PeriodicFrequency, periodicFrequencyWeight k ^ s)))
  simp only [zero_mul, mul_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun _ ↦ bot_le
  · filter_upwards [Ioc_mem_nhdsGT place.eps_pos] with ε hε
    exact packet_negative_bound hf hc place hs hε

/-- The full `q = 2` specialization of the canonical force-convergence field. -/
theorem forceConvergence_two
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hf : ContDiff ℝ ∞ f)
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ s : ℝ, s < criticalOrder ((2 : ℝ≥0∞).toReal) →
      Tendsto (fun ε : ℝ ↦ forceSobolevENormT 2 s
        (periodizedScaledForce f place.x₀ place.T ε)) (𝓝[>] 0) (𝓝 0) := by
  intro s hs
  have hs0 : s < -(1 : ℝ) / 2 := by
    norm_num [criticalOrder] at hs ⊢
    exact hs
  by_cases hslow : s < -(3 : ℝ) / 2
  · exact forceConvergence_two_low hf hc place s hslow
  let r : ℝ := (3 * s - 3 / 2) / 2
  let θ : ℝ := 1 - s / r
  have hr : r < -(3 : ℝ) / 2 := by dsimp [r]; linarith
  have hr0 : r < 0 := by linarith
  have hrs : r < s := by dsimp [r]; linarith
  have h3s : 3 * s < r := by dsimp [r]; linarith
  have hdiv : s / r * r = s := div_mul_cancel₀ _ hr0.ne
  have hd0 : 0 < s / r := div_pos_of_neg_of_neg (by linarith) hr0
  have hd1 : s / r < 1 := (div_lt_one_of_neg hr0).2 hrs
  have hd3 : (1 : ℝ) / 3 < s / r := (lt_div_iff_of_neg hr0).2 (by linarith)
  have hθ : 0 < θ := by dsimp [θ]; linarith
  have hθ1 : θ < 1 := by dsimp [θ]; linarith
  have hexp : 0 < 1 - 3 * θ / 2 := by dsimp [θ]; linarith
  have horder : (1 - θ) * r = s := by dsimp [θ]; nlinarith [hdiv]
  have hfinite (p : ℝ≥0∞) [Fact (1 ≤ p)] : mixedLebesgueENorm 2 p f ≠ ⊤ := by
    rw [mixedLebesgueENorm_eq hf.continuous hc.1]
    exact ne_top_of_le_ne_top (NSFormalization.Source.compact_mixed_memLp hf hc.1 p 2).2.ne
      (eLpNorm_mono_measure _ Measure.restrict_le_self)
  let C : ℝ≥0∞ := mixedLebesgueENorm 2 2 f ^ θ *
    (ENNReal.ofReal (Real.sqrt (3 * ∑' k : PeriodicFrequency, periodicFrequencyWeight k ^ r)) *
      mixedLebesgueENorm 2 1 f) ^ (1 - θ)
  have hC : C ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hθ.le (hfinite 2))
    (ENNReal.rpow_ne_top_of_nonneg (by linarith)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfinite 1)))
  have he : Tendsto (fun ε : ℝ ↦ ENNReal.ofReal (ε ^ (1 - 3 * θ / 2)))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (ENNReal.tendsto_ofReal
      (Filter.tendsto_id.rpow_const_nhds_zero hexp)).mono_left nhdsWithin_le_nhds
  have hu := ENNReal.Tendsto.mul_const he (Or.inr hC)
  simp only [zero_mul] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Eventually.of_forall fun _ ↦ bot_le
  · filter_upwards [Ioc_mem_nhdsGT place.eps_pos] with ε hε
    simpa only [horder] using packet_interpolated_bound hf hc place hr hθ hθ1 hε

/-- Both time exponents in the literal canonical field, from raw packet clauses. -/
theorem forceConvergence
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hf : ContDiff ℝ ∞ f)
    (hc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (place : PlacementData u p f K) :
    ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ, s < criticalOrder q.toReal →
      Tendsto (fun ε : ℝ ↦ forceSobolevENormT q s
        (periodizedScaledForce f place.x₀ place.T ε)) (𝓝[>] 0) (𝓝 0) := by
  intro q hq
  rcases hq with rfl | rfl
  · exact forceConvergence_one hf hc place
  · exact forceConvergence_two hf hc place

end NSFormalization.Section3.T15
