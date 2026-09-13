import Formal.R3QuantitativeLifespan
import Formal.EndpointSafeTwoSpaceConcatenation
import Formal.EndpointSafeTwoSpaceUniqueness

/-!
# Uniform-step extension and the blow-up dichotomy

The maximal-continuation layer for the concrete `R³` endpoint-safe projected mild equation.

* `r3MildLifespan_antitone`: the explicit lifespan is monotone decreasing in the
  initial-datum norm, so a single bound `R` yields a **uniform** positive step.
* `r3EndpointSafeProjected_exists_extension_of_bounded`: a mild solution bounded by `R`
  extends to the horizon `T + r3MildLifespan ν R` (restart datum + explicit-lifespan
  solution + concatenation).
* `r3MildHorizons`: the set of certified horizons for a fixed datum.
* `r3EndpointSafeProjected_horizons_unbounded_of_uniform_bound`: if all certified
  solutions obey a single norm bound, the horizon set is unbounded — otherwise a horizon
  within `r3MildLifespan ν R` of the supremum would extend past it.
* `r3EndpointSafeProjected_blowup_dichotomy`: either arbitrarily long horizons carry mild
  solutions, or the certified solution norms escape every ball.

Scope guard: the dichotomy quantifies over certified horizons; by unrestricted uniqueness
all certified solutions are restrictions of one coherent evolution, but the glued maximal
trajectory `u* : [0, T*) → H³` and the pointwise statement `‖u* t‖ → ∞` are not yet
constructed.  No pressure reconstruction and no Clay statement.
-/

namespace MNS2

open MeasureTheory Set
open scoped NNReal

noncomputable section

theorem r3MildSmallnessThreshold_antitone {r r' : ℝ} (hr : 0 ≤ r) (hrr' : r ≤ r') :
    r3MildSmallnessThreshold r' ≤ r3MildSmallnessThreshold r := by
  have hB : (0 : ℝ) ≤ ‖r3ProjectedConvectionH3ToH2‖ := ContinuousLinearMap.opNorm_nonneg _
  unfold r3MildSmallnessThreshold
  refine min_le_min ?_ ?_
  · refine one_div_le_one_div_of_le ?_ ?_
    · have h1 : (0 : ℝ) ≤ ‖r3ProjectedConvectionH3ToH2‖ * (r + 1) ^ 2 :=
        mul_nonneg hB (sq_nonneg _)
      linarith
    · have hsq : (r + 1) ^ 2 ≤ (r' + 1) ^ 2 := by nlinarith
      have h2 := mul_le_mul_of_nonneg_left hsq hB
      linarith
  · refine one_div_le_one_div_of_le ?_ ?_
    · have h1 : (0 : ℝ) ≤ ‖r3ProjectedConvectionH3ToH2‖ * (2 * (r + 1)) :=
        mul_nonneg hB (by linarith)
      linarith
    · have h2 : ‖r3ProjectedConvectionH3ToH2‖ * (2 * (r + 1)) ≤
          ‖r3ProjectedConvectionH3ToH2‖ * (2 * (r' + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) hB
      linarith

/-- The explicit lifespan is antitone in the initial-datum norm: a single norm bound
yields a uniform positive step. -/
theorem r3MildLifespan_antitone {nu r r' : ℝ} (hnu : 0 < nu) (hr : 0 ≤ r) (hrr' : r ≤ r') :
    r3MildLifespan nu r' ≤ r3MildLifespan nu r := by
  have hδ'pos : 0 < r3MildSmallnessThreshold r' :=
    r3MildSmallnessThreshold_pos (hr.trans hrr')
  have hδpos : 0 < r3MildSmallnessThreshold r := r3MildSmallnessThreshold_pos hr
  have hδle : r3MildSmallnessThreshold r' ≤ r3MildSmallnessThreshold r :=
    r3MildSmallnessThreshold_antitone hr hrr'
  have hc : 0 < (Real.pi * Real.sqrt nu)⁻¹ :=
    inv_pos.mpr (mul_pos Real.pi_pos (Real.sqrt_pos.mpr hnu))
  have hD : (0 : ℝ) < 1 + (Real.pi * Real.sqrt nu)⁻¹ + r3MildSmallnessThreshold r := by
    linarith
  have hD' : (0 : ℝ) < 1 + (Real.pi * Real.sqrt nu)⁻¹ + r3MildSmallnessThreshold r' := by
    linarith
  have hfrac : r3MildSmallnessThreshold r' /
      (1 + (Real.pi * Real.sqrt nu)⁻¹ + r3MildSmallnessThreshold r') ≤
      r3MildSmallnessThreshold r /
        (1 + (Real.pi * Real.sqrt nu)⁻¹ + r3MildSmallnessThreshold r) := by
    rw [div_le_div_iff₀ hD' hD]
    nlinarith [mul_nonneg (sub_nonneg.mpr hδle) hc.le]
  have h0 : (0 : ℝ) ≤ r3MildSmallnessThreshold r' /
      (1 + (Real.pi * Real.sqrt nu)⁻¹ + r3MildSmallnessThreshold r') :=
    (div_pos hδ'pos hD').le
  exact pow_le_pow_left₀ h0 hfrac 2

/-- **Uniform-step extension**: a mild solution bounded by `R` on its horizon extends to
the horizon `T + r3MildLifespan ν R`. -/
theorem r3EndpointSafeProjected_exists_extension_of_bounded {nu T R : ℝ} (hnu : 0 < nu)
    {u0 : R3HsVelocity 3} {u : ℝ → R3HsVelocity 3}
    (h : IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 u) (hR0 : 0 ≤ R)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ R) :
    ∃ w : ℝ → R3HsVelocity 3,
      IsR3EndpointSafeProjectedMildSolutionOn hnu (T + r3MildLifespan nu R) u0 w := by
  have hT0 : (0 : ℝ) ≤ T := h.1
  have huT : ‖u T‖ ≤ R := hbound T (right_mem_Icc.mpr hT0)
  obtain ⟨v, hv, _hvball, _hvuniq⟩ :=
    r3EndpointSafeProjected_exists_mildSolutionOn_mildLifespan hnu (u T)
  have hlifele : r3MildLifespan nu R ≤ r3MildLifespan nu ‖u T‖ :=
    r3MildLifespan_antitone hnu (norm_nonneg _) huT
  have hlife0 : (0 : ℝ) ≤ r3MildLifespan nu R := (r3MildLifespan_pos hnu hR0).le
  have hv' := EndpointSafeTwoSpaceDuhamelContract.IsMildSolutionOn.mono
    (r3EndpointSafeProjectedDuhamelContract hnu) hv hlife0 hlifele
  exact ⟨_, h.concat hv'⟩

/-- The set of certified mild horizons for a fixed viscosity and initial datum. -/
def r3MildHorizons {nu : ℝ} (hnu : 0 < nu) (u0 : R3HsVelocity 3) : Set ℝ :=
  {T | ∃ u : ℝ → R3HsVelocity 3, IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 u}

theorem r3MildHorizons_nonempty {nu : ℝ} (hnu : 0 < nu) (u0 : R3HsVelocity 3) :
    (r3MildHorizons hnu u0).Nonempty := by
  obtain ⟨u, hu, _, _⟩ := r3EndpointSafeProjected_exists_mildSolutionOn_mildLifespan hnu u0
  exact ⟨r3MildLifespan nu ‖u0‖, u, hu⟩

/-- If every certified solution obeys a single norm bound `R`, the horizon set is
unbounded: a certified horizon within `r3MildLifespan ν R` of the supremum would extend
past it by the uniform step. -/
theorem r3EndpointSafeProjected_horizons_unbounded_of_uniform_bound {nu R : ℝ}
    (hnu : 0 < nu) {u0 : R3HsVelocity 3} (hR0 : 0 ≤ R)
    (hbound : ∀ T ∈ r3MildHorizons hnu u0, ∀ u : ℝ → R3HsVelocity 3,
      IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 u →
      ∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ R) :
    ¬ BddAbove (r3MildHorizons hnu u0) := by
  intro hbdd
  have hSne : (r3MildHorizons hnu u0).Nonempty := r3MildHorizons_nonempty hnu u0
  have hlife : 0 < r3MildLifespan nu R := r3MildLifespan_pos hnu hR0
  obtain ⟨T, hTS, hTgt⟩ := exists_lt_of_lt_csSup hSne
    (show sSup (r3MildHorizons hnu u0) - r3MildLifespan nu R <
      sSup (r3MildHorizons hnu u0) by linarith)
  obtain ⟨u, hu⟩ := hTS
  obtain ⟨w, hw⟩ := r3EndpointSafeProjected_exists_extension_of_bounded hnu hu hR0
    (hbound T ⟨u, hu⟩ u hu)
  have hle : T + r3MildLifespan nu R ≤ sSup (r3MildHorizons hnu u0) :=
    le_csSup hbdd ⟨w, hw⟩
  linarith

/-- **Blow-up dichotomy**: either arbitrarily long horizons carry mild solutions, or the
certified solution norms escape every ball. -/
theorem r3EndpointSafeProjected_blowup_dichotomy {nu : ℝ} (hnu : 0 < nu)
    (u0 : R3HsVelocity 3) :
    (∀ M : ℝ, ∃ T ∈ r3MildHorizons hnu u0, M ≤ T) ∨
    ∀ R : ℝ, 0 ≤ R → ∃ T ∈ r3MildHorizons hnu u0, ∃ u : ℝ → R3HsVelocity 3,
      IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 u ∧
      ∃ t ∈ Icc (0 : ℝ) T, R < ‖u t‖ := by
  by_cases hbdd : BddAbove (r3MildHorizons hnu u0)
  · right
    intro R hR0
    by_contra hno
    have hbound : ∀ T ∈ r3MildHorizons hnu u0, ∀ u : ℝ → R3HsVelocity 3,
        IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 u →
        ∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ R := by
      intro T hTS u hu t ht
      by_contra hgt
      exact hno ⟨T, hTS, u, hu, t, ht, not_le.mp hgt⟩
    exact r3EndpointSafeProjected_horizons_unbounded_of_uniform_bound hnu hR0 hbound hbdd
  · left
    intro M
    obtain ⟨T, hTS, hMT⟩ := not_bddAbove_iff.mp hbdd M
    exact ⟨T, hTS, hMT.le⟩

end

end MNS2
