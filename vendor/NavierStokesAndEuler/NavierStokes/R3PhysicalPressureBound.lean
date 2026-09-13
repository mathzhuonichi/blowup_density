import NavierStokes.R3LocalizedPressureTests
import NavierStokes.R3PositiveTests

/-!
# Transfer of the uniform Gaussian estimate to the physical pressure

The physical pressure is used only on compact tests. Its spatially
localized flux is continuous, so square time tests recover the bound at
every interior time.
-/

noncomputable section
namespace NavierStokes.R3PhysicalPressureBound

open Set Filter MeasureTheory TemperedDistribution ProblemStatement
open R3SpaceTime R3SpaceTimePressure R3WeakPressure R3TimeLocalization R3LocalizedPressure
open R3LocalizedPressureTests R3PositiveTests
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal

def Recovery (s : Set ℝ) (G : Fin 3 → Fin 3 → Domain → ℂ) (p : Domain → ℂ) : Prop :=
  ∀ a : ℝ → ℝ, ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ s →
    ∃ gLp : Fin 3 → Fin 3 → Lp ℂ 1 (volume : Measure Domain),
      (∀ i j, gLp i j =ᵐ[volume] localize a (G i j)) ∧
      ∀ i, Represents (∂_{spaceDirection i} (stressPressure gLp))
        (localize a (directional (spaceDirection i) p))

theorem physical_flux_le {s : Set ℝ} (hs : IsOpen s)
    (G : Fin 3 → Fin 3 → Domain → ℂ) (p : Domain → ℂ)
    (hp : ContDiffOn ℝ ∞ p (timeProj ⁻¹' s)) (hrec : Recovery s G p)
    (W : Fin 3 → Domain → ℂ) (hW : ∀ i, ContDiffOn ℝ ∞ (W i) (timeProj ⁻¹' s))
    (K : Set Space) (hK : IsCompact K)
    (hWK : ∀ i z, timeProj z ∈ s → spaceProj z ∉ K → W i z = 0)
    (f H : ℝ → ℝ) (hf : ContinuousOn f s) (hH : ContinuousOn H s)
    (hphysical : ∀ t ∈ s, (∫ x : Space, functionDivergence W (pack t x) * p (pack t x)) = (f t : ℂ))
    (happrox : ∀ n i j t, t ∈ s →
      ‖∫ x : Space, functionDivergence W (pack t x) *
        R3RieszApproximation.regularized n i j (fun y => G i j (pack t y)) x‖ ≤ H t) :
    ∀ t ∈ s, |f t| ≤ 9 * H t := by
  apply abs_le_of_square_test_integrals hs hf (continuousOn_const.mul hH)
  intro a ha hac has
  obtain ⟨gLp, hgLp, hrepr⟩ := hrec a ha hac has
  have hG (i j : Fin 3) : MemLp (localize a (G i j)) 1 :=
    (memLp_congr_ae (hgLp i j)).mp (Lp.memLp (gLp i j))
  have heq : gLp = fun i j => (hG i j).toLp (localize a (G i j)) := by
    funext i j
    exact Lp.ext ((hgLp i j).trans (hG i j).coeFn_toLp.symm)
  have hP (i : Fin 3) : Represents
      (∂_{spaceDirection i} (stressPressure (fun i j => (hG i j).toLp (localize a (G i j)))))
      (directional (spaceDirection i) (localize a p)) := by
    rw [← heq, directional_localize_space hs ha has hp]
    exact hrepr i
  have hlim := localized_pairing_tendsto hs a ha hac has G p hp hG hP W hW K hK hWK
  have ha₂ : HasCompactSupport (fun t => a t ^ 2) := hac.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num)
  have ha₂s : tsupport (fun t => a t ^ 2) ⊆ s :=
    (tsupport_comp_subset (g := fun r : ℝ => r ^ 2) (by norm_num) a).trans has
  have hmajor : Integrable (fun t => a t ^ 2 * H t) :=
    (continuous_test_product hs (ha.continuous.pow 2) hH ha₂s).integrable_of_hasCompactSupport ha₂.mul_right
  have hinside {t : ℝ} (ht : a t ≠ 0) : t ∈ s := has (subset_tsupport _ ht)
  have hbound (n : ℕ) (i j : Fin 3) :
      ‖∫ t : ℝ, (a t ^ 2 : ℝ) * (∫ x : Space, functionDivergence W (pack t x) *
        R3RieszApproximation.regularized n i j (fun y => G i j (pack t y)) x)‖ ≤
      ∫ t : ℝ, a t ^ 2 * H t := by
    apply norm_integral_le_of_norm_le hmajor
    exact Eventually.of_forall fun t => by
      by_cases ht : a t = 0
      · simp [ht]
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
        exact mul_le_mul_of_nonneg_left (happrox n i j t (hinside ht)) (sq_nonneg _)
  have hsum (n : ℕ) :
      ‖∑ i : Fin 3, ∑ j : Fin 3, ∫ t : ℝ, (a t ^ 2 : ℝ) *
        (∫ x : Space, functionDivergence W (pack t x) *
          R3RieszApproximation.regularized n i j (fun y => G i j (pack t y)) x)‖ ≤
      9 * ∫ t : ℝ, a t ^ 2 * H t := by
    apply (norm_sum_le _ _).trans
    apply (Finset.sum_le_sum (fun i _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum (fun j _ => hbound n i j)))).trans_eq
    simp
    ring
  have hlimbound := le_of_tendsto hlim.norm (Eventually.of_forall hsum)
  have hphys : (∫ t : ℝ, (a t ^ 2 : ℝ) * (∫ x : Space, functionDivergence W (pack t x) * p (pack t x))) =
      Complex.ofReal (∫ t : ℝ, a t ^ 2 * f t) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      dsimp only
      by_cases ht : a t = 0
      · simp [ht]
      · rw [hphysical t (hinside ht), Complex.ofReal_mul]
  rw [hphys, Complex.norm_real, Real.norm_eq_abs] at hlimbound
  have he (t : ℝ) : a t ^ 2 * (9 * H t) = 9 * (a t ^ 2 * H t) := by ring
  simpa only [Pi.mul_apply, he, integral_const_mul] using hlimbound

end NavierStokes.R3PhysicalPressureBound
