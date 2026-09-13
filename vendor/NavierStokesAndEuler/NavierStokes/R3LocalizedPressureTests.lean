import NavierStokes.R3PressurePairing

/-!
# Compact time tests for the physical pressure flux

Using the same time cutoff in the equation and vector test produces its
square. No global growth bound on the physical pressure is needed.
-/

noncomputable section
namespace NavierStokes.R3LocalizedPressureTests

open Set Filter MeasureTheory TemperedDistribution ProblemStatement
open R3SpaceTime R3SpaceTimePressure R3WeakPressure R3TimeLocalization R3PressurePairing
open R3LocalizedPressure
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal

theorem localize_compact {s : Set ℝ} {a : ℝ → ℝ} (ha : HasCompactSupport a)
    (has : tsupport a ⊆ s) {W : Domain → ℂ} {K : Set Space} (hK : IsCompact K)
    (hsupp : ∀ z, timeProj z ∈ s → spaceProj z ∉ K → W z = 0) :
    HasCompactSupport (localize a W) := by
  apply HasCompactSupport.intro ((ha.prod hK).image (WithLp.prod_continuous_toLp 2 ℝ Space))
  intro z hz
  by_cases ht : timeProj z ∈ tsupport a
  · have hx : spaceProj z ∉ K := by
      intro hx
      exact hz ⟨(timeProj z, spaceProj z), ⟨ht, hx⟩, rfl⟩
    simp [localize, hsupp z (has ht) hx]
  · simp [localize, image_eq_zero_of_notMem_tsupport ht]

theorem regularized_localize (a : ℝ → ℝ) (G : Domain → ℂ) (n : ℕ) (i j : Fin 3) (z : Domain) :
    R3SpatialConvolution.regularized n i j (localize a G) z =
      (a (timeProj z) : ℂ) * R3RieszApproximation.regularized n i j
        (fun x => G (pack (timeProj z) x)) (spaceProj z) := by
  unfold R3SpatialConvolution.regularized R3RieszApproximation.regularized R3ConvolutionYoung.scalarConvolution
  simp only [localize, timeProj_pack]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by ring

theorem integral_localized_product (a : ℝ → ℝ) (F G : Domain → ℂ)
    (hi : Integrable (fun z => localize a F z * localize a G z)) :
    (∫ z : Domain, localize a F z * localize a G z) =
      ∫ t : ℝ, (a t ^ 2 : ℝ) * (∫ x : Space, F (pack t x) * G (pack t x)) := by
  rw [integral_eq_prod]
  erw [integral_prod _ ((integrable_iff_prod _).mp hi)]
  apply integral_congr_ae
  filter_upwards with t
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by simp only [localize, timeProj_pack]; push_cast; ring

theorem compact_testDivergence (Ψ : Fin 3 → 𝓢(Domain, ℂ))
    (hΨ : ∀ i, HasCompactSupport (Ψ i : Domain → ℂ)) :
    HasCompactSupport (testDivergence Ψ : Domain → ℂ) := by
  have hh : HasCompactSupport (∑ i : Fin 3, ((∂_{spaceDirection i} (Ψ i) : 𝓢(Domain, ℂ)) : Domain → ℂ)) :=
    HasCompactSupport.finset_sum (fun i _ => compact_lineDeriv (Ψ i) (hΨ i) (spaceDirection i))
  convert! hh using 1

/-- The precise time-integrated pairing supplied by pressure recovery. -/
theorem localized_pairing_tendsto {s : Set ℝ} (hs : IsOpen s)
    (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a) (has : tsupport a ⊆ s)
    (G : Fin 3 → Fin 3 → Domain → ℂ) (p : Domain → ℂ)
    (hp : ContDiffOn ℝ ∞ p (timeProj ⁻¹' s))
    (hG : ∀ i j, MemLp (localize a (G i j)) 1)
    (hP : ∀ i, Represents
      (∂_{spaceDirection i} (stressPressure (fun i j => (hG i j).toLp (localize a (G i j)))))
      (directional (spaceDirection i) (localize a p)))
    (W : Fin 3 → Domain → ℂ) (hW : ∀ i, ContDiffOn ℝ ∞ (W i) (timeProj ⁻¹' s))
    (K : Set Space) (hK : IsCompact K)
    (hWK : ∀ i z, timeProj z ∈ s → spaceProj z ∉ K → W i z = 0) :
    Tendsto (fun n => ∑ i : Fin 3, ∑ j : Fin 3,
      ∫ t : ℝ, (a t ^ 2 : ℝ) * (∫ x : Space,
        functionDivergence W (pack t x) * R3RieszApproximation.regularized n i j
          (fun y => G i j (pack t y)) x)) atTop
      (𝓝 (∫ t : ℝ, (a t ^ 2 : ℝ) * (∫ x : Space, functionDivergence W (pack t x) * p (pack t x)))) := by
  have hWc i : HasCompactSupport (localize a (W i)) := localize_compact hac has hK (hWK i)
  have hWs i : ContDiff ℝ ∞ (localize a (W i)) := localize_contDiff ha hs has (hW i)
  let Ψ : Fin 3 → 𝓢(Domain, ℂ) := fun i => (hWc i).toSchwartzMap (hWs i)
  have hΨc (i : Fin 3) : HasCompactSupport (Ψ i : Domain → ℂ) := hWc i
  have hdiv : (testDivergence Ψ : Domain → ℂ) = localize a (functionDivergence W) := by
    funext z
    change (∑ i : Fin 3, directional (spaceDirection i) (localize a (W i)) z) = _
    have hh := congrFun (divergence_localize hs ha has hW) z
    exact hh
  have hpc : ContDiff ℝ ∞ (localize a p) := localize_contDiff ha hs has hp
  have hlim := actual_pressure_pairing_tendsto (fun i j => localize a (G i j)) hG
    (localize a p) hpc hP Ψ hΨc
  have hdC := compact_testDivergence Ψ hΨc
  have hintP : Integrable (fun z => testDivergence Ψ z * localize a p z) :=
    ((testDivergence Ψ).continuous.mul hpc.continuous).integrable_of_hasCompactSupport hdC.mul_right
  have eqP : (∫ z : Domain, testDivergence Ψ z * localize a p z) =
      ∫ t : ℝ, (a t ^ 2 : ℝ) * (∫ x : Space, functionDivergence W (pack t x) * p (pack t x)) := by
    rw [hdiv] at hintP ⊢
    exact integral_localized_product a _ p hintP
  have eqG (n : ℕ) (i j : Fin 3) :
      (∫ z : Domain, testDivergence Ψ z * R3SpatialConvolution.regularized n i j (localize a (G i j)) z) =
      ∫ t : ℝ, (a t ^ 2 : ℝ) * (∫ x : Space, functionDivergence W (pack t x) *
        R3RieszApproximation.regularized n i j (fun y => G i j (pack t y)) x) := by
    have hreg := R3SpatialConvolution.regularized_integrable n i j (memLp_one_iff_integrable.mp (hG i j))
    have hint := hreg.bdd_mul (testDivergence Ψ).continuous.aestronglyMeasurable
      (Eventually.of_forall (SchwartzMap.norm_le_seminorm ℝ (testDivergence Ψ)))
    rw [integral_eq_prod]
    erw [integral_prod _ ((integrable_iff_prod _).mp hint)]
    apply integral_congr_ae
    filter_upwards with t
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [regularized_localize]
    simp only [hdiv, localize, timeProj_pack, spaceProj_pack]
    push_cast
    ring
  simpa only [eqP, eqG] using hlim

end NavierStokes.R3LocalizedPressureTests
