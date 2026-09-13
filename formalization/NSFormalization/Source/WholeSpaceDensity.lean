import NSFormalization.Source.InsertionBreakdown

/-!
# Positive whole-space singular-force approximation

Every forcing field admits an arbitrarily small smooth compact correction,
supported strictly after time zero, such that no actual classical flow in the
displayed finite-energy class extends beyond the deadline. The proof uses the
actual insertion and comparison theorems, not a local-existence premise.

Only the compact correction is evaluated by the pointwise Fourier integral.
No Fourier integral of a potentially non-L1 background field is used.
-/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal FourierTransform
namespace NSFormalization.Source.WholeSpaceDensity
open NavierStokes.ProblemStatement
open SmoothLifespan InsertionFamily LocalReferenceInsertion

def SubcriticalSobolev (q : ℝ≥0∞) (s : ℝ) : Prop :=
  (q = 1 ∧ s < 1 / 2) ∨ (q = 2 ∧ s < -1 / 2)

theorem force_limit {ν : ℝ} {f v : VelocityField} {x₀ : Space} {T : ℝ}
    {θ : Space → ℝ} {η : ℝ → ℝ} (h : ForceApproximation ν f v x₀ T θ η)
    {q : ℝ≥0∞} {s : ℝ} (hs : SubcriticalSobolev q s) :
    Tendsto (fun ε : ℝ => eLpNorm (vectorAngularSobolevNorm s
      (force ν f v x₀ T θ η ε)) q volume) (𝓝[>] 0) (𝓝 0) := by
  rcases hs with ⟨rfl, hs⟩ | ⟨rfl, hs⟩
  · exact h.1 s hs
  · exact h.2.1 s hs

@[simp] theorem vectorAngularSobolevNorm_zero (s t : ℝ) :
    vectorAngularSobolevNorm s (0 : VelocityField) t = 0 := by
  simp [vectorAngularSobolevNorm, angularSobolevSq, angularFourier, coordinateForce,
    Real.fourier_eq', integral_zero]

/-- A fully proved epsilon-density statement for actual force increments.
The initial datum is fixed. The background itself is never assumed to have a
regular evolution: when it has none beyond T, the zero increment suffices. -/
theorem exists_small_singular_compact_correction {ν T s : ℝ}
    (hν : 0 < ν) (hT : 0 < T) {q : ℝ≥0∞} (hs : SubcriticalSobolev q s)
    (a : Space → Space) (g : VelocityField) {ρ : ℝ≥0∞} (hρ : 0 < ρ) :
    ∃ G : VelocityField,
      AdmissibleCompactForce G ∧
      tsupport G ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set Space) ∧
      eLpNorm (vectorAngularSobolevNorm s G) q volume < ρ ∧
      lifespan ν a (g + G) ≤ ENNReal.ofReal T := by
  rcases bad_or_regular_reference hT.le a g with hbad | ⟨R, hTR, ⟨U⟩⟩
  · refine ⟨0, admissibleCompactForce_of_smooth contDiff_const HasCompactSupport.zero, ?_, ?_, ?_⟩
    · simp
    · have hz : vectorAngularSobolevNorm s (0 : VelocityField) = 0 := by
        funext t
        exact vectorAngularSobolevNorm_zero s t
      rw [hz, eLpNorm_zero]
      exact hρ
    · simpa using hbad
  · let δ := R - T
    have hδ : 0 < δ := sub_pos.mpr hTR
    have hR : T + δ = R := by dsimp [δ]; ring
    have hvs : ContDiffOn ℝ ∞ U.velocity (Ico (0 : ℝ) (T + δ) ×ˢ univ) := by
      simpa only [hR] using U.velocity_smooth
    have hps : ContDiffOn ℝ ∞ U.pressure (Ico (0 : ℝ) (T + δ) ×ˢ univ) := by
      simpa only [hR] using U.pressure_smooth
    have hdiv : ∀ t ∈ Ico (0 : ℝ) (T + δ), ∀ x, spatialDivergence U.velocity t x = 0 := by
      simpa only [hR] using U.divergence
    obtain ⟨vhat, u, p, f, K, θ, η, ε₀, hε₀, _, hlim, _, hfamily⟩ :=
      exists_local_approximating_insertion hν hδ hvs hps hdiv
        (le_refl (0 : ℝ)) hT
        (fun t ht => U.equation t ⟨ht.1, ht.2.trans hTR⟩)
        (0 : Space) (show 0 < (1 : ℝ) by norm_num)
    have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        eLpNorm (vectorAngularSobolevNorm s (force ν f vhat 0 T θ η ε)) q volume < ρ :=
      (force_limit hlim hs).eventually (eventually_lt_nhds hρ)
    have heps : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) ε₀ := by
      filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hε₀).filter_mono nhdsWithin_le_nhds] with ε hpos hlt
      exact ⟨hpos, hlt⟩
    obtain ⟨ε, hε, hn⟩ := (heps.and hsmall).exists
    obtain ⟨hi, ha⟩ := hfamily ε hε
    refine ⟨force ν f vhat 0 T θ η ε, ha, ?_, hn,
      insertion_lifespan_le hν hT (le_refl 0) hTR U hi⟩
    exact hi.2.2.2.2.1.trans (Set.prod_mono Subset.rfl (subset_univ _))

/-- The L1 Sobolev threshold in the manuscript's exact unitary angular
Fourier convention, for arbitrary fixed initial data. -/
theorem exists_L1_singular_correction {ν T s : ℝ}
    (hν : 0 < ν) (hT : 0 < T) (hs : s < 1 / 2)
    (a : Space → Space) (g : VelocityField) {ρ : ℝ≥0∞} (hρ : 0 < ρ) :
    ∃ G : VelocityField, AdmissibleCompactForce G ∧
      tsupport G ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set Space) ∧
      eLpNorm (vectorAngularSobolevNorm s G) 1 volume < ρ ∧
      lifespan ν a (g + G) ≤ ENNReal.ofReal T :=
  exists_small_singular_compact_correction hν hT (Or.inl ⟨rfl, hs⟩) a g hρ

/-- The L2 Sobolev threshold, with genuine negative-order low-frequency
control supplied by the previously proved compact-force estimates. -/
theorem exists_L2_singular_correction {ν T s : ℝ}
    (hν : 0 < ν) (hT : 0 < T) (hs : s < -1 / 2)
    (a : Space → Space) (g : VelocityField) {ρ : ℝ≥0∞} (hρ : 0 < ρ) :
    ∃ G : VelocityField, AdmissibleCompactForce G ∧
      tsupport G ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set Space) ∧
      eLpNorm (vectorAngularSobolevNorm s G) 2 volume < ρ ∧
      lifespan ν a (g + G) ≤ ENNReal.ofReal T :=
  exists_small_singular_compact_correction hν hT (Or.inr ⟨rfl, hs⟩) a g hρ

end NSFormalization.Source.WholeSpaceDensity
