import NSFormalization.Section3.T11.LocalExistenceProbe

noncomputable section
namespace NSFormalization.Section3.T11.ExistenceProbe
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal BigOperators

-- Exact U9 named input: in particular, K is BEFORE a and is the SAME for every m.
example : PeriodicQuantitativeLocalInput ↔
    ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∃ δ : ℝ, 0 < δ ∧
      ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 1 a ≤ K →
        ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g →
          (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ K) →
            ∃ w : ClassicalSolutionT ν a g δ,
              NSFormalization.Section3.T11.PeriodicLocalRegularity ν a g δ w := Iff.rfl

-- Verbatim regularity target from api_on_canonical.lean, in this probe namespace.
structure PeriodicLocalRegularity (ν : ℝ) (a : SpatialField) (f : SpaceTimeField)
    (T : ℝ) (w : ClassicalSolutionT ν a f T) : Prop where
  sobolev_smooth : ∀ m : ℕ, ∃ G : ℝ → PeriodicSobolev (m : ℝ),
    IsPeriodicSobolevPathOn (m : ℝ) (Ico (0 : ℝ) T) w.velocity G ∧
      ContDiffOn ℝ ∞ G (Ico (0 : ℝ) T)
  pressure_poisson : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
    scalarSpatialLaplacianT w.pressure t x =
      spatialDivergence f t x -
        spatialDivergence
          (fun z : SpaceTime ↦ convectionDivergenceT w.velocity z.1 z.2) t x
  projected : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
    temporalDerivative w.velocity t x - ν • spatialLaplacian w.velocity t x =
      (f (t, x) - convectionDivergenceT w.velocity t x) -
        pressureGradient w.pressure t x

-- Every regularity field closes for a real classical witness, on one common horizon.
example (ν T : ℝ) (hT : 0 < T) (c : Space)
    (b d : ℝ → ℝ) (hb : ContDiff ℝ ∞ b) (hb0 : b 0 = 1)
    (hd : ∀ t, HasDerivAt b (d t) t) :
    PeriodicLocalRegularity ν (fun _ ↦ c) (fun z ↦ d z.1 • c) T
      (torusHomogeneousSolution ν T hT c b d hb hb0 hd) := by
  have h := torusHomogeneousSolution_regularity ν T hT c b d hb hb0 hd
  exact ⟨h.sobolev_smooth, h.pressure_poisson, h.projected⟩

example (s : ℝ) {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (A : PeriodicSobolev s) : ‖torusHeat s hν ht A‖ ≤ ‖A‖ :=
  torusHeat_norm_le s hν ht A

example (s : ℝ) {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t)
    (A : PeriodicSobolev s) :
    ‖torusHeatSmoothing s hν ht A‖ ≤ torusSmoothingKernel ν t * ‖A‖ :=
  torusHeatSmoothing_norm_le s hν ht A

example (s : ℝ) {ν t u : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (A : PeriodicSobolev s) :
    torusHeat s hν (add_nonneg ht hu) A = torusHeat s hν ht (torusHeat s hν hu A) :=
  torusHeat_add s hν ht hu A

example (s : ℝ) {ν t u : ℝ} (hν : 0 < ν) (ht : 0 < t) (hu : 0 ≤ u)
    (A : PeriodicSobolev s) :
    torusHeatSmoothing s hν (add_pos_of_pos_of_nonneg ht hu) A =
      torusHeat (s + 1) hν.le hu (torusHeatSmoothing s hν ht A) :=
  torusHeatSmoothing_coherent s hν ht hu A

example (s : ℝ) {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t)
    (A : PeriodicSobolev s) (hA : IsSolenoidalPeriodicDatum A) :
    IsSolenoidalPeriodicDatum (torusHeat s hν ht A) :=
  torusHeat_solenoidal s hν ht A hA

-- This is stronger than a zero-data or zero-force test: every exact input premise
-- holds with finite K, and the solution and force are both nonzero at time zero.
example :
    ∃ (K : ℝ≥0∞) (a : SpatialField) (g : SpaceTimeField),
      K ≠ ⊤ ∧ a ∈ initialClassT ∧ periodicSobolevENorm 1 a ≤ K ∧
      ContDiff ℝ ∞ g ∧ IsPeriodicOn univ g ∧
      (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ K) ∧
      ∃ w : ClassicalSolutionT 1 a g 1,
        PeriodicLocalRegularity 1 a g 1 w ∧
        w.velocity (0, 0) ≠ 0 ∧ g (0, 0) ≠ 0 := by
  obtain ⟨K, a, g, hK, ha, hA, hg, hp, hG, w, hw, hu, hf⟩ := nonzero_forced_witness
  exact ⟨K, a, g, hK, ha, hA, hg, hp, hG, w,
    ⟨hw.sobolev_smooth, hw.pressure_poisson, hw.projected⟩, hu, hf⟩

example (H : PeriodicQuantitativeLocalInput) :
    ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∃ δ : ℝ, 0 < δ ∧
      ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 1 a ≤ K →
        ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g →
          (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ K) →
            ENNReal.ofReal δ ≤ maximalLifespanT ν a g :=
  quantitative_lifespan_lower_bound H

end NSFormalization.Section3.T11.ExistenceProbe
