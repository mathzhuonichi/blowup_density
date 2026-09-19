import NSFormalization.Section3.T19.Threading

noncomputable section
namespace NSFormalization.Section3.T19.ThreadingProbe
open Set MeasureTheory Filter Topology Metric
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T15
open NSFormalization.Section3.T16 NSFormalization.Section3.T17 NSFormalization.Section3.T18
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open scoped ContDiff ENNReal

variable {ν : ℝ} (hν : 0 < ν) {a : SpatialField} {g : SpaceTimeField}
  (ha : a ∈ initialClassT) (hg : g ∈ forceClassT) {T δ : ℝ}
  (hT : 0 < T) (hδ : 0 < δ) (reference : ClassicalSolutionT ν a g (T + δ))

local notation "ins" => insertion hν ha hg hT hδ reference

example : 0 < (ins).ε₀ := by
  exact T19.insertion_eps_pos hν ha hg hT hδ reference

example : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀, (ins).force ε ∈ forceClassT := by
  exact T19.force_mem hν ha hg hT hδ reference

example : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
    (fun z => (ins).force ε z - g z) ∈ forceClassT := by
  exact T19.forceDifference_mem hν ha hg hT hδ reference

example : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
    maximalLifespanT ν a ((ins).force ε) = ENNReal.ofReal T := by
  exact T19.lifespan hν ha hg hT hδ reference

example : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
    ∃ w : ClassicalSolutionT ν a ((ins).force ε) T,
      w.velocity = (ins).velocity ε ∧ w.pressure = (ins).pressure ε := by
  exact T19.solution hν ha hg hT hδ reference

example : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
    NSFormalization.Section4.A02.limsupLeft T
        (fun t => NSFormalization.Section4.A02.speedENorm
          (fun x : Space => (ins).velocity ε (t, x))) = ⊤ := by
  exact T19.blowup_limsup hν ha hg hT hδ reference

example : ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
    energyENormT T (fun z => (ins).velocity ε z - (extendByZero reference).velocity z) ≤
      ENNReal.ofReal (((BlowupDensity.Bindings.packetImportFamily.select ν hν).energyBound +
        (BlowupDensity.Bindings.packetImportFamily.select ν hν).dissipationBound) * ε ^ ((1 : ℝ) / 2) +
        (insertionData hν ha hg hT hδ reference).correction.energyConst * ε ^ ((3 : ℝ) / 2)) := by
  exact T19.energyRate hν ha hg hT hδ reference

example : ∀ (p q : ℝ≥0∞), 1 ≤ p → 1 ≤ q →
    0 ≤ (ins).forceDiffMixedConst p q := by
  exact T19.forceDiffMixedConst_nonneg hν ha hg hT hδ reference

example : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
      MemMixedLebesgueT q p (fun z => (ins).force ε z - g z) := by
  exact T19.forceDifference_mixed_memLp hν ha hg hT hδ reference

example : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
    ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
      mixedLebesgueENormT q p (fun z => (ins).force ε z - g z) ≤
        ENNReal.ofReal ((ins).forceDiffMixedConst p q *
          (ε ^ (alphaT p q) +
            ε ^ (alphaT p q + 1))) := by
  exact T19.forceDifference_mixed_bound hν ha hg hT hδ reference

example : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    0 < (ins).forceDiffSobolevConst s := by
  exact T19.forceDiffSobolevConst_pos hν ha hg hT hδ reference

example : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
      MemForceSobolevT 1 s (fun z => (ins).force ε z - g z) := by
  exact T19.forceDifference_sobolev_memLp hν ha hg hT hδ reference

example : ∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
    ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
      forceSobolevENormT 1 s (fun z => (ins).force ε z - g z) ≤
        ENNReal.ofReal ((ins).forceDiffSobolevConst s *
          (ε ^ ((1 : ℝ) / 2 - s) + ε ^ ((3 : ℝ) / 2 - s))) := by
  exact T19.forceDifference_sobolev_bound hν ha hg hT hδ reference

example : ∀ s : ℝ, s < 0 →
    Tendsto (fun ε : ℝ => forceSobolevENormT 1 s (fun z => (ins).force ε z - g z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  exact T19.forceDifference_negativeSobolev_tendsto hν ha hg hT hδ reference

example : ∀ s : ℝ, s < 0 →
    ∀ ε ∈ Ioc (0 : ℝ) (ins).ε₀,
      MemForceSobolevT 1 s (fun z => (ins).force ε z - g z) := by
  exact T19.negative_s_memLp hν ha hg hT hδ reference

example (s : ℝ) (hs : s < 1 / 2) :
    Tendsto (fun ε : ℝ => forceSobolevENormT 1 s (fun z => (ins).force ε z - g z))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  exact T19.forceDifference_sobolev_tendsto hν ha hg hT hδ reference s hs

example : InsertionData := by
  exact insertionData hν ha hg hT hδ reference

example : RawPremises (insertionData hν ha hg hT hδ reference) := by
  exact insertionData_rawPremises hν ha hg hT hδ reference

example : PeriodicInsertionAPI (insertionData hν ha hg hT hδ reference) := by
  exact insertion hν ha hg hT hδ reference

example : EqOn (extendByZero reference).velocity reference.velocity
    (Ico (0 : ℝ) (T + δ) ×ˢ univ) := by
  exact extendByZero_velocity_eqOn reference

example : IsPeriodicOn univ (extendByZero reference).velocity := by
  exact extendByZero_periodic reference

example : ContDiffOn ℝ ∞ (extendByZero reference).velocity
    (Ioo (0 : ℝ) (T + δ) ×ˢ univ) := by
  exact extendByZero_smooth reference

include hν ha hg hT in
example (hreg : RegularThroughT ν a g T) (s : ℝ) (hs : s < 1 / 2)
    (r' : ℝ) (hr' : 0 < r') :
    ∃ f ∈ forceClassT, maximalLifespanT ν a f = ENNReal.ofReal T ∧
      forceSobolevENormT 1 s (fun z => f z - g z) < ENNReal.ofReal r' := by
  exact exists_force_close hν ha hg hT hreg s hs r' hr'

end NSFormalization.Section3.T19.ThreadingProbe
