import NSFormalization.Section3.T19.ThreadingAt

/-! Theorem 3.6, `paper/revised/sections/03-torus.tex:197-222`:
"Fix any nonempty coordinate ball. For all sufficiently small ε > 0, there
are g_ε ∈ 𝓕 and a solution u_ε" with exact lifespan and blowup, unchanged
history, divergence-free difference supported in a ball of diameter O(ε)
inside the chosen ball, and the simultaneous bounds Eclose/Fclose/Hsclose.
The constants M,D are supplied by the registered packet, C by the correction.
All constants and both fields are chosen before ε and all norm indices.
Support is stated on the fundamental cube (the single torus chart). -/
noncomputable section
namespace NSFormalization.Section3.T19
open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T13 NSFormalization.Section3.T15
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField limsupLeft speedENorm)
open scoped ENNReal

/-- Article-scope insertion from raw data, in every prescribed interior coordinate ball. -/
theorem periodicInsertion_from_data :
  ∀ (ν : ℝ), 0 < ν → ∀ (center : Space) (radius : ℝ), 0 < radius →
    closure (Metric.ball center radius) ⊆ interior fundamentalCube →
    ∀ (a : SpatialField) (g : SpaceTimeField), a ∈ initialClassT → g ∈ forceClassT →
    ∀ (T δ : ℝ), 0 < T → 0 < δ →
    ∀ reference : ClassicalSolutionT ν a g (T + δ),
    ∃ ε₀ > 0, ∃ (force velocity : ℝ → SpaceTimeField),
    ∃ (M D C R : ℝ) (Cpq : ℝ≥0∞ → ℝ≥0∞ → ℝ) (Cs : ℝ → ℝ),
      0 ≤ M ∧ 0 ≤ D ∧ 0 ≤ C ∧ 0 < R ∧
      (∀ p q, 1 ≤ p → 1 ≤ q → 0 ≤ Cpq p q) ∧
      (∀ s : ℝ, 0 ≤ s → s < 1 / 2 → 0 < Cs s) ∧
      (∀ s : ℝ, s < 0 →
        Tendsto (fun ε : ℝ => forceSobolevENormT 1 s (fun z => force ε z - g z))
          (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞))) ∧
      ∀ ε ∈ Ioc (0 : ℝ) ε₀,
        force ε ∈ forceClassT ∧
        (fun z => force ε z - g z) ∈ forceClassT ∧
        maximalLifespanT ν a (force ε) = ENNReal.ofReal T ∧
        (∃ w : ClassicalSolutionT ν a (force ε) T, w.velocity = velocity ε) ∧
        limsupLeft T (fun t => speedENorm (fun x : Space => velocity ε (t, x))) = ⊤ ∧
        (∀ t : ℝ, 0 ≤ t → t ≤ T - 2 * ε ^ 2 → ∀ x : Space,
          velocity ε (t, x) = reference.velocity (t, x)) ∧
        (∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
          spatialDivergence (fun z => velocity ε z - reference.velocity z) t x = 0) ∧
        (∀ t ∈ Ico (0 : ℝ) T,
          tsupport (fun x : Space => velocity ε (t, x) - reference.velocity (t, x)) ∩
            fundamentalCube ⊆ Metric.ball center (ε * R)) ∧
        Metric.ball center (ε * R) ⊆ Metric.ball center radius ∧
        energyENormT T (fun z => velocity ε z - reference.velocity z) ≤
          ENNReal.ofReal ((M + D) * ε ^ ((1 : ℝ) / 2) + C * ε ^ ((3 : ℝ) / 2)) ∧
        (∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q →
          MemMixedLebesgueT q p (fun z => force ε z - g z) ∧
          mixedLebesgueENormT q p (fun z => force ε z - g z) ≤
            ENNReal.ofReal (Cpq p q * (ε ^ (alphaT p q) + ε ^ (alphaT p q + 1)))) ∧
        (∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
          MemForceSobolevT 1 s (fun z => force ε z - g z) ∧
          forceSobolevENormT 1 s (fun z => force ε z - g z) ≤
            ENNReal.ofReal (Cs s * (ε ^ ((1 : ℝ) / 2 - s) + ε ^ ((3 : ℝ) / 2 - s)))) ∧
        (∀ s : ℝ, s < 0 → MemForceSobolevT 1 s (fun z => force ε z - g z)) := by
  intro ν hν center radius hρ hcube a g ha hg T δ hT hδ reference
  let A := insertionAt center radius hρ hcube hν ha hg hT hδ reference
  let d := insertionDataAt center radius hρ hcube hν ha hg hT hδ reference
  have raw := insertionDataAt_rawPremises center radius hρ hcube hν ha hg hT hδ reference
  refine ⟨A.ε₀, A.eps_pos, A.force, A.velocity, d.energyBound, d.dissipationBound,
    d.correction.energyConst, A.diffSupportRadius, A.forceDiffMixedConst,
    A.forceDiffSobolevConst, raw.hM, raw.hD, d.correction.energyConst_nonneg,
    A.diffSupportRadius_pos, A.forceDiffMixedConst_nonneg, A.forceDiffSobolevConst_pos,
    A.forceDifference_negativeSobolev_tendsto, ?_⟩
  intro ε hε
  refine ⟨A.force_mem ε hε, A.forceDifference_mem ε hε, A.lifespan ε hε, ?_,
    A.blowup_limsup ε hε,
    At.history center radius hρ hcube hν ha hg hT hδ reference ε hε,
    At.velocityDifference_divFree center radius hρ hcube hν ha hg hT hδ reference ε hε,
    At.velocityDifference_support center radius hρ hcube hν ha hg hT hδ reference ε hε,
    A.diffSupport_in_chart ε hε,
    At.energyRate center radius hρ hcube hν ha hg hT hδ reference ε hε,
    ?_, ?_, fun s hs => A.negative_s_memLp s hs ε hε⟩
  · obtain ⟨w, hw, _⟩ := A.solution ε hε
    exact ⟨w, hw⟩
  · intro p q _ hq
    exact ⟨A.forceDifference_mixed_memLp p q hq ε hε,
      A.forceDifference_mixed_bound p q hq ε hε⟩
  · intro s hs hs'
    exact ⟨A.forceDifference_sobolev_memLp s hs hs' ε hε,
      A.forceDifference_sobolev_bound s hs hs' ε hε⟩

end NSFormalization.Section3.T19
