import Contracts.V1.PeriodicInsertion

/-! Theorem 3.6 (`03-torus.tex:197-222`) from only the article's raw data.
"Fix any nonempty coordinate ball"; clauses (i)–(iv), including single-chart
support and simultaneous Eclose/Fclose/Hsclose, and the negative-order limit.
The implementation supplies M,D from the registered packet. No packet,
placement, scaling or correction record is an argument. -/
namespace BlowupDensity.Contracts.V2.PeriodicInsertion
open Set MeasureTheory Filter Topology
open BlowupDensity.Contracts.V1 BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData BlowupDensity.Contracts.V1.TorusLocalTheory
open BlowupDensity.Contracts.V1.MaximalPartial
open BlowupDensity.T15.Draft
open scoped ENNReal

def periodicInsertionStatementV2 : Prop :=
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
            ENNReal.ofReal (Cpq p q * (ε ^ (BlowupDensity.Contracts.V1.alpha p q) + ε ^ (BlowupDensity.Contracts.V1.alpha p q + 1)))) ∧
        (∀ s : ℝ, 0 ≤ s → s < 1 / 2 →
          MemForceSobolevT 1 s (fun z => force ε z - g z) ∧
          forceSobolevENormT 1 s (fun z => force ε z - g z) ≤
            ENNReal.ofReal (Cs s * (ε ^ ((1 : ℝ) / 2 - s) + ε ^ ((3 : ℝ) / 2 - s)))) ∧
        (∀ s : ℝ, s < 0 → MemForceSobolevT 1 s (fun z => force ε z - g z))

end BlowupDensity.Contracts.V2.PeriodicInsertion
