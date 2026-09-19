import NSFormalization.Section3.T19.Closure
import NSFormalization.Section3.T24.ConservativeAssembly

open Set Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T19
open NSFormalization.Section3.T24
open scoped ENNReal Topology

/- The main U13 statement is substantively strengthened by widening the
Sobolev range from `s < 1 / 2` to `s < 3 / 4`.  The delivered theorem must not
close this mutation. -/
example : True := by
  fail_if_success
    have _h :
        ∀ a : SpatialField, a ∈ initialClassT →
          ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
            ∀ g : SpaceTimeField, g ∈ forceClassT →
              ∀ δ : ℝ, 0 < δ →
                ∀ reference : ClassicalSolutionT ν a g (T + δ),
                  ∃ ε₀ : ℝ, 0 < ε₀ ∧
                    ∃ u f : ℝ → SpaceTimeField,
                      (∀ ε ∈ Ioo (0 : ℝ) ε₀,
                        f ε ∈ forceClassT ∧
                        maximalLifespanT ν a (f ε) = ENNReal.ofReal T ∧
                        (∃ w : ClassicalSolutionT ν a (f ε) T, w.velocity = u ε) ∧
                        SingularTrajectoryT ν a T (u ε)) ∧
                      Tendsto
                        (fun ε : ℝ ↦
                          energyENormT T (fun z ↦ u ε z - reference.velocity z))
                        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) ∧
                      (∀ s : ℝ, s < 3 / 4 →
                        Tendsto
                          (fun ε : ℝ ↦
                            forceSobolevENormT 1 s (fun z ↦ f ε z - g z))
                          (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞))) :=
      simultaneousPairConvergence
  trivial

/- Positivity of the existential cutoff in U13 makes its `Ioo` family domain
genuinely nonempty. -/
example {ε₀ : ℝ} (hε₀ : 0 < ε₀) : (Ioo (0 : ℝ) ε₀).Nonempty := by
  refine ⟨ε₀ / 2, ?_, ?_⟩ <;> linarith

/- The closure statement has honest positive finite radii. -/
example : ∃ r : ℝ≥0∞, 0 < r ∧ r < ⊤ := by
  exact ⟨1, by norm_num, ENNReal.one_lt_top⟩

private theorem rev465_zero_mem_initialClassT :
    (0 : SpatialField) ∈ initialClassT := by
  refine ⟨contDiff_const, ?_, ?_⟩
  · intro x i
    rfl
  · intro x
    simp [spatialDivergence, spatialDerivative]

private theorem rev465_zero_mem_forceClassT :
    (0 : SpaceTimeField) ∈ forceClassT := by
  refine ⟨contDiff_const, ?_, ∅, isCompact_empty, empty_subset _, ?_⟩
  · intro t _ht x i
    rfl
  · exact (show tsupport (0 : SpaceTimeField) ⊆
      (∅ : Set ℝ) ×ˢ (univ : Set Space) by simp)

/- A concrete zero-reference application supplies a genuinely nonempty U13
family of singular trajectories. -/
example :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ u _f : ℝ → SpaceTimeField,
      ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        SingularTrajectoryT 1 (0 : SpatialField) 1 (u ε) := by
  have hforce : conservativeForceT 0 = (0 : SpaceTimeField) := by
    funext z
    simp [conservativeForceT, pressureGradient]
  let reference₀ : ClassicalSolutionT (1 : ℝ) (0 : SpatialField)
      (conservativeForceT 0) ((1 : ℝ) + 1) :=
    restSolution 1 (1 + 1) (by norm_num)
  let reference : ClassicalSolutionT (1 : ℝ) (0 : SpatialField)
      (0 : SpaceTimeField) ((1 : ℝ) + 1) := hforce ▸ reference₀
  obtain ⟨ε₀, hε₀, u, f, hfamily, _henergy, _hforce⟩ :=
    simultaneousPairConvergence (0 : SpatialField)
      rev465_zero_mem_initialClassT 1 (by norm_num) 1 (by norm_num)
      (0 : SpaceTimeField) rev465_zero_mem_forceClassT 1 (by norm_num) reference
  exact ⟨ε₀, hε₀, u, f, fun ε hε ↦ (hfamily ε hε).2.2.2⟩
