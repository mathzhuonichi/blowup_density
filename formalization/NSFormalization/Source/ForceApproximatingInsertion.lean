import NSFormalization.Source.InsertionForceConvergence
import NSFormalization.Source.InsertionMixedNorms
import NSFormalization.Source.GridInsertionFamily
import NSFormalization.Paper3.CompactForceAdmissibility

/-!
# One singular family with simultaneous force approximation

The existential quantifiers precede every norm exponent: the same packet,
cutoffs and inserted fields work for all the stated topologies and observations.
The reference here is globally smooth. Arbitrary-data local existence, the
critical obstructions and the manuscripts' full maximal-lifespan theory remain
separate obligations.
-/
noncomputable section
namespace NSFormalization.Source.InsertionFamily
open NavierStokes.ProblemStatement NavierStokesR3.CompactEnergy
open MeasureTheory Set Filter Topology
open Paper1.CorrectionMixedNorms Paper3
open scoped ContDiff ENNReal

/-- The actual compact physical force has Sobolev-valued smoothness and both
global Bochner time integrability properties at every nonnegative integer order. -/
def AdmissibleCompactForce (F : VelocityField) : Prop :=
  ∃ hF : ContDiff ℝ ∞ F, ∃ hc : HasCompactSupport F,
    ∀ m : ℕ, ContDiff ℝ ∞ (compactVectorFourierLp (m : ℝ) F hF hc) ∧
      MemLp (compactVectorFourierLp (m : ℝ) F hF hc) 1 volume ∧
      MemLp (compactVectorFourierLp (m : ℝ) F hF hc) 2 volume

theorem admissibleCompactForce_of_smooth {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) : AdmissibleCompactForce F :=
  ⟨hF, hc, compact_vector_force_sobolev_regular hF hc⟩

/-- Simultaneous limits in the exact angular Fourier convention and in the
actual mixed Lebesgue norms, all measured on the entire real time axis. -/
def ForceApproximation (ν : ℝ) (f v : VelocityField) (x₀ : Space) (T : ℝ)
    (θ : Space → ℝ) (η : ℝ → ℝ) : Prop :=
  (∀ s : ℝ, s < 1 / 2 → Tendsto (fun ε : ℝ => eLpNorm
    (vectorAngularSobolevNorm s (force ν f v x₀ T θ η ε)) 1 volume) (𝓝[>] 0) (𝓝 0)) ∧
  (∀ s : ℝ, s < -1 / 2 → Tendsto (fun ε : ℝ => eLpNorm
    (vectorAngularSobolevNorm s (force ν f v x₀ T θ η ε)) 2 volume) (𝓝[>] 0) (𝓝 0)) ∧
  (∀ p q : ℝ≥0∞, 1 ≤ p → 1 ≤ q → 0 < -3 + 3 / p.toReal + 2 / q.toReal →
    Tendsto (fun ε : ℝ => mixedNorm p q (force ν f v x₀ T θ η ε)) (𝓝[>] 0) (𝓝 0))

theorem forceApproximation_of_smooth (ν : ℝ) {f v : VelocityField}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    ForceApproximation ν f v x₀ T θ η :=
  ⟨fun _ hs => force_angular_L1_tendsto_zero ν hf hfc hv x₀ T hθ hη hθc hηc hs,
    fun _ hs => force_angular_L2_tendsto_zero ν hf hfc hv x₀ T hθ hη hθc hηc hs,
    fun p q hp hq hβ => force_mixed_tendsto_zero ν hf hfc hv x₀ T hθ hη hθc hηc p q hp hq hβ⟩

theorem exists_force_approximating_insertion {ν : ℝ} (hν : 0 < ν)
    {v g : VelocityField} {q : PressureField}
    (hv : ContDiff ℝ ∞ v) (hq : ContDiff ℝ ∞ q)
    (hvdiv : ∀ t x, spatialDivergence v t x = 0)
    (x₀ : Space) {r T τ : ℝ} (hr : 0 < r) (hτ0 : 0 ≤ τ) (hτT : τ < T)
    (hvNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, residual ν v q t x = g (t, x)) :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
    ∃ θ : Space → ℝ, ∃ η : ℝ → ℝ, ∃ ε₀ : ℝ,
      NavierStokesR3.ProblemStatement.CandidateProperties ν u p f K ∧
      IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1) ∧
      ContDiff ℝ ∞ θ ∧ ContDiff ℝ ∞ η ∧
      HasCompactSupport θ ∧ HasCompactSupport η ∧ 0 < ε₀ ∧
      ForceApproximation ν f v x₀ T θ η ∧
      ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        InsertionProperties ν v q g x₀ r T τ
          (velocity u v x₀ T θ η ε) (pressure p q x₀ T ε) (force ν f v x₀ T θ η ε) ∧
        AdmissibleCompactForce (force ν f v x₀ T θ η ε) := by
  obtain ⟨u, p, f, K, θ, η, ε₀, hc, hD, hθ, hη, hθc, hηc, hε₀, hfamily⟩ :=
    exists_insertion_family hν hv hq hvdiv x₀ hr hτ0 hτT hvNS
  refine ⟨u, p, f, K, θ, η, ε₀, hc, hD, hθ, hη, hθc, hηc, hε₀,
    forceApproximation_of_smooth ν hc.force_smooth hc.force_support.1 hv x₀ T hθ hη hθc hηc, ?_⟩
  intro ε hε
  exact ⟨hfamily ε hε, admissibleCompactForce_of_smooth
    (force_smooth_all ν hc.force_smooth hv x₀ T ε hθ hη)
    (force_compact_nonzero ν v hc.force_support.1 x₀ T ε hε.1.ne' hθc hηc)⟩

/-- The same singular family simultaneously preserves every grid-cell average
and converges in every subcritical force norm listed in `ForceApproximation`. -/
theorem exists_force_approximating_grid_insertion {J : Type*} [Fintype J]
    (grids : J → CartesianGrid) {ν : ℝ} (hν : 0 < ν)
    {v g : VelocityField} {q : PressureField}
    (hv : ContDiff ℝ ∞ v) (hq : ContDiff ℝ ∞ q) (hg : ContDiff ℝ ∞ g)
    (hvdiv : ∀ t x, spatialDivergence v t x = 0)
    {T τ : ℝ} (hτ0 : 0 ≤ τ) (hτT : τ < T)
    (hvNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, residual ν v q t x = g (t, x)) :
    ∃ x₀ : Space, ∃ r : ℝ, ∃ u : VelocityField, ∃ p : PressureField,
    ∃ f : VelocityField, ∃ K : Set Space, ∃ θ : Space → ℝ, ∃ η : ℝ → ℝ, ∃ ε₀ : ℝ,
      0 < r ∧ NavierStokesR3.ProblemStatement.CandidateProperties ν u p f K ∧
      IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1) ∧
      ContDiff ℝ ∞ θ ∧ ContDiff ℝ ∞ η ∧
      HasCompactSupport θ ∧ HasCompactSupport η ∧ 0 < ε₀ ∧
      ForceApproximation ν f v x₀ T θ η ∧
      ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        InsertionProperties ν v q g x₀ r T τ
          (velocity u v x₀ T θ η ε) (pressure p q x₀ T ε) (force ν f v x₀ T θ η ε) ∧
        AdmissibleCompactForce (force ν f v x₀ T θ η ε) ∧
        ∀ t ∈ Ico (0 : ℝ) T, ∀ j k i,
          componentCellAverage ((grids j).cell k) (fun x => velocity u v x₀ T θ η ε (t, x)) i =
            componentCellAverage ((grids j).cell k) (fun x => v (t, x)) i ∧
          componentCellAverage ((grids j).cell k) (fun x => g (t, x) + force ν f v x₀ T θ η ε (t, x)) i =
            componentCellAverage ((grids j).cell k) (fun x => g (t, x)) i := by
  obtain ⟨x₀, r, u, p, f, K, θ, η, ε₀, hr, hc, hD, hθ, hη, hθc, hηc, hε₀, hfamily⟩ :=
    GridInsertionFamily.exists_grid_insertion_family grids hν hv hq hg hvdiv hτ0 hτT hvNS
  refine ⟨x₀, r, u, p, f, K, θ, η, ε₀, hr, hc, hD, hθ, hη, hθc, hηc, hε₀,
    forceApproximation_of_smooth ν hc.force_smooth hc.force_support.1 hv x₀ T hθ hη hθc hηc, ?_⟩
  intro ε hε
  exact ⟨(hfamily ε hε).1, admissibleCompactForce_of_smooth
    (force_smooth_all ν hc.force_smooth hv x₀ T ε hθ hη)
    (force_compact_nonzero ν v hc.force_support.1 x₀ T ε hε.1.ne' hθc hηc), (hfamily ε hε).2⟩

end NSFormalization.Source.InsertionFamily
