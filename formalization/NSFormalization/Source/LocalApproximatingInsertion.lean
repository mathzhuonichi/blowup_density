import NSFormalization.Source.LocalReferenceInsertion
import NSFormalization.Source.ForceApproximatingInsertion
import NSFormalization.Paper1.InsertionEnergy

/-!
# Local-reference insertion with simultaneous force and energy convergence

All norms refer to the same explicit physical fields. The reference needs to
be smooth only on its prescribed finite time slab. This theorem proves an
actual singular evolution; identifying it with the arbitrary-data maximal
evolution still requires the separate local existence and uniqueness theory.
-/
noncomputable section
namespace NSFormalization.Source.LocalReferenceInsertion
open NavierStokes.ProblemStatement NavierStokesR3.CompactEnergy
open InsertionFamily Paper1.InsertionEnergy Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal

theorem velocityOn_difference (u v vhat : VelocityField) (x₀ : Space) (T : ℝ)
    (θ : Space → ℝ) (η : ℝ → ℝ) (ε : ℝ) :
    (fun z => velocityOn u v vhat x₀ T θ η ε z - v z) =
      perturbation u vhat x₀ T θ η ε := by
  funext z
  simp only [velocityOn, perturbation, velocity]
  abel

theorem velocityOn_difference_apply (u v vhat : VelocityField) (x₀ : Space) (T : ℝ)
    (θ : Space → ℝ) (η : ℝ → ℝ) (ε : ℝ) (z : SpaceTime) :
    velocityOn u v vhat x₀ T θ η ε z - v z = perturbation u vhat x₀ T θ η ε z :=
  congrFun (velocityOn_difference u v vhat x₀ T θ η ε) z

/-- The actual difference has finite energy and gradient time norms, and its
energy norm tends to zero on the complete presingular interval. -/
def EnergyApproximation (T : ℝ) (v : VelocityField) (V : ℝ → VelocityField) : Prop :=
  (∀ᶠ ε in 𝓝[>] (0 : ℝ),
    MemLp (velocityL2 (fun z => V ε z - v z)) ⊤ (volume.restrict (Ioo (0 : ℝ) T)) ∧
    MemLp (gradientL2 (fun z => V ε z - v z)) 2 (volume.restrict (Ioo (0 : ℝ) T))) ∧
  Tendsto (fun ε => energyNorm T (fun z => V ε z - v z)) (𝓝[>] 0) (𝓝 0)

theorem energyApproximation_of_family {ν δ T τ ε₀ : ℝ} (hδ : 0 < δ) (hT : 0 < T)
    {u v vhat g : VelocityField} {p q : PressureField} {f : VelocityField} {K : Set Space}
    {x₀ : Space} {r : ℝ} {θ : Space → ℝ} {η : ℝ → ℝ}
    (hv : ContDiffOn ℝ ∞ v (Ico (0 : ℝ) (T + δ) ×ˢ univ))
    (hvhat : ContDiff ℝ ∞ vhat)
    (hc : NavierStokesR3.ProblemStatement.CandidateProperties ν u p f K)
    (hD : IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1))
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (hε₀ : 0 < ε₀)
    (hfamily : ∀ ε ∈ Ioo (0 : ℝ) ε₀,
      InsertionProperties ν v q g x₀ r T τ
        (velocityOn u v vhat x₀ T θ η ε) (pressure p q x₀ T ε)
        (force ν f vhat x₀ T θ η ε)) :
    EnergyApproximation T v (velocityOn u v vhat x₀ T θ η) := by
  have hvOn : ContDiffOn ℝ ∞ v (Ico (0 : ℝ) T ×ˢ univ) := hv.mono (by
    intro z hz
    exact ⟨⟨hz.1.1, by linarith [hz.1.2]⟩, hz.2⟩)
  have heps : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) ε₀ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hε₀).filter_mono nhdsWithin_le_nhds] with ε hpos hlt
    exact ⟨hpos, hlt⟩
  have hreg : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ L : Set Space, IsCompact L ∧
      ContDiffOn ℝ ∞ (perturbation u vhat x₀ T θ η ε) (Ioo (0 : ℝ) T ×ˢ univ) ∧
      ∀ t ∈ Ioo (0 : ℝ) T, tsupport (fun x => perturbation u vhat x₀ T θ η ε (t,x)) ⊆ L := by
    filter_upwards [heps] with ε hε
    simpa only [velocityOn_difference, velocityOn_difference_apply] using
      difference_regular_of_properties hvOn (hfamily ε hε)
  constructor
  · obtain ⟨A, B, C, D, _, _, _, _, hb⟩ := insertion_energy_bound hvhat hc.energy_bounded hD
      x₀ hT.le hθ hη hθc hηc
    have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ 2 ≤ T := by
      have ht : Tendsto (fun ε : ℝ => ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
        have hcont : Continuous (fun ε : ℝ => ε ^ 2) := by fun_prop
        simpa using (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
      exact (ht.eventually (eventually_lt_nhds hT)).mono (fun _ h => h.le)
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds, hsmall, hreg]
      with ε hpos hlt hs hr
    obtain ⟨L, hL, hF, hFs⟩ := hr
    have h := hb ε ⟨hpos, hlt.le⟩ hs L hL hF hFs
    simpa only [velocityOn_difference] using And.intro h.1 h.2.1
  · simpa only [velocityOn_difference] using
      insertion_energy_tendsto_zero hvhat hc.energy_bounded hD x₀ hT hθ hη hθc hηc hreg

/-- A single fixed-profile family has the actual PDE, local blowup, preserved
history and support, all subcritical force limits, and energy convergence. -/
theorem exists_local_approximating_insertion {ν δ : ℝ} (hν : 0 < ν) (hδ : 0 < δ)
    {v g : VelocityField} {q : PressureField} {T τ : ℝ}
    (hv : ContDiffOn ℝ ∞ v (Ico (0 : ℝ) (T + δ) ×ˢ univ))
    (hq : ContDiffOn ℝ ∞ q (Ico (0 : ℝ) (T + δ) ×ˢ univ))
    (hvdiv : ∀ t ∈ Ico (0 : ℝ) (T + δ), ∀ x, spatialDivergence v t x = 0)
    (hτ0 : 0 ≤ τ) (hτT : τ < T)
    (hvNS : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x, residual ν v q t x = g (t, x))
    (x₀ : Space) {r : ℝ} (hr : 0 < r) :
    ∃ vhat : VelocityField, ∃ u : VelocityField, ∃ p : PressureField,
    ∃ f : VelocityField, ∃ K : Set Space, ∃ θ : Space → ℝ, ∃ η : ℝ → ℝ, ∃ ε₀ : ℝ,
      0 < ε₀ ∧ NavierStokesR3.ProblemStatement.CandidateProperties ν u p f K ∧
      ForceApproximation ν f vhat x₀ T θ η ∧
      EnergyApproximation T v (velocityOn u v vhat x₀ T θ η) ∧
      ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        InsertionProperties ν v q g x₀ r T τ
          (velocityOn u v vhat x₀ T θ η ε) (pressure p q x₀ T ε)
          (force ν f vhat x₀ T θ η ε) ∧
        AdmissibleCompactForce (force ν f vhat x₀ T θ η ε) := by
  obtain ⟨vhat, u, p, f, K, θ, η, ε₀, hvhat, _, hc, hD,
      hθ, hη, hθc, hηc, hε₀, hfamily⟩ :=
    exists_local_reference_insertion_family hν hδ hv hq hvdiv hτ0 hτT hvNS x₀ hr
  refine ⟨vhat, u, p, f, K, θ, η, ε₀, hε₀, hc,
    forceApproximation_of_smooth ν hc.force_smooth hc.force_support.1 hvhat
      x₀ T hθ hη hθc hηc,
    energyApproximation_of_family hδ (hτ0.trans_lt hτT) hv hvhat hc hD
      hθ hη hθc hηc hε₀ hfamily, ?_⟩
  intro ε hε
  exact ⟨hfamily ε hε, admissibleCompactForce_of_smooth
    (force_smooth_all ν hc.force_smooth hvhat x₀ T ε hθ hη)
    (force_compact_nonzero ν vhat hc.force_support.1 x₀ T ε hε.1.ne' hθc hηc)⟩

end NSFormalization.Source.LocalReferenceInsertion
