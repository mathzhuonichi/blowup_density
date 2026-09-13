import NSFormalization.Paper1.PeriodicForceSpace
import NSFormalization.Paper1.PeriodicSubcriticalMainline
import NSFormalization.Paper1.PeriodicForceConvergence
import NSFormalization.Paper1.PeriodicFlowRestriction

/-!
# Fixed-initial-data periodic singular-force fiber

This is the concrete fixed-profile density fiber supplied by the insertion
construction.  It separates the analytic force approximation from the still
missing identification of the paper's maximal solution with the actual flow
class used by `PeriodicLifespan`.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicDensityFiber

open Set Filter MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Source
open NSFormalization.Paper1.PeriodicForceSpace
open NSFormalization.Paper1.PeriodicLifespan
open NSFormalization.Paper1.PeriodicForceConvergence
open NSFormalization.Paper1.PeriodicInsertion
open NSFormalization.Paper1.PeriodicSubcriticalMainline
open NavierStokes.PeriodicLocalization
open scoped ContDiff ENNReal Topology

/-- The extended-valued periodic `L¹_t H^s_x` gauge used for the force fiber.
It is a convergence gauge only; no separation or completeness assertion is
made here. -/
def forceDistance (s : ℝ) (f₁ f₂ : VelocityField) : ℝ≥0∞ :=
  eLpNorm (fun t : ℝ =>
    NSFormalization.Paper1.PeriodicForceConvergence.periodicVectorSobolevNorm
      s (f₁ - f₂) t) 1 volume

theorem forceDistance_comm (s : ℝ) (f₁ f₂ : VelocityField) :
    forceDistance s f₁ f₂ = forceDistance s f₂ f₁ := by
  unfold forceDistance
  apply eLpNorm_congr_ae
  filter_upwards [] with t
  rw [show f₁ - f₂ = -(f₂ - f₁) by
    funext z
    simp [sub_eq_add_neg]]
  exact periodicVectorSobolevNorm_neg s (f₂ - f₁) t

theorem forceDistance_total_add (s : ℝ) (g F : VelocityField) :
    forceDistance s (fun z => g z + F z) g =
      eLpNorm (fun t =>
        NSFormalization.Paper1.PeriodicForceConvergence.periodicVectorSobolevNorm
          s F t) 1 volume := by
  unfold forceDistance
  have hsub : (fun z => g z + F z) - g = F := by
    funext z
    simp
  rw [hsub]

/-- Exact positive-horizon existence in the actual periodic flow class.
Despite the historical name, this predicate does not identify pressures or
construct the manuscript's normalized maximal solution. For inserted fields
it follows from restriction and the proved obstruction to later flows. -/
def MaximalFlowIdentified (ν : ℝ) (a : Space → Space) (f : VelocityField)
    (T : ℝ) : Prop :=
  ∀ S : ℝ, 0 < S → (Nonempty (Flow ν a f S) ↔ S ≤ T)

/-- Compact positive-time support admits a strictly positive lower time. -/
theorem IsTestForce.exists_positive_time_lower_bound
    {g : VelocityField} (hg : IsTestForce g) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ z ∈ tsupport g, τ ≤ z.1 := by
  obtain ⟨K, hK, hKpos, hKg⟩ := hg.time_support
  by_cases hne : K.Nonempty
  · obtain ⟨τ, hτK, hleast⟩ := hK.exists_isLeast hne
    refine ⟨τ, hKpos hτK, ?_⟩
    intro z hz
    exact hleast (hKg hz).1
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz
    exact (hne ⟨z.1, (hKg hz).1⟩).elim

/-- Given a regular periodic reference flow continuing past `T`, the actual
insertion family supplies arbitrarily small periodic singular force
perturbations at the same initial datum.  The distance is stated in the
concrete periodic `L¹_t H^s_x` norm used by Paper 1. -/
theorem exists_periodic_singular_force_approximation
    {ν T τ S : ℝ} (hν : 0 < ν) (hτ : 0 < τ) (hτT : τ < T)
    (hT : 0 < T) (hτS : T < S) {a : Space → Space} {g : VelocityField}
    (hg : IsTestForce g) (W : Flow ν a g S) {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1 / 2) {s : ℝ} (hs : s < 1 / 2)
    {ρ : ℝ≥0∞} (hρ : 0 < ρ) :
    ∃ F : VelocityField, IsTestForce F ∧
      forceDistance s (fun z => g z + F z) g < ρ ∧
      lifespan ν a (fun z => g z + F z) = ENNReal.ofReal T := by
  obtain ⟨vhat, u, p, f, K, θ, η, ε₀, hvhat, hc, hθ, hη, hθc, hηc,
      hε₀, hfamily⟩ := PeriodicForceSpace.exists_testForce_insertion_family
    hν hτ hτT hr hrhalf hg W hτS
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      eLpNorm (fun t =>
        NSFormalization.Paper1.PeriodicForceConvergence.periodicVectorSobolevNorm s
        (periodize (InsertionFamily.force ν f vhat 0 T θ η ε)) t) 1 volume < ρ := by
    exact (insertion_force_subcritical_mainline ν hc.force_smooth hc.force_support.1
      hvhat T hθ hη hθc hηc hs).eventually (eventually_lt_nhds hρ)
  have heps : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo (0 : ℝ) ε₀ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hε₀).filter_mono nhdsWithin_le_nhds] with ε hpos hlt
    exact ⟨hpos, hlt⟩
  obtain ⟨ε, hε, hεsmall⟩ := (heps.and hsmall).exists
  obtain ⟨hp, htest, hLife⟩ := hfamily ε hε
  refine ⟨PeriodicInsertion.force (InsertionFamily.force ν f vhat 0 T θ η ε),
    testForce_of_insertion hτ hp, ?_, hLife⟩
  rw [forceDistance_total_add]
  simpa only [PeriodicInsertion.force] using hεsmall

/-- The same fiber approximation while retaining the complete insertion
properties.  In particular, `hp` carries the periodic PDE, divergence-free
condition, support and local blow-up data; the smallness estimate is attached
to its actual force component. -/
theorem exists_periodic_insertion_fiber_member
    {ν T τ S : ℝ} (hν : 0 < ν) (hτ : 0 < τ) (hτT : τ < T)
    (hT : 0 < T) (hτS : T < S) {a : Space → Space} {g : VelocityField}
    (hg : IsTestForce g) (W : Flow ν a g S) {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1 / 2) {s : ℝ} (hs : s < 1 / 2)
    {ρ : ℝ≥0∞} (hρ : 0 < ρ) :
    ∃ U F : VelocityField, ∃ P : PressureField,
      NSFormalization.Paper1.PeriodicInsertion.Properties
        ν r T τ W.velocity W.pressure g U F P ∧
      IsTestForce (fun z => g z + F z) ∧
      forceDistance s (fun z => g z + F z) g < ρ ∧
      lifespan ν a (fun z => g z + F z) = ENNReal.ofReal T := by
  obtain ⟨vhat, u, p, f, K, θ, η, ε₀, hvhat, hc, hθ, hη, hθc, hηc,
      hε₀, hfamily⟩ := PeriodicForceSpace.exists_testForce_insertion_family
    hν hτ hτT hr hrhalf hg W hτS
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      eLpNorm (fun t => periodicVectorSobolevNorm s
        (periodize (InsertionFamily.force ν f vhat 0 T θ η ε)) t) 1 volume < ρ := by
    exact (insertion_force_subcritical_mainline ν hc.force_smooth hc.force_support.1
      hvhat T hθ hη hθc hηc hs).eventually (eventually_lt_nhds hρ)
  have heps : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo (0 : ℝ) ε₀ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hε₀).filter_mono nhdsWithin_le_nhds] with ε hpos hlt
    exact ⟨hpos, hlt⟩
  obtain ⟨ε, hε, hεsmall⟩ := (heps.and hsmall).exists
  obtain ⟨hp, htest, hLife⟩ := hfamily ε hε
  let U : VelocityField := PeriodicInsertion.velocity T W.velocity
    (Source.LocalReferenceInsertion.velocityOn u W.velocity vhat 0 T θ η ε)
  let P : PressureField := PeriodicInsertion.pressure T W.pressure
    (Source.InsertionFamily.pressure p W.pressure 0 T ε)
  let F : VelocityField := PeriodicInsertion.force
    (Source.InsertionFamily.force ν f vhat 0 T θ η ε)
  refine ⟨U, F, P, ?_, ?_, ?_, hLife⟩
  · simpa only [U, P, F] using hp
  · simpa only [U, P, F] using htest
  · rw [forceDistance_total_add]
    simpa only [F, PeriodicInsertion.force] using hεsmall

/-- The same construction stated directly in the force space: the returned
object is the total force `g + F`, while the distance is measured from `g`.
This is still a fixed-profile, subcritical fiber statement; it does not
assert the paper's unrestricted density proposition. -/
theorem exists_periodic_singular_total_force_approximation
    {ν T τ S : ℝ} (hν : 0 < ν) (hτ : 0 < τ) (hτT : τ < T)
    (hT : 0 < T) (hτS : T < S) {a : Space → Space} {g : VelocityField}
    (hg : IsTestForce g) (W : Flow ν a g S) {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1 / 2) {s : ℝ} (hs : s < 1 / 2)
    {ρ : ℝ≥0∞} (hρ : 0 < ρ) :
    ∃ G : VelocityField, IsTestForce G ∧
      forceDistance s G g < ρ ∧
      lifespan ν a G = ENNReal.ofReal T := by
  obtain ⟨F, hF, hdist, hlife⟩ := exists_periodic_singular_force_approximation
    hν hτ hτT hT hτS hg W hr hrhalf hs hρ
  refine ⟨(fun z => g z + F z), hg.add hF, ?_, hlife⟩
  · simpa only [forceDistance_total_add] using hdist

/-- The total-force approximation has exactly the positive flow horizons
`S ≤ T`. This follows from the constructed flow and its restrictions; no
additional maximal-flow hypothesis is needed. -/
theorem exists_periodic_singular_total_force_approximation_identified
    {ν T τ S : ℝ} (hν : 0 < ν) (hτ : 0 < τ) (hτT : τ < T)
    (hT : 0 < T) (hτS : T < S) {a : Space → Space} {g : VelocityField}
    (hg : IsTestForce g) (W : Flow ν a g S) {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1 / 2) {s : ℝ} (hs : s < 1 / 2)
    {ρ : ℝ≥0∞} (hρ : 0 < ρ) :
    ∃ G : VelocityField, IsTestForce G ∧
      forceDistance s G g < ρ ∧
      lifespan ν a G = ENNReal.ofReal T ∧
      MaximalFlowIdentified ν a G T := by
  obtain ⟨U, F, P, hp, hG, hdist, hlife⟩ := exists_periodic_insertion_fiber_member
    hν hτ hτT hT hτS hg W hr hrhalf hs hρ
  exact ⟨(fun z => g z + F z), hG, hdist, hlife,
    PeriodicLifespan.flow_nonempty_iff_le_of_insertion hν hτ.le hτT hp W.initial⟩

end NSFormalization.Paper1.PeriodicDensityFiber
