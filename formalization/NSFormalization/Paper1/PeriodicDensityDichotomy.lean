import NSFormalization.Paper1.PeriodicDensityFiber
import NSFormalization.Paper1.PeriodicFlowRestriction
import NSFormalization.Paper1.PeriodicInitialData

/-!
# The concrete periodic density dichotomy

This module assembles the two cases in Paper 1, Proposition `prop:density`,
for the actual smooth periodic flow class. A positive flow witness is retained
in the conclusion, so the empty supremum cannot stand for a singular solution.
Because test forces vanish near time zero, one unforced local flow from the
initial datum supplies the local witness for every test force. The resting
initial datum has such a flow explicitly. Local existence for every admissible
smooth divergence-free periodic initial datum and
identification with the manuscript's normalized maximal solution remain separate.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicDensityDichotomy

open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Source
open NSFormalization.Paper1.PeriodicForceSpace
open NSFormalization.Paper1.PeriodicLifespan
open NSFormalization.Paper1.PeriodicDensityFiber
open NSFormalization.Paper1.PeriodicForceConvergence
open NSFormalization.Paper1.PeriodicInitialData
open scoped ContDiff ENNReal

@[simp] theorem forceDistance_self (s : ℝ) (g : VelocityField) :
    forceDistance s g g = 0 := by
  simp [forceDistance, periodicVectorSobolevNorm, periodicSobolevSq,
    coordinateForce, periodicFourierCoeff_eq_cube, PeriodicIntegration.cubeIntegral]

/-- Changing a force outside the open equation interval leaves the same flow
valid. No extension of its velocity or pressure is asserted. -/
def flowWithForce {ν S : ℝ} {a : Space → Space} {f g : VelocityField}
    (W : Flow ν a f S)
    (hfg : ∀ t ∈ Ioo (0 : ℝ) S, ∀ x, f (t, x) = g (t, x)) :
    Flow ν a g S :=
  { W with equation := fun t ht x => (W.equation t ht x).trans (hfg t ht x) }

/-- The smooth positive-time force class is identically zero before some
strictly positive time, including all negative times. -/
theorem force_zero_before {g : VelocityField} (hg : IsTestForce g) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ t < τ, ∀ x, g (t, x) = 0 := by
  obtain ⟨τ, hτ, hlower⟩ :=
    NSFormalization.Paper1.PeriodicDensityFiber.IsTestForce.exists_positive_time_lower_bound hg
  refine ⟨τ, hτ, ?_⟩
  intro t ht x
  by_contra hne
  exact (not_le_of_gt ht) (hlower (t, x) (subset_tsupport g hne))

/-- One unforced local solution is sufficient to initiate every force in
the paper's test-force class, since each such force vanishes near zero. -/
theorem localFlow_for_testForce {ν R : ℝ} {a : Space → Space}
    (W : Flow ν a (0 : VelocityField) R) {g : VelocityField} (hg : IsTestForce g) :
    ∃ S : ℝ, Nonempty (Flow ν a g S) := by
  obtain ⟨τ, hτ, hgzero⟩ := force_zero_before hg
  let S := min R τ
  have hS : 0 < S := lt_min W.horizon_pos hτ
  refine ⟨S, ⟨flowWithForce (W.restrict hS (min_le_left R τ)) ?_⟩⟩
  intro t ht x
  exact (hgzero t (ht.2.trans_le (min_le_right R τ)) x).symm

/-- A positive actual flow witness excludes the empty-supremum case. -/
theorem lifespan_pos_of_flow {ν S : ℝ} {a : Space → Space} {g : VelocityField}
    (W : Flow ν a g S) : 0 < lifespan ν a g :=
  (ENNReal.ofReal_pos.mpr W.horizon_pos).trans_le (horizon_le_lifespan W)

/-- The two-case density argument at any force possessing a genuine local
flow. The result has a positive lifespan and an actual local solution, even
when the original force is already singular by the deadline. -/
theorem exists_nearby_singular_force_of_localFlow
    {ν T s : ℝ} (hν : 0 < ν) (hT : 0 < T) (hs : s < 1 / 2)
    {a : Space → Space} {g : VelocityField} (hg : IsTestForce g)
    (hlocal : ∃ S : ℝ, Nonempty (Flow ν a g S))
    {ρ : ℝ≥0∞} (hρ : 0 < ρ) :
    ∃ G : VelocityField, IsTestForce G ∧ forceDistance s G g < ρ ∧
      (∃ R : ℝ, Nonempty (Flow ν a G R)) ∧
      0 < lifespan ν a G ∧ lifespan ν a G ≤ ENNReal.ofReal T := by
  rcases bad_or_regular_reference hT.le a g with hbad | ⟨S, hTS, hW⟩
  · obtain ⟨R, hR⟩ := hlocal
    exact ⟨g, hg, by simpa using hρ, ⟨R, hR⟩,
      lifespan_pos_of_flow hR.some, hbad⟩
  · obtain ⟨U, F, P, hp, hG, hdist, hlife⟩ := exists_periodic_insertion_fiber_member
      hν (half_pos hT) (half_lt_self hT) hT hTS hg hW.some
      (r := 1 / 4) (by norm_num) (by norm_num) hs hρ
    refine ⟨(fun z => g z + F z), hG, hdist,
      ⟨T, ⟨insertionFlow (half_pos hT).le (half_lt_self hT) hp hW.some.initial⟩⟩,
      ?_, hlife.le⟩
    rw [hlife]
    exact ENNReal.ofReal_pos.mpr hT

/-- For a fixed initial datum, one unforced local flow suffices for the full
test-force quantifier in the concrete positive-lifespan density statement. -/
theorem exists_nearby_singular_force_of_unforced_localFlow
    {ν T s R : ℝ} (hν : 0 < ν) (hT : 0 < T) (hs : s < 1 / 2)
    {a : Space → Space} (W : Flow ν a (0 : VelocityField) R)
    {g : VelocityField} (hg : IsTestForce g) {ρ : ℝ≥0∞} (hρ : 0 < ρ) :
    ∃ G : VelocityField, IsTestForce G ∧ forceDistance s G g < ρ ∧
      (∃ S : ℝ, Nonempty (Flow ν a G S)) ∧
      0 < lifespan ν a G ∧ lifespan ν a G ≤ ENNReal.ofReal T :=
  exists_nearby_singular_force_of_localFlow hν hT hs hg
    (localFlow_for_testForce W hg) hρ

/-- The unforced solution at rest exists on every positive horizon. -/
def restingFlow (ν : ℝ) {S : ℝ} (hS : 0 < S) :
    Flow ν (fun _ => 0) (0 : VelocityField) S where
  velocity := fun _ => 0
  pressure := fun _ => 0
  horizon_pos := hS
  velocity_smooth := contDiffOn_const
  pressure_smooth := contDiffOn_const
  velocity_periodic := fun _ _ _ _ => rfl
  pressure_periodic := fun _ _ _ _ => rfl
  initial := fun _ => rfl
  divergence := by intro t ht x; simp [spatialDivergence, spatialDerivative]
  equation := by
    intro t ht x
    simp [Source.residual, temporalDerivative, advection, spatialLaplacian,
      spatialDerivative, pressureGradient]

/-- The zero-data density approximation has no assumed local-existence or
maximal-flow premise. It concerns the actual `Flow` lifespan, with a positive
solution witness retained, and uses the genuine periodic force gauge. -/
theorem exists_nearby_singular_force_from_rest
    {ν T s : ℝ} (hν : 0 < ν) (hT : 0 < T) (hs : s < 1 / 2)
    {g : VelocityField} (hg : IsTestForce g) {ρ : ℝ≥0∞} (hρ : 0 < ρ) :
    ∃ G : VelocityField, IsTestForce G ∧ forceDistance s G g < ρ ∧
      (∃ S : ℝ, Nonempty (Flow ν (fun _ => 0) G S)) ∧
      0 < lifespan ν (fun _ => 0) G ∧
      lifespan ν (fun _ => 0) G ≤ ENNReal.ofReal T :=
  exists_nearby_singular_force_of_unforced_localFlow hν hT hs
    (restingFlow ν zero_lt_one) hg hρ

theorem zero_slice_density_from_rest
    {ν T s : ℝ} (hν : 0 < ν) (hT : 0 < T) (hs : s < 1 / 2)
    {g : VelocityField} (hg : IsTestForce g) {ρ : ℝ≥0∞} (hρ : 0 < ρ) :
    ∃ G : VelocityField, IsTestForce G ∧ forceDistance s G g < ρ ∧
      lifespan ν (fun _ => 0) G ≤ ENNReal.ofReal T := by
  obtain ⟨G, hG, hdist, _, _, hupper⟩ :=
    exists_nearby_singular_force_from_rest hν hT hs hg hρ
  exact ⟨G, hG, hdist, hupper⟩

/-! Local existence is quantified over the manuscript's admissible initial
data. Quantifying over all functions `Space → Space` would be impossible:
every `Flow` already implies `IsAdmissibleInitialData` at time zero. -/
def UnforcedLocalExistence (ν : ℝ) : Prop :=
  ∀ a : Space → Space, IsAdmissibleInitialData a →
    ∃ R : ℝ, Nonempty (Flow ν a (0 : VelocityField) R)

theorem periodic_density_fixed_slice_of_unforced_local
    {ν T s : ℝ} (hν : 0 < ν) (hT : 0 < T) (hs : s < 1 / 2)
    (hlocal : UnforcedLocalExistence ν) {a : Space → Space}
    (ha : IsAdmissibleInitialData a)
    {g : VelocityField} (hg : IsTestForce g) {ρ : ℝ≥0∞} (hρ : 0 < ρ) :
    ∃ G : VelocityField, IsTestForce G ∧ forceDistance s G g < ρ ∧
      lifespan ν a G ≤ ENNReal.ofReal T := by
  obtain ⟨R, hR⟩ := hlocal a ha
  obtain ⟨G, hG, hdist, _, _, hupper⟩ :=
    exists_nearby_singular_force_of_unforced_localFlow hν hT hs hR.some hg hρ
  exact ⟨G, hG, hdist, hupper⟩

end NSFormalization.Paper1.PeriodicDensityDichotomy
