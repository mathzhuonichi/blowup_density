import NSFormalization.Paper1.PeriodicDensityDichotomy

/-!
# Subcritical density in the periodic force gauge

This file is the compact Paper 1 density interface.  It works directly with
the extended-valued periodic `L¹_t H^s_x` gauge `forceDistance`; no metric or
topological structure is put on the subtype of test forces.  The singular
slice is the set of test forces whose actual-flow lifespan is at most the
prescribed deadline.  The two density theorems below separate the unconditional
zero-data slice from the conditional arbitrary-admissible-data slice.
-/
noncomputable section

namespace NSFormalization.Paper1.PeriodicDense

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Paper1.PeriodicForceSpace
open NSFormalization.Paper1.PeriodicDensityFiber
open NSFormalization.Paper1.PeriodicDensityDichotomy
open NSFormalization.Paper1.PeriodicInitialData
open NSFormalization.Paper1.PeriodicLifespan
open scoped ENNReal

/- The target set in the fixed initial-data slice.  It is a set of the actual
   `TestForce` subtype, so membership retains smoothness, periodicity, and
   compact positive-time support. -/
def singularSlice (ν : ℝ) (a : Space → Space) (T : ℝ) : Set TestForce :=
  {G | lifespan ν a G.1 ≤ ENNReal.ofReal T}

/- The local relation used by the gauge-density statement.  The first
   conjunct says that the target is in the singular slice, and the second is
   the exact force gauge inequality. -/
def GaugeApprox (ν : ℝ) (a : Space → Space) (T s : ℝ)
    (ρ : ℝ≥0∞) (g G : TestForce) : Prop :=
  G ∈ singularSlice ν a T ∧ forceDistance s G.1 g.1 < ρ

/- `GaugeDense` is deliberately a quantifier statement rather than a claim
   about a (nonexistent) metric instance on `TestForce`. -/
def GaugeDense (ν : ℝ) (a : Space → Space) (T s : ℝ) : Prop :=
  ∀ g : TestForce, ∀ ρ : ℝ≥0∞, 0 < ρ →
    ∃ G : TestForce, GaugeApprox ν a T s ρ g G

@[simp] theorem mem_singularSlice_iff
    {ν T : ℝ} {a : Space → Space} {G : TestForce} :
    G ∈ singularSlice ν a T ↔ lifespan ν a G.1 ≤ ENNReal.ofReal T :=
  Iff.rfl

@[simp] theorem GaugeApprox_iff
    {ν T s : ℝ} {a : Space → Space} {ρ : ℝ≥0∞}
    {g G : TestForce} :
    GaugeApprox ν a T s ρ g G ↔
      lifespan ν a G.1 ≤ ENNReal.ofReal T ∧ forceDistance s G.1 g.1 < ρ :=
  Iff.rfl

/- The rest slice is unconditional.  The positive-flow witness supplied by
   the dichotomy is intentionally hidden by the target set, while the exact
   gauge inequality and lifespan upper bound are retained. -/
theorem zero_slice_GaugeDense
    {ν T s : ℝ} (hν : 0 < ν) (hT : 0 < T) (hs : s < 1 / 2) :
    GaugeDense ν (fun _ : Space => 0) T s := by
  intro g ρ hρ
  obtain ⟨G, hG, hdist, hupper⟩ :=
    zero_slice_density_from_rest hν hT hs g.2 hρ
  refine ⟨⟨G, hG⟩, ?_⟩
  exact ⟨hupper, hdist⟩

/- For an arbitrary admissible datum, the only additional input is the
   unforced local-existence premise.  The proof is exactly the fixed-slice
   branch of the concrete dichotomy. -/
theorem admissible_slice_GaugeDense
    {ν T s : ℝ} (hν : 0 < ν) (hT : 0 < T) (hs : s < 1 / 2)
    (hlocal : UnforcedLocalExistence ν) {a : Space → Space}
    (ha : IsAdmissibleInitialData a) :
    GaugeDense ν a T s := by
  intro g ρ hρ
  obtain ⟨G, hG, hdist, hupper⟩ :=
    periodic_density_fixed_slice_of_unforced_local hν hT hs hlocal ha g.2 hρ
  refine ⟨⟨G, hG⟩, ?_⟩
  exact ⟨hupper, hdist⟩

end NSFormalization.Paper1.PeriodicDense
