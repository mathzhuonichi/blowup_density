import NSFormalization.Paper1.PeriodicDense

/-!
# Paper 1 main density-threshold assembly

This module packages the proved subcritical insertion branch together with an
explicit interface for the still-missing critical regular-ball estimate.  The
critical input is a separation statement in the actual periodic force gauge;
no topological or PDE conclusion is hidden in the interface.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicMain

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Paper1.PeriodicForceSpace
open NSFormalization.Paper1.PeriodicDensityFiber
open NSFormalization.Paper1.PeriodicDense
open NSFormalization.Paper1.PeriodicInitialData
open NSFormalization.Paper1.PeriodicDensityDichotomy
open scoped ENNReal

/-- A gauge ball disjoint from the singular slice.  This is the concrete
form of the regular-neighborhood obstruction needed at and above the critical
exponent. -/
def GaugeSeparated (ν : ℝ) (a : Space → Space) (T s : ℝ) : Prop :=
  ∃ g : TestForce, ∃ ρ : ℝ≥0∞, 0 < ρ ∧
    ∀ G : TestForce, G ∈ singularSlice ν a T →
      ¬ forceDistance s G.1 g.1 < ρ

/-- A separated gauge ball rules out gauge density of the singular slice. -/
theorem not_GaugeDense_of_GaugeSeparated
    {ν T s : ℝ} {a : Space → Space}
    (hsep : GaugeSeparated ν a T s) :
    ¬ GaugeDense ν a T s := by
  rintro hdense
  obtain ⟨g, ρ, hρ, hdisj⟩ := hsep
  obtain ⟨G, hG⟩ := hdense g ρ hρ
  exact hdisj G hG.1 hG.2

/-- Zero-data density has the sharp threshold once the critical regular-ball
obstruction is supplied.  The subcritical half is the actual insertion
construction; the other half remains an explicit analytic premise. -/
theorem zero_slice_GaugeDense_iff_subcritical
    {ν T s : ℝ} (hν : 0 < ν) (hT : 0 < T)
    (hcritical : (1 : ℝ) / 2 ≤ s → GaugeSeparated ν (fun _ : Space => 0) T s) :
    GaugeDense ν (fun _ : Space => 0) T s ↔ s < (1 : ℝ) / 2 := by
  constructor
  · intro hd
    by_contra hs
    exact not_GaugeDense_of_GaugeSeparated (hcritical (le_of_not_gt hs)) hd
  · intro hs
    exact zero_slice_GaugeDense hν hT hs

/-- Main Paper 1 interface in the concrete periodic force gauge.  For every
admissible initial datum the subcritical singular forces are gauge-dense, and
for the resting datum the equivalence at the critical threshold follows from
the supplied regular-ball separation premise. -/
theorem paper1_main
    {ν T s : ℝ} (hν : 0 < ν) (hT : 0 < T)
    (hlocal : UnforcedLocalExistence ν)
    (hcritical : (1 : ℝ) / 2 ≤ s →
      GaugeSeparated ν (fun _ : Space => 0) T s) :
    (s < (1 : ℝ) / 2 →
      ∀ a : Space → Space, IsAdmissibleInitialData a →
        GaugeDense ν a T s) ∧
      (GaugeDense ν (fun _ : Space => 0) T s ↔ s < (1 : ℝ) / 2) := by
  constructor
  · intro hs a ha
    exact admissible_slice_GaugeDense hν hT hs hlocal ha
  · exact zero_slice_GaugeDense_iff_subcritical hν hT hcritical

end NSFormalization.Paper1.PeriodicMain
