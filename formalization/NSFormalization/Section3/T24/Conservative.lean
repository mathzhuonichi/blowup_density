import NSFormalization.Section3.T11.LocalTheory
import NSFormalization.Paper1.ConservativeForce

/-!
# T24c: conservative forcing, canonical vocabulary

The definitions in this file are the T10/T11 spelling of the two declarations
in `research/T24/Spec.lean`.  In particular this module does not import the
registered contract: the probe performs the fieldwise conversion from the
contract's copies.  The proof of the zero-from-rest clause is the closed-slab
argument already established in `Paper1.ConservativeForce`.
-/

noncomputable section

namespace NSFormalization.Section3.T24

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section4.A02 (SpatialField SpaceTimeScalar SpaceTimeField)
open scoped ContDiff

/-- The smooth, unit-spatially-periodic potentials used by `prop:conservative`.
This is the canonical T10 spelling of `BlowupDensity.T24.Conservative.PeriodicPotentialT`.
-/
def PeriodicPotentialT (φ : SpaceTimeScalar) : Prop :=
  ContDiff ℝ ∞ φ ∧ IsPeriodicOn univ φ

/-- The conservative force `f = -∇φ`, in the canonical pressure-gradient token.
-/
def conservativeForceT (φ : SpaceTimeScalar) : SpaceTimeField :=
  fun z ↦ -pressureGradient φ z.1 z.2

/-- T24c Uc1, verbatim on the canonical T10/T11 solution class. -/
theorem zero_from_rest :
    ∀ (ν : ℝ), 0 < ν → ∀ (T : ℝ), 0 < T →
      ∀ φ : SpaceTimeScalar, PeriodicPotentialT φ →
        ∀ S : ClassicalSolutionT ν (0 : SpatialField) (conservativeForceT φ) T,
          ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, S.velocity (t, x) = 0 := by
  intro ν hν T hT φ hφ S t ht x
  have hz := NSFormalization.Paper1.ConservativeForce.zero_of_negative_gradient_on_Ico
    (ν := ν) (S := T) hν
    S.velocity_smooth S.pressure_smooth hφ.1.contDiffOn
    S.velocity_periodic S.pressure_periodic
    (fun s _hs y i => hφ.2 s (mem_univ s) y i)
    (fun s hs y => S.divergence s ⟨hs.1.le, hs.2⟩ y)
    (fun s hs y => S.momentum s hs y)
    S.initial
  exact hz t ht x

end NSFormalization.Section3.T24
