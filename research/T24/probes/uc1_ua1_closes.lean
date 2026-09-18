import Contracts.V1.Packet
import Contracts.V1.TorusLocalTheory
import Bindings.Packet
import Bindings.TorusLocalTheory
import NSFormalization.Section3.T24.Conservative
import NSFormalization.Section3.T24.AffineBasics

noncomputable section

namespace BlowupDensity.T24.ProbeUc1Ua1

open Set
open BlowupDensity.Bindings.TorusLocalTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 (IsPeriodicOn ClassicalSolutionT)
open NSFormalization.Section4.A02
  (SpatialField SpaceTimeField SpaceTimeScalar)
open scoped ContDiff

/-! These are the small registered-spelling fragments of the T24a spec used by
Ua1.  They are copied here (as in the other canonical probes), rather than
importing a `research/` file as a Lean module. -/
namespace AffineSpec

def specAffineCylinder (c : Space) (r τ₀ τ₁ : ℝ) : Set SpaceTime :=
  Ioo τ₀ τ₁ ×ˢ Metric.ball c r

def specAffineAdmissible (c : Space) (r τ₀ τ₁ : ℝ) (b : SpaceTimeField) : Prop :=
  ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
    tsupport b ⊆ specAffineCylinder c r τ₀ τ₁ ∧
    (∀ t : ℝ, ∀ x : Space,
      BlowupDensity.Contracts.V1.spatialDivergence b t x = 0)

def specAffineVelocity (U b : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ U z + b z

end AffineSpec

example (c : Space) (r τ₀ τ₁ : ℝ) :
    AffineSpec.specAffineCylinder c r τ₀ τ₁ =
      NSFormalization.Section3.T24.affineCylinder c r τ₀ τ₁ := rfl

example (c : Space) (r τ₀ τ₁ : ℝ) (b : SpaceTimeField) :
    AffineSpec.specAffineAdmissible c r τ₀ τ₁ b =
      NSFormalization.Section3.T24.AffineAdmissible c r τ₀ τ₁ b := rfl

example (u b : SpaceTimeField) :
    AffineSpec.specAffineVelocity u b =
      NSFormalization.Section3.T24.affineVelocity u b := rfl


/-! The conservative field is converted directly: the two canonical
periodicity/residual predicates are definitionally the registered spellings. -/
example :
    ∀ (ν : ℝ), 0 < ν → ∀ (T : ℝ), 0 < T →
      ∀ φ : SpaceTimeScalar,
        (ContDiff ℝ ∞ φ ∧
          BlowupDensity.Contracts.V1.TorusData.IsPeriodicOn
            (Set.univ : Set ℝ) φ) →
        ∀ S : BlowupDensity.Contracts.V1.TorusLocalTheory.ClassicalSolutionT ν
            (0 : SpatialField)
            (fun z ↦ -BlowupDensity.Contracts.V1.pressureGradient φ z.1 z.2) T,
          ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, S.velocity (t, x) = 0 := by
  intro ν hν T hT φ hφ S t ht x
  exact NSFormalization.Section3.T24.zero_from_rest ν hν T hT φ hφ
    (BlowupDensity.Bindings.TorusLocalTheory.ofContract S) t ht x

/-! The five Ua1 fields are checked against the registered packet selected by
the binding.  The packet clauses are supplied as raw hypotheses, as required
by the canonical module's no-`Contracts.*` import rule. -/
example {r : ℝ} (hr : 0 < r) :
    0 < r := by
  exact NSFormalization.Section3.T24.radius_pos hr

example {τ₀ τ₁ : ℝ} (hτ₀ : 0 < τ₀) (hτ₀τ₁ : τ₀ < τ₁) (hτ₁ : τ₁ < 1) :
    0 < τ₀ ∧ τ₀ < τ₁ ∧ τ₁ < 1 := by
  exact NSFormalization.Section3.T24.window hτ₀ hτ₀τ₁ hτ₁

example (ν : ℝ) (hν : 0 < ν) (c : Space) (r τ₀ τ₁ : ℝ)
    (hτ₀ : 0 < τ₀) (b : SpaceTimeField)
    (hb : AffineSpec.specAffineAdmissible c r τ₀ τ₁ b) :
    ∀ x : Space,
      AffineSpec.specAffineVelocity
          (BlowupDensity.Bindings.packet ν hν).velocity b (0, x) = 0 := by
  exact NSFormalization.Section3.T24.zero_initial
    hτ₀ (BlowupDensity.Bindings.packet ν hν).zero_initial_velocity b hb

example (ν : ℝ) (hν : 0 < ν) (c : Space) (r τ₀ τ₁ : ℝ)
    (b : SpaceTimeField) (hb : AffineSpec.specAffineAdmissible c r τ₀ τ₁ b) :
    ∀ t : ℝ, τ₁ ≤ t → ∀ x : Space,
      AffineSpec.specAffineVelocity
          (BlowupDensity.Bindings.packet ν hν).velocity b (t, x) =
        (BlowupDensity.Bindings.packet ν hν).velocity (t, x) := by
  exact NSFormalization.Section3.T24.late_agreement b hb

example (ν : ℝ) (hν : 0 < ν) (c : Space) (r τ₀ τ₁ : ℝ)
    (b₁ b₂ : SpaceTimeField)
    (_hb₁ : AffineSpec.specAffineAdmissible c r τ₀ τ₁ b₁)
    (_hb₂ : AffineSpec.specAffineAdmissible c r τ₀ τ₁ b₂) (hne : b₁ ≠ b₂) :
    AffineSpec.specAffineVelocity
          (BlowupDensity.Bindings.packet ν hν).velocity b₁ ≠
      AffineSpec.specAffineVelocity
          (BlowupDensity.Bindings.packet ν hν).velocity b₂ := by
  exact NSFormalization.Section3.T24.distinct _ _ _ _hb₁ _hb₂ hne

end BlowupDensity.T24.ProbeUc1Ua1
