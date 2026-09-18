import NSFormalization.Section3.T10.PeriodicData
import NSFormalization.Section3.T13.Localization
import NSFormalization.Source.PacketScaling
import NSFormalization.Source.ParabolicScaling
import NavierStokes.PeriodicLocalization
import NSFormalization.Section4.B01.Compact

/-!
# T15 canonical rescaling vocabulary and definitional bridges

The T15 specification writes the packet rescaling in the same syntax as the
registered Section 4 scaling contract.  This module is deliberately on the
formalization side of the dependency: it imports the canonical T10/T13 data
and the upstream implementation, but never imports `Contracts.*`.  The
contract-facing spelling is checked in `research/T15/probes/api_on_canonical.lean`.
-/

noncomputable section

namespace NSFormalization.Section3.T15

open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Section4.A02 (SpaceTimeField SpaceTimeScalar)
open NSFormalization.Source
open NSFormalization.Source.PacketScaling
open scoped ENNReal BigOperators Topology

/-! The first two Spec drift checks concern the registered completed-space
abbreviations.  B01 is the canonical upstream restatement of the common
`CompletedDenseVia` vocabulary; the homogeneous spelling is the one local
abbreviation used by the specification (the upstream library intentionally
does not give it a second name). -/

theorem completedDense_eq_via (q : ℝ≥0∞) (s : ℝ)
    (S : Set NSFormalization.Section4.B01.SpaceTimeField) :
    NSFormalization.Section4.B01.CompletedDense q s S =
      NSFormalization.Section4.B01.CompletedDenseVia q s
        (NSFormalization.Section4.D01.IsSobolevPath s) S := rfl

def completedDenseHomogeneous (q : ℝ≥0∞) (s : ℝ)
    (S : Set NSFormalization.Section4.B01.SpaceTimeField) : Prop :=
  NSFormalization.Section4.B01.CompletedDenseVia q s
    (NSFormalization.Section4.D01.Homogeneous.IsHomogeneousPath s) S

theorem completedDenseHomogeneous_eq_via (q : ℝ≥0∞) (s : ℝ)
    (S : Set NSFormalization.Section4.B01.SpaceTimeField) :
    completedDenseHomogeneous q s S =
      NSFormalization.Section4.B01.CompletedDenseVia q s
        (NSFormalization.Section4.D01.Homogeneous.IsHomogeneousPath s) S := rfl

/-! ## The rescaling definitions from `research/T15/Spec.lean` -/

/-- `03-torus.tex:106`: the shifted packet start time `t_ε=T-ε²`. -/
def scaledStartTime (T ε : ℝ) : ℝ := T - ε ^ 2

/-- `03-torus.tex:112-118`: the time-first source point
`((t-t_ε)/ε²,(x-x₀)/ε)`. -/
def scaledSourcePoint (x₀ : Space) (T ε : ℝ) (z : SpaceTime) : SpaceTime :=
  ((ε⁻¹) ^ 2 * (z.1 - scaledStartTime T ε), ε⁻¹ • (z.2 - x₀))

/-- `03-torus.tex:108-114`: the velocity rescaling, using the packet's
smooth negative-time zero extension. -/
def scaledVelocity (u : VelocityField) (x₀ : Space) (T ε : ℝ) : VelocityField :=
  fun z ↦ ε⁻¹ • zeroPastField u (scaledSourcePoint x₀ T ε z)

/-- `03-torus.tex:108-116`: the pressure rescaling, using the packet's
smooth negative-time zero extension. -/
def scaledPressure (p : PressureField) (x₀ : Space) (T ε : ℝ) : PressureField :=
  fun z ↦ (ε⁻¹) ^ 2 * zeroPastField p (scaledSourcePoint x₀ T ε z)

/-- `03-torus.tex:108-109,117-118`: the force rescaling. -/
def scaledForce (f : VelocityField) (x₀ : Space) (T ε : ℝ) : VelocityField :=
  fun z ↦ (ε⁻¹) ^ 3 • f (scaledSourcePoint x₀ T ε z)

/-- `03-torus.tex:130-131`: `α(p,q)=-3+3/p+2/q`. -/
def alphaT (p q : ℝ≥0∞) : ℝ := -3 + 3 / p.toReal + 2 / q.toReal

/-- `03-torus.tex:120`: spatial periodization of the scaled velocity. -/
def periodizedScaledVelocity (u : VelocityField) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeField :=
  fun z ↦ periodize (fun x ↦ scaledVelocity u x₀ T ε (z.1, x)) z.2

/-- `03-torus.tex:120`: spatial periodization of the raw scaled pressure. -/
def periodizedScaledPressure (p : PressureField) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeScalar :=
  fun z ↦ ∑' n : PeriodicFrequency,
    scaledPressure p x₀ T ε (z.1, z.2 - latticeVector n)

/-- `03-torus.tex:120`: spatial periodization of the scaled force. -/
def periodizedScaledForce (f : VelocityField) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeField :=
  fun z ↦ periodize (fun x ↦ scaledForce f x₀ T ε (z.1, x)) z.2

/-- `03-torus.tex:123`: subtract the normalized Haar mean from a periodic
pressure slice.  `pressureMeanT` and `normalizePressureT` are the canonical
T10 definitions imported above. -/
def normalizedScaledPressure (p : PressureField) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeScalar :=
  normalizePressureT (periodizedScaledPressure p x₀ T ε)

/-! ## Definitional drift theorems -/

/-- The local velocity rescaling is the upstream object to which the
registered `Contracts.V1.scaledPacket` is `rfl`-bound. -/
theorem scaledVelocity_eq_parabolicVelocity (u : VelocityField) (x₀ : Space)
    (T ε : ℝ) :
    scaledVelocity u x₀ T ε =
      parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField u) := rfl

/-- The local pressure rescaling is the upstream object to which the
registered `Contracts.V1.scaledPressure` is `rfl`-bound. -/
theorem scaledPressure_eq_parabolicPressure (p : PressureField) (x₀ : Space)
    (T ε : ℝ) :
    scaledPressure p x₀ T ε =
      parabolicPressure ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField p) := rfl

/-- The local force rescaling is the upstream object to which the
registered `Contracts.V1.scaledForce` is `rfl`-bound. -/
theorem scaledForce_eq_parabolicForce (f : VelocityField) (x₀ : Space)
    (T ε : ℝ) :
    scaledForce f x₀ T ε =
      parabolicForce ε⁻¹ (T - ε ^ 2) x₀ f := rfl

/-- `alphaT` has the registered contract's defining formula.  The contract's
`alpha` is a copied contract definition and has no separate upstream object. -/
theorem alphaT_formula (p q : ℝ≥0∞) :
    alphaT p q = -3 + 3 / p.toReal + 2 / q.toReal := rfl

/-- The pressure-adjustment formula is definitionally the T10 normalization. -/
theorem normalizedScaledPressure_formula (p : PressureField) (x₀ : Space)
    (T ε t : ℝ) (x : Space) :
    normalizedScaledPressure p x₀ T ε (t, x) =
      periodizedScaledPressure p x₀ T ε (t, x) -
        pressureMeanT (periodizedScaledPressure p x₀ T ε) t := rfl

/-! ## Lane-352 periodization bridge -/

/-- T13's spatial periodizer is definitionally the space-slice of the vendor
`NavierStokes.PeriodicLocalization.periodize`. -/
theorem periodize_eq_vendor (f : Space → Space) (t : ℝ) (x : Space) :
    periodize f x =
      NavierStokes.PeriodicLocalization.periodize
        (fun z : SpaceTime => f z.2) (t, x) := by
  rfl

end NSFormalization.Section3.T15
