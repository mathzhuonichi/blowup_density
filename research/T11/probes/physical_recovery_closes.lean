import NSFormalization.Section3.T11.PhysicalRecovery

/-!
Partial-delivery probe. The filename is the requested lane artifact name;
this file checks the delivered Fourier inverse and the exact conclusion for
the affine constant family. It does NOT certify the general U9d target below.

Still OPEN, copied verbatim from EXISTENCE_ROUTE.md:

∀ (ν : ℝ), 0 < ν → ∀ (C : TorusTwoSpaceContract ν)
  (a : SpatialField) (g : SpaceTimeField) (T : ℝ),
  a ∈ initialClassT → ContDiff ℝ ∞ g → IsPeriodicOn univ g → 0 < T →
  ∀ (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3),
    IsPeriodicDatum 3 a A → IsPeriodicSobolevPath 3 g F →
    (∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t)) →
    TorusForcedMildOn C A P T u →
    ∃ w : ClassicalSolutionT ν a g T,
      PeriodicLocalRegularity ν a g T w ∧
      IsPeriodicSobolevPathOn 3 (Ico 0 T) w.velocity u
-/
noncomputable section
namespace NSFormalization.Section3.T11.PhysicalRecoveryProbe
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open scoped ContDiff

example (A : PeriodicSobolev 3) :
    IsPeriodicDatum 3 (torusPhysicalField A) A := torusPhysicalField_datum A

example {a : SpatialField} {A : PeriodicSobolev 3}
    (ha : Continuous a) (hA : IsPeriodicDatum 3 a A) :
    torusPhysicalField A = a := torusPhysicalField_eq ha hA

example (u : ℝ → PeriodicSobolev 3) (T : ℝ) :
    IsPeriodicSobolevPathOn 3 (Ico 0 T) (torusPhysicalVelocity u) u :=
  torusPhysicalVelocity_datum u _

example {ν T : ℝ} {C : TorusTwoSpaceContract ν} {a : SpatialField}
    {A : PeriodicSobolev 3} {P u : ℝ → PeriodicSobolev 3}
    (ha : a ∈ initialClassT) (hA : IsPeriodicDatum 3 a A)
    (hu : TorusForcedMildOn C A P T u) :
    ContinuousOn (torusPhysicalVelocity u) (Icc 0 T ×ˢ (univ : Set Space)) ∧
      IsPeriodicOn univ (torusPhysicalVelocity u) ∧
      (∀ x, torusPhysicalVelocity u (0, x) = a x) ∧
      IsPeriodicSobolevPathOn 3 (Ico 0 T) (torusPhysicalVelocity u) u :=
  ⟨torusForcedMildOn_physical_continuous hu, torusPhysicalVelocity_periodic u,
    torusPhysicalVelocity_initial ha hA hu, torusPhysicalVelocity_datum u _⟩

-- This checks genuine order-changing weights; the phantom carrier alone does not suffice.
example {s : ℝ} {I : Set ℝ} {u : ℝ → PeriodicSobolev 3}
    {U : ℝ → PeriodicSobolev s}
    (hU : ∀ t ∈ I, IsPeriodicReweight 3 s (u t) (U t)) :
    IsPeriodicSobolevPathOn s I (torusPhysicalVelocity u) U :=
  torusPhysicalVelocity_reweight hU

-- Exact same T in the mild certificate and all three classical regularity fields.
example (ν T : ℝ) (C : TorusTwoSpaceContract ν) (c : Space) (hT : 0 < T) :
    TorusForcedMildOn C (torusConstantDatum 3 c) (fun _ ↦ torusConstantDatum 3 c) T
      (fun t ↦ (1+t) • torusConstantDatum 3 c) ∧
    ∃ w : ClassicalSolutionT ν (fun _ ↦ c) (fun _ ↦ c) T,
      PeriodicLocalRegularity ν (fun _ ↦ c) (fun _ ↦ c) T w ∧
      IsPeriodicSobolevPathOn 3 (Ico 0 T) w.velocity
        (fun t ↦ (1+t) • torusConstantDatum 3 c) :=
  ⟨torusForcedMildOn_affine_constant C c hT.le,
    torusPhysicalRecovery_affine_constant ν T c hT⟩

-- Nonzero velocity AND force; the contract is supplied unconditionally by lane 317.
example : ∃ (C : TorusTwoSpaceContract 1) (T : ℝ) (u : ℝ → PeriodicSobolev 3),
    0 < T ∧ TorusForcedMildOn C (torusConstantDatum 3 (coordinateVector 0))
      (fun _ ↦ torusConstantDatum 3 (coordinateVector 0)) T u ∧
    IsPeriodicSobolevPathOn 3 (Ico 0 T) (torusPhysicalVelocity u) u ∧
    torusPhysicalVelocity u (0, 0) ≠ 0 ∧
    torusPhysicalField (torusConstantDatum 3 (coordinateVector 0)) 0 ≠ 0 :=
  torusPhysicalRecovery_nonzero

end NSFormalization.Section3.T11.PhysicalRecoveryProbe
