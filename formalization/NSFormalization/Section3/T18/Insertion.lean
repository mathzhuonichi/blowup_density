import NSFormalization.Section3.T17.Correction

/-!
# T18 U1: the inserted velocity, pressure, and force

This is the canonical, contract-free first layer of `thm:insertion`
(`research/T18/Spec.lean:1658-1734`).  Since `formalization/` cannot import the
contract `PacketImportAPI`, its packet parameter is represented by the six raw
fields used by T15's canonical `PlacementData` and `ScalingAPI`.

`InsertionData` packages the remaining threaded parameters: a canonical T10
reference solution, the canonical T17 correction record, and the three paper
hypotheses.  The definitions and theorems below are the first eleven fields of
the reconciled `PeriodicInsertionAPI`, with every Spec parameter replaced by a
projection of this bundle.
-/

noncomputable section

namespace NSFormalization.Section3.T18

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T15
open NSFormalization.Section3.T16
open NSFormalization.Section3.T17
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)

/-- The parameters and paper hypotheses consumed by the U1 layer of periodic
insertion, in the raw-field spelling permitted inside `formalization/`.

The packet fields correspond to `P.velocity`, `P.pressure`, `P.force`,
`P.carrier`, `P.energyBound`, and `P.dissipationBound`.  The canonical
`ClassicalSolutionT` packages the reference `(v, π, g)` and all T11 solution
hypotheses threaded by the Spec. -/
structure InsertionData where
  ν : ℝ
  packetVelocity : VelocityField
  packetPressure : PressureField
  packetForce : VelocityField
  carrier : Set Space
  energyBound : ℝ
  dissipationBound : ℝ
  place : PlacementData packetVelocity packetPressure packetForce carrier
  scaling : ScalingAPI (ν := ν) packetVelocity packetPressure packetForce carrier
    energyBound dissipationBound place
  a : SpatialField
  g : SpaceTimeField
  r : ℝ
  δ : ℝ
  D : CutoffData
  reference : ClassicalSolutionT ν a g (place.T + δ)
  correction : CorrectionAPI ν place reference.velocity r δ D
  hδ : 0 < δ
  hg : g ∈ forceClassT
  ha : a ∈ initialClassT

/-- `03-torus.tex:314`: `u_ε = v + w_ε + U_ε`. -/
def velocity (data : InsertionData) (ε : ℝ) (z : SpaceTime) : Space :=
  data.reference.velocity z + data.D.correction ε z +
    periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε z

/-- `03-torus.tex:314,318-320`: the pressure sum in the normalized torus
gauge. -/
def pressure (data : InsertionData) (ε : ℝ) : SpaceTimeScalar :=
  normalizePressureT (fun z ↦ data.reference.pressure z +
    periodizedScaledPressure data.packetPressure data.place.x₀ data.place.T ε z)

/-- `03-torus.tex:314`: `g_ε = g + H_ε + F_ε`. -/
def force (data : InsertionData) (ε : ℝ) (z : SpaceTime) : Space :=
  data.g z + correctionForce data.ν data.reference.velocity data.D ε z +
    periodizedScaledForce data.packetForce data.place.x₀ data.place.T ε z

/-- `03-torus.tex:314`, first display of `eq:insertion`. -/
theorem velocity_formula (data : InsertionData) : ∀ ε : ℝ, ∀ z : SpaceTime,
    velocity data ε z = data.reference.velocity z + data.D.correction ε z +
      periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε z := by
  intro ε z
  rfl

/-- `03-torus.tex:314,318-320`, second display of `eq:insertion`. -/
theorem pressure_formula (data : InsertionData) : ∀ ε : ℝ,
    pressure data ε = normalizePressureT
      (fun z ↦ data.reference.pressure z +
        periodizedScaledPressure data.packetPressure data.place.x₀ data.place.T ε z) := by
  intro ε
  rfl

/-- `03-torus.tex:314`, third display of `eq:insertion`. -/
theorem force_formula (data : InsertionData) : ∀ ε : ℝ, ∀ z : SpaceTime,
    force data ε z = data.g z +
      correctionForce data.ν data.reference.velocity data.D ε z +
      periodizedScaledForce data.packetForce data.place.x₀ data.place.T ε z := by
  intro ε z
  rfl

/-- The common threshold for the scaling and correction families. -/
def ε₀ (data : InsertionData) : ℝ := min data.place.ε₀ data.D.ε₀

/-- The common threshold is positive. -/
theorem eps_pos (data : InsertionData) : 0 < ε₀ data :=
  lt_min data.place.eps_pos data.correction.potential.eps_pos

/-- The inserted family lies inside the scaling range. -/
theorem eps_le_scaling (data : InsertionData) : ε₀ data ≤ data.place.ε₀ :=
  min_le_left _ _

/-- The inserted family lies inside the correction range. -/
theorem eps_le_cutoff (data : InsertionData) : ε₀ data ≤ data.D.ε₀ :=
  min_le_right _ _

/-- The reference solution extends a positive time beyond the target. -/
theorem delta_pos (data : InsertionData) : 0 < data.δ := data.hδ

/-- The threaded reference force belongs to the torus force class. -/
theorem reference_force_mem (data : InsertionData) : data.g ∈ forceClassT := data.hg

/-- The threaded initial datum belongs to the periodic smooth solenoidal
class. -/
theorem initial_mem (data : InsertionData) : data.a ∈ initialClassT := data.ha

end NSFormalization.Section3.T18
