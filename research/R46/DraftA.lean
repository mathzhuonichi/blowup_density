import Contracts.V1.InsertionFamily

/-!
# Draft A specification: Proposition 4.6 (`prop:Renergy`)

This file is an independent statement-only transcription of
`paper/sections/04-whole-space.tex:218-229`.  It uses the registered completed
Bochner-space predicates from `Contracts.V1.Data` and the registered reference
and insertion-family vocabulary from `Contracts.V1.InsertionFamily`.

The only local notion is `StrongTrajectoryClosure`, the literal simultaneous
limit displayed at `04-whole-space.tex:223-226`.  It is marked below as needing
registration.  No implementation module is imported.
-/

noncomputable section

namespace BlowupDensity.Research.R46.DraftA

open Set Filter Topology
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-! ## Local notion absent from the registered vocabulary -/

/-- **Needs registration.**  The simultaneous strong-closure conclusion of
Proposition 4.6, `paper/sections/04-whole-space.tex:221-228`, for one of the
families furnished by Theorem 4.2.

The first limit is `‖u_ε-v‖_{E_T} → 0` (`:223`).  The second is the single
displayed sum of the three force-difference norms (`:224-226`).  In particular,
the homogeneous norm is applied only to the compact difference `g_ε-g`, as
required by `:228`; it imposes no homogeneous-space membership on `g`. -/
def StrongTrajectoryClosure {ν : ℝ} {P : PacketAPI ν}
    (A : InsertionFamilyAPI ν P) : Prop :=
  Tendsto
      (fun ε : ℝ =>
        energyENorm A.T (A.velocityDifference ε))
      (𝓝[>] 0) (𝓝 0) ∧
    Tendsto
      (fun ε : ℝ =>
        forceSobolevENorm 1 0 (A.forceDifference ε) +
          forceSobolevENorm 2 (-1) (A.forceDifference ε) +
          forceHomogeneousENorm 2 (-1) (A.forceDifference ε))
      (𝓝[>] 0) (𝓝 0)

/-! ## Proposition 4.6 -/

/-- **Proposition 4.6** (`prop:Renergy`),
`paper/sections/04-whole-space.tex:218-229`: density in the completed
inhomogeneous and homogeneous force spaces, and simultaneous strong closure of
the insertion trajectories and forces.

The first two fields preserve the manuscript's outer order
`a ∈ 𝒳_ℝ`, `ν > 0`, `T > 0`.  The last field follows the exact registered
quantifier order of the references consumed by Theorem 4.2's
`insertionFamilyStatement`; the existential family is one family on which both
limits in `StrongTrajectoryClosure` hold. -/
structure REnergyAPI where
  /-- `paper/sections/04-whole-space.tex:219`, first density clause.  For
  `q ∈ {1,2}` and `s < s_q`, smooth compact forces whose maximal lifespan is at
  most `T` are dense in the full completed space
  `L^q(0,∞;H^s(ℝ^3;ℝ^3))`.

  `CompletedDense` quantifies over every finite, strongly measurable datum path
  in the completion and realizes an approximating physical force through
  `IsSobolevPath s`. -/
  completedSobolevDensity :
    ∀ (a : SpatialField), a ∈ initialClassR →
      ∀ ν : ℝ, 0 < ν →
        ∀ T : ℝ, 0 < T →
          ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) →
            ∀ s : ℝ, s < criticalOrder q.toReal →
              CompletedDense q s
                (breakdownSetIn forceClassCompact ν a T)

  /-- `paper/sections/04-whole-space.tex:219`, second density clause.  Smooth
  compact forces whose maximal lifespan is at most `T` are dense in the full
  completed space `L²(0,∞;Ḣ⁻¹(ℝ^3;ℝ^3))`.

  `CompletedDenseHomogeneous` uses the same completed datum carrier as the
  inhomogeneous clause but realizes physical forces through
  `IsHomogeneousPath (-1)`, the realization fixed at
  `paper/sections/02-preliminaries.tex:57-73`. -/
  completedHomogeneousDensity :
    ∀ (a : SpatialField), a ∈ initialClassR →
      ∀ ν : ℝ, 0 < ν →
        ∀ T : ℝ, 0 < T →
          CompletedDenseHomogeneous 2 (-1)
            (breakdownSetIn forceClassCompact ν a T)

  /-- `paper/sections/04-whole-space.tex:221-228`.  For every reference in
  Theorem 4.2, one may choose a single registered insertion family, based on
  that same scaling record and initial datum, for which the energy trajectory
  and the displayed sum of all three force-difference norms converge strongly
  to zero simultaneously.

  The binders through the two reference-identification equalities are copied
  from the registered `insertionFamilyStatement`; adding
  `StrongTrajectoryClosure A` to its existential conclusion renders the words
  “one may simultaneously arrange” without asserting that every possible
  insertion family has the property. -/
  strongTrajectoryClosure :
    ∀ (ν : ℝ) (P : PacketAPI ν) (S : ScalingAPI ν P) (a : SpatialField)
      (R : ClassicalSolutionR ν a S.correction.g
        (S.correction.T + S.correction.δ)),
      R.velocity = S.correction.v → R.pressure = S.correction.π →
        ∃ A : InsertionFamilyAPI ν P,
          A.scaling = S ∧ A.a = a ∧ StrongTrajectoryClosure A

end BlowupDensity.Research.R46.DraftA
