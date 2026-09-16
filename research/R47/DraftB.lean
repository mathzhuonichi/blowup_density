import Contracts.V1.Data

/-!
Independent draft B of Theorem 4.7, `04-whole-space.tex:297-303`.
Only registered vocabulary is imported. `Data.Grid`, its `cell`,
`Data.cellAverage`, and `Data.gridObservation` already register all observation
notions (`04-whole-space.tex:288-295`); no local definition needs registration.
Equality below is equality of the entire cell-indexed sequence.

Raw solution data avoids making the theorem conditional on a preselected
`InsertionFamilyAPI`: the ball and family must be chosen AFTER the grids.
One witness carries every clause. No witness or proof is supplied here.
-/

noncomputable section

namespace BlowupDensity.Contracts.V1.RGridDraftB

open Set Filter Topology
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-- The single chosen family in `04-whole-space.tex:298-303`, with the
reference and finite grid family fixed before any output data. -/
structure RGridFamily (ν : ℝ) (a : SpatialField) (g : SpaceTimeField)
    (T δ : ℝ) (reference : ClassicalSolutionR ν a g (T + δ))
    (n : ℕ) (grids : Fin n → Grid) where
  /-- `04-whole-space.tex:303,306`: center of the common localization ball. -/
  center : Space
  /-- `04-whole-space.tex:303,306`: radius of the common localization ball. -/
  radius : ℝ
  /-- `04-whole-space.tex:306`: the ball is nonempty. -/
  radius_pos : 0 < radius
  /-- `04-whole-space.tex:303,306`: one containing cell of each grid,
  chosen once for the entire family; closure lies in the cell interior. -/
  containingCell : ∀ i : Fin n, ∃ k : Fin 3 → ℤ,
    closure (Metric.ball center radius) ⊆ interior ((grids i).cell k)
  /-- `04-whole-space.tex:32,298`: a single sufficiently-small-scale cutoff. -/
  ε₀ : ℝ
  /-- `04-whole-space.tex:32,298`: the scale interval is nonempty. -/
  eps_pos : 0 < ε₀
  /-- `04-whole-space.tex:32,298`: the chosen forces, one family. -/
  force : ℝ → SpaceTimeField
  /-- `04-whole-space.tex:32,298`: solutions with the original initial datum.
  Values outside the admissible scale interval are arbitrary extensions. -/
  solution : ∀ ε : ℝ, ClassicalSolutionR ν a (force ε) T
  /-- `04-whole-space.tex:32,298`: admissibility of each inserted force. -/
  force_mem : ∀ ε ∈ Ioc (0 : ℝ) ε₀, MemForceR (force ε)
  /-- `04-whole-space.tex:36,298`: unchanged earlier history of the insertion. -/
  history : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t : ℝ, 0 ≤ t → t ≤ T - 2 * ε ^ 2 →
    ∀ x : Space, (solution ε).velocity (t, x) = reference.velocity (t, x)
  /-- `04-whole-space.tex:38,298`: the force difference is smooth and
  compactly supported in positive spacetime. -/
  forceDifference_compact : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    MemForceCompact (fun z => force ε z - g z)
  /-- `04-whole-space.tex:300-301`: velocity observations agree on EVERY
  cell, at EVERY time including zero and excluding T, for EVERY fixed grid. -/
  velocity_observations : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ i : Fin n,
    ∀ t ∈ Ico (0 : ℝ) T,
      gridObservation (grids i) (fun x => (solution ε).velocity (t, x)) =
        gridObservation (grids i) (fun x => reference.velocity (t, x))
  /-- `04-whole-space.tex:300-301`: the same equality for force observations. -/
  force_observations : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ i : Fin n,
    ∀ t ∈ Ico (0 : ℝ) T,
      gridObservation (grids i) (fun x => force ε (t, x)) =
        gridObservation (grids i) (fun x => g (t, x))
  /-- `04-whole-space.tex:303`: exact maximal lifespan, not merely ≤ T. -/
  lifespan : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    maximalLifespanR ν a (force ε) = ENNReal.ofReal T
  /-- `04-whole-space.tex:303`, referring to `:221-223`: energy convergence
  of this same family as ε decreases to zero. -/
  energy_convergence : Tendsto
    (fun ε : ℝ => energyENorm T
      (fun z => (solution ε).velocity z - reference.velocity z))
    (𝓝[>] 0) (𝓝 0)
  /-- `04-whole-space.tex:303`, referring to `:224-228`: the sum of the
  three force norms tends to zero, including the homogeneous norm of the
  DIFFERENCE, with time interval (0,∞). -/
  force_convergence : Tendsto
    (fun ε : ℝ => forceSobolevENorm 1 0 (fun z => force ε z - g z) +
      forceSobolevENorm 2 (-1) (fun z => force ε z - g z) +
      forceHomogeneousENorm 2 (-1) (fun z => force ε z - g z))
    (𝓝[>] 0) (𝓝 0)
  /-- `04-whole-space.tex:303`: velocity differences lie in the common ball
  throughout the domain of the classical solutions. -/
  velocity_support : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ico (0 : ℝ) T,
    tsupport (fun x => (solution ε).velocity (t, x) - reference.velocity (t, x)) ⊆
      Metric.ball center radius
  /-- `04-whole-space.tex:303`, with the compact representative of `:306`:
  pressure differences lie in the same ball modulo a spatially constant,
  possibly time-dependent gauge. Zero gauge is permitted. -/
  pressure_support : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∃ c : ℝ → ℝ,
    ∀ t ∈ Ico (0 : ℝ) T,
      tsupport (fun x => (solution ε).pressure (t, x) -
        reference.pressure (t, x) - c t) ⊆ Metric.ball center radius
  /-- `04-whole-space.tex:303`, inheriting `:38`: the full spacetime support
  of the force difference projects into the ball, also after T. -/
  force_support : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ z ∈ tsupport (fun z => force ε z - g z), z.2 ∈ Metric.ball center radius

/-- Theorem 4.7 (`04-whole-space.tex:297-303`). Universal regular reference,
then arbitrary finite grid family, then ONE chosen insertion family. -/
structure RGridAPI where
  /-- `04-whole-space.tex:298`: the regular-reference hypotheses of `:32`.
  An explicit positive extension margin and reference trajectory unpack
  `RegularThrough ν a g T` while retaining the actual observed velocity.
  The half-open horizon convention is the registered R42 convention. -/
  choose : ∀ ν : ℝ, 0 < ν →
    ∀ a : SpatialField, a ∈ initialClassR →
    ∀ g : SpaceTimeField, MemForceR g →
    ∀ T : ℝ, 0 < T → ∀ δ : ℝ, 0 < δ →
    ∀ reference : ClassicalSolutionR ν a g (T + δ),
    ∀ n : ℕ, ∀ grids : Fin n → Grid,
      Nonempty (RGridFamily ν a g T δ reference n grids)

end BlowupDensity.Contracts.V1.RGridDraftB
