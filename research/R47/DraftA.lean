import Contracts.V1.InsertionFamily

/-!
# Draft A specification: Theorem 4.7 (`thm:Rgrid`)

This file states only the manuscript contract.  It deliberately uses the
registered `InsertionFamilyAPI`: that record makes the reference solution, the
inserted velocity/pressure/force, the scale parameter, and every support and
convergence assertion belong to one and the same family.

The registered data vocabulary already contains complete uniform Cartesian
grids, their cells, cell averages, and the observation map.  The two local
predicates below are the only missing notions used by this draft; both are
marked for registration.
-/

noncomputable section

namespace BlowupDensity.Research.R47.DraftA

open Set Filter Topology
open scoped ENNReal
open BlowupDensity.Contracts.V1

/-- **Needs registration.**  The two spacetime fields have identical
`A_h`-observations on every cell of `grid` at every time `0 ≤ t < T`.

This is the literal equality in `paper/sections/04-whole-space.tex:299-302`.
The equality is equality in the full function codomain
`(Fin 3 → ℤ) → Space`, hence is coordinatewise over every grid cell.  In
particular it asserts nothing at `t = T`. -/
def IdenticalCellObservationsBefore
    (grid : Data.Grid) (T : ℝ)
    (z₁ z₂ : Data.SpaceTimeField) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t < T →
    Data.gridObservation grid (fun x => z₁ (t, x)) =
      Data.gridObservation grid (fun x => z₂ (t, x))

/-- **Needs registration.**  A pressure difference is supported in `B` at
presingular times after removal of a spatially constant pressure gauge.

The function `c` may depend on time, exactly as permitted by the pressure
convention; for each fixed time it is constant in space.  This spells out the
exception in `paper/sections/04-whole-space.tex:303-304` and the gauge discussed
in its proof at `paper/sections/04-whole-space.tex:313-320`. -/
def PressureDifferenceSupportedInBallModuloGauge
    (T : ℝ) (x₀ : NavierStokes.ProblemStatement.Space) (r : ℝ)
    (p π : Data.SpaceTimeScalar) : Prop :=
  ∃ c : ℝ → ℝ, ∀ t : ℝ, 0 ≤ t → t < T →
    tsupport (fun x : NavierStokes.ProblemStatement.Space =>
      p (t, x) - π (t, x) - c t) ⊆
      Metric.ball x₀ r

/-- **Theorem 4.7** (`thm:Rgrid`),
`paper/sections/04-whole-space.tex:297-304`: identical whole-space cell
observations for one prescribed finite family of complete uniform Cartesian
grids.

`ι` is the finite index type of the prescribed grid family.  The record stores
the family of inserted solutions *after* the grids have been fixed.  Carrying
one `InsertionFamilyAPI` rather than separately quantified raw fields enforces
the last sentence of Theorem 4.2: all conclusions use the same inserted
family.  Its `reference` field is the regular reference through `T + δ`, so the
regular-reference hypotheses of Theorem 4.2 are carried without duplicating
them here. -/
structure RGridAPI
    (ν : ℝ) (P : PacketAPI ν)
    (ι : Type) [Finite ι] (grids : ι → Data.Grid) where
  /-- The single inserted family chosen after the finite grid family is fixed;
  this is “The inserted solutions may be chosen so that” in
  `paper/sections/04-whole-space.tex:297-299`. -/
  family : InsertionFamilyAPI ν P

  /-- `A_h u_ε(t) = A_h v(t)` for every prescribed grid, every admissible
  insertion scale, and every `0 ≤ t < T`,
  `paper/sections/04-whole-space.tex:298-302`. -/
  velocityObservations : ∀ i : ι, ∀ ε ∈ Ioc (0 : ℝ) family.ε₀,
    IdenticalCellObservationsBefore (grids i) family.scaling.correction.T
      (family.velocity ε) family.scaling.correction.v

  /-- `A_h g_ε(t) = A_h g(t)` for every prescribed grid, every admissible
  insertion scale, and every `0 ≤ t < T`,
  `paper/sections/04-whole-space.tex:298-302`. -/
  forceObservations : ∀ i : ι, ∀ ε ∈ Ioc (0 : ℝ) family.ε₀,
    IdenticalCellObservationsBefore (grids i) family.scaling.correction.T
      (family.force ε) family.scaling.correction.g

  /-- `T^ν_{max,ℝ}(a,g_ε) = T` for every admissible scale,
  `paper/sections/04-whole-space.tex:303`. -/
  lifespan : ∀ ε ∈ Ioc (0 : ℝ) family.ε₀,
    Data.maximalLifespanR ν family.a (family.force ε) =
      ENNReal.ofReal family.scaling.correction.T

  /-- The energy convergence from Proposition 4.6:
  `‖u_ε-v‖_{E_T} → 0`, as invoked at
  `paper/sections/04-whole-space.tex:303` and stated at
  `paper/sections/04-whole-space.tex:221-226`. -/
  energyConvergence :
    Tendsto
      (fun ε : ℝ =>
        Data.energyENorm family.scaling.correction.T
          (fun z => family.velocity ε z - family.scaling.correction.v z))
      (𝓝[>] (0 : ℝ)) (𝓝 0)

  /-- The three simultaneous force convergences from Proposition 4.6, as
  invoked at `paper/sections/04-whole-space.tex:303` and displayed at
  `paper/sections/04-whole-space.tex:224-226`:
  `L¹_tL²_x`, `L²_tH⁻¹_x`, and `L²_tḢ⁻¹_x`. -/
  forceConvergences :
    Tendsto
      (fun ε : ℝ =>
        let difference :=
          fun z => family.force ε z - family.scaling.correction.g z
        Data.mixedLebesgueENorm 1 2 difference +
          Data.forceSobolevENorm 2 (-1) difference +
          Data.forceHomogeneousENorm 2 (-1) difference)
      (𝓝[>] (0 : ℝ)) (𝓝 0)

  /-- The one ball used by the insertion family is contained in one (possibly
  differently indexed) cell of every prescribed grid,
  `paper/sections/04-whole-space.tex:303-304`. -/
  ballContainedInEveryGrid : ∀ i : ι, ∃ k : Fin 3 → ℤ,
    Metric.ball family.scaling.correction.x₀ family.scaling.correction.r ⊆
      (grids i).cell k

  /-- The velocity difference is supported in the common ball at every
  presingular time, the velocity part of “All differences are supported inside
  a ball” in `paper/sections/04-whole-space.tex:303-304`. -/
  velocityDifference_support : ∀ ε ∈ Ioc (0 : ℝ) family.ε₀,
    ∀ t ∈ Ico (0 : ℝ) family.scaling.correction.T,
      tsupport
          (fun x : NavierStokes.ProblemStatement.Space =>
            family.velocity ε (t, x) - family.scaling.correction.v (t, x)) ⊆
        Metric.ball family.scaling.correction.x₀ family.scaling.correction.r

  /-- The pressure difference is supported in the common ball modulo the
  optional spatially constant gauge, the pressure exception in
  `paper/sections/04-whole-space.tex:303-304`. -/
  pressureDifference_support : ∀ ε ∈ Ioc (0 : ℝ) family.ε₀,
    PressureDifferenceSupportedInBallModuloGauge
      family.scaling.correction.T family.scaling.correction.x₀
      family.scaling.correction.r (family.pressure ε)
      family.scaling.correction.π

  /-- The entire spacetime support of the force difference projects into the
  common ball, the force part of “All differences are supported inside a ball”
  in `paper/sections/04-whole-space.tex:303-304`. -/
  forceDifference_support : ∀ ε ∈ Ioc (0 : ℝ) family.ε₀,
    ∀ z ∈ tsupport
        (fun z => family.force ε z - family.scaling.correction.g z),
      z.2 ∈ Metric.ball family.scaling.correction.x₀ family.scaling.correction.r

end BlowupDensity.Research.R47.DraftA
