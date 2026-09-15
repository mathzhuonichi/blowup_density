import Contracts.V1.Data

/-! Stable specification for the **proved part** of the whole-space local-regularity
interface on `R³` (`prop:local`, existence half).

Task `collaboration/tasks/A01.md`, graph node `A01`
(`formalization/blueprint/DEPENDENCY_GRAPH.md:172`).  Version 1 fixes the two
fields of `research/A01/Spec.lean`'s `ManuscriptLocalRegularity` (`:167-229`)
that are now **theorems of every `ClassicalSolutionR`** — discharged in the tree,
needing no transport from any mild/strong source:

* `projected` (`Spec.lean:214`; `paper/sections/02-preliminaries.tex:81`
  eq:projected, force `P f` of `appendix-a-local-theory.tex:76-77`): the projected
  forced equation `∂ₜu − νΔu = (f − ∇·(u⊗u)) − ∇p` at interior times.  Lane 093,
  `Section4/A01/ProjectedEquation.lean` `projected_of_classicalSolution`, from
  `velocity_smooth` + `divergence` + `momentum` through unit E1's
  `navierStokesResidual_eq_iff_projected`.
* `pressure_potential` (`Spec.lean:227`; `02-preliminaries.tex:96-100`): the
  scalar pressure is gauge-equivalent to the manuscript's explicit radial
  potential `∫₀¹ G(rx,t)·x dr` of its own gradient.  Lane 106,
  `Section4/A01/PressureGauge.lean` `pressure_potential_of_classicalSolution`,
  from `pressure_smooth` alone.

## Structure shape (recorded choice)

`ManuscriptLocalRegularity` (`Spec.lean:167`) is a `Prop` structure *parameterized*
by `u : ClassicalSolutionR ν a f T`.  Mirroring `Contracts.V1.EnergyAbsorptionPartial`'s
handling of `velocityJets` — which flattens a per-solution clause into a single
`∀`-statement over `ClassicalSolutionR` — each field here is flattened to
`∀ ν a f T (u : Data.ClassicalSolutionR ν a f T), <field body>`.  Unlike
`EnergyAbsorptionPartial.velocityJets`, **no** `0 < ν` / `a ∈ initialClassR` /
`MemForceR f` hypotheses are added: the spec's structure carries none, and neither
discharging theorem needs them (both hold for an *arbitrary* classical solution),
so this partial contract is strictly the stronger, hypothesis-free reading.

## Out of scope, and asserted nowhere below

The other two fields of `ManuscriptLocalRegularity`, not proved in the tree on this
branch and asserted nowhere here (see `research/A01/REVIEW_M4.md` "What A01 still
lacks"):

* `sobolev_smooth` (`Spec.lean:180`, split row **m1**, size **L**): all-order
  Sobolev *time* smoothness (`appendix-a-local-theory.tex:71-76`); strictly
  stronger than `ClassicalSolutionR.sobolev`'s `ContinuousOn`, not harvestable;
* `pressure_recovery` (`Spec.lean:197`, split row **m2**, size **M**): eq:Rpressure
  `∇p = (I−P)(f − ∇·(u⊗u))` on `Ico 0 T`; its inputs are unit **P3** (HeliCorgi's
  Helmholtz pressure) and **P2** (`IsLerayComplement` single-valuedness, a Liouville
  gap).

Also asserted nowhere: everything in `LocalTheoryAPI` (`Spec.lean:277`) — the
existence data `solution`, the `regularity` bundle, the uniform lower bound
`horizon_lower_bound` — and any uniqueness/maximal-lifespan clause (those are A02).

**Fidelity note (`REVIEW_M4.md` #7).**  `pressure_potential` on its own carries
**no Navier–Stokes content**: its proof consumes only `u.pressure_smooth`, so it
reads "every `C²` scalar field equals the radial potential of its own gradient, up
to a function of time".  That is the correct reading of the spec — eq:Rpressure's
physical content lives in `pressure_recovery`, which is out of scope — so
registering `pressure_potential` does not pin the pressure down; it fixes the gauge
representative only.

## Conventions

Every object quantified over is the canonical one of
`verification/Contracts/V1/Data.lean`: `ClassicalSolutionR ν a f T` the classical
solution on `[0,T)`, `pressurePotential` the manuscript's radial potential
(`Data.lean:596`), `PressureGaugeEquivOn` the pressure gauge (`Data.lean:589`).
`pressureGradient`, `temporalDerivative`, `spatialLaplacian`, `coordinateVector`,
`Space`, `SpaceTime` are the pinned upstream `NavierStokes.ProblemStatement`
objects.  None of these is re-defined.

Two spec-local `def`s that `Data.lean` deliberately leaves out (`research/D01/
RECONCILIATION.md`, "genuinely absent objects") are restated verbatim below,
because `prop:local` is their first consumer:

* `convectionDivergence`, the manuscript's `∇·(u⊗u)` (`Spec.lean:103`), mentioned
  by `projected`;
* `HasSymmetricJacobian`, the symmetric-Jacobian predicate `∂_iG_j = ∂_jG_i`
  (`Spec.lean:119`, `02-preliminaries.tex:94`).  It is **not** referenced by either
  registered field; it is restated here **reserved for `IsLerayComplement` /
  `pressure_recovery`**: the excluded `pressure_recovery` runs through
  `Spec.lean:135`'s `IsLerayComplement`, whose second clause is exactly this
  predicate, so the lane that registers `pressure_recovery` imports this def rather
  than restating it again.  (`RadialPotential.HasSymmetricJacobian` mirrors the draft
  spec, not a contract, so there was no bridge debt for it; only `pressurePotential`
  was the load-bearing debt, `REVIEW_M4.md` finding 6.)  `Bindings.RegularityPartial`
  records both by `rfl`.
-/

noncomputable section

namespace BlowupDensity.Contracts.V1.RegularityPartial

open Set
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal

/-! ## 1. Spec-local objects `prop:local` needs and `Data.lean` does not define -/

/-- `research/A01/Spec.lean:103-105` (`paper/sections/02-preliminaries.tex:81`
eq:projected, `:90` eq:Rpressure): the tensor divergence `∇·(u⊗u)`, whose `k`-th
component is `∑_j ∂_j(u_j u_k)`, written literally as `∑_j ∂_j (u_j • u)`, a
vector-valued spatial derivative at frozen time.  Kept in the manuscript's own
spelling so that `projected` *displays* eq:projected's form; in this contract that
is display, not extra content — E1 is an `iff`, so `projected` is *equivalent* to
`ClassicalSolutionR.momentum` (see the `projected` field).
`Bindings.RegularityPartial` records by `rfl` that this is
`NSFormalization.Section4.A01.convectionDivergence`. -/
def convectionDivergence (u : SpaceTimeField) (t : ℝ) (x : Space) : Space :=
  ∑ j : Fin 3,
    fderiv ℝ (fun y : Space => (u (t, y) j) • u (t, y)) x (coordinateVector j)

/-- `research/A01/Spec.lean:119-122` (`paper/sections/02-preliminaries.tex:94`,
"its Fourier transform is parallel to `ξ`.  Hence `∂_jG_k = ∂_kG_j`"): `G` is
differentiable and its spatial Jacobian is symmetric.  This is the hypothesis under
which the manuscript's radial potential differentiates back to `G`
(`02-preliminaries.tex:96-100`).

Not referenced by `projected` or `pressure_potential`; restated only so the
implementation's identical restatement in `Section4/A01/RadialPotential.lean` has a
canonical contract-side home (`REVIEW_M4.md` finding 6).  `Bindings.RegularityPartial`
records the `rfl` bridge. -/
def HasSymmetricJacobian (G : SpatialField) : Prop :=
  Differentiable ℝ G ∧
    ∀ x : Space, ∀ i j : Fin 3,
      (fderiv ℝ G x (coordinateVector i)) j = (fderiv ℝ G x (coordinateVector j)) i

/-! ## 2. The contract -/

/-- The **proved** fields of the whole-space local-regularity interface on `R³`
(`research/A01/Spec.lean`'s `ManuscriptLocalRegularity`, `:167-229`), each flattened
into a statement about an arbitrary `Data.ClassicalSolutionR` (see the module
docstring for the shape choice and the two excluded fields).

No field is a hypothesis about an unspecified proposition, and no field is `True`,
`∃ x, True` or any similar placeholder. -/
structure ManuscriptLocalRegularityPartialAPI where
  /-- **`projected`** (`research/A01/Spec.lean:214-217`;
  `paper/sections/02-preliminaries.tex:81` eq:projected, force `P f` of
  `appendix-a-local-theory.tex:76-77`): for every classical whole-space solution `u`
  of `eq:NS` at viscosity `ν` with force `f`, the projected forced equation
  `∂ₜu − νΔu = (f − ∇·(u⊗u)) − ∇p` holds at every interior time, imposed on
  `Ioo 0 T` to match `ClassicalSolutionR.momentum` (the upstream `temporalDerivative`
  is a two-sided time `fderiv` and need not exist at `t = 0`).

  **Equivalent to `momentum`, not stronger (the parallel of `pressure_potential`'s
  caveat).**  Unit E1's `navierStokesResidual_eq_iff_projected` is an `iff` at any
  spatially-differentiable, divergence-free point, and every `ClassicalSolutionR`
  supplies both at interior times, so this field is *equivalent* to
  `ClassicalSolutionR.momentum`; the manuscript's `∇·(u⊗u)` spelling buys the
  displayed eq:projected form, not extra content.  Reading it as eq:projected's
  Leray-projected right-hand side `−P∇·(u⊗u) + P f` requires the excluded
  `pressure_recovery` field (which licenses `∇p = (I−P)(f − ∇·(u⊗u))`). -/
  projected : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
      (u : ClassicalSolutionR ν a f T),
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
      temporalDerivative u.velocity t x - ν • spatialLaplacian u.velocity t x =
        (f (t, x) - convectionDivergence u.velocity t x) -
          pressureGradient u.pressure t x
  /-- **`pressure_potential`** (`research/A01/Spec.lean:227-229`;
  `paper/sections/02-preliminaries.tex:96-100`): for every classical whole-space
  solution `u`, the scalar pressure `u.pressure` is gauge-equivalent on `Ico 0 T`
  (differs by a function of time only, `02-preliminaries.tex:31`) to the manuscript's
  explicit radial potential `p(x,t) = ∫₀¹ G(rx,t)·x dr` of its own gradient
  `G = ∇p`.  Fixes the gauge representative; carries no Navier–Stokes content
  (`REVIEW_M4.md` #7, the module docstring). -/
  pressure_potential : ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
      (u : ClassicalSolutionR ν a f T),
    PressureGaugeEquivOn (Ico (0 : ℝ) T)
      (pressurePotential (fun z : SpaceTime => pressureGradient u.pressure z.1 z.2))
      u.pressure

end BlowupDensity.Contracts.V1.RegularityPartial
