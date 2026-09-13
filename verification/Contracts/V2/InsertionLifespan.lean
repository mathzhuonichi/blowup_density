import Contracts.V1.InsertionLifespan
import Contracts.V2.MaximalPartial

/-! Version 2 of the **two lifespan clauses of Theorem 4.2**: the version-one
record `InsertionLifespanAPI` (`Contracts/V1/InsertionLifespan.lean`, contract
`R42.insertion_lifespan`), extended by the three exports the version-one review
listed as owed but not exported (`research/R42/REVIEW_CONTRACT.md:386-390,443-452`).

Task `collaboration/tasks/R42.md`, graph node `R42`.  This is a version 2 of the
existing id `R42.insertion_lifespan`, not a new id: the version-one record is
proved and stays untouched (`Contracts/V1/InsertionLifespan.lean`).  Version two
adds only the three fields already discharged inside
`verification/Bindings/InsertionLifespan.lean` (lane 098) and re-exposed here.

## Why a new version

`R42.insertion_lifespan` deliberately stops at the two maximal-lifespan numbers.
Its `contracts.json` scope closes with an explicit "NOT asserted" list, and the
version-one reviewer (`research/R42/REVIEW_CONTRACT.md:443-452`) named exactly the
three things a downstream consumer (`R41D`, `R46`, `R47`) still had to reach into
the binding for:

* the inserted pair as a **full-horizon** `Data.ClassicalSolutionR` on `[0,T)` —
  the single object carrying `sobolev` and `∇p_ε ∈ L²` for `u_ε`, which
  `sol_on_shorter` builds per shorter horizon but never assembles at `T`
  (`REVIEW_CONTRACT.md:386-387,450-452`);
* the inserted pair's **identification as *the* maximal solution**,
  `IsMaximalSolution ν a g_ε u_ε p_ε` — "Proposition~\ref{prop:local} identifies
  the solution with the unique maximal solution" (`04-whole-space.tex:53`),
  registered nowhere (`REVIEW_CONTRACT.md:447-449`);
* the **essential-supremum form** of the blow-up display,
  `limsup_{t↑T}‖u_ε(t)‖_{L^∞} = ∞` (`04-whole-space.tex:35`), which the tree lemma
  `limsupLeft_speedENorm_eq_top` proves but `R42.insertion_lifespan` registers only
  in the pointwise `SpeedUnboundedAt` form (`REVIEW_CONTRACT.md:443-446`).

## What changed, exactly

`InsertionLifespanV2API` extends `Contracts.V1.InsertionLifespan.InsertionLifespanAPI`
unchanged and adds **three** fields, all over the inherited `family`:

* `solution` (`04-whole-space.tex:32,53`; `research/R42/REVIEW_CONTRACT.md:450-452`):
  for every `ε ∈ (0, ε₀]` the inserted pair `(u_ε, p_ε)` is a
  `Data.ClassicalSolutionR ν a g_ε T` on the full horizon `[0,T)`, with velocity
  `family.velocity ε` and pressure `family.pressure ε`.  Discharged by
  `Bindings.InsertionLifespan.sol_fullHorizon` (lane 098).  This is the object a
  consumer opens to get `sobolev` and `pressure_gradient` for `u_ε`.
* `maximal` (`04-whole-space.tex:53`; `research/section4/STATEMENTS.md:346`): for
  every `ε ∈ (0, ε₀]`, `(u_ε, p_ε)` **is** the maximal classical solution of
  `(ν, a, g_ε)`, in the registered `Contracts.V2.MaximalPartial.IsMaximalSolution`
  vocabulary (contract `A02.maximal_partial_v2`).  Discharged by
  `Bindings.InsertionLifespan.isMaximalSolution_of_inserted` (lane 098).
* `blowup_limsup` (`04-whole-space.tex:35`; `research/section4/STATEMENTS.md:348`):
  for every `ε ∈ (0, ε₀]` the second display of the theorem,
  `limsup_{t↑T}‖u_ε(t)‖_{L^∞} = ∞`, in the frozen `Contracts.V1.MaximalPartial`
  vocabulary (`limsupLeft`, `speedENorm`, `Contracts/V1/MaximalPartial.lean:101,106`
  = `⟪D01:limsupLeft⟫`/`⟪D01:normLinfty⟫`).  Discharged by the tree lemma
  `limsupLeft_speedENorm_eq_top` applied to `family.blowup`, exactly as version
  one's binding uses it inside `lifespan_upper`
  (`Bindings/InsertionLifespan.lean:215-217`).

No version-one field is removed, weakened, renamed or restated; `extends` makes
that structural.  The two version-one hypotheses `memForce`/`regular` are inherited
and are still the *only* hypotheses the binding needs (see `Bindings/InsertionLifespanV2.lean`).

## Fidelity of `blowup_limsup` to the manuscript display

`research/section4/STATEMENTS.md:348` records the display abstractly as
`⟪D01:limsupLeft⟫ T (fun t => ⟪D01:normLinfty⟫ (u_ε t))`, where `u_ε t` is the
spatial field at time `t`.  This record renders it as
`limsupLeft family.T (fun t => speedENorm (fun x => family.velocity ε (t, x)))`.
The only difference is the slice notation: `family.velocity ε` is a spacetime
field (`SpaceTime → Space`, matching `Data.ClassicalSolutionR.velocity` and the
`R42.insertion_family` `velocity` field), so its spatial slice at time `t` is
`fun x => family.velocity ε (t, x)` rather than a curried `family.velocity ε t`.
The operators `limsupLeft`/`speedENorm` are the same abstract
`limsup_{t↑T}`/`L^∞` of the manuscript; this is byte-for-byte the form the
version-one binding proves in `lifespan_upper` (`Bindings/InsertionLifespan.lean:215`)
and consumes through `lifespan_le_of_unbounded`.

## Self-containedness

Only `Contracts.V1.InsertionLifespan` and `Contracts.V2.MaximalPartial` are
imported, both `Contracts.*` (import policy satisfied); hence transitively
`Contracts.V1.{InsertionFamily, MaximalPartial, Data, …}`.  Every notion used —
`InsertionLifespanAPI`, `InsertionFamilyAPI`, `PacketAPI`, `Data.ClassicalSolutionR`,
`Data.maximalLifespanR`, `Contracts.V2.MaximalPartial.IsMaximalSolution`,
`Contracts.V1.MaximalPartial.{limsupLeft, speedENorm}` — is defined in those
contracts; this file copies none of them and needs no new `rfl` bridge.  No field
is a hypothesis about an unspecified proposition, and none is `True`, `∃ x, True`
or any similar placeholder.

This module introduces one structure and one statement definition and proves
nothing. -/

noncomputable section

namespace BlowupDensity.Contracts.V2.InsertionLifespan

open Set
open BlowupDensity.Contracts.V1
open scoped ENNReal

/-- **The two lifespan clauses of Theorem 4.2, version 2.**  Version one's
`InsertionLifespanAPI` (the inherited `family`, the two manuscript hypotheses
`memForce`/`regular`, and the two lifespan clauses `referenceLifespan`/`lifespan`),
together with the three exports the version-one review named as owed
(`research/R42/REVIEW_CONTRACT.md:443-452`): the inserted pair as a full-horizon
classical solution, its identification as the maximal solution, and the
essential-supremum form of the blow-up.

Every field of `Contracts.V1.InsertionLifespan.InsertionLifespanAPI` is inherited
verbatim through `toInsertionLifespanAPI`; see `Contracts/V1/InsertionLifespan.lean`
for their docstrings and manuscript citations.

No new field is a hypothesis about an unspecified proposition, and none is `True`,
`∃ x, True` or any similar placeholder. -/
structure InsertionLifespanV2API (ν : ℝ) (P : PacketAPI ν) extends
    Contracts.V1.InsertionLifespan.InsertionLifespanAPI ν P where
  /-- "there are `g_ε ∈ F_R` and **a solution** `u_ε`" (`04-whole-space.tex:32`),
  and "Proposition~\ref{prop:local} identifies **the solution**"
  (`04-whole-space.tex:53`): for every `ε ∈ (0, ε₀]` the inserted pair
  `(u_ε, p_ε)` is a `Data.ClassicalSolutionR ν a g_ε T` on the **full** horizon
  `[0,T)` — one velocity `family.velocity ε`, one pressure `family.pressure ε`,
  one `sobolev` path continuous on all of `[0,T)`, and `∇p_ε ∈ L²` at every
  `t < T`.  This is the object `R42.insertion_lifespan` did not export
  (`research/R42/REVIEW_CONTRACT.md:386-387,450-452`), from which a consumer
  recovers `sobolev`/`pressure_gradient` for `u_ε`.  Discharged by
  `Bindings.InsertionLifespan.sol_fullHorizon` (lane 098). -/
  solution : ∀ ε ∈ Ioc (0 : ℝ) family.ε₀,
    ∃ w : Data.ClassicalSolutionR ν family.a (family.force ε) family.T,
      w.velocity = family.velocity ε ∧ w.pressure = family.pressure ε
  /-- "Proposition~\ref{prop:local} identifies the solution with the unique
  maximal solution" (`04-whole-space.tex:53`; `research/section4/STATEMENTS.md:346`):
  for every `ε ∈ (0, ε₀]` the inserted pair `(u_ε, p_ε)` **is** the maximal
  classical solution of `(ν, a, g_ε)`, stated in the registered
  `Contracts.V2.MaximalPartial.IsMaximalSolution` vocabulary (contract
  `A02.maximal_partial_v2`).  Not asserted by `R42.insertion_lifespan`, which gives
  only the lifespan number (`research/R42/REVIEW_CONTRACT.md:447-449`).  Discharged
  by `Bindings.InsertionLifespan.isMaximalSolution_of_inserted` (lane 098). -/
  maximal : ∀ ε ∈ Ioc (0 : ℝ) family.ε₀,
    Contracts.V2.MaximalPartial.IsMaximalSolution ν family.a (family.force ε)
      (family.velocity ε) (family.pressure ε)
  /-- The **second display** of Theorem 4.2, `limsup_{t↑T}‖u_ε(t)‖_∞ = ∞`
  (`04-whole-space.tex:35`; `research/section4/STATEMENTS.md:348`), for every
  `ε ∈ (0, ε₀]`, in the frozen `Contracts.V1.MaximalPartial` vocabulary
  (`limsupLeft`/`speedENorm` = `⟪D01:limsupLeft⟫`/`⟪D01:normLinfty⟫`,
  `Contracts/V1/MaximalPartial.lean:101,106`).  `R42.insertion_lifespan` registers
  the blow-up only in the pointwise `SpeedUnboundedAt` form
  (`research/R42/REVIEW_CONTRACT.md:443-446`); this field states the displayed
  essential-supremum form, the one the binding proves inside `lifespan_upper`
  (`Bindings/InsertionLifespan.lean:215-217`) through
  `limsupLeft_speedENorm_eq_top`.  The spatial slice is `fun x => family.velocity ε
  (t, x)` because `family.velocity` is spacetime-valued (see the module docstring's
  fidelity note). -/
  blowup_limsup : ∀ ε ∈ Ioc (0 : ℝ) family.ε₀,
    Contracts.V1.MaximalPartial.limsupLeft family.T
        (fun t => Contracts.V1.MaximalPartial.speedENorm
          (fun x : Space => family.velocity ε (t, x))) = ⊤

/-! ## The existential form consumed downstream -/

/-- What `R41D`, `R46` and `R47` receive from R42's version-2 record, in the shape
of `Contracts.V1.InsertionLifespan.insertionLifespanStatement`
(`Contracts/V1/InsertionLifespan.lean:154`): given an inserted family `F` with
reference force in `F_R` and reference regular through `T + δ`, all five clauses
hold for that very family, i.e. there is an `InsertionLifespanV2API` whose `family`
is `F`.

`A.family = F` is an equation, not an existential: the clauses are about the
**given** family, not a substituted one (lane-092 review finding 5).  The two
hypotheses are exactly version one's — `Data.MemForceR F.g` and
`Data.RegularThrough ν F.a F.g (F.T + F.margin)`; `0 < ν` and `F.a ∈ Data.initialClassR`
are derived inside the binding, not assumed.

Introducing this definition asserts nothing. -/
def insertionLifespanV2Statement : Prop :=
  ∀ (ν : ℝ) (P : PacketAPI ν) (F : InsertionFamilyAPI ν P),
    Data.MemForceR F.g →
    Data.RegularThrough ν F.a F.g (F.T + F.margin) →
      ∃ A : InsertionLifespanV2API ν P, A.family = F

end BlowupDensity.Contracts.V2.InsertionLifespan
