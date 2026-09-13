import Contracts.V1.InsertionFamily
import Contracts.V1.InsertionLifespan
import Contracts.V1.MaximalPartial
import Contracts.V1.DatumLemmas
import Bindings.MaximalPartial
import Bindings.DatumLemmas
import NSFormalization.Section4.R42.SolutionOnShorter
import NSFormalization.Section4.R42.BlowupEssSup

/-! The Bindings-level assembly of the **two lifespan clauses of Theorem 4.2**
(`paper/sections/04-whole-space.tex:32,34`) from the registered contracts and the
merged `R42` modules.  This file has two inhabitants:

* §8 `insertionLifespanAPI` inhabits the **registered** contract
  `R42.insertion_lifespan` (version 1 of a new id,
  `Contracts.V1.InsertionLifespan.InsertionLifespanAPI`, 5 fields — lane 096);
  this is the record consumers should use.
* §7 `insertionLifespan` inhabits the legacy, frozen, unregistered 3-field
  `Contracts.V1.InsertionFamily.InsertionLifespanAPI`
  (`Contracts/V1/InsertionFamily.lean:421-436`) — the lane-092 record.  It is
  kept because it is that structure's only inhabitant and §8 reuses its two
  clause proofs (`referenceLifespan`, `lifespan_eq`) verbatim.

The whole assembly rests on three registered interfaces and the merged R42
analytic lemmas:

* `BlowupDensity.Bindings.maximalPartial` — the registered
  `Contracts.V1.MaximalPartial.MaximalPartialAPI` (A02's proved maximal-solution
  interface), giving `lifespan_ge_of_forall_shorter`, `lifespan_le_of_unbounded`
  and `regularThrough_iff`, all stated in `Data` vocabulary
  (`Data.maximalLifespanR`, `Data.RegularThrough`, `Data.ClassicalSolutionR`);
* `BlowupDensity.Bindings.datumLemmas` — the registered
  `Contracts.V1.DatumLemmas.DatumLemmasAPI` (D01), giving
  `memForceR_of_compact_difference`;
* `Bindings.MaximalPartial`'s `uniqueness_toA02` / `maximalPartial_ofA02`, the
  field-by-field conversions between the contract's `Data.ClassicalSolutionR` and
  the `Section4/A02` restatement (a `rfl` bridge being impossible for two
  separately declared structures);
* `NSFormalization.Section4.R42.{classicalSolutionR_of_inserted,
  limsupLeft_speedENorm_eq_top, continuous_slice_of_velocity_smooth}` — the merged
  `sol_on_shorter` construction (lane 087) and the pointwise → essSup blow-up
  transfer (lane 080).

## Route (see `research/R42/LIFESPAN_SPLIT.md`)

1. `sol_on_shorter` (split #1): the inserted pair is a `Data.ClassicalSolutionR`
   on every `[0,S)`, `S < T` — the reviewer-verified 22-line instantiation of
   `classicalSolutionR_of_inserted` (`research/R42/REVIEW_SOL_SHORTER.md`).
2. `memForceR_force` (split #3): `g_ε ∈ F_R` from `g ∈ F_R` and
   `forceDifference_compact`, one application of the registered D01 unit.
3. `lifespan_lower` (split #5): `ofReal T ≤ maximalLifespanR ν a g_ε`, from (1) and
   `lifespan_ge_of_forall_shorter` — the only structural input is `0 < T`, which is
   `CorrectionAPI.time_pos`, so **no extra hypothesis** here.
4. `lifespan_upper` (split #4): `maximalLifespanR ν a g_ε ≤ ofReal T`, from (1),
   (2), the essSup blow-up transfer of `F.blowup` and `lifespan_le_of_unbounded`.
5. `lifespan_eq` := `le_antisymm` of 4 and 3 — the `lifespan` field.
6. `referenceLifespan` (split #6): `ofReal (T+δ) < maximalLifespanR ν a g`, one
   step from `regularThrough_iff` at `T' = T+δ`.  Taken through the registered
   `maximalPartial.regularThrough_iff` (Data vocabulary), so no `A02`/`Data`
   `RegularThrough` bridge is needed.
7. `insertionLifespan` — the legacy frozen 3-field inhabitant (lane 092).
8. `insertionLifespanAPI` — the registered `R42.insertion_lifespan` inhabitant
   (lane 096), reusing (6) and `lifespan_eq` and additionally storing `hg`/`hreg`
   as the record's `memForce`/`regular` fields.

## The registered contract's hypothesis list

`insertionLifespanAPI` — the registered `R42.insertion_lifespan` — adds exactly
**two** hypotheses beyond `F : InsertionFamilyAPI ν P`, and no more:

* `hg  : Data.MemForceR F.g`  (the reference force is in `F_R`,
  `04-whole-space.tex:32`).  `Data.ClassicalSolutionR` has no force-class field
  and `g_ε − g ∈ C_c^∞` alone cannot give it (`DatumLemmas.lean:378-381`), so this
  must be carried.  Enters only `lifespan_upper`.
* `hreg : Data.RegularThrough ν F.a F.g (F.T + F.margin)`  (the reference is *the*
  solution, regular through `T+δ`, `04-whole-space.tex:32`).
  `InsertionFamilyAPI.reference` is only a solution on the half-open `[0,T+δ)`,
  which gives `≤`, not the strict `<`; `RegularThrough` supplies a solution past
  `T+δ`.  Enters only `referenceLifespan`.

Four things that look like hypotheses but are **derived from the ambient
contracts** (lane-092 review findings 1, 2; corrected from an earlier draft that
listed the first two as hypotheses):

* `0 < ν`  = `P.viscosity_pos` (`Packet.lean:199`; `P` is a parameter of every
  structure here);
* `F.a ∈ Data.initialClassR` (`X_R`) = `initialClassR_a F`, derived from
  `F.reference` at `t = 0` (reviewer's 12-line derivation, below);
* `0 < F.T` = `CorrectionAPI.time_pos`, `0 < F.margin` = `CorrectionAPI.margin_pos`;
* the essSup blow-up = `F.blowup` + `F.velocity_smooth` through
  `limsupLeft_speedENorm_eq_top`.

Lane 072's `Section4/R42/Lifespan.lean` (`memForceR_insertedForce`,
`lt_maximalLifespanR_of_regularThrough`) is **deliberately not imported**: both are
`A02`-vocabulary restatements of steps we take directly through the registered
`Data`-vocabulary fields `datumLemmas.memForceR_of_compact_difference` and
`maximalPartial.regularThrough_iff`, which need no `A02`↔`Data` bridge.

Every declaration carries the `BlowupDensity.Bindings.InsertionLifespan`
namespace; `maximalPartial`, `datumLemmas`, `uniqueness_toA02`,
`maximalPartial_ofA02` are visible through the parent `BlowupDensity.Bindings`.
-/

noncomputable section

namespace BlowupDensity.Bindings.InsertionLifespan

open Set
open BlowupDensity.Contracts.V1
open scoped ENNReal

variable {ν : ℝ} {P : PacketAPI ν} (F : InsertionFamilyAPI ν P) {ε : ℝ}

/-! ## 1. `sol_on_shorter` (split #1)

The inserted pair `(u_ε, p_ε)` is a classical solution `Data.ClassicalSolutionR`
on every shorter horizon `0 < S < T`, with velocity `u_ε` and pressure `p_ε`.
This is the reviewer-verified 22-line instantiation of the merged
`classicalSolutionR_of_inserted` (`research/R42/REVIEW_SOL_SHORTER.md`): the
reference is moved into the `A02` restatement by `uniqueness_toA02`, the datum
threshold `t₁ = T − 2ε² > 0` comes from `ScalingAPI.eps_time`, the three
history/support hypotheses are the API fields rewritten through
`reference_velocity` / `reference_pressure`, and the resulting `A02` solution is
moved back to `Data.ClassicalSolutionR` by `maximalPartial_ofA02`. -/
theorem sol_on_shorter (hε : ε ∈ Ioc (0 : ℝ) F.ε₀) :
    ∀ S : ℝ, 0 < S → S < F.T →
      ∃ w : Data.ClassicalSolutionR ν F.a (F.force ε) S,
        w.velocity = F.velocity ε ∧ w.pressure = F.pressure ε := by
  intro S hS0 hST
  have hεS : ε ∈ Ioc (0 : ℝ) F.scaling.ε₀ := ⟨hε.1, hε.2.trans F.eps_le_scaling⟩
  have ht₁ : 0 < F.scaling.correction.T - 2 * ε ^ 2 := by
    have := lt_of_lt_of_le (F.scaling.eps_time ε hεS) (min_le_left _ _); linarith
  have href : F.reference.velocity = F.scaling.correction.v := F.reference_velocity
  have hrefp : F.reference.pressure = F.scaling.correction.π := F.reference_pressure
  obtain ⟨w, hv, hp⟩ := NSFormalization.Section4.R42.classicalSolutionR_of_inserted
    (uniqueness_toA02 F.reference) F.scaling.correction.margin_pos ht₁
    (F.velocity ε) (F.pressure ε)
    (F.velocity_smooth ε hε) (F.pressure_smooth ε hε) (F.initial ε hε)
    (F.incompressible ε hε) (F.momentum ε hε)
    (by intro t h0 h1 x
        show F.velocity ε (t, x) = F.reference.velocity (t, x)
        rw [href]; exact F.history ε hε t h0 h1 x)
    (by intro t ht
        show tsupport (fun x => F.velocity ε (t, x) - F.reference.velocity (t, x)) ⊆ _
        rw [href]; exact F.velocityDifference_support ε hε t ht)
    (by intro t ht
        show tsupport (fun x => F.pressure ε (t, x) - F.reference.pressure (t, x)) ⊆ _
        rw [hrefp]; exact F.pressureDifference_support ε hε t ht)
    hS0 hST
  exact ⟨maximalPartial_ofA02 w, hv, hp⟩

/-! ## 2. `memForceR_force` (split #3)

`g_ε ∈ F_R` from `g ∈ F_R` and the compact force difference `g_ε − g ∈ C_c^∞`,
one application of the registered D01 unit
`datumLemmas.memForceR_of_compact_difference`.  `F.g` unfolds to
`F.scaling.correction.g`, so `F.forceDifference_compact ε hε` is exactly the
`Data.MemForceCompact (fun z => F.force ε z − F.g z)` the field consumes. -/
theorem memForceR_force (hg : Data.MemForceR F.g) (hε : ε ∈ Ioc (0 : ℝ) F.ε₀) :
    Data.MemForceR (F.force ε) :=
  datumLemmas.memForceR_of_compact_difference F.g (F.force ε) hg
    (F.forceDifference_compact ε hε)

/-! ## 2b. `initialClassR_a` — `a ∈ X_R`, derived (not a hypothesis)

`F.a ∈ Data.initialClassR = {a | MemHInfty a ∧ IsSolenoidal a}` (`Data.lean:509`)
follows from the reference solution at `t = 0`: `F.a = F.reference.velocity(0,·)`
(`F.reference.initial`), which is smooth (`D01.contDiff_slice` on
`F.reference.velocity_smooth`, already in this module's import closure via
`Bindings.DatumLemmas`), has the datum path `F.reference.sobolev` at `t = 0`, and
is divergence-free (`F.reference.divergence` at `t = 0`).  Derivation supplied by
the lane-092 reviewer (`research/R42/REVIEW_BINDING.md` finding 2,
`/tmp/r42rev092/Scratch.lean`); this replaces the earlier `ha` hypothesis. -/
theorem initialClassR_a : F.a ∈ Data.initialClassR := by
  have hzero : (0 : ℝ) ∈ Ico (0 : ℝ) (F.scaling.correction.T + F.scaling.correction.δ) :=
    ⟨le_rfl, F.reference.horizon_pos⟩
  have ha_eq : (fun y : Space => F.reference.velocity (0, y)) = F.a :=
    funext F.reference.initial
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have h := NSFormalization.Section4.D01.contDiff_slice F.reference.velocity_smooth hzero
    rwa [ha_eq] at h
  · intro m
    obtain ⟨G, _, hGd⟩ := F.reference.sobolev m
    exact ⟨G 0, by rw [← ha_eq]; exact hGd 0 hzero⟩
  · intro x
    have h := F.reference.divergence 0 hzero x
    simpa only [Data.IsSolenoidal, NavierStokes.ProblemStatement.spatialDivergence,
      NavierStokes.ProblemStatement.spatialDerivative, ← ha_eq] using h

/-! ## 3. `lifespan_lower` (split #5)

`ofReal T ≤ maximalLifespanR ν a g_ε`, from `sol_on_shorter` and the registered
`lifespan_ge_of_forall_shorter`.  Its only structural input `0 < T` is
`CorrectionAPI.time_pos`, so this clause needs no extra hypothesis. -/
theorem lifespan_lower (hε : ε ∈ Ioc (0 : ℝ) F.ε₀) :
    ENNReal.ofReal F.T ≤ Data.maximalLifespanR ν F.a (F.force ε) :=
  maximalPartial.lifespan_ge_of_forall_shorter ν F.a (F.force ε) F.T
    F.scaling.correction.time_pos
    (fun b hb0 hbT => ⟨(sol_on_shorter F hε b hb0 hbT).choose⟩)

/-! ## 4. `lifespan_upper` (split #4)

`maximalLifespanR ν a g_ε ≤ ofReal T`, from `sol_on_shorter`, `memForceR_force`,
the essSup blow-up transfer, and the registered `lifespan_le_of_unbounded`.  The
blow-up hypothesis is produced from the pointwise `F.blowup` and the slice
continuity of `F.velocity_smooth` via lane 080's `limsupLeft_speedENorm_eq_top`;
its `A02.limsupLeft`/`A02.speedENorm` conclusion is definitionally the contract's
`MaximalPartial.limsupLeft`/`speedENorm` (`Bindings/MaximalPartial.lean:57,61`,
both `rfl`). -/
theorem lifespan_upper (hg : Data.MemForceR F.g) (hε : ε ∈ Ioc (0 : ℝ) F.ε₀) :
    Data.maximalLifespanR ν F.a (F.force ε) ≤ ENNReal.ofReal F.T := by
  have hgε : Data.MemForceR (F.force ε) := memForceR_force F hg hε
  have hblow : MaximalPartial.limsupLeft F.T
      (fun t => MaximalPartial.speedENorm (fun x : Space => F.velocity ε (t, x))) = ⊤ :=
    NSFormalization.Section4.R42.limsupLeft_speedENorm_eq_top (F.blowup ε hε)
      (NSFormalization.Section4.R42.continuous_slice_of_velocity_smooth
        (F.velocity_smooth ε hε))
  exact maximalPartial.lifespan_le_of_unbounded ν F.a (F.force ε) F.T P.viscosity_pos
    (initialClassR_a F) hgε F.scaling.correction.time_pos (F.velocity ε) (F.pressure ε)
    (sol_on_shorter F hε) hblow

/-! ## 5. `lifespan_eq` — the `lifespan` field

`T^ν_{max,R}(a, g_ε) = T` (`04-whole-space.tex:34`), `le_antisymm` of the two
bounds. -/
theorem lifespan_eq (hg : Data.MemForceR F.g) (hε : ε ∈ Ioc (0 : ℝ) F.ε₀) :
    Data.maximalLifespanR ν F.a (F.force ε) = ENNReal.ofReal F.T :=
  le_antisymm (lifespan_upper F hg hε) (lifespan_lower F hε)

/-! ## 6. `referenceLifespan` — the `referenceLifespan` field (split #6)

`ofReal (T+δ) < maximalLifespanR ν a g` (`04-whole-space.tex:32`), one step from
the registered `maximalPartial.regularThrough_iff` at `T' = T+δ`.  The positivity
`0 < T+δ` is `add_pos time_pos margin_pos`.  Because the field is taken in `Data`
vocabulary, no `A02`/`Data` `RegularThrough` bridge is needed. -/
theorem referenceLifespan (hreg : Data.RegularThrough ν F.a F.g (F.T + F.margin)) :
    ENNReal.ofReal (F.T + F.margin) < Data.maximalLifespanR ν F.a F.g :=
  (maximalPartial.regularThrough_iff ν F.a F.g (F.T + F.margin)
    (add_pos F.scaling.correction.time_pos F.scaling.correction.margin_pos)).mp hreg

/-! ## 7. `insertionLifespan` — the legacy frozen 3-field inhabitant (lane 092)

Inhabits the frozen, unregistered `Contracts.V1.InsertionFamily.InsertionLifespanAPI`.
Takes exactly the two hypotheses `hg`, `hreg` — the same two the registered
`R42.insertion_lifespan` carries (see §8).  `0 < ν` and `F.a ∈ Data.initialClassR`
are derived inside `lifespan_upper` from `P.viscosity_pos` and `initialClassR_a`. -/
def insertionLifespan (hg : Data.MemForceR F.g)
    (hreg : Data.RegularThrough ν F.a F.g (F.T + F.margin)) :
    InsertionLifespanAPI ν P where
  family := F
  referenceLifespan := referenceLifespan F hreg
  lifespan := fun _ε hε => lifespan_eq F hg hε

/-- Regression guard (lane-092 review finding 5): the two clauses are about the
**given** family `F`, not a substituted one. -/
theorem insertionLifespan_family (hg : Data.MemForceR F.g)
    (hreg : Data.RegularThrough ν F.a F.g (F.T + F.margin)) :
    (insertionLifespan F hg hreg).family = F := rfl

/-! ## 8. `insertionLifespanAPI` — the **registered** structure inhabitant

Inhabits the registered `Contracts.V1.InsertionLifespan.InsertionLifespanAPI`
(`Contracts/V1/InsertionLifespan.lean`, contract `R42.insertion_lifespan`).  It
differs from the frozen 3-field `insertionLifespan` above only by additionally
storing the two hypotheses `hg`, `hreg` as the new record's `memForce`/`regular`
fields — so a downstream consumer holding the record can reuse them (R47 needs
`g ∈ F_R`).  The two lifespan clauses reuse the same `referenceLifespan` and
`lifespan_eq` proofs. -/
def insertionLifespanAPI (hg : Data.MemForceR F.g)
    (hreg : Data.RegularThrough ν F.a F.g (F.T + F.margin)) :
    Contracts.V1.InsertionLifespan.InsertionLifespanAPI ν P where
  family := F
  memForce := hg
  regular := hreg
  referenceLifespan := referenceLifespan F hreg
  lifespan := fun _ε hε => lifespan_eq F hg hε

/-- Regression guard (lane-092 review finding 5): the two clauses of the
registered record are about the **given** family `F`, not a substituted one. -/
theorem insertionLifespanAPI_family (hg : Data.MemForceR F.g)
    (hreg : Data.RegularThrough ν F.a F.g (F.T + F.margin)) :
    (insertionLifespanAPI F hg hreg).family = F := rfl

end BlowupDensity.Bindings.InsertionLifespan
