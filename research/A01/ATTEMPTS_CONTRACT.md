# A01 — lane 112: registering `A01.regularity_partial`

Contract lane. Registers the two *proved* fields of
`research/A01/Spec.lean`'s `ManuscriptLocalRegularity` — `projected` (lane 093)
and `pressure_potential` (lane 106) — as the versioned partial contract
`A01.regularity_partial`, and clears the `pressurePotential` /
`HasSymmetricJacobian` bridge debt `REVIEW_M4.md` finding 6 records. No new
mathematics; the two fields are already theorems of every `ClassicalSolutionR`.

## Decisions recorded

1. **Shape: flatten, no membership hypotheses.** `ManuscriptLocalRegularity` is
   a `Prop` structure *parameterized* by `u : ClassicalSolutionR ν a f T`. Two
   options were on the table (task brief): keep the structure-with-parameter shape
   (a `Prop` structure over `u` plus a `∀ u` wrapper), or flatten each field to
   `∀ ν a f T (u : Data.ClassicalSolutionR ν a f T), <body>`. Chose **flatten**,
   mirroring `Contracts/V1/EnergyAbsorptionPartial`'s `velocityJets`.
   Unlike `velocityJets`, **no** `0 < ν` / `a ∈ initialClassR` / `MemForceR f`
   hypotheses were added: the spec structure carries none and neither discharging
   theorem (`projected_of_classicalSolution`, `pressure_potential_of_classicalSolution`)
   needs them, so the registered form is the strictly stronger hypothesis-free
   reading (holds for *any* classical solution). `velocityJets` kept those three
   only because C01's `EnergyAbsorptionAPI.velocityJets` had them.

2. **`Prop` structure, inferred not annotated.** Both fields are propositional, so
   the API lands in `Prop`. Matched `Contracts/V1/Uniqueness.UniquenessAPI`: declared
   `structure ... where` (no explicit `: Prop`; Lean infers it), binding is a
   `theorem`, test is a `theorem checkedRegularityPartial`. (An earlier draft wrote
   `structure ... : Prop where`; switched to the un-annotated form to match the
   established `UniquenessAPI` precedent exactly. Both elaborate.)

3. **Which spec-local defs to restate.** `projected` mentions `convectionDivergence`
   (spec-local) → restated. `pressure_potential` mentions only `Data.pressurePotential`
   and `Data.PressureGaugeEquivOn` (reused from `Data.lean`, never restated).
   `HasSymmetricJacobian` is mentioned by **neither** registered field, but is
   restated in the contract anyway — **reserved for the excluded `pressure_recovery`**,
   whose `IsLerayComplement` (`Spec.lean:135`) has this predicate as its second clause,
   so the lane that registers `pressure_recovery` imports it rather than restating it
   a second time. (Contract review Finding 2 corrected an earlier framing: this is not
   a CLAUDE.md "bridge debt" — `RadialPotential.HasSymmetricJacobian` mirrors a *draft
   spec*, not a contract, so no debt existed for it; only `pressurePotential` was the
   load-bearing debt of `REVIEW_M4.md` #6.) It is a genuine predicate `def`, not a
   placeholder `Prop` field, so hard-rule 3 is not touched. Documented as "referenced
   by no field of this version" in both contract and binding.

4. **Bridges cleared** (all `rfl`, verified in a throwaway scratch *before* writing
   the frozen files — see "What worked" below):
   * `Contracts.V1.Data.pressurePotential = RadialPotential.pressurePotential` — the
     load-bearing debt from `REVIEW_M4.md` #6 (`REVIEW_P1` had predicted it elaborates).
   * `RegularityPartial.convectionDivergence = Section4.A01.convectionDivergence`.
   * `RegularityPartial.HasSymmetricJacobian = RadialPotential.HasSymmetricJacobian`.
   * `PressureGaugeEquivOn` reuses the already-registered
     `Bindings.uniqueness_pressureGaugeEquivOn_eq`; not restated.

5. **Field-wise transport.** `Data.ClassicalSolutionR` and the `Section4/A02`
   restatement are distinct inductive types (no structure `rfl` bridge possible), so
   both fields apply their A01 theorem to `Bindings.uniqueness_toA02 u` — the reused
   field-wise converter, exactly as `Bindings/EnergyAbsorptionPartial.velocityJets`
   does. Field types are defeq, so the assignments typecheck without conversion lemmas.

## What worked / did not

* **De-risk probe — cited by content, not by path** (per `logs/LESSONS.md`'s warning
  about volatile probe citations). Before writing the frozen files I ran a throwaway
  scratch (since deleted) that restated the two spec-local defs locally and checked,
  under `lake env lean`, the three `rfl` bridges (`Data.pressurePotential =
  RadialPotential.pressurePotential`; `convectionDivergence`; `HasSymmetricJacobian`)
  and both field assignments (each A01 theorem applied through `uniqueness_toA02`). It
  elaborated at exit 0 with only unused-variable warnings, confirming every defeq the
  contract relies on. That evidence is now **permanent by other means**: the same three
  bridges and two assignments compile in the frozen `Bindings/RegularityPartial.lean`,
  so nothing rests on the vanished scratch. `lake build Tests.RegularityPartial` then
  compiled on the first attempt (`checked; standard logical axioms only`).

* **Negative example — JSON re-encoding.** First append to `verification/contracts.json`
  used `json.dumps(..., indent=2)` with the default `ensure_ascii=True`, which re-escaped
  every existing Unicode scope string (`ν → ν`, `R³ → R³`, …) and produced an
  18-insertion / 7-deletion diff touching unrelated entries. Reverted with
  `git checkout` and re-appended with `ensure_ascii=False`; the file is canonical under
  `json.dumps(data, indent=2, ensure_ascii=False) + '\n'`, giving a clean 11-line
  addition. Lesson: for this registry always use `ensure_ascii=False`.

## Excluded (asserted nowhere by this contract)

* `sobolev_smooth` (Spec.lean:180, split row m1, size **L**): all-order Sobolev *time*
  smoothness; strictly stronger than `ClassicalSolutionR.sobolev`'s `ContinuousOn`,
  not harvestable.
* `pressure_recovery` (Spec.lean:197, split row m2, size **M**): eq:Rpressure on
  `Ico 0 T`; needs unit P3 (HeliCorgi Helmholtz pressure) and the P2 Liouville gap.
* Everything in `LocalTheoryAPI` (Spec.lean:277): `solution`, `regularity`,
  `horizon_lower_bound`. And any uniqueness / maximal-lifespan clause (A02).
* Fidelity caveat (`REVIEW_M4.md` #7): `pressure_potential` carries **no**
  Navier–Stokes content — its proof consumes only `u.pressure_smooth`. Registering it
  fixes the gauge representative; it does not pin the pressure down.
