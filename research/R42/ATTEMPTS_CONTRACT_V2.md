# ATTEMPTS — R42.insertion_lifespan_v2 (lane 114)

Version-2 contract for the two lifespan clauses, adding the three exports the V1
review named as owed (`REVIEW_CONTRACT.md:443-452`). All three are already proved
in `Bindings/InsertionLifespan.lean` (lane 098); this lane only re-exposes them as
contract fields.

## Decisions

- **`extends`, not a new id.** `InsertionLifespanV2API extends
  Contracts.V1.InsertionLifespan.InsertionLifespanAPI ν P` (frozen V1 untouched).
  Mirrors the `Contracts/V2/MaximalPartial.lean` + `Bindings/MaximalPartialV2.lean`
  pair. The V1 record's `family` field is inherited and is referenced directly by
  name in the three new field types (`family.ε₀`, `family.a`, `family.force ε`,
  `family.velocity ε`, `family.pressure ε`, `family.T`) — legal because inherited
  fields are in scope in the child structure body.
- **Binding via `{ … with … }`.** `insertionLifespanV2API F hg hreg :=
  { insertionLifespanAPI F hg hreg with solution := …, maximal := …,
  blowup_limsup := … }`, exactly as `maximalPartialV2` reuses `maximalPartial`.
  So every V1 field (`memForce`, `regular`, `referenceLifespan`, `lifespan`) is
  inherited unchanged and `toInsertionLifespanAPI` recovers V1 by rfl.
- **Field ← binding theorem, verbatim.**
  - `solution` ← `sol_fullHorizon F hε` (`Bindings/InsertionLifespan.lean:319`).
  - `maximal` ← `isMaximalSolution_of_inserted F hg hε` (`:349`), in the
    `Contracts.V2.MaximalPartial.IsMaximalSolution` vocabulary
    (`A02.maximal_partial_v2`).
  - `blowup_limsup` ← new standalone theorem `blowup_essSup` in the V2 binding.
    V1 kept this term only as `have hblow` inside `lifespan_upper`
    (`:215-217`); I lifted the identical term
    `limsupLeft_speedENorm_eq_top (F.blowup ε hε)
    (continuous_slice_of_velocity_smooth (F.velocity_smooth ε hε))` to a named
    theorem so the field can name it. No new proof content.
- **No new hypothesis.** `#check @insertionLifespanV2API` prints the same explicit
  arguments as `@insertionLifespanAPI`: `F`, `hg : Data.MemForceR F.g`,
  `hreg : Data.RegularThrough ν F.a F.g (F.T + F.margin)`, plus implicit `{ν} {P}`.
  `sol_fullHorizon`/`blowup_essSup` need neither hypothesis;
  `isMaximalSolution_of_inserted` needs only `hg` (through `lifespan_eq`). See
  `axioms_contract_v2.lean` output.
- **`insertionLifespanV2Statement`** added to the V2 contract, shaped like V1's
  `insertionLifespanStatement`, so `checkedInsertionLifespanV2` is a closed Prop
  for `checkAxioms`; its `rfl` pins `A.family = F` (anti-substitution guard).

## Fidelity: what does NOT match the manuscript token-for-token, and why

`blowup_limsup`. `STATEMENTS.md:348` records the second display abstractly as
`⟪D01:limsupLeft⟫ T (fun t => ⟪D01:normLinfty⟫ (u_ε t))`, where `u_ε t` is the
spatial field at time `t`. The field renders it as

```
limsupLeft family.T (fun t => speedENorm (fun x => family.velocity ε (t, x)))
```

The **only** difference is the slice notation: `family.velocity ε` is a *spacetime*
field (`SpaceTime → Space`, matching `Data.ClassicalSolutionR.velocity` and the
`R42.insertion_family` `velocity` field), so its spatial slice at time `t` is
`fun x => family.velocity ε (t, x)`, not a curried `family.velocity ε t`. The
operators are identical: `Contracts.V1.MaximalPartial.limsupLeft`/`speedENorm`
(`MaximalPartial.lean:101,106`) are the frozen restatements of
`⟪D01:limsupLeft⟫`/`⟪D01:normLinfty⟫`, `= limsup_{t↑T}` over `𝓝[<]T` and the `L^∞`
essential supremum. This is byte-for-byte the term the V1 binding proves in
`lifespan_upper` and feeds to `lifespan_le_of_unbounded`; the slice notation is
forced by the record's velocity representation, not a change of statement.

The other two fields (`solution`, `maximal`) match their proved binding theorems
token-for-token; no gap.

## Negative example (with pasted error text)

First draft of `Bindings/InsertionLifespanV2.lean` wrote the three field bodies as
`fun ε hε => …`. `ε` is not referenced (the reused theorems take `ε` implicitly),
so the unused-variable linter fired three times:

```
warning: Bindings/InsertionLifespanV2.lean:85:20: Variable name `ε` is not explicitly referenced.
Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _ε
```

`Bindings` is not `warningAsError`, so this did not fail the build, but the fix
matches the V1 convention (`insertionLifespan := fun _ε hε => lifespan_eq …`,
`LESSONS`/REVIEW note on the `_ε` underscore): renamed to `fun _ε hε => …`, warning
gone. No such issue in `Tests` (each `example` uses all its binders: `ν`, `P` in
`A`'s type, `A`, `ε`, `hε`).

No hard compile failure was hit: the three theorems already typecheck in the V1
binding, the field types are defeq to them (`family = F` by rfl after `{ … with }`),
and `limsupLeft`/`speedENorm` bridge to the `Section4/A02` copies by rfl
(`Bindings/MaximalPartial.lean:57,61`).

## Commands and results

| command | result |
|---|---|
| `lake build Tests.InsertionLifespan Bindings.MaximalPartialV2` (warm) | `Build completed successfully (9975 jobs)` |
| `lake build Tests.InsertionLifespanV2` | success; `Tests/InsertionLifespanV2.lean:32:0: Contract …checkedInsertionLifespanV2: checked; standard logical axioms only` |
| `lake env lean ../research/R42/axioms_contract_v2.lean` | `blowup_essSup`, `insertionLifespanV2API`, `insertionLifespanV2API_family` each `[propext, Classical.choice, Quot.sound]`; `@insertionLifespanV2API` signature identical to `@insertionLifespanAPI` (only `F`/`hg`/`hreg`) |
| `make check` | `test_contract_policy.py` 13/13 OK; `check_work_queue.py` "30 work items: … consistent"; `Tests.InsertionLifespanV2` in the closure |
| `make test` | all 20 registered contracts "checked; standard logical axioms only", incl. `checkedInsertionLifespanV2`; no `error:` |
| `make test-mutations` | `implementation_refactor: accepted`; `admitted_proof`/`extra_axiom`/`weakened_hypothesis` "rejected as required"; "Mutation suite passed." |
| `check_contracts.py --base-ref origin/erenup/integration` | `registered_contracts: 20`, `base_compatibility_checked: True`, `R42.insertion_lifespan_v2` in closures |
| `git diff verification/contracts.json \| grep -c '^-'` | `1` (the `--- a/` header only) — purely additive, no scope churn |
