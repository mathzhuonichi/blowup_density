# I02 version 2 — attempts and decisions (lane 029)

Goal: let the *caller* of the correction contract pin the cutoff radius above a
prescribed compact set, so that `eps_space : ε · θRadius < r` alone places the
rescaled packet **force** inside `B`. Filed independently by two reviewers —
`research/I03/REVIEW_CONTRACT.md` §5.1 item 4 and `research/R42/ATTEMPTS.md` §3,
§5b — as the clean repair of the `K → K_*` interface gap.

## 0. What was built

| file | lines | content |
|---|---|---|
| `verification/Contracts/V2/Correction.lean` | 167 | `CorrectionAPI ν P K` (extends V1, one new field) + `correctionStatement` |
| `verification/Bindings/CorrectionV2.lean` | 553 | `correctionV2`, `correctionV1_of_v2`, `prescribed_subset_ball`, `correctionStatement_of_v2`, `isCompact_carrierStar`, `force_carrier_subset_ball` |
| `verification/Tests/CorrectionV2.lean` | 30 | `checkedCorrectionV2` + `run_cmd TestSupport.checkAxioms` |
| `formalization/NSFormalization/Section4/I02/Prescribed.lean` | 57 | `exists_prescribed_cutoff` — the only new mathematics |

Registered as `I02.correction_v2`, version 2. `I02.correction` (version 1), its
specification, its binding and `Tests/Correction.lean` are untouched.

## 1. The design choice: prescribed **set**, not prescribed **radius**

Both were admissible under the task. A radius parameter would have read
`prescribedRadius ≤ θRadius`, with the caller responsible for producing a radius
that already bounds whatever it cares about.

Set wins, for three reasons.

1. **It is the manuscript's own formulation.** `03-torus.tex:101-102` says
   "choose a compact set `K_*` containing `K` and the spatial projection of
   `supp F`", and only then builds `θ`, `R_*` and the smallness conditions of
   `:104-105` around it. A radius parameter would formalize a step the paper
   does not take and would leave `K_*` unnamed in the record.
2. **The radius form pushes the same work onto every caller.** To supply a
   radius, `R42` would still have to run
   `hKall.isBounded.exists_pos_norm_le` on `P.carrier ∪ Prod.snd '' tsupport
   P.force` — which is exactly the boilerplate §3 of `research/R42/ATTEMPTS.md`
   complains about, merely relocated. With the set form, `exists_prescribed_cutoff`
   runs it once, inside the binding.
3. **The set form is strictly stronger and still cheap.** A radius bound gives
   `K ⊆ ball 0 θRadius` only if the caller separately proves it; the set form
   gives the *plateau* clause `K ⊆ plateau`, which additionally yields `θ = 1`
   on `K` — the hypothesis shape every background-removal lemma in
   `Source/PhysicalRemoval.lean` takes. The ball form is recovered in three
   lines (`Bindings.prescribed_subset_ball`), so nothing is lost.

The added field is therefore `prescribed_subset_plateau : K ⊆ plateau`, stated
against `plateau` rather than against `Metric.ball 0 θRadius`. It is a
**conclusion**, not a hypothesis: an inhabitant must build the cutoff around
`P.carrier ∪ K`. Hence V2 ⇒ V1, checked as `Bindings.correctionStatement_of_v2`.

### 1.1 `K` as a structure parameter, not a field

`CorrectionAPI ν P K` takes `K` the way it already takes `P`. The alternative —
a field `prescribed : Set Space` plus a pinning equation `A.prescribed = K` in
the statement — was rejected on the precedent `research/I03/ATTEMPTS.md` §2
sets: identifications that can be made definitional should not become fields
with no proof content, because a consumer can then mismatch them. With `K` in
the type, `Bindings.force_carrier_subset_ball` can be stated *about*
`CorrectionAPI ν P (P.carrier ∪ Prod.snd '' tsupport P.force)` with no side
condition at all.

`IsCompact K` is a hypothesis of `correctionStatement`, not a field of the
record. It is the manuscript's "choose a compact set" and it cannot be dropped:
`plateau ⊆ ball 0 θRadius`, so the statement is false for unbounded `K`. It is
not a field because a record is a list of what holds, and a consumer that chose
`K` already has its compactness.

### 1.2 `extends` rather than a re-typed structure

`structure CorrectionAPI (ν) (P) (K) extends V1.CorrectionAPI ν P where
prescribed_subset_plateau : K ⊆ plateau`.

Copying all 73 version-one fields into `Contracts/V2/` was considered and
rejected: the compatibility claim "V2 differs from V1 in exactly one field"
would then be a claim about copied text that nothing checks, and a typo in any
of the 73 docstring-bearing fields would silently weaken the registered V2.
With `extends`, `A.toCorrectionAPI : V1.CorrectionAPI ν P` is a *definitional*
projection — `Bindings.correctionV1_of_v2` is literally `A.toCorrectionAPI` —
so a V2 that dropped, renamed or weakened any version-one field would fail to
typecheck. Mathlib's `Subgroup extends Submonoid` is the same pattern, including
the reference to a parent field (`carrier` there, `plateau` here) in a later
field's type.

For the same reason `Contracts/V2/Correction.lean` **imports**
`Contracts.V1.Correction` and reuses its ten re-defined notions (`curl`,
`cross`, `scaledSpatialCutoff`, `scaledTemporalCutoff`, `dilateField`,
`parabolicVelocity`, `scaledPacket`, `alpha`, …) rather than copying them: the
`rfl` bridges in `Bindings/Correction.lean` already guard every one of those
against upstream drift, and a second copy would be an unguarded spelling.
`experiments/check_contracts.py` allows `Contracts.*` imports in a
specification, so this costs nothing at the policy level.

## 2. Reused vs new Lean

**Reused unchanged.** `Paper1.exists_spatial_cutoff`,
`Paper1.exists_temporal_cutoff`, `Paper1.exists_global_reference_extension`;
the whole `Source/PhysicalRemoval.lean` chain (`physical_smooth`,
`physical_divergence`, `physical_compact`, `physical_support`,
`physical_removes`); `Paper1.CorrectionProfile` /
`CorrectionForceProfile.physicalForce_spatial_derivative_bound` /
`CorrectionMixedNorms.physical_force_mixed_bound` /
`CorrectionEnergy.physicalCorrection_uniform_energy` /
`InsertionEnergy.correction_gradientSquare_bound`; all four existing
`Section4/I02/*.lean` modules; `Source/LocalizedInsertion`,
`Source/PacketScaling`, `Source/InsertionFamily`. The task's premise was right:
every one of these already takes the cutoff radius as a parameter, so **not one
of them needed a variant**. The version-two record is built from the same `R_*`,
`θ`, `η`, `ε₀ = min 1 (min (r/(R_*+1)) √(δ₁/2))` as version one.

Also reused, by import rather than by copy: the whole `Correspondence` section
of `Bindings.Correction` — **14** declarations, **12** of them `:= rfl`
(`derivativeEntry_eq` … `spatialGradient_eq` and `energyENorm_eq`), the other two
being `alpha_add_one` and `mixedLebesgueENorm_le`.
`Bindings/CorrectionV2.lean` imports `Bindings.Correction` and does not restate
any of them, which is why V1's drift guards cover V2 as well.

**New.** One theorem, `Section4.I02.exists_prescribed_cutoff`: a single cutoff
whose open plateau covers *two* prescribed compact sets, with the enclosing
radius produced rather than assumed. `Source/InsertionFamily.lean:218-234` forms
`Kall = K ∪ Prod.snd '' tsupport f` inline but then builds the plateau around
`K` alone and recovers the force radius separately as `hfR`, which is precisely
the shape `R42` could not discharge through the contract; this lemma puts both
sets inside the plateau.

**The duplication.** `Bindings/CorrectionV2.lean` repeats the 394-line
version-one argument. `verification/Bindings/Correction.lean` is the frozen
witness of the registered version-one contract and this lane does not edit it,
and the version-one record cannot produce a version-two one (its `θRadius` is
existentially bound and its witness fixes it from `P.carrier` alone), so there
is no factoring that avoids the copy without touching V1. The copy is exact:
`diff -u` of the two files is **seven hunks**, of which only **three** fall
inside the shared proof body — the signature and target type, the cutoff block,
and the record literal gaining one field —

```
-  choose Rb hRb hRle using P.carrier_compact.isBounded.exists_pos_norm_le
-  set R : ℝ := Rb + 1 with hRdef ;  have hR ; have hKR ;
-  choose θ O hθ hθc hθR hO hKO hθone using exists_spatial_cutoff P.carrier_compact hR hKR
+  choose R θ O hR hθ hθc hθR hO hKO hKplateau hθone using
+    exists_prescribed_cutoff P.carrier_compact hK
```

— and nothing else in 394 lines. The remaining four file hunks are outside the
shared body: the imports, the module docstring, the deletion of the
`Correspondence` section (imported from `Bindings.Correction`, not recopied),
and the five new trailing declarations. Hunk counts are context-dependent: at
`--unified=0` the proof body splits into five, the signature region accounting
for three of them. The mathematical delta is one `choose` against
`exists_prescribed_cutoff` under any context setting, and the file compiled on
the first attempt — the evidence that the reused lemmas really are parametric in
the cutoff radius.

(`research/I02/REVIEW_V2.md` issue 4 asks for "four hunks *of the proof body*".
Measured, that number is 3 at `diff -u`'s default context and 5 at
`--unified=0`; the 4 is `7 − 3` at file level, which counts the new trailing
declarations as proof body. The exact split above is recorded instead.)

## 3. Approaches tried and rejected

1. **Derive V2 from V1 by enlarging the packet.** Apply `Bindings.correction` to
   a packet `P'` with `P'.carrier = P.carrier ∪ K` (legal in principle:
   `PacketAPI.velocity_support`/`pressure_support` are upper bounds, so they
   survive enlargement), then transport `CorrectionAPI ν P'` back to
   `CorrectionAPI ν P`. Rejected without implementing: the transport is a
   73-field hand copy — the exact drift risk §1.2 rejects — the resulting record
   would be about a packet the caller did not supply, and `P.carrier_compact`
   would have to be re-derived. The direct construction is what the manuscript
   describes and is three proof-body hunks of edit.
2. **Reuse the version-one *record* and enlarge afterwards.** Structurally
   impossible: `θ` and `plateau` are fields of the record, so nothing outside can
   widen the plateau after the fact. This is the same observation the two reviews
   make about `θRadius` being existentially bound.
3. **`prescribed_subset_ball : K ⊆ Metric.ball 0 θRadius` as the new field.**
   Weaker than the plateau form and it loses `θ = 1` on `K`. Kept as a derived
   theorem in the binding instead, so the contract stays assertion-free (the
   version-one review valued "the contract asserts nothing": 10 `def`s, one
   `structure`, one `def … : Prop`, no `theorem`/`example`/`instance`; V2 is one
   `structure` and one `def … : Prop`).
4. **Dropping `carrier_subset_plateau` because `K` may already contain
   `P.carrier`.** Rejected. A caller may pass an unrelated `K`, and a new version
   never removes a specification field. `correctionStatement_of_v2` takes
   `K := P.carrier` and so exercises both fields on the same set.
5. **Reusing the id `I02.correction` with `version: 2`.** Rejected by the
   registry — see §4.

## 4. How the registry and the policy scripts treat V2

No script needed modification. Exactly what each one does:

* **`experiments/check_contracts.py`**
  * `assert len(ids) == len(set(ids)), 'Duplicate contract IDs'` — ids are the
    primary key, so a second entry cannot reuse `I02.correction`. The registered
    id is **`I02.correction_v2`**, with `"version": 2`. (Reusing the id would
    also have tripped `check_compatibility`'s
    `Changed stable contract I02.correction: version`.)
  * `assert f'/V{contract["version"]}/' in contract['specification']` — version
    `2` forces the path `verification/Contracts/V2/Correction.lean`. Creating the
    `V2/` directory is all that is required; nothing enumerates version
    directories.
  * The contract-import predicate accepts `Contracts.*`, so
    `Contracts.V2.Correction` may import `Contracts.V1.Correction`. The
    `axiom|sorry|admit` scan runs over every `Contracts.*` module, V2 included.
  * `assert registered_tests == {m for m in modules if m.startswith('Tests.')}`
    — a new `Tests/*.lean` **must** be registered, so the test file and the
    registry entry have to land together.
  * `check_compatibility` walks `git ls-tree <base> -- verification/Contracts`,
    i.e. only files that exist at the base ref. `Contracts/V2/Correction.lean` is
    new, so it is not frozen; `Contracts/V1/*.lean` and `Tests/Correction.lean`
    are byte-compared and unchanged. `--base-ref erenup/integration` reports
    `base_compatibility_checked: true`.
* **`experiments/test_contract_policy.py`** already contains
  `test_new_version_does_not_replace_old_version`, which registers a second entry
  with id `test.v2`, `version: 2` and a `Contracts/V2/` path alongside the
  original — this lane is the case that test was written for. 13 tests, all pass.
* **`experiments/test_contract_mutations.py`** does **not** read the registry:
  its four cases are hardcoded against `Contracts.V1.Thresholds` /
  `Bindings.Thresholds`. It runs `lake test` first, so the only effect of this
  lane is that the new test must be green. Nothing to change.
* **`experiments/check_work_queue.py`** asserts `set(item['contracts']) ⊆
  registered`, so `I02.correction_v2` was added to the `I02` work item and
  `tasks.py render` regenerated `collaboration/TASKS.md` and
  `collaboration/tasks/I02.md` (the only two files it changed).
* **`experiments/build_changed_lean.py`** needs no change; `targets()` maps the
  four new paths to `Bindings.CorrectionV2`, `Contracts.V2.Correction`,
  `NSFormalization.Section4.I02.Prescribed`, `Tests.CorrectionV2`.

Nothing in the toolchain would have to change to register a V3 the same way.

## 5. Note for R42 (lane 027)

`research/R42/ATTEMPTS.md` §5b item 1 is now available, and the premise §3
route 2 abandoned is provable.

* Take `K := P.carrier ∪ Prod.snd '' tsupport P.force`, the manuscript's `K_*`
  of `03-torus.tex:101-102`. Its compactness is
  `Bindings.isCompact_carrierStar P` (from `P.force_support.1.isCompact.image
  continuous_snd`), so `checkedCorrectionV2` applies with no new hypothesis.
* `Bindings.force_carrier_subset_ball` then gives
  `∀ z ∈ tsupport P.force, z.2 ∈ ball 0 A.θRadius` — exactly the `hfR` premise of
  `Source.insertion_at_scale`, and exactly the `force_carrier_subset` field that
  `research/I03/REVIEW_CONTRACT.md` §5.1 item 4 had to delete from `ScalingAPI`
  as undischargeable.
* Consequently `eps_space : ε · θRadius < r` places **all five** rescaled fields
  `w_ε, H_ε, U_ε, P_ε, F_ε` inside `B` on the whole version-two range. `R42` can
  take `ε₀ = S.ε₀` instead of `min S.ε₀ (r / (R_F + 1))`, and the field
  `eps_le_scaling` that recorded the shrink becomes an equality-or-deletion
  decision for an `R42` V2 — not something this lane changes.
* This lane does **not** touch `Contracts/V1/Scaling.lean`. An `I03` V2 carrying
  a `Contracts.V2.CorrectionAPI` is the natural follow-up; until it exists,
  `R42` can consume `checkedCorrectionV2` directly, since `ScalingAPI.correction`
  is reachable as `A.toCorrectionAPI` through `Bindings.correctionV1_of_v2`.

The reviewer's instruction that `R42` v1 must not be held for this still stands:
nothing here obliges lane 027 to re-open.

## 6. Not verified by this lane

* No claim that `K_*` is *optimal* or that the choice
  `P.carrier ∪ Prod.snd '' tsupport P.force` is forced; the contract accepts any
  compact `K`, including `∅`.
* The `I03`/`R42` migration itself. `Contracts/V1/Scaling.lean` still reads
  `correction : CorrectionAPI ν P` (version one), and its docstring at
  `:180-190` still records the deletion of `force_carrier_subset`. Updating that
  narrative belongs to an `I03` V2.
* Nothing about Theorem 4.2's lifespan or density conclusions, which are
  unchanged and still blocked on `D01` (see `research/R42/ATTEMPTS.md` §5).
* `make paper` / `make snapshot` were not run: no manuscript or copied-source
  file changed.

## 7. Gates

From the worktree root, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`.

| command | result |
|---|---|
| `make check` | exit 0. `Explicit axiom/admission tokens, all copied sources: 11`; `registered_contracts: 7`; `test_contract_policy` `Ran 13 tests … OK`; `check_work_queue` `30 work items: … consistent.` |
| `make test` | exit 0, seven `Contract …: checked; standard logical axioms only` lines, including `checkedCorrection` (V1, unchanged) and `checkedCorrectionV2`. |
| `make test-mutations` | exit 0. `implementation_refactor: accepted` / `admitted_proof: rejected as required` / `extra_axiom: rejected as required` / `weakened_hypothesis: rejected as required`. |
| `check_contracts.py --base-ref erenup/integration` | exit 0, `registered_contracts: 7`, **`base_compatibility_checked: true`**; closures 5 / 534 / 597 / **600** / 60 / 59 / 621 modules. |
| `build_changed_lean.py --base-ref erenup/integration --dry-run` | `Changed Lean modules: Bindings.CorrectionV2, Contracts.V2.Correction, NSFormalization.Section4.I02.Prescribed, Tests.CorrectionV2` — exactly the four, and `lake build` of them exits 0. (Before the lane was committed the same four came from applying `targets()` to the working-tree paths.) |
| axiom audit | scratch file importing `Tests.CorrectionV2`: `checkedCorrectionV2`, `correctionV2`, `correctionV1_of_v2`, `prescribed_subset_ball`, `correctionStatement_of_v2`, `isCompact_carrierStar`,
`force_carrier_subset_ball`, `exists_prescribed_cutoff` — each `depends on axioms: [propext, Classical.choice, Quot.sound]`. |
| hygiene | `grep -nE 'sorry\|axiom\|admit\|native_decide\|unsafe'` over the four new files: zero hits, comments included. |
