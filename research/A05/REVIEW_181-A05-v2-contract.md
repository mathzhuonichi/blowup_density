ACCEPT-WITH-NOTES

## 1. What the lane claims

Reviewed commit `71898f7` on `erenup/181-A05-v2-contract` against
`origin/erenup/integration`.  The branch adds a 29th registered contract,
`A05.gradient_l6_v2`, whose checked implementation fixes one explicit positive
constant and supplies the order-half velocity `L³` estimate.  The registry says
`parent_task: A05`, `version: 2`, and names the V2 contract/binding/test modules
at `verification/contracts.json:313-320`.

The required Spec field is exactly (`research/A05/Spec.lean:366-368`):

```lean
  velocityCriticalL3 :
    ∀ v : SpatialField, MemHInfty v →
      eLpNorm v 3 volume ≤ ENNReal.ofReal (C (1 / 2)) * dotHomogeneousENorm (1 / 2) v
```

The registered V2 field is exactly (`verification/Contracts/V2/GradientL6.lean:46-48`):

```lean
  velocityCriticalL3 :
    ∀ v : SpatialField, MemHInfty v →
      eLpNorm v 3 volume ≤ ENNReal.ofReal (C (1 / 2)) * dotHomogeneousENorm (1 / 2) v
```

`diff -u` on those three-line slices exits 0.  The norm name in the contract is
not a restatement: the file imports `Contracts.V1.HomogeneousNorm` at
`verification/Contracts/V2/GradientL6.lean:2` and opens its registered
`dotHomogeneousENorm` at `:35`.  The V2 record structurally extends the frozen
V1 API at `:41-42`.

The paper says that the Euclidean inequality initially holds for Schwartz
functions and extends to the homogeneous completion
(`paper/sections/appendix-b-embeddings.tex:11-24`), then states
`‖v‖₃ ≤ C‖v‖_{Ḣ¹⁄²}` whenever that norm is finite (`:26-37`).  Its two uses are
the critical estimate `‖u‖₃ ≤ Cy` at `paper/sections/04-whole-space.tex:91-99`
and the H¹ absorption at `:169-173`.  The registered field is therefore the
downstream `MemHInfty` specialization requested by the Spec, not the paper's
full minimal-domain completion theorem.

Finding N2 (documentation, non-blocking): `MemHInfty` is stronger regularity
than the paper's minimal finite homogeneous-completion domain.  It is exactly
the Spec and source hypothesis, and the registry scope already names it, but
`research/A05/REPORT_181.md:5-16` should call the result the **`MemHInfty`
specialization** of Lemma B.1 rather than the unqualified whole lemma.

## 2. What is in Lean

### Statement, hypotheses, constant, and bridges

The source theorem is
`NSFormalization.Section4.A05.velocityCriticalL3` at
`formalization/NSFormalization/Section4/A05/CriticalL3.lean:394-409`.  Its only
field hypothesis is `A02.MemHInfty`; its conclusion has exponent `3`, positive
constant `criticalL3Const`, and the datum-form order-half homogeneous norm
(`:394-397`).  The registered contract has the same hypothesis: the binding's
bridge

```lean
Contracts.V1.Data.MemHInfty v = A02.MemHInfty v := rfl
```

is at `verification/Bindings/GradientL6V2.lean:31-33`.  Thus nothing is weakened
relative to the source theorem, and there is no added solenoidality, solution,
time-interval, or finiteness premise.  The source proof really uses `hz` in the
finite-datum branch through `u7_vector_eLpNorm_le_of_datum`
(`CriticalL3.lean:379-388,398-402`); it is not an unused binder.

The constant is explicit, not existential.  The implementation defines

```lean
criticalL3Const = 3 * scalarCriticalConst (1 / 2)
```

at `CriticalL3.lean:300-306` and proves it positive there.  The checked binding
selects the constant family `fun _ => criticalL3Const` before quantifying `v`
(`verification/Bindings/GradientL6V2.lean:54-57`) and exports positivity for
every argument at `:68-71`.  The actual record update is
`{ gradientL6 with velocityCriticalL3 := ... }` at `:60-66`; the V1 projection
is definitionally unchanged by `gradientL6_of_v2 := rfl` at `:73-75`.

The implementation-to-contract norm chain is honest.  The A05-to-D01 link is
an explicit `rfl` theorem at `verification/Bindings/GradientL6V2.lean:38-40`,
and the existing D01-to-contract bridge is `rfl` at
`verification/Bindings/HomogeneousNorm.lean:12-14`.  The composite is recorded
at `verification/Bindings/GradientL6V2.lean:44-52`.  The independent probe proves
all three equalities directly by bare `rfl`, without `simp` or unfolding
(`research/A05/probes/rev181_fidelity_nonvacuity.lean:15-29`), and elaborates
with zero output.

There is no `.toReal`, empty interval, or hidden post-datum choice in the field.
The totalized source proof does use the honest empty-infimum `⊤` branch when no
half-order datum exists (`CriticalL3.lean:398-409`).  It is not globally
vacuous: the reviewer probe constructs the nonzero compact bump `zB`, proves
`MemHInfty`, supplies a half-order homogeneous datum, proves both the registered
norm and the complete right side are not `⊤`, and applies the checked V2 field
(`research/A05/probes/rev181_fidelity_nonvacuity.lean:31-93`).

The public test fixes the checked concrete record and runs the axiom checker at
`verification/Tests/GradientL6V2.lean:18-22`; its conformance example repeats
the field at `:27-32`.  The permanent axiom file names eight declarations at
`research/A05/axioms_v2_contract.lean:26-33`, all of which print exactly
`[propext, Classical.choice, Quot.sound]`.

### Freeze, registry, and hygiene

The exact freeze comparison

```text
git diff origin/erenup/integration -- verification/Contracts/V1 verification/Tests/GradientL6.lean verification/Bindings/GradientL6.lean
```

has no output and exits 0.  The merge-base diff contains no modified existing
Lean module: it adds only the three new V2 modules and the research axiom file;
the other changes are the required registry/task/record updates.  The registry
diff is exactly:

```text
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```

The new entry is at `verification/contracts.json:312-321`; its scope honestly
names the explicit constant, `MemHInfty`, the registered norm, and the excluded
fields.  JSON parsing passes, and a literal `\\u[0-9a-fA-F]{4}` scan finds no
Unicode escapes.  The contract imports only two `Contracts.*` modules
(`verification/Contracts/V2/GradientL6.lean:1-2`).  There is no Lean-code use of
`sorry`, `admit`, `axiom`, `native_decide`, or `maxHeartbeats` in the added lane
Lean files.  The only textual `axiom` matches are in comments saying
"transitive-axiom".

### Negative check and mutation-suite finding

The substantive reviewer mutation changes the main target from `L³` to `L⁴`
(`research/A05/probes/rev181_mutation.lean:10-18`).  Lean rejects it because the
checked theorem has `eLpNorm v 3` where the mutation requires `eLpNorm v 4`; no
argument was merely dropped.

Finding N1 (test coverage): `make test-mutations` passes, but its named
`extra_axiom` and `weakened_hypothesis` cases do **not** target this V2 contract.
The harness imports only `Contracts.V1.Thresholds` and `Bindings.Thresholds`
(`experiments/test_contract_mutations.py:10-15`); both cases are written solely
against `ThresholdAPI`/`Bindings.thresholds` (`:27-39`).  This does not affect
the successful V2 axiom audit or reviewer mutation, but it fails the lead's
lane-specific mutation-coverage checkpoint.

## 3. Gaps

The lane's scope exclusions are honest.  Whole-tree `grep -rn` searches under
`formalization/NSFormalization/Section4` found no declarations named
`embeddingPair`, `C_pos`, `criticalRepresentative`, `homogeneousLeSobolev`,
`dotThreeHalvesLeGradientSobolev`, `derivativeCriticalL3`, or
`besselCriticalL3`.  The only `homogeneousLeSobolev` hit is the explicit
residual comment in `formalization/NSFormalization/Section4/A05/CriticalL3.lean:190`.
Their requested draft statements remain at `research/A05/Spec.lean:203,
268-291,355-359,384-408`.

This search does find the claimed completed result and constant only:
`velocityCriticalL3` at `CriticalL3.lean:394` and `criticalL3Const`/
`criticalL3Const_pos` at `:302-305`.  R43 and R44 have partial arithmetic,
bootstrap, and endpoint lemmas, but explicitly say the PDE energy inequalities
remain outside those modules (`formalization/NSFormalization/Section4/R43/Pieces.lean:38-43`;
`formalization/NSFormalization/Section4/R44/Pieces.lean:5-21`).  A registry search
finds no `R43` or `R44` contract entry, so the report's narrower claim that their
PDE conclusions remain **unregistered** is correct; it does not falsely claim
that the tree contains no partial R43/R44 work.

Exact fixes for the two notes:

1. N1: add V2-specific `extra_axiom` and `weakened_hypothesis` mutation cases that import `Tests.GradientL6V2` and exercise `checkedGradientL6V2`, instead of reporting only the V1 Thresholds cases as coverage for this lane.
2. N2: change the first claim in `research/A05/REPORT_181.md` to "registers the `MemHInfty` specialization of Lemma B.1's order-half velocity embedding."

No mathematical statement or binding change is required.

## 4. Commands and results

All Lake commands were run from `verification/` after sourcing
`scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`, one at a time.

### Build and direct elaboration

`lake build Tests.GradientL6V2` — exit 0.  Lake replayed pre-existing warnings
from upstream modules; the lane target's exact terminal lines were:

```text
ℹ [9931/9931] Replayed Tests.GradientL6V2
info: Tests/GradientL6V2.lean:22:0: Contract BlowupDensity.Tests.checkedGradientL6V2: checked; standard logical axioms only
Build completed successfully (9931 jobs).
```

`lake env lean Contracts/V2/GradientL6.lean` — exit 0, output bytes 0.

`lake env lean Bindings/GradientL6V2.lean` — exit 0, output bytes 0.

`lake env lean Tests/GradientL6V2.lean` — exit 0:

```text
Contract BlowupDensity.Tests.checkedGradientL6V2: checked; standard logical axioms only
```

`lake env lean ../research/A05/axioms_v2_contract.lean` — exit 0, eight
declarations:

```text
'NSFormalization.Section4.A05.velocityCriticalL3' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.gradientL6V2_memHInfty_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.gradientL6V2_A05_dotHomogeneousENorm_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.gradientL6V2_dotHomogeneousENorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.gradientL6V2Constant_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.gradientL6V2' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.gradientL6_of_v2' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedGradientL6V2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Required gates

`make check` — exit 0.  The exact relevant terminal results were:

```text
  "registered_contracts": 29,
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.053s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

The same command also reports the pre-existing repository-wide informational
value `"source_hashes_match": false`; it is non-fatal, and this lane changes no
formalization source file.

`scripts/gates.sh` — exit 0.  The exact V2 line and final gate sections were:

```text
== make test
info: Tests/GradientL6V2.lean:22:0: Contract BlowupDensity.Tests.checkedGradientL6V2: checked; standard logical axioms only
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
```

The full `make test` output checked all registered tests and included the V2
line quoted above.  The limitation of the two generic mutation cases is finding
N1, not a gate-process failure.

`python3 experiments/check_contracts.py --base-ref origin/erenup/integration`
— exit 0.  The JSON begins and ends with:

```text
{
  "registered_contracts": 29,
  "closures": {
    ...
  },
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

The omitted middle is only the 289659-byte module-closure listing; no diagnostic
or failure line occurred.

### Reviewer probes and repository checks

`lake env lean ../research/A05/probes/rev181_fidelity_nonvacuity.lean` — exit 0,
output bytes 0.

`lake env lean ../research/A05/probes/rev181_mutation.lean` — expected exit 1:

```text
../research/A05/probes/rev181_mutation.lean:18:2: error: Type mismatch
  BlowupDensity.Tests.checkedGradientL6V2.velocityCriticalL3
has type
  ∀ (v : SpatialField),
    MemHInfty v →
      eLpNorm v 3 volume ≤
        ENNReal.ofReal (BlowupDensity.Bindings.gradientL6V2Constant (1 / 2)) * dotHomogeneousENorm (1 / 2) v
but is expected to have type
  ∀ (v : SpatialField),
    MemHInfty v →
      eLpNorm v 4 volume ≤
        ENNReal.ofReal (BlowupDensity.Bindings.gradientL6V2Constant (1 / 2)) * dotHomogeneousENorm (1 / 2) v
```

`git diff --name-only origin/erenup/integration...HEAD` — exit 0:

```text
collaboration/TASKS.md
collaboration/tasks/A05.md
collaboration/work_items.json
research/A05/ATTEMPTS_V2_CONTRACT.md
research/A05/COMPARISON.md
research/A05/REPORT_181.md
research/A05/axioms_v2_contract.lean
verification/Bindings/GradientL6V2.lean
verification/Contracts/V2/GradientL6.lean
verification/Tests/GradientL6V2.lean
verification/contracts.json
```

`git diff --check origin/erenup/integration...HEAD` — exit 0, output bytes 0.

`git diff --stat verification/contracts.json` — exit 0, output bytes 0 because
the worker change is committed.  The base comparison gives exactly:

```text
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)
```

The frozen-path diff, Unicode-escape scan, forbidden-code-token scan, and
`maxHeartbeats` scan all have zero findings.  The whole-tree missing-declaration
search has the results recorded in §3.
