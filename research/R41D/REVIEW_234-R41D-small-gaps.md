ACCEPT-WITH-NOTES

## 1. What the lane claims

Reviewed HEAD `03fdcda3c2720e49cc28364a2cace18b940b9c9d` against the
`origin/erenup/integration` snapshot
`417c0cc76354503ee78930bafda89553aa865339`, read-only except for this required
review and the permitted `research/R41D/probes/rev234_*.lean` probe.

`research/R41D/REPORT_234.md:5-12` claims all four requested facts without
weakening:

- G2, rapid forces lie in the ambient class;
- G3, adding a compactly supported correction preserves rapid decay;
- G4, Schwartz-solenoidal initial data lie in the ambient initial class; and
- G5, the zero physical force has zero Sobolev enorm, strengthened from
  `q = 1 or q = 2` to every `q`, together with `g-g=0`.

This is the mathematics requested by the paper.  The ambient classes are
`X_R` and `F_R` at `paper/sections/02-preliminaries.tex:12-25`; the compact and
rapid subclasses and `S_sigma` are at
`paper/sections/04-whole-space.tex:185-192`; and the corollary explicitly says
that Theorem 4.1 remains valid in both subclasses and for fixed
`a in S_sigma` at `paper/sections/04-whole-space.tex:194-198`.

There is one honesty correction to the report's scope history:
`research/R41D/REPORT_234.md:14` and
`research/R41D/ATTEMPTS_SMALL_GAPS.md:12` say that no later lane had already
proved any of G2--G5, but the final reviewed tree contains the earlier
contract-vocabulary G5 theorem
`BlowupDensity.Bindings.density_forceSobolevENorm_zero` at
`verification/Bindings/DensityFromInsertion.lean:16-27`.  This does not make
the new local theorem false or unusable, but the records must distinguish G5
from the genuinely absent G2--G4 results.

## 2. What is in Lean

1. **G2 statement fidelity: pass.**
   `formalization/NSFormalization/Section4/R41/ClassFacts.lean:1068-1071` is
   exactly `MemForceRapid f -> D01.MemForceR f`; `:1074-1076` is the equivalent
   set inclusion.  There is no additional finiteness, positivity, interval, or
   `.toReal` hypothesis.  The source and contract predicates agree by the
   `rfl` bridges at `research/R41D/axioms_class_facts.lean:20-24`.  The ambient
   target really contains a smooth datum path at every order and both time
   `L1` and `L2` conditions (`verification/Contracts/V1/Data.lean:544-550`), so
   this is not a weakened pointwise-decay substitute.

2. **G3 statement fidelity: pass.**
   `formalization/NSFormalization/Section4/R41/ClassFacts.lean:1163-1169` has
   the requested explicit binder order `g f`,
   assumes exactly `MemForceRapid g` and
   `D01.MemForceCompact (fun z => f z - g z)`, and concludes
   `MemForceRapid f`.  Its two ingredients are the honest compact-to-rapid
   theorem at `:1107-1127` and rapid addition at `:1132-1160`; the final rewrite
   is `g + (f-g) = f`.  The compact predicate is the globally smooth,
   positive-time compact-support predicate from
   `verification/Contracts/V1/Data.lean:555-563`, not an empty support
   assumption.

3. **G4 statement fidelity: pass.**
   `formalization/NSFormalization/Section4/R41/ClassFacts.lean:1190-1197` is exactly
   `initialClassSchwartz subset A02.initialClassR`.  The source class at
   `ClassFacts.lean:48-49` is definitionally the contract class
   (`axioms_class_facts.lean:22`), whose definition is the existence of a
   vector-valued Schwartz representative plus the same solenoidal condition
   (`verification/Contracts/V1/Data.lean:509-514`).  The cited constructor
   theorem really supplies a datum for every real order
   (`formalization/NSFormalization/Section4/B01/Spatial.lean:97-109`).

4. **G5 statement fidelity: pass.**
   `formalization/NSFormalization/Section4/R41/ClassFacts.lean:1207-1219`
   proves the stronger every-`q`, every-`s` zero
   identity with an explicit zero measurable path in the defining infimum;
   `:1222-1224` has the brief's exact `q = 1 or q = 2` interface and binder
   order, and `:1227-1229` is the pointwise subtraction identity.  The named
   `_hq` is intentionally unused and isolated because the preceding theorem is
   stronger; the report states this strengthening explicitly.  The norm being
   proved is definitionally the measurable-path infimum at
   `verification/Contracts/V1/Data.lean:225-228`, so there is no
   `top.toReal = 0` loophole.

5. **Proof citations and conformance: pass.**  The finite-jet estimate cited in
   the attempts exists with the stated square-norm bound at
   `formalization/NSFormalization/Section4/C01/PressureJetPath.lean:146-159`,
   and the compact-support decay lemma exists with a positive constant and
   full future-time bound at
   `vendor/NavierStokesAndEuler/NavierStokes/CompactSpatialForceDecay.lean:43-78`.
   All seven contract-facing theorem statements are present at
   `research/R41D/axioms_class_facts.lean:28-71`, and the seven local plus seven
   contract results are audited at `:73-87`.

6. **Non-vacuity: pass, with an audit-note fix.**  The delivered audit gives a
   rapid zero force (`axioms_class_facts.lean:92-95`), its ambient membership
   (`:97-101`), a Schwartz zero initial datum (`:103-109`), and the zero norm
   (`:111-112`).  It does not actually instantiate G3 despite the comment at
   `:89-90`.  The reviewer probe closes that omission: rapid zero and compact
   zero difference are constructed at
   `research/R41D/probes/rev234_zero_constant.lean:10-27`, then supplied
   together to G3 at `:29-32`.  No nonzero closed rapid-force witness was found
   by the requested repository searches, so the brief expressly permits zero.

7. **Trust and hygiene: pass.**  Every printed axiom list is exactly
   `[propext, Classical.choice, Quot.sound]`.  The forbidden-token and
   `maxHeartbeats` searches over the new proof and audit files have no matches;
   there is no local heartbeat override.  `git diff --diff-filter=M -- '*.lean'`
   is empty: the only changed Lean module is the new `ClassFacts.lean`.
   `git diff --check` is clean.

## 3. Gaps, absence claims, and negative check

There is no mathematical gap and no reproducing build error in the delivered
theorems.  The two notes are exact record/audit fixes:

1. **N1 (records, minor):** replace the blanket no-pre-existing-proof claims at
   `REPORT_234.md:14` and `ATTEMPTS_SMALL_GAPS.md:12` with: “No pre-existing
   Section4 proof of G2--G4 was found; G5 already exists in contract vocabulary
   as `Bindings.density_forceSobolevENorm_zero`
   (`verification/Bindings/DensityFromInsertion.lean:16-27`), while this lane
   supplies its local-vocabulary copy.”
2. **N2 (audit wording, minor):** either change
   `axioms_class_facts.lean:89-90` to say that the existing examples instantiate
   G2, G4, and G5, or add the zero compact-difference G3 example demonstrated
   by `rev234_zero_constant.lean:10-32`.

The mandated whole-`Section4` searches were run before accepting any absence
claim:

```sh
grep -rnE 'MemForceRapid|forceClassRapid' formalization/NSFormalization/Section4
grep -rnE 'memForceRapid_of_compact_difference|initialClassSchwartz_subset_initialClassR|forceSobolevENorm_zero(_of_one_or_two)?' formalization/NSFormalization/Section4
```

Every hit is in the new `formalization/NSFormalization/Section4/R41/ClassFacts.lean`;
there is no sibling Section4 implementation of G2--G5.  The wider required
search over `verification/Bindings` is what finds the pre-existing G5 theorem,
so the report's global G2--G5 absence sentence cannot stand unchanged.

**Substantive mutation:**
`research/R41D/probes/rev234_zero_constant.lean:38-40` changes G5's result from
zero to one without dropping any argument.  The probe first proves the mutated
statement is false at `:34-36`; applying the original theorem then fails with
the expected changed-constant mismatch:

```text
../research/R41D/probes/rev234_zero_constant.lean:40:2: error: Type mismatch
  forceSobolevENorm_zero_of_one_or_two 1 (Or.inl rfl) 0
has type
  D01.forceSobolevENorm 1 0 0 = 0
but is expected to have type
  D01.forceSobolevENorm 1 0 0 = 1
```

Exit 1.  The preceding G3 non-vacuity declarations elaborate, so this is the
probe's only error.

## 4. Commands and results

Read `CLAUDE.md`, `.claude/skills/lane-review/SKILL.md`, the top 40 lines of
`logs/LESSONS.md`, the brief, worker report, attempts/comparison records, the
paper passages, contract definitions, and cited tree lemmas.  Every Lean shell
sourced `scripts/lean-env.sh`, used `LEAN_NUM_THREADS=6`, and invoked Lake only
from `verification/`.  Long gate output is reported by exact head/tail excerpts
with omissions marked, as required by the repository lesson against pasting
tens of thousands of inventory lines.

| Command | Result |
|---|---|
| `lake build NSFormalization.Section4.R41.ClassFacts` | exit 0; 298 lines / 17,132 bytes; only replayed pre-existing dependency diagnostics, no `ClassFacts.lean` diagnostic |
| `lake env lean ../formalization/NSFormalization/Section4/R41/ClassFacts.lean` | exit 0; exactly 0 lines / 0 bytes |
| `lake env lean ../research/R41D/axioms_class_facts.lean` | exit 0; fourteen standard axiom reports, exact output below |
| `make check` | exit 0; 33,680 lines / 1,385,378 bytes; exact tail below |
| `lake env lean ../research/R41D/probes/rev234_zero_constant.lean` | expected exit 1; exact sole error above |
| forbidden-token / `maxHeartbeats` `rg` | exit 1 for each; no matches |
| `git diff --check origin/erenup/integration...HEAD` | exit 0; no output |

Exact audit output:

```text
'NSFormalization.Section4.R41.memForceR_of_memForceRapid' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.forceClassRapid_subset_forceClassR' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R41.memForceRapid_of_compact_difference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R41.initialClassSchwartz_subset_initialClassR' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R41.forceSobolevENorm_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R41.forceSobolevENorm_zero_of_one_or_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R41.sub_self_force' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassFactsConformance.contract_memForceR_of_memForceRapid' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassFactsConformance.contract_forceClassRapid_subset_forceClassR' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ClassFactsConformance.contract_memForceRapid_of_compact_difference' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ClassFactsConformance.contract_initialClassSchwartz_subset_initialClassR' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ClassFactsConformance.contract_forceSobolevENorm_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'ClassFactsConformance.contract_forceSobolevENorm_zero_of_one_or_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ClassFactsConformance.contract_sub_self_force' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Build output (exact first/last excerpts):

```text
⚠ [8777/9489] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'

Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:23:37: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [h]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/FiniteHilbertBochner.lean:39:23: This simp argument is unused:
  PiLp.single_apply

Hint: Omit it from the simp argument list.
  [apply] simp [insert, coord]
[... middle omitted ...]
⚠ [10515/10548] Replayed NSFormalization.Source.FractionalRealization
warning: NSFormalization/Source/FractionalRealization.lean:60:2: Try this:
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: NSFormalization/Source/FractionalRealization.lean:83:2: Try this:
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
warning: NSFormalization/Source/FractionalRealization.lean:104:2: Try this:
  letI̵

The goal is a proposition, so `let` is preferred over `letI`.
The difference between `let` and `letI` is that `letI` inlines the value.
But this is not relevant for proofs because of proof irrelevance.

Note: This linter can be disabled with `set_option linter.style.haveILetI false`
Build completed successfully (10548 jobs).
```

Exact `make check` tail:

```text
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.042s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

The earlier inventory contains `source_hashes_match: false` and the known copied
`Paper1/BoundaryCorollary.lean` `sorry`; `make check` exits 0, neither file is in
this lane's diff/import audit, and all fourteen delivered results have only the
three standard axioms.

Exact committed diff:

```text
A	formalization/NSFormalization/Section4/R41/ClassFacts.lean
A	research/R41D/ATTEMPTS_SMALL_GAPS.md
M	research/R41D/COMPARISON.md
A	research/R41D/REPORT_234.md
A	research/R41D/axioms_class_facts.lean
```

`git diff --name-only origin/erenup/integration...HEAD -- verification/`
produced exactly zero output, so the brief's conditional
`scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration` gates do not apply.
The unconditional `make check` did run the ordinary `check_contracts.py` and
passed as shown above.
