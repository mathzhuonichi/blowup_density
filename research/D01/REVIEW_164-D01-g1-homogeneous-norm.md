REJECT

# Review of lane 164-D01-g1-homogeneous-norm

## 1. What the lane claims

The report claims one promoted definition and five consumer theorems.  Every
claimed declaration exists with the reported statement:

* `dotHomogeneousENorm` is exactly the infimum over
  `{G : RealVectorSobolev s // IsHomogeneousSliceDatum s z G}` at
  `formalization/NSFormalization/Section4/D01/HomogeneousNorm.lean:26-27`.
* The long and short datum upper-bound spellings are at
  `HomogeneousNorm.lean:30-40`.
* The zero theorem is at `HomogeneousNorm.lean:43-50`.
* The datum-witness and existential finiteness theorems are at
  `HomogeneousNorm.lean:53-63`.

Statement fidelity passes.  The definition is character-for-character equal to
the two independent spec-local definitions at `research/A05/Spec.lean:131-132`
and `research/R43/Spec.lean:142-143` (an exact `diff -u` produced no output).
The R44 reconciliation is also honest: `research/R44/Spec.lean:47-54` explicitly
says that its zero datum means there is no spatial homogeneous norm, while
`research/R44/Spec.lean:56-67` instead uses the inhomogeneous force norm.

The mathematical citations check out.  Proposition 4.3 uses
`‖a‖_{Ḣ^{1/2}}` at `paper/sections/04-whole-space.tex:82-88`; the critical
embedding is displayed at `paper/sections/appendix-b-embeddings.tex:26-32`.
The two cited tree estimates consume the norm of the fractional datum at
`formalization/NSFormalization/Paper1/SchwartzCriticalEmbedding.lean:57-61`
and `:171-175`.  The rejected pointwise alternative really is an
`angularFourier` lower integral at `verification/Contracts/V1/Data.lean:395-413`,
with the `L¹ ∩ L²` caveat at `:404-409`; its `3/2` and `1/2` abbreviations
are at `:415-428`.

There is no `.toReal`, interval, positivity guard, or unused binder in the new
statements.  Each named hypothesis is the actual datum witness used by the
infimum or finiteness proof (`HomogeneousNorm.lean:30-40,53-63`).  The zero
theorem constructs an actual zero distribution and datum rather than using an
empty infimum (`HomogeneousNorm.lean:43-50`).  The premise-free reviewer probe
constructs the witness explicitly at
`research/D01/probes/rev164_nonvacuity.lean:12-17` and compiles with zero output.

The report is also accurate that the contract definition and implementation
definition are definitionally equal: the restatement is at
`verification/Contracts/V1/HomogeneousNorm.lean:31-32` and the `rfl` bridge at
`verification/Bindings/HomogeneousNorm.lean:12-14`.

## 2. What is in Lean

The implementation is mathematically sound and provides exactly the basic G1
interface in `formalization/NSFormalization/Section4/D01/HomogeneousNorm.lean`.
The contract test checks the bridge at
`verification/Tests/HomogeneousNorm.lean:12-17`.  The registry adds
`D01.homogeneous_norm`, version 1, at
`verification/contracts.json:291-299`.

However, the actual contract declaration is in
`verification/Contracts/V1/HomogeneousNorm.lean:1-34`, not the brief-mandated
`verification/Contracts/V2/HomogeneousNorm.lean`.  The binding, test, axiom
audit, and registry consistently point to the V1 namespace/path
(`verification/Bindings/HomogeneousNorm.lean:1,12-14`,
`verification/Tests/HomogeneousNorm.lean:1,13-15`,
`research/D01/axioms_g1.lean:1,44`, and
`verification/contracts.json:294`).  This is not an accidental report omission:
the report expressly claims the V1 placement at
`research/D01/REPORT_164.md:44-55`.

That placement is checker-legal for a new component—the guard distinguishes a
lane's new V1 file from an already-merged frozen one at
`.claude/hooks/guard.py:46-56`—but it does not satisfy this lane's explicit
deliverable.  The repository's upstream review guidance also calls this a
`Contracts/V2/Data`-style addition and notes that V1 is frozen at
`research/R43/REVIEW_SPLIT.md:113-123`; the P4 handoff routes the addition away
from frozen `Contracts/V1/Data.lean` at `collaboration/HANDOFF.md:79-83`.
Therefore the lane is not accepted as delivered even though every Lean gate is
green.

Hygiene otherwise passes.  Relative to `origin/erenup/integration`, the only
formalization module is the new module; no existing formalization module or
existing test was modified.  A source-only scan of the new Lean files found no
`sorry`, `admit`, `axiom`, `native_decide`, or `maxHeartbeats`, and
`git diff --check` emitted nothing.  All nine declarations audited in
`research/D01/axioms_g1.lean:35-46` print exactly
`[propext, Classical.choice, Quot.sound]`.

The substantive negative mutation changes the zero theorem's right side from
`0` to `1`, without dropping an argument
(`research/D01/probes/rev164_mutate_zero_to_one.lean:12-20`).  The original
construction then fails exactly at the reverse inequality `1 ≤
dotHomogeneousENorm s 0`.  The companion proof establishes that the mutated
statement is false at `research/D01/probes/rev164_nonvacuity.lean:19-22`.

## 3. Gaps

### Finding 1 (blocking): contract version/path does not match the brief

The lane brief requires the restatement in
`verification/Contracts/V2/Data.lean` or a new
`verification/Contracts/V2/HomogeneousNorm.lean`.  The latter file is absent,
while the declaration is under V1 (`verification/Contracts/V1/HomogeneousNorm.lean:19-32`).
The reproducer is:

```text
$ sed -n '1,40p' verification/Contracts/V2/HomogeneousNorm.lean
sed: can't read verification/Contracts/V2/HomogeneousNorm.lean: No such file or directory
<exit 2>
```

Required fix: restore the mathematical declaration under
`Contracts.V2.HomogeneousNorm`; if the registry's version-path invariant still
requires a V1 specification path, make `Contracts/V1/HomogeneousNorm.lean` an
import-only, declaration-free shim.  Then update the binding, test, axiom audit,
and registry scope/namespace references to the V2 declaration.  This is a
coordinated multi-file contract change, so it is larger than an
`ACCEPT-WITH-NOTES` one-line correction.

### Accepted declared mathematical gaps

The optional comparison was not claimed as proved.  Its actual draft shape has
`0 ≤ a`, `a < 3/2`, and `MemHInfty z` at
`research/A05/Spec.lean:260-271`.  The tree's own gap record explains the
missing general homogeneous multiplier and realization identity at
`formalization/NSFormalization/Section4/D01/HalfOrder.lean:40-54`.

As required, the whole `formalization/NSFormalization/Section4` tree was checked
with `grep -rn` before accepting that gap.  No named spatial/path comparison or
Sobolev-datum-to-homogeneous-datum conversion was found.  The only constructor
hits are the disclosed Schwartz/compact routes, including
`formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean:471-490`
and `:513-528`, plus B02's specialized `L¹ ∩ L²` machinery.  Thus the report's
decision not to invent the comparison is honest.  It does not affect G1's
mathematical definition, but the A05 comparison and the time-integrated G2/G3
work remain open exactly as reported.

No other statement-fidelity, build, axiom, hygiene, or non-vacuity defect was
found.

## 4. Commands and results

All shells sourced `scripts/lean-env.sh`.  Every `lake` invocation ran from
`verification/` with `LEAN_NUM_THREADS=6`.

### Module build

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.D01.HomogeneousNorm
⚠ [8778/8816] Replayed NSFormalization.Source.FiniteHilbertBochner
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

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
⚠ [8800/8816] Replayed NSFormalization.Source.RealSobolev
warning: NSFormalization/Source/RealSobolev.lean:90:30: This simp argument is unused:
  Complex.smul_re

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_im]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/RealSobolev.lean:90:47: This simp argument is unused:
  Complex.smul_im

Hint: Omit it from the simp argument list.
  [apply] simp [Complex.smul_re]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
warning: NSFormalization/Source/RealSobolev.lean:90:64: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [8804/8816] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).
⚠ [8811/8816] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [8814/8816] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (8816 jobs).
<exit 0>
```

All warnings are replayed from imported modules; direct Lean checking confirms
that the new module itself is silent:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/D01/HomogeneousNorm.lean
<0 output; exit 0>
```

### Axiom audit

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/D01/axioms_g1.lean
'NSFormalization.Section4.D01.dotHomogeneousENorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.D01.dotHomogeneousENorm_le_of_isHomogeneousSlice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.D01.le_of_isHomogeneousSlice' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.D01.dotHomogeneousENorm_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.D01.dotHomogeneousENorm_ne_top_of_isHomogeneousSlice' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.D01.dotHomogeneousENorm_ne_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Contracts.V1.HomogeneousNorm.dotHomogeneousENorm' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.dotHomogeneousENorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedHomogeneousNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
<exit 0>
```

### `make check`, gates, and contract compatibility

The full `make check` and contract-checker stdout is a 25,000-line dependency
closure JSON; it was not suppressed during execution.  These are the exact
decisive lines and exit statuses:

```text
$ LEAN_NUM_THREADS=6 make check
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 473,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tokens_in_copied_umbrella_closure": [
    {
      "module": "NSFormalization.Paper1.BoundaryCorollary",
      "path": "formalization/NSFormalization/Paper1/BoundaryCorollary.lean",
      "line": 90,
      "token": "sorry"
    }
  ],
  "tracked_cache_free": true,
  "source_hashes_match": false
}
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
  "registered_contracts": 27,
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.043s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
<exit 0>
```

The copied-source token shown here is the known, unreachable
`Paper1/BoundaryCorollary.lean:90`; it is not in this lane's changed module or
registered closure.

```text
$ LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section4.D01.HomogeneousNorm
== make check
30 work items: ownership, contract registration and task cards consistent.
== lake build NSFormalization.Section4.D01.HomogeneousNorm
Build completed successfully (8816 jobs).
== make test
info: Tests/HomogeneousNorm.lean:17:0: Contract BlowupDensity.Tests.checkedHomogeneousNorm: checked; standard logical axioms only
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
<exit 0>
```

The gate also printed the same imported-module warnings shown in the standalone
build and successful axiom lines for all 27 registered tests; none was an error.

```text
$ LEAN_NUM_THREADS=6 python3 experiments/check_contracts.py --base-ref origin/erenup/integration
{
  "registered_contracts": 27,
  ... dependency closures omitted here only from this report ...
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
<exit 0>
```

### Whole-tree negative search

```text
$ grep -rn -E 'dotHomogeneousENorm.*sobolevENorm|homogeneousLeSobolev|forceHomogeneousENorm.*forceSobolevENorm|forceSobolevENorm.*forceHomogeneousENorm' formalization/NSFormalization/Section4
<0 output; exit 1>

$ grep -rn -E 'IsSobolevDatum.*IsHomogeneousSliceDatum|IsHomogeneousSliceDatum.*IsSobolevDatum|IsSobolevPath.*IsHomogeneousPath|IsHomogeneousPath.*IsSobolevPath' formalization/NSFormalization/Section4
formalization/NSFormalization/Section4/B02/SeparatedAssembly.lean:16:`IsHomogeneousPath s` / `IsHomogeneousSliceDatum s` replace `IsSobolevPath s` / `IsSobolevDatum s`.
<exit 0; docstring only>
```

The multiplier-vocabulary grep returned only the disclosed specialized
constructors and the gap record: B02 `LebesgueDatum.lean:30,184,260`, B02
`SeparatedAssembly.lean:68,85`, D01 `HomogeneousWitness.lean:63,161,274`, D01
`HalfOrder.lean:45,48`, and A01 `CarrierBridge.lean:56`.

### Hygiene and changed-file audit

```text
$ git diff --name-only origin/erenup/integration...HEAD
formalization/NSFormalization/Section4/D01/HomogeneousNorm.lean
research/D01/ATTEMPTS_G1.md
research/D01/REPORT_164.md
research/D01/axioms_g1.lean
verification/Bindings/HomogeneousNorm.lean
verification/Contracts/V1/HomogeneousNorm.lean
verification/Tests/HomogeneousNorm.lean
verification/contracts.json

$ rg -n -i '\b(sorry|admit|axiom|native_decide)\b|maxHeartbeats' formalization/NSFormalization/Section4/D01/HomogeneousNorm.lean verification/Contracts/V1/HomogeneousNorm.lean verification/Bindings/HomogeneousNorm.lean verification/Tests/HomogeneousNorm.lean
<0 output; exit 1>

$ git diff --check origin/erenup/integration...HEAD
<0 output; exit 0>
```

### Reviewer probes

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/D01/probes/rev164_nonvacuity.lean
<0 output; exit 0>

$ LEAN_NUM_THREADS=6 lake env lean ../research/D01/probes/rev164_mutate_zero_to_one.lean
../research/D01/probes/rev164_mutate_zero_to_one.lean:20:75: error: Application type mismatch: The argument
  bot_le
has type
  ⊥ ≤ ?m.38
but is expected to have type
  1 ≤ dotHomogeneousENorm s 0
in the application
  le_antisymm
    (LE.le.trans (dotHomogeneousENorm_le_of_isHomogeneousSlice hzero)
      (of_eq_true (Eq.trans (congrFun' (congrArg LE.le enorm_zero) 1) zero_le._simp_1)))
    bot_le
<exit 1, expected>
```

Verdict: **REJECT** until the contract declaration is restored to the required
V2 module and every dependent namespace/path reference is updated.  No Lean
mathematics change is requested.
