ACCEPT

## 1. What the lane claims

The lane claims that the three colliding proof-module instance pairs were
removed, one explicitly named probability instance was added to the canonical
data module, all four proof modules now coexist, and the binding is a direct
ten-theorem assembly (`research/T10/REPORT_296.md:5-33`).  It also claims no
definition or proof-theorem statement changed, no protected contract/test/
registry file changed, and no implementation or contract gap remains
(`research/T10/REPORT_296.md:10-11`, `research/T10/REPORT_296.md:58-70`).

Those claims are correct.  The protected hashes printed at
`research/T10/REPORT_296.md:62-65` reproduce exactly, and the direct binding is
visible at `verification/Bindings/TorusData.lean:147-159`.

The mathematics remains the approved T10 API.  The manuscript defines the
unit-torus Fourier coefficients, Sobolev weights, and vector norm convention at
`paper/sections/01-introduction.tex:80-103`; its homogeneous zero-mode convention
is at `paper/sections/01-introduction.tex:104-109`; conjugate-reflection reality
is at `paper/sections/02-preliminaries.tex:70-73`; the periodic Leray symbol,
including identity at zero, is at `paper/sections/02-preliminaries.tex:75-80`;
and the mean/mean-free split is at `paper/sections/03-torus.tex:395-411`.  The
chosen quotient realization is the existing tree definition at
`formalization/NSFormalization/Paper1/TorusCube.lean:20-26`.  Nothing in this
maintenance lane changes those statements.

## 2. What is in Lean

### Instance deduplication and direct binding

There is exactly one instance declaration across the five reviewed T10 modules:
the explicitly named
`periodicTorusMeasure_isProbabilityMeasure` at
`formalization/NSFormalization/Section3/T10/PeriodicData.lean:41-47`.  Its field
proves that the explicit `Fin 3` product of normalized circle Haar measures has
mass one.  Whole-file inspection and the instance grep in Part 4 find no local
or anonymous instance helper in `PhysicalBridge`, `DatumBasics`, `Parseval`, or
`Leray`.  The combined import file imports all four at
`research/T10/probes/all_four_import.lean:1-4` and elaborates silently.

The binding imports the four canonical proof modules at
`verification/Bindings/TorusData.lean:2-5`, retains its drift guards at
`verification/Bindings/TorusData.lean:31-143`, and declares the proposition as
`theorem torusData` at `verification/Bindings/TorusData.lean:147-159`.  Each of
the ten record fields is filled by the corresponding fully qualified public
theorem; no private re-proof remains.

### Exact statement audit

Every claimed theorem exists and its declared type is exactly the corresponding
`TorusDataAPI` field.  The four `*_closes.lean` probes copy those types literally
and all elaborate with zero output.

| Field | Contract statement | Canonical theorem |
|---|---:|---:|
| `datum_unique` | `verification/Contracts/V1/TorusData.lean:248` | `formalization/NSFormalization/Section3/T10/DatumBasics.lean:129` |
| `datum_real` | `verification/Contracts/V1/TorusData.lean:261` | `formalization/NSFormalization/Section3/T10/DatumBasics.lean:141` |
| `parseval_forward` | `verification/Contracts/V1/TorusData.lean:275` | `formalization/NSFormalization/Section3/T10/Parseval.lean:116` |
| `parseval_backward` | `verification/Contracts/V1/TorusData.lean:287` | `formalization/NSFormalization/Section3/T10/Parseval.lean:60` |
| `torusLift_injective` | `verification/Contracts/V1/TorusData.lean:300` | `formalization/NSFormalization/Section3/T10/PhysicalBridge.lean:61` |
| `torusLift_surjective` | `verification/Contracts/V1/TorusData.lean:312` | `formalization/NSFormalization/Section3/T10/PhysicalBridge.lean:70` |
| `mean_decomposition` | `verification/Contracts/V1/TorusData.lean:324` | `formalization/NSFormalization/Section3/T10/PhysicalBridge.lean:91` |
| `meanZero_datum` | `verification/Contracts/V1/TorusData.lean:339` | `formalization/NSFormalization/Section3/T10/DatumBasics.lean:150` |
| `leray_exists_contraction` | `verification/Contracts/V1/TorusData.lean:353` | `formalization/NSFormalization/Section3/T10/Leray.lean:178` |
| `leray_projector` | `verification/Contracts/V1/TorusData.lean:365` | `formalization/NSFormalization/Section3/T10/Leray.lean:260` |

`git diff HEAD^ HEAD` changes no theorem declaration or body in those four proof
modules: it deletes only the helper instances, plus one Parseval docstring line.
`Leray.lean` is byte-identical.  The binding's drift-guard declaration block is
also byte-identical; only imports, obsolete private proofs, the direct assembly,
and its docstring changed.

### Hypothesis honesty, non-vacuity, and mutation

The API has no interval endpoint, no `.toReal` conclusion, and no totalization
that can turn `top` into zero.  `IsPeriodicDatum` explicitly requires Haar
integrability at `verification/Contracts/V1/TorusData.lean:121-129`, and forward
Parseval separately requires physical `L²` membership at
`verification/Contracts/V1/TorusData.lean:266-278`.  The reviewer non-vacuity
probe constructs a zero-field datum satisfying both premises and applies both
Parseval directions (`research/T10/probes/rev296_nonvacuity.lean:14-27`); it
elaborates with exactly zero output.

Two inherited hypotheses are logically redundant but are neither new nor
vacuity-inducing.  `datum_real` does not use its datum premise because the
carrier is already the real submodule
(`formalization/NSFormalization/Section3/T10/DatumBasics.lean:141-146`), and
`mean_decomposition` does not use periodicity after integrability is supplied
(`formalization/NSFormalization/Section3/T10/PhysicalBridge.lean:91-105`).  They
are verbatim contract hypotheses and honestly delimit the intended physical
domain.

The substantive negative probe retains every binder and hypothesis and changes
only the forward Parseval conclusion to `2 * eLpNorm`
(`research/T10/probes/rev296_parseval_constant_mutation.lean:14-21`).  The
canonical proof fails for the expected changed-constant mismatch; exact output
is in Part 4.

## 3. Gaps

There is no Lean, theorem-fidelity, axiom, contract, or record gap, and there is
no required fix.

The worker does not make a missing-Section-4-lemma claim.  Its statement that
the solution-class layer remains outside this contract
(`research/T10/REPORT_296.md:85-86`) is a scope statement, not a claim that the
definitions are absent globally: the canonical definitions are present at
`formalization/NSFormalization/Section3/T10/PeriodicData.lean:220-340`.  As a
defensive check, the requested whole-tree `grep -rn` for those names and all ten
API theorem names under `formalization/NSFormalization/Section4` produced no
output; no missing-lemma assertion is being accepted from that absence.

Hygiene passes.  There is no `sorry`, `admit`, `axiom` declaration,
`native_decide`, or `maxHeartbeats` in the five reviewed proof/data modules,
the binding, or the axiom audit.  No file under `verification/Contracts/` or
`verification/Tests/`, and no `verification/contracts.json`, changed.  The four
proof-module edits and the binding edit are exactly the exceptions authorized
by the lane brief.  The branch is behind the current integration ref, but the
base-side changed-file set has no overlap with the lane commit, and the explicit
base compatibility check passes.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`; every Lake command ran from
`verification/` with `LEAN_NUM_THREADS=6`, sequentially.

### Canonical build

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T10.PeriodicData NSFormalization.Section3.T10.PhysicalBridge NSFormalization.Section3.T10.DatumBasics NSFormalization.Section3.T10.Parseval NSFormalization.Section3.T10.Leray
⚠ [8778/9077] Replayed NSFormalization.Source.FiniteHilbertBochner
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
⚠ [9320/9358] Replayed NSFormalization.Source.RealSobolev
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
⚠ [9324/9358] Replayed NSFormalization.Paper3.SpatiallyCompactTime
warning: NSFormalization/Paper3/SpatiallyCompactTime.lean:88:19: `ContinuousLinearMap.sub_apply` has been deprecated: Use `sub_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.sub_apply` to `sub_apply x`).
⚠ [9331/9358] Replayed NSFormalization.Paper3.RealPositiveDensity
warning: NSFormalization/Paper3/RealPositiveDensity.lean:67:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:76:63: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:88:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
warning: NSFormalization/Paper3/RealPositiveDensity.lean:100:59: Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice

Note: This linter can be disabled with `set_option linter.unnecessarySeqFocus false`
⚠ [9334/9358] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hc

Note: This linter can be disabled with `set_option linter.unusedVariables false`
⚠ [9344/9358] Replayed NSFormalization.Source.PacketForceExtension
warning: NSFormalization/Source/PacketForceExtension.lean:44:25: `if_pos` has been deprecated: Use `ite_eq_left` instead
⚠ [9347/9358] Replayed NSFormalization.Source.ViscosityPacket
warning: NSFormalization/Source/ViscosityPacket.lean:34:63: This simp argument is unused:
  Function.comp_def

Hint: Omit it from the simp argument list.
  [apply] simp [viscosityVelocity, dilateField, viscosityHomeomorph, Prod.map]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
Build completed successfully (9358 jobs).
[exit 0]
```

All diagnostics above are replayed inherited-module warnings; the five requested
modules themselves are silent.

### Direct module and probe elaboration

Each command below exited `0` with output exactly `""`:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T10/PeriodicData.lean
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T10/PhysicalBridge.lean
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T10/DatumBasics.lean
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T10/Parseval.lean
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T10/Leray.lean
$ LEAN_NUM_THREADS=6 lake env lean Bindings/TorusData.lean
$ LEAN_NUM_THREADS=6 lake env lean ../research/T10/probes/all_four_import.lean
$ LEAN_NUM_THREADS=6 lake env lean ../research/T10/probes/datum_basics_closes.lean
$ LEAN_NUM_THREADS=6 lake env lean ../research/T10/probes/leray_closes.lean
$ LEAN_NUM_THREADS=6 lake env lean ../research/T10/probes/parseval_closes.lean
$ LEAN_NUM_THREADS=6 lake env lean ../research/T10/probes/physical_bridge_closes.lean
$ LEAN_NUM_THREADS=6 lake env lean ../research/T10/probes/rev296_nonvacuity.lean
```

The binding/test build also exits zero.  Its only terminal lane-relevant output
is the contract checker info; all warnings before it are the same inherited
replayed warnings shown above:

```text
ℙ [9365/9365] Replayed Tests.TorusData
info: Tests/TorusData.lean:21:0: Contract BlowupDensity.Tests.checkedTorusData: checked; standard logical axioms only
Build completed successfully (9365 jobs).
[exit 0]
```

### Axiom audit

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/T10/axioms_contract.lean
'BlowupDensity.Bindings.periodicTorus_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.periodicTorusMeasure_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.torusLift_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.periodicFourierCoeff_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.realPeriodicSubmodule_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.periodicSobolev_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.isPeriodicDatum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.isPeriodicHomogeneousDatum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.isPeriodicReweight_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.torusData' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedTorusData' depends on axioms: [propext, Classical.choice, Quot.sound]
[exit 0]
```

Every remaining `#print axioms` is exactly the required three-item list.

### Negative check

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/T10/probes/rev296_parseval_constant_mutation.lean
../research/T10/probes/rev296_parseval_constant_mutation.lean:21:2: error: Type mismatch
  torusData.parseval_forward z A hA hz
has type
  ‖A‖ₑ = eLpNorm (torusLift z) 2 periodicTorusMeasure
but is expected to have type
  ‖A‖ₑ = 2 * eLpNorm (torusLift z) 2 periodicTorusMeasure
[exit 1, expected]
```

### Repository gates

The raw `make check` closure inventory is hundreds of kilobytes.  A second
run was presentation-filtered with `awk`; `setopt pipefail` preserved the gate
exit status.  These are the exact result-bearing lines:

```text
$ setopt pipefail
$ LEAN_NUM_THREADS=6 make check 2>&1 | awk '/^python3 / || /"task_count"/ || /"missing_copied_imports"/ || /"tracked_cache_free"/ || /"source_hashes_match"/ || /^Explicit axiom\/admission tokens/ || /"registered_contracts"/ || /"base_compatibility_checked"/ || /^Ran [0-9]+ tests/ || /^OK$/ || /work items:/'
python3 experiments/check_formalization_plan.py --check
  "task_count": 45,
  "missing_copied_imports": [],
  "tracked_cache_free": true,
  "source_hashes_match": false
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
  "registered_contracts": 38,
  "base_compatibility_checked": false,
python3 experiments/test_contract_policy.py
Ran 13 tests in 0.044s
OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
[exit 0]
```

The reported admission tokens are inherited repository inventory, while the
source-hash flag is informational for changed formalization sources; the
command succeeds, and the lane-scoped hygiene grep is empty.

The full scripted suite was likewise presentation-filtered only after running:

```text
$ setopt pipefail
$ BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh 2>&1 | awk '/^== / || /work items:/ || /Contract BlowupDensity.Tests.checkedTorusData/ || /extra_axiom:/ || /weakened_hypothesis:/ || /Mutation suite passed/ || /"registered_contracts"/ || /"base_compatibility_checked"/ || /"scope"/ || /^== gates OK/'
== make check
  "registered_contracts": 38,
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
45 work items: ownership, contract registration and task cards consistent.
== make test
info: Tests/TorusData.lean:21:0: Contract BlowupDensity.Tests.checkedTorusData: checked; standard logical axioms only
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
== gates OK
[exit 0]
```

Explicit compatibility check:

```text
$ setopt pipefail
$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3 | awk '/"registered_contracts"/ || /"base_compatibility_checked"/ || /"scope"/'
  "registered_contracts": 38,
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
[exit 0]
```

### Diff, protected files, hygiene, and whole-tree search

```text
$ git diff --name-only origin/erenup/integration-section3...HEAD
formalization/NSFormalization/Section3/T10/DatumBasics.lean
formalization/NSFormalization/Section3/T10/Parseval.lean
formalization/NSFormalization/Section3/T10/PeriodicData.lean
formalization/NSFormalization/Section3/T10/PhysicalBridge.lean
research/T10/ATTEMPTS_DEDUPE.md
research/T10/REPORT_296.md
research/T10/axioms_contract.lean
research/T10/probes/all_four_import.lean
verification/Bindings/TorusData.lean
[exit 0]
```

```text
$ sha256sum verification/Contracts/V1/TorusData.lean verification/Tests/TorusData.lean verification/contracts.json
9ce0a3b755b523b1b322bc62ae4597aad73c4d88f4bf8144adcd63ff015a9ce4  verification/Contracts/V1/TorusData.lean
bcbf7dcd0f3635055e733388c47da0e38fa98cf32f65865c189f3bffc3c6b6da  verification/Tests/TorusData.lean
ec7cae7bd19e0d45f61e4b2d436ba8e9005b4f10c711c532d7f7c6061cc2bead  verification/contracts.json
[exit 0]
```

```text
$ grep -rnE '^[[:space:]]*(local[[:space:]]+)?instance([[:space:]]|:)' formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray}.lean
formalization/NSFormalization/Section3/T10/PeriodicData.lean:42:instance periodicTorusMeasure_isProbabilityMeasure :
[exit 0]

$ grep -rnE 'IsPeriodicSobolevPath|forceSobolevENormT|initialClassT|MemForceT|forceClassT|PressureGaugeT|ClassicalSolutionT|maximalLifespanT|breakdownSetT|RelativelyDenseT|energyENormT|parseval_forward|parseval_backward|torusLift_injective|torusLift_surjective|mean_decomposition|meanZero_datum|leray_exists_contraction|leray_projector' formalization/NSFormalization/Section4
[no output; exit 0]

$ grep -rnE '(^|[^A-Za-z])(sorry|admit|native_decide)([^A-Za-z]|$)|^[[:space:]]*axiom\b|set_option[[:space:]]+maxHeartbeats' formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray}.lean verification/Bindings/TorusData.lean research/T10/axioms_contract.lean
[no declaration/token output; exit 0]
```

The broad word `axiom` occurs only in the title comment of
`research/T10/axioms_contract.lean:4`; there is no Lean `axiom` declaration.
