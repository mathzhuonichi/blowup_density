ACCEPT

# 1. What the lane claims

The worker claims three results: the two exact `TorusDataAPI` fields
`leray_exists_contraction` and `leray_projector`, plus the requested
coefficientwise fixed-point lemma `periodicLeray_of_solenoidal`
(`research/T10/REPORT_287.md:5`, `research/T10/REPORT_287.md:18`).  It also
claims that the API fixed-point field closes, that all three exported theorems
have only the standard three axioms, and that a concrete zero-datum instance
elaborates (`research/T10/REPORT_287.md:28`, `research/T10/REPORT_287.md:36`).

These claims are accurate.  The cited manuscript says that the nonzero torus
symbol is `I - k⊗k/|k|²`, the zero-mode symbol is the identity, and the map is
bounded on every Sobolev order (`paper/sections/02-preliminaries.tex:76`).  The
canonical definitions encode exactly that symbol and exact graph relation
(`formalization/NSFormalization/Section3/T10/PeriodicData.lean:182`,
`formalization/NSFormalization/Section3/T10/PeriodicData.lean:188`,
`formalization/NSFormalization/Section3/T10/PeriodicData.lean:198`).  Thus the
requested contraction, solenoidal range, idempotence, and fixed-point facts are
the intended mathematics, not a weakened surrogate.

# 2. What is in Lean

The declarations exist with the reported statements:

- `periodicLeray_of_solenoidal` is at
  `formalization/NSFormalization/Section3/T10/Leray.lean:151` and has exactly
  one named mathematical assumption, `IsSolenoidalPeriodicDatum A`.
- `leray_exists_contraction` is at
  `formalization/NSFormalization/Section3/T10/Leray.lean:178`; its statement is
  token-for-token the API field at `research/T10/probes/api_on_canonical.lean:148`
  (also `research/T10/Spec.lean:552`).
- `leray_projector` is at
  `formalization/NSFormalization/Section3/T10/Leray.lean:260`; its statement is
  token-for-token the API field at `research/T10/probes/api_on_canonical.lean:160`
  (also `research/T10/Spec.lean:564`).
- The exact conformance examples elaborate at
  `research/T10/probes/leray_closes.lean:7`,
  `research/T10/probes/leray_closes.lean:13`, and
  `research/T10/probes/leray_closes.lean:18`.

The proof realizes the formula as projection onto the orthogonal complement
(`formalization/NSFormalization/Section3/T10/Leray.lean:29`) and identifies its
coordinates with the canonical symbol
(`formalization/NSFormalization/Section3/T10/Leray.lean:32`).  The underlying
tree lemmas inspected are the projection formula
`verification/.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean:404`,
the orthogonal decomposition at the same file's line 542, contraction at line
361, and the fixed-point characterization at line 240.  The `lp` construction
uses `memℓp_gen` and the exact norm/series identity at
`verification/.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/lpSpace.lean:102`
and line 464; the outer `L²` identity is at
`verification/.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean:791`.

There is no vacuity-inducing hypothesis.  The existence theorem has no premise;
the graph relation fixes every output coefficient to the formula.  The
idempotence premises are both used (`formalization/NSFormalization/Section3/T10/Leray.lean:264`
and line 270), and the solenoidality premise is used to obtain the frequency
dot-product equality (`formalization/NSFormalization/Section3/T10/Leray.lean:158`).
There are no interval binders or extended-real `.toReal` norm bounds.  Every
`.toReal` occurrence is only the fixed exponent `2` in the standard `lp` API
(`formalization/NSFormalization/Section3/T10/Leray.lean:184`).  The phantom
Sobolev-order binder is the repository's intentional carrier design
(`formalization/NSFormalization/Section3/T10/PeriodicData.lean:86`).  Finally,
the reported concrete zero-datum instance is present at
`formalization/NSFormalization/Section3/T10/Leray.lean:273` and was re-elaborated
by the silent direct module check.

The implementation is hygienic: no `sorry`, `admit`, `axiom`, or
`native_decide` occurs in the lane Lean files; there is no `maxHeartbeats`
override; and `git diff --name-status origin/erenup/integration-section3...HEAD`
reports five additions and no
modified pre-existing module:

```text
A formalization/NSFormalization/Section3/T10/Leray.lean
A research/T10/ATTEMPTS_LERAY.md
A research/T10/REPORT_287.md
A research/T10/axioms_leray.lean
A research/T10/probes/leray_closes.lean
```

# 3. Gaps

There are no residual named hypotheses or mathematical gaps.  The report makes
no "not in the tree" gap claim.  As an additional audit, the required full-tree
command

```text
grep -R -n -E 'leray_exists_contraction|periodicLeray_of_solenoidal|leray_projector|IsPeriodicLerayDatum' formalization/NSFormalization/Section4
```

produced no output.  Related older raw-coefficient facts do exist, notably the
frequencywise contraction at
`formalization/NSFormalization/Paper1/PeriodicLerayNorm.lean:74`, divergence
cancellation at `formalization/NSFormalization/Paper1/PeriodicLerayDivergence.lean:78`,
and raw fixed points at the latter file's line 129.  None constructs the
canonical real `PeriodicSobolev` output or proves the exact T10 API fields, so
the narrower statement in `research/T10/ATTEMPTS_LERAY.md:121` is honest.

The substantive reviewer mutation is
`research/T10/probes/rev287_mutation.lean:7`: it changes the contraction factor
from `1` to `1/2`, without deleting any argument.  The unchanged proof fails at
line 14 with the expected statement mismatch (exit 1):

```text
../research/T10/probes/rev287_mutation.lean:14:2: error: Type mismatch
  leray_exists_contraction
has type
  ∀ (s : ℝ) (A : ↥(PeriodicSobolev s)), ∃ B, IsPeriodicLerayDatum A B ∧ ‖B‖ ≤ ‖A‖ ∧ IsSolenoidalPeriodicDatum B
but is expected to have type
  ∀ (s : ℝ) (A : ↥(PeriodicSobolev s)), ∃ B, IsPeriodicLerayDatum A B ∧ ‖B‖ ≤ 1 / 2 * ‖A‖ ∧ IsSolenoidalPeriodicDatum B
```

# 4. Commands and results

Environment preflight (`bash scripts/lean-install.sh`) found Lean
`4.34.0-rc2`, no missing cache files, and ended with exact line `== OK`.

The required module build exited 0.  Lake replayed pre-existing warnings from
imported modules, but emitted no diagnostic from `T10/Leray.lean`; its exact
final line was:

```text
$ cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T10.Leray
[pre-existing imported-module replay warnings omitted]
Build completed successfully (9353 jobs).
```

Commands and exact direct outputs:

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T10/Leray.lean
(no output; exit 0)

$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T10/probes/leray_closes.lean
(no output; exit 0)

$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T10/axioms_leray.lean
'NSFormalization.Section3.T10.periodicLeray_of_solenoidal' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.leray_exists_contraction' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T10.leray_projector' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`LEAN_NUM_THREADS=6 make check` exited 0.  Because its JSON output is hundreds
of thousands of bytes, the exact first and last lines (the middle was only the
reported closure arrays) are reproduced here:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 552,
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
[... exact middle omitted ...]
      "TestSupport.Axioms",
      "Tests.CompletedDensity"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
MAKE_CHECK_PIPELINE_EXIT=0
```

The forbidden-token search, heartbeat search, `git diff --check`, and the full
Section4 exact-name search all produced no output.  No path under
`verification/` appears in the base diff, so the brief's conditional
`scripts/gates.sh` and `check_contracts.py --base-ref
origin/erenup/integration-section3` gates are not applicable.

Fixes: none.
