ACCEPT

# Independent review — lane 161-A01-b1-time-ladder

Reviewed read-only at `425dfc5` on branch `erenup/161-A01-b1-time-ladder`, against
`origin/erenup/integration`. The only reviewer-created files besides this report are
`research/A01/probes/rev161_fidelity.lean` and
`research/A01/probes/rev161_mutation_widen.lean`. I made no git state change and did not edit any
lane Lean file or pre-existing record.

## 1. What the lane claims

The worker claims five new theorems and R1 of the B1 time ladder through every
`m ≤ q + 1`, including a genuinely continuous datum selection rather than merely
`∀ t, ∃ A`. The five signatures are printed in `research/A01/REPORT_161.md:11`, `:17`, `:25`,
`:32`, and `:44`; the R1–R4 ladder and sizes are in `research/A01/B1_LADDER.md:12-17`.

Statement-by-statement audit:

1. `continuous_cylinder_word`: the reported statement at `research/A01/REPORT_161.md:11-14`
   is exactly the declaration at
   `formalization/NSFormalization/Section4/A01/DatumPathContinuous.lean:23-27`. The independent
   verbatim restatement is `research/A01/probes/rev161_fidelity.lean:16-19`.
2. `weakDerivsBound_word_top`: the reported statement at
   `research/A01/REPORT_161.md:17-22` is exactly the declaration at
   `formalization/NSFormalization/Section4/A01/DatumPathContinuous.lean:30-48`. The independent
   restatement is `research/A01/probes/rev161_fidelity.lean:21-26`.
3. `weakDerivsBound_cylinder_top`: the reported statement at
   `research/A01/REPORT_161.md:25-29` is exactly the declaration at
   `formalization/NSFormalization/Section4/A01/DatumPathContinuous.lean:51-55`. The independent
   restatement is `research/A01/probes/rev161_fidelity.lean:28-32`.
4. `datum_sub_norm_sq_le`: the reported statement at `research/A01/REPORT_161.md:32-41`
   is exactly the declaration at
   `formalization/NSFormalization/Section4/A01/DatumPathContinuous.lean:58-80`. The independent
   restatement is `research/A01/probes/rev161_fidelity.lean:34-43`.
5. `exists_continuous_datumPath`: the reported statement at
   `research/A01/REPORT_161.md:44-52` is exactly the declaration at
   `formalization/NSFormalization/Section4/A01/DatumPathContinuous.lean:83-105`. The independent
   restatement is `research/A01/probes/rev161_fidelity.lean:45-53`.

All five restatements typecheck with zero output. The result is the mathematics requested by R1:
the prescribed-horizon source really supplies the two named inputs
`ordinaryLift (U t) = value 1 (u t)` and angular invariance at
`formalization/NSFormalization/Section4/A01/Horizon.lean:143-153`; the new theorem consumes exactly
those at `DatumPathContinuous.lean:84-92` and returns a datum of the physical slice `⇑(U t)` plus
`Continuous A` at `:89-90`.

The proof mechanism is faithful:

- word evaluation is continuous because it is a continuous coordinate evaluation composed with
  the continuous cylinder path (`DatumPathContinuous.lean:23-27`);
- the no-loss descent used in the weak-derivative induction is the actual tree theorem
  `exists_ordinaryLift_of_invariant` (`Section4/A01/L2Descent.lean:61-65`), and the Schwartz pairing
  interface is `weakDeriv_pairing_of_lift_hasDerivAt`
  (`Section4/A01/EulerPairing.lean:259-271`);
- the difference datum is legitimate at every order, without A03's extra `2 ≤ m`, by
  `D01.isSobolevDatum_sub` (`Section4/D01/OrderZeroAlgebra.lean:46-54`);
- the bound used is really the sharp `4^m` constructor/uniqueness transfer
  (`Section4/D01/FiniteOrderNorm.lean:486-539`), giving the displayed increment estimate at
  `DatumPathContinuous.lean:58-80`;
- the selected path's continuity follows from that estimate and continuity of `u`, not from an
  unjustified continuity of `Classical.choose` (`DatumPathContinuous.lean:91-105`).

The paper citation is correct. `paper/sections/appendix-a-local-theory.tex:71-76` says that the
projected equation first gives `W^{1,∞}_t H^k_x`, then a continuous right-hand side and repeated
time differentiation give every `C^j_t H^k_x`, including the initial one-sided derivatives. The
lane claims only the earlier R1 selection result and explicitly leaves the Duhamel derivative step
to R2 (`research/A01/B1_LADDER.md:68-73`), so it does not substitute continuity for the paper's
bootstrap.

No vacuity or dishonest hypothesis was found. There is no `ENNReal.toReal` in the new module, so the
known `⊤.toReal = 0` failure mode is absent. The theorem permits an empty `Icc 0 S` when `S < 0`,
but it does not rely on that case: the worker's conformance example uses the inhabited interval
`Icc 0 1` and top order `q+1` (`research/A01/axioms_b1_ladder.lean:16-24`), and the reviewer probe
separately constructs an inhabitant and fires the theorem there
(`research/A01/probes/rev161_fidelity.lean:55-65`). The hypotheses `hu`, `hU`, and `hm` are used at
`DatumPathContinuous.lean:92` and `:97-99`; none was silently added to trivialize the conclusion.

## 2. What is in Lean

The lane adds exactly one source module and six A01 records/artifacts. Exact base diff:

```text
$ git diff --name-only origin/erenup/integration...HEAD
formalization/NSFormalization/Section4/A01/DatumPathContinuous.lean
research/A01/ATTEMPTS_B1_LADDER.md
research/A01/B1_LADDER.md
research/A01/REPORT_161.md
research/A01/axioms_b1_ladder.lean
research/A01/gate_b1_build.log.gz
research/A01/gate_b1_check.log.gz
```

All are `create mode`; no existing module was modified. `verification/` has no path in the diff.
`git diff --check origin/erenup/integration...HEAD` exits 0 with no output.

The new source module contains the five declarations at
`formalization/NSFormalization/Section4/A01/DatumPathContinuous.lean:23-105`. The conformance file
prints all five declarations and provides the non-vacuity instance at
`research/A01/axioms_b1_ladder.lean:10-24`. The ladder table gives conclusions, available tree
interfaces, gaps, and sizes at `research/A01/B1_LADDER.md:12-17`, with the necessary R2 context and
anti-circularity qualifications at `:53-81`.

Hygiene checks over the new source module and conformance file found no occurrence of
`sorry`, `admit`, `axiom`, or `native_decide`, and no `set_option`/`maxHeartbeats`; the exact grep
output was empty. The added git diff has no heartbeat setting. The words `sorry`/`axiom` that occur
inside the worker's pasted `make check` output are records of the repository-wide architecture
scanner, not Lean declarations in this lane. The five kernel dependency reports are the standard
three axioms (Part 4).

The cited nearby interfaces are accurately described:

- `A04.timeDeriv_isSobolevDatum` assumes both a `ClassicalSolutionR` and an already
  `ContDiffOn ℝ ∞` datum path (`Section4/A04/TimeDerivative.lean:181-191`);
- `C01.residualPath` is `f - advection + νΔu`, takes a `ClassicalSolutionR`, and its continuity
  result has the same input (`Section4/C01/JetPaths.lean:242-269`);
- `pressureGradientPath_jetLp_continuous` works on `[c,S]` with `0 < c` and `S < T`
  (`Section4/C01/PressureJetPath.lean:222-240`);
- `exists_smoothL2Field_of_memHInfty` assumes `ContDiff ℝ ∞ z`
  (`Section4/D01/DatumToJets.lean:304-309`);
- the cited periodic representative results exist with the claimed C⁰/spatial-derivative scope
  at `Paper1/PeriodicH3RepresentativeBridge.lean:22-29` and `:81-88`.

## 3. Gaps

The lane closes only R1. Its remaining-size assessment is honest:

| Rung | Review result | Evidence |
|---|---|---|
| R1: continuous datum selection | DONE through every `m ≤ q+1` | `DatumPathContinuous.lean:83-105`; fidelity probe `rev161_fidelity.lean:45-53` |
| R2: Duhamel ⇒ derivative datum | L, still absent | Full-tree searches found no file containing both `quadraticDuhamel` and any of `HasDerivWithinAt`, `HasDerivAt`, or `ContDiffOn`; the closest derivative theorem instead assumes classical smoothness (`TimeDerivative.lean:181-191`), while the residual path also assumes it (`JetPaths.lean:245-269`). |
| R3: all `C^j_t H^m_x` | L, still absent | `HasSmoothSobolevPath` merely defines the desired already-smooth datum paths (`Section4/A04/DerivNorm.lean:81-91`); its derivative lemmas consume that condition (`:106-122`). The manuscript requires the force regularity and repeated differentiation at `appendix-a-local-theory.tex:68-76`. |
| R4: one jointly pointwise `C∞` representative | L, still absent | The tree has datum-to-jet continuity (`Section4/C01/Evolution.lean:142-176`) and fixed-order periodic C⁰ representatives (`Paper1/PeriodicH3RepresentativeBridge.lean:22-29`, `:81-88`), but no theorem with the R4 output shape. `D01`'s representative packaging already assumes spatial smoothness (`DatumToJets.lean:304-309`). |

I reran the required negative searches over the whole
`formalization/NSFormalization/Section4` tree, not merely selected directories. Exact decisive
outputs:

```text
$ comm -12 <(rg -l 'quadraticDuhamel' formalization/NSFormalization/Section4 | sort) \
    <(rg -l 'HasDerivWithinAt|HasDerivAt|ContDiffOn' formalization/NSFormalization/Section4 | sort)
[no output]

$ rg -n 'quadraticDuhamel.*(HasDeriv|ContDiff)|(HasDeriv|ContDiff).*quadraticDuhamel' \
    formalization/NSFormalization/Section4
[no output; exit 1]

$ rg -n '^\\s*(def|theorem|structure|class|abbrev)\\s+CarrierConstructorFull\\b' \
    formalization/NSFormalization/Section4 research/A01
[no output; exit 1]

$ find formalization/NSFormalization/Section4 -name ConstructorPieces.lean -print
[no output]
```

The worker is therefore right that this checkout has neither a declaration named
`CarrierConstructorFull` nor `ConstructorPieces.lean`. The brief's cited reviewer artifact actually
defines `CarrierConstructor` at `research/A01/probes/rev157_constructor_loop.lean:32-40`, matching
the correction in `research/A01/B1_LADDER.md:96-100`. A broader constructor search did find existing
`ClassicalSolutionR` outputs in A02/R42, but inspection confirms they restrict, patch, or otherwise
start from an existing classical solution; the closest prior audit records this distinction at
`research/A01/REVIEW_SLICE_WIRING.md:200-221`. None supplies mild-to-classical R2–R4.

Negative mutation: `research/A01/probes/rev161_mutation_widen.lean:13-22` substantively widens the
main R1 order range from `m ≤ q+1` to `m ≤ q+2`, without dropping an argument. The original proof
application fails at exactly the range boundary:

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/A01/probes/rev161_mutation_widen.lean
../research/A01/probes/rev161_mutation_widen.lean:22:48: error: Application type mismatch: The argument
  hm
has type
  m ≤ q + 2
but is expected to have type
  m ≤ q + 1
in the application
  exists_continuous_datumPath u U hu hU m hm
```

No fixes are required.

## 4. Commands and results

Every shell sourced `scripts/lean-env.sh`; every `lake` invocation ran from `verification/` with
`LEAN_NUM_THREADS=6`. All required positive gates exited 0.

### Module build

```text
$ cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.DatumPathContinuous
[exit 0; 11931 output bytes; SHA-256 cc0c581bc36750702e78d8e09b2d8c553e8e5c98254fe71ef1b3a4f0f8fe81cb]
⚠ [8777/9367] Replayed NSFormalization.Source.FiniteHilbertBochner
...
⚠ [9933/9984] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead

Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
Build completed successfully (9984 jobs).
```

The omitted middle consists only of replayed dependency warnings, with no line from the lane module.
For an exact, non-truncated record: the complete committed output is
`research/A01/gate_b1_build.log.gz`; the reviewer's complete output is byte-for-byte its decompressed
contents after applying this exact diff (the cached rerun does not rebuild the final module):

```diff
--- research/A01/gate_b1_build.log.gz.decompressed
+++ reviewer-build.out
@@ -1,4 +1,4 @@
-⚠ [8777/9033] Replayed NSFormalization.Source.FiniteHilbertBochner
+⚠ [8777/9367] Replayed NSFormalization.Source.FiniteHilbertBochner
 warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'
 
 Note: This linter can be disabled with `set_option linter.unnecessarySimpa false`
@@ -202,5 +202,4 @@
 warning: NSFormalization/Paper3/SobolevDirectionalDerivative.lean:103:16: `SchwartzMap.smul_apply` has been deprecated: Use `smul_apply` instead
 
 Note: The updated constant is in a different namespace. Dot notation may need to be changed (e.g., from `x.smul_apply` to `smul_apply x`).
-✔ [9984/9984] Built NSFormalization.Section4.A01.DatumPathContinuous (4.6s)
 Build completed successfully (9984 jobs).
```

Thus the module itself is silent: all displayed warnings are from replayed dependencies.

### Direct Lean check

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A01/DatumPathContinuous.lean
[exit 0; stdout+stderr exactly 0 bytes]
```

### Axiom and non-vacuity check

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/A01/axioms_b1_ladder.lean
'NSFormalization.Section4.A01.continuous_cylinder_word' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.weakDerivsBound_word_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.weakDerivsBound_cylinder_top' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.datum_sub_norm_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.exists_continuous_datumPath' depends on axioms: [propext, Classical.choice, Quot.sound]
[exit 0]
```

### Repository check

```text
$ make check
[exit 0; 1042470 output bytes; SHA-256 715c770b3e7c9f98c9065355b1d7c7195d176ce3f8d58f39e03e70fb1fe934b8]
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
[the complete 26-contract closure JSON]
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.044s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

The complete million-byte output is exactly the decompressed committed
`research/A01/gate_b1_check.log.gz`, with this sole byte-level difference:

```diff
--- research/A01/gate_b1_check.log.gz.decompressed
+++ reviewer-make-check.out
@@ -25360,7 +25360,7 @@
 python3 experiments/test_contract_policy.py
 .............
 ----------------------------------------------------------------------
-Ran 13 tests in 0.045s
+Ran 13 tests in 0.044s
 
 OK
 python3 experiments/check_work_queue.py
```

The architecture scanner's `source_hashes_match: false` and copied
`Paper1/BoundaryCorollary.lean:90` token are repository-wide pre-existing reports; the command exits
0, the lane did not edit either source or snapshot, and the direct five-theorem axiom audit above is
clean.

### Reviewer probes and conditional gates

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/A01/probes/rev161_fidelity.lean
[exit 0; stdout+stderr exactly 0 bytes]
```

The substantive mutation output is pasted in Part 3 and exits 1 as expected. Since
`git diff --name-only origin/erenup/integration...HEAD -- verification` has exactly zero output,
the review brief's conditional `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration` gates were not applicable and were not
run.

Verdict: ACCEPT

Fixes: none.
