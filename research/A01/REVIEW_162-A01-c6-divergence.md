ACCEPT

## 1. What the lane claims

The worker claims two declarations, and both exist with the statements reproduced in the report.

1. `NSFormalization.Section4.A01.divergence_ae_of_cylinder` is stated at
   `formalization/NSFormalization/Section4/A01/ConstructorDivergence.lean:66-75`; it matches the
   worker's transcription at `research/A01/REPORT_162.md:8-18`.  From one angle-invariant cylinder
   slice, its ordinary descent, the cylinder divergence-free clause, and a smooth representative of
   the ordinary carrier, it concludes
   `(∀ᵐ x ∂volume) ∑ i, (fderiv ℝ Z.field x (coordinateVector i)) i = 0`.
2. `NSFormalization.Section4.A01.divergence_of_cylinder_pointwise_of_contDiff` is stated at
   `formalization/NSFormalization/Section4/A01/ConstructorDivergence.lean:147-161`; it matches the
   worker's transcription at `research/A01/REPORT_162.md:28-43`.  Its conclusion is token-for-token
   the `ClassicalSolutionR.divergence` field at
   `formalization/NSFormalization/Section4/A02/SolutionClass.lean:127-128`:
   `∀ t ∈ Ico 0 T, ∀ x, spatialDivergence velocity t x = 0`.

This is the requested mathematics.  The paper defines incompressibility by `∇·u=0` in
`paper/sections/01-introduction.tex:2-7`; the A01 split asks for exactly this constructor field at
`research/A01/A01_SPLIT.md:107`.  The coordinate spelling is correct because
`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:59-68` defines
`spatialDivergence` as the displayed sum of diagonal Fréchet derivatives.

The cylinder hypotheses are genuine outputs of the named source.  In particular,
`localTheory_on_prescribed_horizon` returns `u` and `U` at
`formalization/NSFormalization/Section4/A01/Horizon.lean:143-144`, descent at `:148`,
divergence-free membership at `:149`, and angle invariance at `:153`.  Reordering the last clause's
two universal binders gives the theorem's `hu` without strengthening it.

The source audit in `research/A01/ATTEMPTS_C6.md:17-49` is accurate:

- HeliCorgi's cited `r3DecodedFrequency_incompressible_ae_decoder` really concerns
  `r3L2SolenoidalSubmodule` and has the stated `C¹`, pointwise-divergence, a.e.-decoder conclusion at
  `vendor/HeliCorgi/Formal/R3InversionConsistency.lean:136-150`.
- The Horizon carrier instead uses `divergenceFreeSpace`, defined as the orthogonal complement of
  `gradientSpace` at `vendor/NavierStokesAndEuler/Euler/EulerProof.lean:1339-1341`; its weak test
  identity is at `:1353-1364`.
- The cited weak-to-classical bridge has exactly the needed statement at
  `vendor/NavierStokesAndEuler/Euler/ClassicalDivergence.lean:15-21`, and the angle-independent
  derivative reduction is exactly
  `vendor/NavierStokesAndEuler/Euler/MeanCylinderSolenoidal.lean:18-31`.

There is no hidden `⊤.toReal = 0` or norm-finiteness escape in either statement.  Although the
pointwise theorem is (harmlessly) true over an empty `Ico 0 T` when `T ≤ 0`, the conformance instance
uses `T = 1` at `research/A01/axioms_c6.lean:35-57`, so the delivered result is demonstrably inhabited
on a nonempty time interval.  The a.e. zero-cylinder instance is at `:17-32`.  Both compile in the
axioms gate below.

## 2. What is in Lean

The a.e. theorem really performs the three requested word descents:

- `word_descent_ae_top` is applied once for every `i : Fin 3` at
  `ConstructorDivergence.lean:77-80`; its upstream statement is
  `formalization/NSFormalization/Section4/A01/L2Descent.lean:137-145`.
- `word_descent_ae_full` identifies each descended word with the smooth representative's classical
  word at `ConstructorDivergence.lean:81-85`; its upstream induction is
  `L2Descent.lean:151-190`.
- `wordField_field`, stated at
  `formalization/NSFormalization/Section4/A01/CarrierWords.lean:203-212`, reduces the length-one word
  to the displayed Fréchet derivative at `ConstructorDivergence.lean:110-115`.
- The three components are summed at `ConstructorDivergence.lean:116-132`.

The actual zero input is the vendor weak-to-classical theorem, applied at
`ConstructorDivergence.lean:87-107`.  A review probe proves that this theorem already gives the a.e.
conclusion without `hu` or any word descent:
`research/A01/probes/rev162_direct_without_words.lean:14-43` compiles with zero output.  Thus the
word-descent segment is logically redundant, but it is present, correctly typed, and does not make
the statement or report false.  This is a later simplifier concern, not an acceptance blocker.

The pointwise theorem first upgrades the continuous divergence sum from a.e. equality to function
equality at `ConstructorDivergence.lean:164-176`, then upgrades the common a.e. carrier equality to
pointwise slice equality at `:177-181`, and unfolds the exact target at `:182-183`.  The c3 input is
honestly isolated as the named `hslice_contDiff` hypothesis at `:159-160`; no pointwise divergence
hypothesis is assumed.

Hygiene is clean.  Against `origin/erenup/integration`, the committed lane delta is exactly:

```text
formalization/NSFormalization/Section4/A01/ConstructorDivergence.lean
research/A01/A3_SPLIT.md
research/A01/ATTEMPTS_C6.md
research/A01/REPORT_162.md
research/A01/axioms_c6.lean
```

The only formalization module is new; no existing Lean module was modified.  The targeted scan

```text
rg -n '\b(sorry|admit|axiom|native_decide)\b|set_option[[:space:]]+maxHeartbeats' \
  formalization/NSFormalization/Section4/A01/ConstructorDivergence.lean \
  research/A01/axioms_c6.lean research/A01/probes/rev162_*.lean
```

returned no output.  `git diff --check origin/erenup/integration...HEAD` also returned no output.
There is no heartbeat override.

The substantive negative mutation is retained at
`research/A01/probes/rev162_mutate_divergence_constant.lean:13-31`.  It changes the main conclusion's
constant from `0` to `1` without deleting or weakening any hypothesis.  Lean fails as expected:

```text
../research/A01/probes/rev162_mutate_divergence_constant.lean:30:2: error: Type mismatch
  divergence_of_cylinder_pointwise_of_contDiff u U hu hU hdiv Z hZ velocity hslice hslice_contDiff
has type
  ∀ t ∈ Ico 0 T, ∀ (x : Space), spatialDivergence velocity t x = 0
but is expected to have type
  ∀ t ∈ Ico 0 T, ∀ (x : Space), spatialDivergence velocity t x = 1
```

## 3. Gaps

There is no remaining c6 analytic gap under the theorem's stated carrier hypotheses.  The worker
correctly leaves construction of `Z`, `hslice`, and c3 smoothness to the surrounding constructor at
`research/A01/REPORT_162.md:69-76`.

I reran the required whole-tree searches before accepting the negative claims.  For a direct
cylinder word/divergence bridge,

```text
grep -rnE 'divergence.*word|word.*divergence|divergenceFreeSpace' \
  formalization/NSFormalization/Section4
```

found only the Horizon/continuation membership clauses, the new lane module, and its documentation:

```text
formalization/NSFormalization/Section4/A01/Horizon.lean:149:        (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
formalization/NSFormalization/Section4/A01/Horizon.lean:179:        (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
formalization/NSFormalization/Section4/A01/ContinuationInvariant.lean:296:        (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
formalization/NSFormalization/Section4/A01/Continuation.lean:126:    ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0 := by
formalization/NSFormalization/Section4/A01/Continuation.lean:128:      ∈ divergenceFreeSpace 1 1 0 :=
formalization/NSFormalization/Section4/A01/Continuation.lean:191:        (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
formalization/NSFormalization/Section4/A01/Continuation.lean:231:        (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
```

The new module's own matches are omitted from that pre-existing-tree list.  A second full-tree grep
for `velocitySliceSmoothL2`, `hslice`, slice/ordinary bridges, and `ClassicalSolutionR` constructors
found only consumers of `hslice` in A01.  In particular,
`formalization/NSFormalization/Section4/A01/SliceWiring.lean:45-71` explicitly records the missing
carrier constructor.  Its `velocitySliceSmoothL2` at `:99-106` constructs `Z` only from an already
given `ClassicalSolutionR`, so it does not fill the mild-to-classical construction gap.

No fix is required for this lane.  Non-blocking note: because
`divergenceFree_classical_divergence_zero` already yields a pointwise result, the word descent is a
verification detour rather than a load-bearing analytic step.

## 4. Commands and results

Every Lean shell sourced `scripts/lean-env.sh`; every `lake` command ran from `verification/` with
`LEAN_NUM_THREADS=6`.

1. Module build.  The exact replay headers and terminal line were (the intervening, unchanged linter
   explanation bodies are omitted):

   ```text
   $ cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.ConstructorDivergence
   ⚠ [8777/9068] Replayed NSFormalization.Source.FiniteHilbertBochner
   ⚠ [9838/9987] Replayed Formal.R3LerayFrequencySymbol
   ⚠ [9847/9987] Replayed Formal.R3StokesL2Operator
   ⚠ [9848/9987] Replayed Formal.R3L2ScalarAux
   ⚠ [9856/9987] Replayed NSFormalization.Source.PacketForceExtension
   ⚠ [9869/9987] Replayed NSFormalization.Source.RealSobolev
   ⚠ [9873/9987] Replayed NSFormalization.Paper3.SpatiallyCompactTime
   ⚠ [9880/9987] Replayed NSFormalization.Paper3.RealPositiveDensity
   ⚠ [9883/9987] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
   ⚠ [9889/9987] Replayed Formal.FlowMapNonextendibilityCriterion
   ⚠ [9890/9987] Replayed Formal.UniformRestartContinuation
   ⚠ [9891/9987] Replayed Formal.R3SobolevCarrier
   ⚠ [9894/9987] Replayed Formal.R3CoordinateLinearAux
   ⚠ [9897/9987] Replayed Formal.R3DivergencePointwise
   ⚠ [9901/9987] Replayed Formal.R3LerayL2Operator
   ⚠ [9902/9987] Replayed Formal.R3LerayFourierBridge
   ⚠ [9903/9987] Replayed Formal.R3LerayComplexFiberSymbol
   ℹ [9917/9987] Replayed NSFormalization.Source.PhysicalBesselSobolev
   ⚠ [9922/9987] Replayed NSFormalization.Source.ViscosityPacket
   ⚠ [9936/9987] Replayed NSFormalization.Paper3.SobolevDirectionalDerivative
   Build completed successfully (9987 jobs).
   ```

   Exit 0.  All warning bodies belong to the listed pre-existing imported modules.  There is no
   warning or error from `ConstructorDivergence` itself.

2. Direct module check:

   ```text
   $ cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A01/ConstructorDivergence.lean
   ```

   Exit 0, exactly zero output.

3. Axiom and non-vacuity check:

   ```text
   $ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/A01/axioms_c6.lean
   'NSFormalization.Section4.A01.divergence_ae_of_cylinder' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section4.A01.divergence_of_cylinder_pointwise_of_contDiff' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   ```

   Exit 0.  These are all public declarations in the new module, and both zero-cylinder examples
   typecheck in the same run.

4. Repository check.  This command emitted 25,367 lines because `check_contracts.py` prints every
   generated dependency closure; the exact diagnostic prefix and result tail are pasted below, with
   only that generated closure table elided:

   ```text
   $ make check
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
   [check_contracts.py printed the generated closure table for all 26 registered contracts]
     "base_compatibility_checked": false,
     "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   }
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.045s

   OK
   python3 experiments/check_work_queue.py
   30 work items: ownership, contract registration and task cards consistent.
   ```

   Exit 0.  The `source_hashes_match: false` and copied-source token count are repository-level
   diagnostics also disclosed by the worker; the lane adds no copied-source admission.

5. Review probes:

   ```text
   $ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/A01/probes/rev162_direct_without_words.lean
   ```

   Exit 0, exactly zero output.  The mutation command exited 1 with the exact type mismatch pasted
   in part 2.

6. `git diff --name-only origin/erenup/integration...HEAD -- verification` returned exactly zero
   output.  Therefore the review brief's conditional `scripts/gates.sh` and
   `check_contracts.py --base-ref origin/erenup/integration` gates do not apply to this lane.

Fixes: none.
