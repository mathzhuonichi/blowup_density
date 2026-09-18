REJECT

## 1. What the lane claims

The worker report claims three results: the definitional API bridge, scalar/vector
supported-in-cube transfer, and a finite-nonzero-`p` reduction of the periodic
Haar/cube identity to a lintegral identity
(`research/T12/REPORT_366.md:3-7`).  It explicitly reports that the measurable
ENNReal identity and endpoints remain open (`research/T12/REPORT_366.md:9-10`),
and that the full build and `make check` were not run by the worker
(`research/T12/REPORT_366.md:12-13`).

The governing U1 statement is stronger: for every `p`, it asks for the actual
Haar/cube equality, supported transfer with a `tsupport` hypothesis, and the
gradient-tensor carrier `Space -> WithLp 2 (Fin 3 -> Space)`
(`research/T12/T12_SPLIT.md:50-56`).  U4 and U5 consume the actual equality at
`p = 3` and the gradient-tensor equality at `p = 6`, respectively
(`research/T12/T12_SPLIT.md:75-96`).

I opened the cited mathematics.  The paper says that the endpoint `L^2` and
gradient identities follow by integration over the single supported copy
(`paper/sections/03-torus.tex:23-29`, `paper/sections/03-torus.tex:96-98`).  Its
fundamental-domain calculation partitions space into cube translates and uses
periodicity (`paper/sections/03-torus.tex:53-72`).  The cited tree declarations
do exist with the advertised content:

- closed/half-open cube a.e. equality:
  `formalization/NSFormalization/Section3/T13/TorusIdentity.lean:402-415`;
- continuous nonnegative cube lintegral:
  `formalization/NSFormalization/Section3/T13/TorusIdentity.lean:419-436`;
- `torusPoint_sub` and periodic lift evaluation:
  `formalization/NSFormalization/Section3/T13/TorusIdentity.lean:456-461`;
- the existing `p = 2` supported endpoint:
  `formalization/NSFormalization/Section3/T13/ConstantEndpoints.lean:364-374`;
- the general measurable ENNReal tiling lemma, not mentioned in the attempts:
  `formalization/NSFormalization/Section3/T13/TorusIdentity.lean:341-373`.

## 2. What is in Lean

1. **The API bridge is exact.**
   `periodicLpENorm_eq_eLpNorm_torusLift` is `rfl`
   (`formalization/NSFormalization/Section3/T12/HaarCube.lean:11-14`), matching
   the definition of `periodicLpENorm`
   (`formalization/NSFormalization/Section3/T12/MeanZeroCalculus.lean:69-73`).

2. **A useful generic support theorem is proved, but not with the requested
   signature.**  `eLpNorm_restrict_eq_of_support` assumes
   `Function.support w ⊆ interior fundamentalCube`, then invokes Mathlib's
   restriction lemma (`formalization/NSFormalization/Section3/T12/HaarCube.lean:16-22`).
   This is non-vacuous: the review probe constructs a smooth nonzero bump
   (`research/T12/probes/rev366_nonvacuity.lean:13-22`), proves its support lies
   inside the cube (`research/T12/probes/rev366_nonvacuity.lean:24-72`), and
   instantiates the theorem at `p = 3` and `p = 6`
   (`research/T12/probes/rev366_nonvacuity.lean:74-82`).

3. **The named vector specialization has the wrong carrier for the requested
   gradient tensor.**  It uses `WithLp 2 (Fin 3 -> ℝ)`
   (`formalization/NSFormalization/Section3/T12/HaarCube.lean:24-29`), whereas
   `gradientTensor v` has carrier `WithLp 2 (Fin 3 -> Space)`
   (`formalization/NSFormalization/Section3/T12/MeanZeroCalculus.lean:82-85`).
   The generic theorem can be instantiated at the latter carrier, but the
   claimed named vector theorem is not that statement.

4. **The only periodic theorem is conditional and covers only finite nonzero
   exponents.**  `eLpNorm_torusLift_eq_restrict_of_lintegral` assumes the full
   norm-density lintegral equality plus `p != 0` and `p != top`
   (`formalization/NSFormalization/Section3/T12/HaarCube.lean:31-43`).  Its
   periodicity hypothesis `hv` is unused, as both source inspection and Lean's
   warning show.  The proof merely applies the finite-exponent formula and
   `congrArg` to `hlin` (`formalization/NSFormalization/Section3/T12/HaarCube.lean:41-43`).

5. **Axiom audit.**  Every declaration actually printed in the submitted
   axioms file has exactly `[propext, Classical.choice, Quot.sound]`
   (`research/T12/axioms_haar_cube.lean:1-4`).  That file omits the public vector
   theorem; the reviewer separately printed it and obtained the same three
   axioms.

## 3. Gaps and findings

1. **BLOCKER — the main U1 theorem is absent.**  There is no
   `eLpNorm_torusLift_eq_restrict`, no smooth unconditional corollary, no scalar
   periodic specialization, and no `gradientTensor` periodic specialization.
   The reproducer at `research/T12/probes/rev366_required_name.lean:9-14` fails:

   ```text
   ../research/T12/probes/rev366_required_name.lean:14:8: error(lean.unknownIdentifier): Unknown identifier `eLpNorm_torusLift_eq_restrict`
   ```

   This misses exactly what downstream U4/U5 require
   (`research/T12/T12_SPLIT.md:75-96`).

2. **BLOCKER — the residual theorem violates the no-repackaging requirement.**
   Its only mathematical input is `hlin`, the equality whose rpow is the
   conclusion; `hv` contributes nothing
   (`formalization/NSFormalization/Section3/T12/HaarCube.lean:33-43`).  This is
   not a periodic transfer theorem and does not isolate a measurability
   hypothesis.  It also omits both required endpoint cases.  There is no
   `top.toReal = 0` trick because `p = top` is explicitly excluded; the problem
   is missing mathematics, not endpoint vacuity.

3. **MAJOR — support statements are not exact.**  The brief requires
   `tsupport w ⊆ interior fundamentalCube`; the delivered declaration of the
   requested name uses `Function.support`
   (`formalization/NSFormalization/Section3/T12/HaarCube.lean:17-20`).  Although
   the delivered result is strong enough to derive the requested result via
   `support ⊆ tsupport`, statement fidelity requires the advertised theorem.
   The explicit vector theorem also has the carrier mismatch described above.

4. **MAJOR — the required deliverable probe is not present in substance.**
   `haar_cube_closes.lean` only checks the definitional API bridge at `3` and `6`
   for an arbitrary field (`research/T12/probes/haar_cube_closes.lean:6-9`).  It
   neither imports/instantiates the two-mode field from
   `tame_product_closes.lean` nor exercises Haar/cube or support transfer.  The
   requested two-mode witness is available at
   `research/T12/probes/tame_product_closes.lean:35-139`.

5. **MAJOR — module output fails the zero-output gate.**  The lane module emits
   two deprecation warnings and the unused-`hv` warning at lines 41, 42, and 35.
   The build succeeds, but it is not silent.  The submitted axioms audit also
   omits `eLpNorm_restrict_eq_of_support_vector`
   (`research/T12/axioms_haar_cube.lean:1-4`).

6. **NOTE — the declared tree gap was checked and the direct bridge is indeed
   absent.**  Literal recursive greps over all of `Section4` found no Haar/cube
   `eLpNorm`, lintegral, or ess-sup bridge.  The same grep over T10/T12/T13 found
   no direct all-`p` theorem outside this lane.  However, the attempts' statement
   that the existing T13 result is merely the continuous-real theorem
   (`research/T12/ATTEMPTS_HAAR_CUBE.md:5-7`) is incomplete: T13 also contains
   the general measurable ENNReal lattice-tiling lemma at
   `TorusIdentity.lean:343-373`.

7. **Hygiene otherwise passes.**  There are no `sorry`, `admit`, `axiom`,
   `native_decide`, or `maxHeartbeats` occurrences in changed Lean files.  The
   formalization diff adds only the new module; no existing Lean module was
   modified.  `git diff --check` is empty.  The worker report itself does not
   use the required four-part format (`research/T12/REPORT_366.md:1-13`).

The substantive negative mutation adds `+ 1` to the whole-space side rather
than dropping an argument (`research/T12/probes/rev366_mutation.lean:8-13`).  It
fails for the expected reason:

```text
../research/T12/probes/rev366_mutation.lean:13:2: error: Type mismatch
  eLpNorm_restrict_eq_of_support w hw p
has type
  eLpNorm w p (volume.restrict fundamentalCube) = eLpNorm w p volume
but is expected to have type
  eLpNorm w p (volume.restrict fundamentalCube) = eLpNorm w p volume + 1
```

## 4. Commands and results

All `lake` commands were run from `verification/` after sourcing
`scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

### Module build

Command:

```text
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T12.HaarCube
```

Exit `0`.  Exact lane-relevant tail (the preceding output consists of replayed
upstream warnings):

```text
⚠ [9919/9919] Replayed NSFormalization.Section3.T12.HaarCube
warning: NSFormalization/Section3/T12/HaarCube.lean:41:6: `MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm` has been deprecated: Use `MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal` instead
warning: NSFormalization/Section3/T12/HaarCube.lean:42:4: `MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm` has been deprecated: Use `MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal` instead
warning: NSFormalization/Section3/T12/HaarCube.lean:35:5: Variable name `hv` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hv

Note: This linter can be disabled with `set_option linter.unusedVariables false`
Build completed successfully (9919 jobs).
```

### Direct Lean checks

Module command:

```text
lake env lean ../formalization/NSFormalization/Section3/T12/HaarCube.lean
```

Exit `0`, exact output:

```text
../formalization/NSFormalization/Section3/T12/HaarCube.lean:41:6: warning: `MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm` has been deprecated: Use `MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal` instead
../formalization/NSFormalization/Section3/T12/HaarCube.lean:42:4: warning: `MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm` has been deprecated: Use `MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal` instead
../formalization/NSFormalization/Section3/T12/HaarCube.lean:35:5: warning: Variable name `hv` is not explicitly referenced.

Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
  [apply] _hv

Note: This linter can be disabled with `set_option linter.unusedVariables false`
```

Thus the required zero-output module check fails.

Submitted probe command:

```text
lake env lean ../research/T12/probes/haar_cube_closes.lean
```

Exit `0`; exact output: empty.

Submitted axioms command:

```text
lake env lean ../research/T12/axioms_haar_cube.lean
```

Exit `0`; exact output:

```text
'NSFormalization.Section3.T12.periodicLpENorm_eq_eLpNorm_torusLift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T12.eLpNorm_restrict_eq_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T12.eLpNorm_torusLift_eq_restrict_of_lintegral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Reviewer vector-axiom command:

```text
lake env lean ../research/T12/probes/rev366_vector_axioms.lean
```

Exit `0`; exact output:

```text
'NSFormalization.Section3.T12.eLpNorm_restrict_eq_of_support_vector' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Reviewer non-vacuity command:

```text
lake env lean ../research/T12/probes/rev366_nonvacuity.lean
```

Exit `0`; exact output: empty.

The required-name and mutation commands exited `1` with the exact errors pasted
in Part 3.

### Repository checks

Command:

```text
LEAN_NUM_THREADS=6 make check
```

Exit `0`.  Per the review rule limiting huge raw logs, exact first/last 20-line
capture follows (45,708 total lines):

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 600,
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
... [middle omitted; total lines=45708] ...
      "NavierStokes.WeightedClasses",
      "NavierStokes.WeightedODEJets",
      "NavierStokes.WeightedQuotients",
      "NavierStokes.WeightedRadialPrimitive",
      "NavierStokes.ZerothStressIdentity",
      "TestSupport.Axioms",
      "Tests.PacketImport"
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
PIPELINE_EXIT=0
```

`git diff --name-status origin/erenup/integration-section3...HEAD` returned:

```text
A formalization/NSFormalization/Section3/T12/HaarCube.lean
A research/T12/ATTEMPTS_HAAR_CUBE.md
A research/T12/REPORT_366.md
M research/T12/T12_SPLIT.md
A research/T12/axioms_haar_cube.lean
A research/T12/probes/haar_cube_closes.lean
```

`git diff --name-only ... -- verification` returned no paths, so the
verification-touch-only `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` gates were
not applicable and were not run.  The forbidden-token grep and
`git diff --check` both produced no output.

The required whole-tree gap check was:

```text
grep -rnE 'eLpNorm.*torusLift|torusLift.*eLpNorm|lintegral.*fundamentalCube|fundamentalCube.*lintegral|essSup.*fundamentalCube|fundamentalCube.*essSup|Haar.*cube|cube.*Haar' formalization/NSFormalization/Section4 --include='*.lean'
```

Exit `0`; exact output: empty.  The corresponding T10/T12/T13 grep returned
the existing `p = 2`/API occurrences, the lane's conditional theorem, and:

```text
formalization/NSFormalization/Section3/T13/TorusIdentity.lean:419:theorem lintegral_fundamentalCube_ofReal {F : Space → ℝ} (hF : Continuous F)
```

A declaration-specific recursive grep also found the general tiling lemmas:

```text
formalization/NSFormalization/Section3/T13/TorusIdentity.lean:343:theorem lintegral_eq_tsum_halfOpenCube {g : Space → ℝ≥0∞} (hg : Measurable g) :
formalization/NSFormalization/Section3/T13/TorusIdentity.lean:419:theorem lintegral_fundamentalCube_ofReal {F : Space → ℝ} (hF : Continuous F)
formalization/NSFormalization/Section3/T13/TorusIdentity.lean:439:theorem lintegral_halfOpenCube_ofReal {F : Space → ℝ} (hF : Continuous F)
formalization/NSFormalization/Section3/T13/TorusIdentity.lean:905:theorem lintegral_cube_periodicKernel {s : ℝ} {f : SpatialField}
formalization/NSFormalization/Section3/T13/TorusIdentity.lean:990:theorem lintegral_cube_diff_sq {f : SpatialField} (hfp : IsPeriodicSpatial f)
```

Required fixes: prove the actual all-`p` Haar/cube theorem (including `0` and
`top`) from honest measurability/periodicity hypotheses and add the smooth
corollary; expose the requested scalar and gradient-tensor forms; give the
support theorem the requested `tsupport` signature; replace the submitted probe
with real `p = 3`/`p = 6` two-mode transfer checks; audit every public theorem;
remove the three module warnings; and rewrite the worker report in four parts.

---

## Fix note (lane 366 r1)

All required fixes applied in `Section3/T12/HaarCube.lean`:

1. **Main U1 theorem now present and unconditional in `p`.**
   `eLpNorm_torusLift_eq_restrict (v) (_hv : IsPeriodicSpatial v) (p)` holds for
   every `p : ℝ≥0∞` including `p = 0` and `p = ⊤`.  Route replaced: instead of a
   hypothesised lintegral identity, one measure identity `map_torusChart`
   (`Measure.map torusChart periodicTorusMeasure = volume.restrict fundamentalCube`)
   plus `MeasurableEmbedding.eLpNorm_map_measure` closes all exponents at once
   (the map-measure lemma covers finite `p` by `∫⁻ ‖·‖ₑ^p.toReal` and `p = ⊤` by
   `essSup` internally).  `rev366_required_name.lean` now succeeds.
2. **No repackaging.** The rejected `…_of_lintegral` residual is deleted; the new
   theorem's proof takes no goal-equal hypothesis.  `_hv` is retained (the
   required-name probe passes it, and the paper says "unit-periodic `v`") but is
   underscored — unused in the proof, no linter warning.
3. **Smooth corollary + exact scalar / gradient-tensor forms added**
   (`_smooth`, `_scalar`, `_gradientTensor` with carrier `WithLp 2 (Fin 3 → Space)`),
   plus `periodicLpENorm_eq_restrict[_gradientTensor]`.
4. **Support theorem `tsupport` spelling added** (`eLpNorm_restrict_eq_of_tsupport`,
   `…_tsupport_vector`), while `eLpNorm_restrict_eq_of_support(_vector)` is kept for
   the reviewer probes; the vector carrier is corrected to `WithLp 2 (Fin 3 → Space)`.
5. **Probe replaced.** `haar_cube_closes.lean` now runs the genuine `p = 3`,
   `p = 6`, `p = ⊤` Haar/cube transfer and the `periodicLpENorm` bridge on the
   two-mode field `scalarOfCoeff probeCoeff`, and re-checks its two-mode
   non-vacuity.
6. **Axioms audited.** `axioms_haar_cube.lean` prints all 11 public declarations,
   each `[propext, Classical.choice, Quot.sound]`.
7. **Zero-output gate met.** The three module warnings are gone; `lake env lean`
   on the module is empty.

`rev366_mutation.lean` still fails as intended (wrong `+1` RHS).
