ACCEPT

## 1. What the lane claims

The worker claims two deliverables and three supporting lemmas in
`NSFormalization.Section3.T15.Pressure` (`research/T15/REPORT_447.md:3-79`):

- `pressureSlice_integrable` is claimed to have the literal
  `ScalingAPI.pressureSlice_integrable` conclusion.  The claimed type at
  `research/T15/REPORT_447.md:11-24` is identical to the declaration at
  `formalization/NSFormalization/Section3/T15/Pressure.lean:96-109` and to the
  canonical field at
  `formalization/NSFormalization/Section3/T15/Scaling.lean:307-319`.
- `pressure_gauge` is claimed to give exactly the gauge required by a
  `ClassicalSolutionT`.  Its reported type
  (`research/T15/REPORT_447.md:30-40`) is identical to the declaration
  (`formalization/NSFormalization/Section3/T15/Pressure.lean:142-152`).  The
  consumer field is
  `ClassicalSolutionT.pressure_gauge` at
  `formalization/NSFormalization/Section3/T10/PeriodicData.lean:298-299`, and
  `normalizedScaledPressure` is definitionally the canonical
  `normalizePressureT` at
  `formalization/NSFormalization/Section3/T15/Bridges.lean:97-102`.
- The three helper statements reported at
  `research/T15/REPORT_447.md:43-69` occur with exactly those types at
  `formalization/NSFormalization/Section3/T15/Pressure.lean:31-52`,
  `:58-66`, and `:125-129`.

These are the requested mathematics.  The paper places and periodizes the
rescaled pressure at `paper/sections/03-torus.tex:101-123`; its pressure
convention is explicitly mean zero at `paper/sections/02-preliminaries.tex:28`
and again in the pressure recovery equation at
`paper/sections/02-preliminaries.tex:84-88`.  The formal integrability guard is
the honesty condition needed before taking that mean, as documented in the
canonical API at
`formalization/NSFormalization/Section3/T15/Scaling.lean:307-319`.

No hypothesis makes the result vacuous.  `PlacementData` requires `0 < T` and
`0 < ε₀` at `formalization/NSFormalization/Section3/T15/Scaling.lean:108-115`
and `:165-183`, so both quantified intervals are inhabited.  In the proof,
`hcarrier_compact` and `hpressure_support` are passed into the support theorem
at `formalization/NSFormalization/Section3/T15/Pressure.lean:111-115`, while
`hpressure_smooth` is used at `:116-118`.  The theorem contains no extended-real
reciprocal or `toReal` expression.  The implicit `u` and `f` merely index the
shared `PlacementData`; no new named analytic input or goal alias was added.

The lane's concrete probe uses a nonzero spatial bump but deliberately bypasses
the main past-zero smoothness premise (`research/T15/probes/pressure_closes.lean:10-15`).
I therefore added `research/T15/probes/rev447_nonvacuity.lean`: its pressure is
the nonzero smooth field `expNegInvGlue(t) * bump(x)` (`:25-38`, `:120-125`),
its zero-past extension and support satisfy the actual main hypotheses
(`:40-57`), its placement has `T = 1`, `ε₀ = 1/2` (`:88-118`), and both main
theorems are instantiated at `ε = 1/4`, `t = 1/2` (`:127-145`).

## 2. What is in Lean

The implementation follows an honest route:

1. `scaledPressure_slice_contDiff` transports the packet's past-zero
   smoothness through the parabolic pressure scaling and restricts it to a
   spatial slice
   (`formalization/NSFormalization/Section3/T15/Pressure.lean:31-52`).
2. Placement puts that slice strictly inside the fundamental cube
   (`formalization/NSFormalization/Section3/T15/Placement.lean:290-307`).  The
   generic U3 helper converts this to the vendor support bound
   (`formalization/NSFormalization/Section3/T15/SingleCopy.lean:32-43`), and the
   vendor locally-finite periodizer preserves smoothness
   (`vendor/NavierStokesAndEuler/NavierStokes/PeriodicLocalization.lean:153-164`).
   The two lattice embeddings are connected by the real theorem at
   `formalization/NSFormalization/Section3/T13/Assembly.lean:87-91`, used at
   `formalization/NSFormalization/Section3/T15/Pressure.lean:79-82`.
3. The continuous complex lift is in every `MemLp`, hence in `L¹`, by
   `formalization/NSFormalization/Paper1/TorusCube.lean:54-69`; taking real
   parts proves the requested real integrability
   (`formalization/NSFormalization/Section3/T15/Pressure.lean:83-91`).
4. `normalizePressureT_pressureGauge` applies `integral_sub` and
   `integral_const` (`formalization/NSFormalization/Section3/T15/Pressure.lean:125-138`).
   The required mass-one instance is proved at
   `formalization/NSFormalization/Section3/T10/PeriodicData.lean:41-47`, and the
   definitions of `pressureMeanT`, `PressureGaugeT`, and `normalizePressureT`
   are exactly those at `:249-261`.

The negative probe mutates the principal gauge constant from `0` to `1`
(`research/T15/probes/rev447_negative.lean:27-32`).  It fails for the intended
reason, rather than because an argument was removed:

```text
../research/T15/probes/rev447_negative.lean:32:2: error: Type mismatch
  hzero
has type
  pressureMeanT (normalizedScaledPressure p place.x₀ place.T ε) t = 0
but is expected to have type
  pressureMeanT (normalizedScaledPressure p place.x₀ place.T ε) t = 1
```

The axiom audit covers all five module declarations
(`research/T15/axioms_u10.lean:10-14`), and each has exactly
`[propext, Classical.choice, Quot.sound]`.

## 3. Gaps and hygiene

No proof, statement, or mathematical gap was found.  The worker report makes no
"not in the tree" gap claim (`research/T15/REPORT_447.md:95-117`), so the
Section4-wide missing-lemma grep requirement is not applicable.  Its one
historical diagnostic is resolved by the existing
`latticeVector_eq_lattice` theorem
(`formalization/NSFormalization/Section3/T13/Assembly.lean:87-91`).

The base comparison lists the following six lane files and no others:

```text
formalization/NSFormalization/Section3/T15/Pressure.lean
research/T15/ATTEMPTS_U10.md
research/T15/REPORT_447.md
research/T15/T15_SPLIT.md
research/T15/axioms_u10.lean
research/T15/probes/pressure_closes.lean
```

`Pressure.lean` is an added file; the modified-existing-formalization query had
zero output.  No `verification/` path was touched.  The exact hygiene outputs
were:

```text
MODIFIED_EXISTING_FORMALIZATION:
ADDED_FORMALIZATION:
formalization/NSFormalization/Section3/T15/Pressure.lean
FORBIDDEN_TOKENS:
DIFF_CHECK:
HEAD:
ef6bd65944c24e05b4597f2681c4a060f0db9f02 [447-T15-U10] Prove pressure normalization
```

Thus there is no `sorry`, `admit`, `axiom`, `native_decide`, or
`set_option maxHeartbeats` in the delivered module/probe or reviewer probes,
and `git diff --check` is silent.  Since `verification/` is absent from the base
diff, the brief's conditional `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` gates were
not triggered.

## 4. Commands and results

All Lake commands below were run from `verification/` after sourcing
`../scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

1. `lake build NSFormalization.Section3.T15.Pressure` — exit 0.  Lake replayed
   warnings from unchanged upstream modules, but emitted no warning or error
   from `Section3/T15/Pressure.lean`.  The exact target-local projection was:

   ```text
   Build completed successfully (10004 jobs).
   ```

2. `lake env lean ../formalization/NSFormalization/Section3/T15/Pressure.lean`
   — exit 0, exact output: empty.

3. `lake env lean ../research/T15/probes/pressure_closes.lean` — exit 0,
   exact output: empty.

4. `lake env lean ../research/T15/axioms_u10.lean` — exit 0, exact output:

   ```text
   'NSFormalization.Section3.T15.scaledPressure_slice_contDiff' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T15.periodizedScaledPressure_slice_integrable' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T15.pressureSlice_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T15.normalizePressureT_pressureGauge' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T15.pressure_gauge' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

5. `lake env lean ../research/T15/probes/rev447_nonvacuity.lean` — exit 0,
   exact output: empty.

6. `lake env lean ../research/T15/probes/rev447_negative.lean` — exit 1 as
   required, with the exact diagnostic pasted in part 2.

7. `make check` — exit 0.  The command's contract-closure JSON is over 1 MB;
   the exact final output was:

   ```text
     },
     "base_compatibility_checked": false,
     "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   }
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.050s

   OK
   python3 experiments/check_work_queue.py
   45 work items: ownership, contract registration and task cards consistent.
   ```

8. `git diff --name-only origin/erenup/integration-section3...HEAD` produced the
   six-file list in part 3.  The follow-up `verification/` filter printed
   exactly `NO verification/ paths`.

Fixes required: none.
