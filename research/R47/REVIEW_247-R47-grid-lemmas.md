ACCEPT

## 1. What the lane claims

The worker claims exactly two new binding theorems (`research/R47/REPORT_247.md:5-13`), and both
exist with the reported statements:

1. `exists_ball_in_common_cell` quantifies `n`, `Fin n → Grid`, and the requested final
   `Space` argument, then produces one `x₀`, one positive `r`, and a possibly grid-dependent
   cell index containing the same ball (`verification/Bindings/GridLemmas.lean:35-39`).  This is
   exactly the geometric clause needed by the reconciled `containingCell` field (lane-246
   `research/R47/Spec.lean:51-57`) and by the dependency ruling
   (`research/R47/RECONCILIATION.md:27-30`).  It is stronger internally: the reused theorem puts
   the ball in every open cell interior (`formalization/NSFormalization/Paper3/GridGeometry.lean:68-78`),
   and the binding only forgets that strengthening through
   `cellInterior_subset_cell` (`formalization/NSFormalization/Paper3/GridGeometry.lean:80-88`).
2. `gridObservation_locality` has exactly the reported support containment, containing-cell
   containment, two containing-cell integrability assumptions, and zero vector integral, and
   concludes equality of the full observation functions
   (`verification/Bindings/GridLemmas.lean:49-56`).  The containing-cell proof uses both
   integrability hypotheses at the sole point where the totalized Bochner integral is split
   (`verification/Bindings/GridLemmas.lean:61-65`); the hypotheses are therefore honest rather
   than decorative.

The mathematical vocabulary is faithful.  Registered `Grid` is the existing per-axis,
positive-width Cartesian grid with half-open cells (`verification/Contracts/V1/Data.lean:755-766`),
and `cellAverage`/`gridObservation` are precisely the vector Bochner cell average and full cell
index function (`verification/Contracts/V1/Data.lean:768-784`).  The manuscript defines those
observations at `paper/sections/04-whole-space.tex:288-295`, asserts one support ball in a cell of
every fixed finite grid at `paper/sections/04-whole-space.tex:297-304`, and derives the velocity
and force zero-cell-integral facts separately at `paper/sections/04-whole-space.tex:306-320`.
Thus the locality theorem does not silently infer zero mean from support alone.

The requested `x : Space` argument of `exists_ball_in_common_cell` is genuinely unused, but it is
not concealed: it is named `_x` in the theorem (`verification/Bindings/GridLemmas.lean:35`) and
the limitation is stated in both the theorem docstring (`verification/Bindings/GridLemmas.lean:31-34`)
and the report (`research/R47/REPORT_247.md:40-43`).  Neither the paper nor the reconciled
`containingCell` field requires proximity to a prescribed point, so this is an explicitly retained
interface argument, not a false near-point claim or a vacuity-inducing hypothesis.

No interval, `ENNReal.toReal`, or other totalized side condition occurs in either statement.  The
reviewer non-vacuity probe uses two distinct concrete grids and obtains a positive common ball
(`research/R47/probes/rev247_nonvacuity.lean:12-27`).  It also discharges every locality
hypothesis for a genuinely nonzero observed constant field, including vector-valued cell
integrability (`research/R47/probes/rev247_nonvacuity.lean:29-43`).

## 2. What is in Lean

The geometric proof is a direct specialization of `finite_grids_common_ball` followed by the
interior-to-half-open-cell inclusion (`verification/Bindings/GridLemmas.lean:37-39`).  The locality
proof expands the registered definitions, treats `k = k₀` using the zero integral, proves distinct
half-open grid cells disjoint coordinatewise, and gets pointwise equality off the topological
support (`verification/Bindings/GridLemmas.lean:57-87`).  This proves equality at every cell index,
as required by the R47 `velocity_observations` and `force_observations` fields (lane-246
`research/R47/Spec.lean:96-112`).

The lane's cited analytic route is also accurate.  Smooth compact solenoidal differences have
zero component set integrals (`formalization/NSFormalization/Paper3/CompactObservations.lean:18-48`).
The tree additionally contains PDE-level component observation theorems for actual velocity and
force differences (`formalization/NSFormalization/Paper3/ActualGridObservations.lean:19-70` and
`:72-89`).  In particular, the report's force bullet is a downstream discharge/assembly
obligation, not a claim that the analytic component theorem is absent.

The axiom audit names both public declarations (`research/R47/axioms_grid_lemmas.lean:17-18`) and
prints exactly `[propext, Classical.choice, Quot.sound]` for each.  The lane audit also has a
one-grid positive-radius example and a simultaneous locality-hypothesis example
(`research/R47/axioms_grid_lemmas.lean:20-38`).

Hygiene is clean:

- `git diff --name-status origin/erenup/integration...HEAD` reports four additions and no
  modification of an existing module: `research/R47/ATTEMPTS_GRID_LEMMAS.md`,
  `research/R47/REPORT_247.md`, `research/R47/axioms_grid_lemmas.lean`, and
  `verification/Bindings/GridLemmas.lean`.
- `git diff --diff-filter=M --name-only origin/erenup/integration...HEAD` has no output.
- The scoped forbidden-token scan for `sorry`, `admit`, declaration-form `axiom`, and
  `native_decide` has no output.  There is no `maxHeartbeats` setting in the implementation or
  audit, and `git diff --check origin/erenup/integration...HEAD` has no output.
- The worker's citations to the registered definitions, paper proof, and upstream grid theorem
  resolve to the stated declarations (`research/R47/ATTEMPTS_GRID_LEMMAS.md:3-18` and
  `:20-43`).

The substantive negative mutation doubles the radius in the conclusion while retaining the
original proof (`research/R47/probes/rev247_mutation.lean:12-20`).  It fails for the intended
reason, not because an argument was dropped:

```text
exit=1
../research/R47/probes/rev247_mutation.lean:20:2: error: Type mismatch
  LE.le.trans (hball i) (CartesianGrid.cellInterior_subset_cell (grids i) (indices i))
has type
  Metric.ball x₀ r ⊆ CartesianGrid.cell (grids i) (indices i)
but is expected to have type
  Metric.ball x₀ (2 * r) ⊆ CartesianGrid.cell (grids i) (indices i)
```

## 3. Gaps

The only R47-level gap stated by the lane is correct: these are reusable grid lemmas, not the
construction of the complete `RGridFamily` (`research/R47/REPORT_247.md:29-38`).  The required
`Section4`-wide missing-lemma search was run with

```text
grep -RniE 'RGridFamily|RGridAPI|gridObservation|cellAverage|containingCell|finite_grids_common_ball|setIntegral_component_eq_zero|actual_force_cell_averages_eq|zero[_ -]?mean|mean[_ -]?zero' formalization/NSFormalization/Section4
Section4 grep exit=1, bytes=0
```

and the packet-specific mean search was:

```text
grep -niE 'zero[_ -]?mean|mean[_ -]?zero' verification/Contracts/V1/Packet.lean
Packet grep exit=1, bytes=0
```

The broader `Paper3` search prevents overstating that gap and returned the already-existing
ingredients:

```text
formalization/NSFormalization/Paper3/ActualGridObservations.lean:22:theorem actual_force_cell_averages_eq (grid : CartesianGrid)
formalization/NSFormalization/Paper3/ActualGridObservations.lean:73:theorem actual_velocity_cell_averages_eq (grid : CartesianGrid)
formalization/NSFormalization/Paper3/CompactObservations.lean:33:theorem setIntegral_component_eq_zero {u : Space → Space}
formalization/NSFormalization/Paper3/CompactObservations.lean:51:theorem setIntegral_component_eq_zero_of_disjoint {u : Space → Space}
formalization/NSFormalization/Paper3/GridGeometry.lean:69:theorem finite_grids_common_ball {G : Type*} [Fintype G] (grids : G → CartesianGrid) :
```

Accordingly, the remaining work is wiring the existing R42 family and PDE hypotheses into these
grid results and then the R47 record; no missing geometric or generic locality lemma remains.
There is no need for a near-prescribed-point/open-set variant for the reconciled theorem.

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`; all `lake` commands were run from
`verification/` with `LEAN_NUM_THREADS=6`.

1. `lake build Bindings.GridLemmas` — exit 0.  The exact output was 3,277 bytes.  It contains
   only replayed warnings from pre-existing upstream files (none from `GridLemmas.lean`) and ends:

   ```text
   ⚠ [8815/8819] Replayed NSFormalization.Paper3.RealVectorPositiveDensity
   warning: NSFormalization/Paper3/RealVectorPositiveDensity.lean:29:5: Variable name `hc` is not explicitly referenced.

   Hint: The binding can be removed (if unused) or named `_` (if used implicitly). Alternatively, prefix the name with `_` to silence this warning:
     [apply] _hc

   Note: This linter can be disabled with `set_option linter.unusedVariables false`
   Build completed successfully (8819 jobs).
   ```

2. `lake env lean Bindings/GridLemmas.lean` — exit 0, exact output: 0 bytes.

3. `lake env lean ../research/R47/axioms_grid_lemmas.lean` — exit 0, exact output:

   ```text
   'BlowupDensity.Bindings.exists_ball_in_common_cell' depends on axioms: [propext, Classical.choice, Quot.sound]
   'BlowupDensity.Bindings.gridObservation_locality' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

4. Reviewer probes.  `lake build NSFormalization.Paper3.CellIntegrability` produced:

   ```text
   ✔ [8771/8771] Built NSFormalization.Paper3.CellIntegrability (2.2s)
   Build completed successfully (8771 jobs).
   ```

   `lake env lean ../research/R47/probes/rev247_nonvacuity.lean` then exited 0 with exactly
   0 bytes.  The mutation command and exact error are recorded in part 2 above.

5. `. scripts/lean-env.sh && LEAN_NUM_THREADS=6 make check` — exit 0.  The command emitted
   31,833 lines because `check_contracts.py` enumerates every registered closure.  The exact head
   and tail were as follows; the unchanged closure-enumeration middle is omitted between
   the two exact excerpts:

   ```text
   python3 experiments/check_formalization_plan.py --check
   {
     "task_count": 30,
     "source_counts": {
       "formalization": 547,
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
   ```

   ```text
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.045s

   OK
   python3 experiments/check_work_queue.py
   30 work items: ownership, contract registration and task cards consistent.
   ```

   The displayed copied-source token and `source_hashes_match: false` are non-fatal baseline
   diagnostics; the command completed successfully.

6. `. scripts/lean-env.sh && LEAN_NUM_THREADS=6 scripts/gates.sh Bindings.GridLemmas` —
   exit 0.  Its phase/result tail was exactly:

   ```text
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

   The preceding `== lake build Bindings.GridLemmas` phase ended with
   `Build completed successfully (8819 jobs).`, and every `make test` declaration reported
   `checked; standard logical axioms only`.

7. `. scripts/lean-env.sh && python3 experiments/check_contracts.py --base-ref origin/erenup/integration`
   — exit 0.  It emitted 31,801 lines of closure enumeration and ended exactly:

   ```text
     },
     "base_compatibility_checked": true,
     "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   }
   ```

Fixes required: none.
