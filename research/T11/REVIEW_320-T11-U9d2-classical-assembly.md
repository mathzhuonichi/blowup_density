REJECT

Reproducing error (substantive interval mutation): `lake env lean ../research/T11/probes/rev320_negative_interval.lean` exits 1 with `Type mismatch`: `persistence_physical_sobolev h` supplies `ContinuousOn G (Ico 0 T)` but the mutated goal expects `ContinuousOn G (Ioo 0 T)` (`rev320_negative_interval.lean:9-15`).

## 1. What the lane claims

The report is candid that this is a partial delivery (`research/T11/REPORT_320.md:1-20`, `:93-119`). It claims the persistence input, all-order physical Sobolev paths, spatial smoothness, coefficient/mild solenoidality and physical divergence, and a projected equation for an already existing classical solution (`REPORT_320.md:22-72`). It does not claim that the general U9d2 existential is proved (`REPORT_320.md:95-119`).

The required target is nevertheless the unchanged universal theorem in `research/T11/EXISTENCE_ROUTE.md:253-266`: for every positive viscosity, two-space contract, admissible datum and smooth periodic force, positive `T`, datum path, Leray graph and `TorusForcedMildOn`, produce `w : ClassicalSolutionT` with `PeriodicLocalRegularity` and the same H³ path. The paper requires the projected equation and torus pressure recovery/gauge (`paper/sections/02-preliminaries.tex:75-88`), and local theory requires one common all-order interval and smoothness (`paper/sections/02-preliminaries.tex:105-120`, `paper/sections/appendix-a-local-theory.tex:60-77`). Thus the report's partial status is a blocking failure against this lane brief, not a completed conditional assembly.

## 2. What is in Lean

The displayed statements in the report match the declarations in the new module:

- `PersistenceInput` is exactly `∀ m, ∃ u_m`, `ContinuousOn` on `Ico 0 T`, and equality of physical coefficients (`formalization/NSFormalization/Section3/T11/ClassicalAssembly.lean:25-30`; report copy `REPORT_320.md:10-15`). The coefficient/reweight equivalence is proved at `ClassicalAssembly.lean:32-51`, and the canonical reweight-to-datum bridge is `PhysicalRecovery.lean:406-410`.
- `persistence_physical_sobolev` has the report's exact `IsPeriodicDatum` conclusion (`ClassicalAssembly.lean:53-63`; report `REPORT_320.md:24-31`).
- `persistence_physical_spatial_smooth` has the exact `Ico` hypothesis and `ContDiff ℝ ∞` slice conclusion (`ClassicalAssembly.lean:153-182`; report `REPORT_320.md:33-37`).
- The coefficient solenoidality chain is present: continuous divergence functional (`ClassicalAssembly.lean:293-304`), scalar-multiplier preservation (`:306-325`), interval-integral preservation (`:327-340`), mild preservation (`:342-377`), Leray range (`:402-413`), and physical divergence on `Ico` (`:415-426`). This uses the tree's Leray-range theorem (`Section3/T10/Leray.lean:131-145,176-181`) and the recovered-field datum theorem (`Section3/T11/PhysicalRecovery.lean:234-262`).
- `assembly_mild_solenoidal` and `persistence_mild_physical_divergence` match the report's binders and conclusions (`ClassicalAssembly.lean:315-348,415-426`; report `REPORT_320.md:39-56`). The hypotheses are the genuine datum/Leray/mild hypotheses, not an impossible `⊤.toReal` or empty-interval premise; the nonzero `T=1` witness is at `ClassicalAssembly.lean:428-454`.
- `classicalSolutionT_projected` matches the displayed statement (`ClassicalAssembly.lean:267-281`; report `REPORT_320.md:58-65`). It starts from `w : ClassicalSolutionT`; it is an application of the canonical equivalence `navierStokesResidual_eq_iff_projected` (`Section4/A01/ConvectionDivergence.lean:127-139`), so it cannot establish a classical solution from a mild path.
- `persistence_of_classicalSolutionT` is a converse necessity lemma (`ClassicalAssembly.lean:283-291`), not an existence theorem. `classicalAssembly_nonzero` is only the affine constant family at `T=1` (`ClassicalAssembly.lean:428-454`; the underlying full special-case recovery is `PhysicalRecovery.lean:530-549`).

The structure fields that the brief asks to assemble are genuinely substantial: `ClassicalSolutionT` contains smoothness, initial value, divergence, interior momentum, all-order continuous Sobolev data, pressure-gradient integrability, periodicity and pressure gauge (`Section3/T10/PeriodicData.lean:265-299`), while `PeriodicLocalRegularity` additionally requires all-order `ContDiffOn` paths, pressure Poisson and projected equations (`Section3/T11/LocalTheory.lean:79-92`). The probe intentionally checks only the delivered fields and the special witness (`research/T11/probes/classical_assembly_closes.lean:3-54`), so its successful exit is not conformance to the universal target.

No lane Lean file contains `sorry`, `admit`, `axiom`, or `native_decide`; both declaration-local heartbeat overrides are exactly `400000` and commented (`ClassicalAssembly.lean:97-102,125-129`). The 26 guarded declarations in the axiom file are all checked (`research/T11/axioms_classical_assembly.lean:1-108`), and the direct module check is silent. `git diff --name-only origin/erenup/integration-section3...HEAD` shows only the new assembly module and research records; no existing Lean module or `verification/` file was modified. `git diff --check` does report one trailing blank line in `research/T11/axioms_classical_assembly.lean:108`.

## 3. Gaps and rejection reason

1. **Blocking — the required theorem is absent.** There is no declaration with the universal target at `EXISTENCE_ROUTE.md:253-266`. The module's own header says it does not assert general classical existence (`ClassicalAssembly.lean:4-9`), and the report explicitly says the target remains unproved even with `PersistenceInput` (`REPORT_320.md:93-119`). The probe header says the same (`classical_assembly_closes.lean:3-8`).

2. **Blocking — the peeling rule was not completed.** Defining `PersistenceInput` is allowed, but the brief requires proving the full target from it. The delivered module leaves Duhamel time differentiation, endpoint/joint time regularity, general pressure construction, pressure gradient/smoothness/gauge/periodicity/Poisson, momentum, and final structure assembly open (`REPORT_320.md:95-100`; `EXISTENCE_ROUTE.md:329-333`). A single affine constant example cannot replace the universal quantifiers over `ν,C,a,g,T,A,F,P,u` (`ClassicalAssembly.lean:428-454` versus `EXISTENCE_ROUTE.md:256-265`).

3. **Pressure gap is real but should be described precisely.** The whole-tree search required by the review found analogues, not the requested theorem. The coefficient inverse only proves a zero-mode-compatible raw coefficient equation (`Paper1/PeriodicPressureSymbolOperator.lean:23-41`), and the periodic pressure bridge explicitly assumes an existing flow (`Paper1/PeriodicPressureRecoveryBridge.lean:6-10,27-49`). Section 4's `ConstructorPressure` can construct a pressure only under supplied smooth velocity, gradient, symmetry, residual and time-derivative hypotheses (`Section4/A01/ConstructorPressure.lean:124-152,188-245`); `DatumPathDeriv` differentiates a different cylinder/Duhamel representation (`Section4/A01/DatumPathDeriv.lean:344-398`). None has the `TorusForcedMildOn`/`PeriodicSobolev`/U9d binders, so these do not close the lane's missing pressure/PDE assembly.

The required whole-tree search was:

```text
grep -rnE 'TorusForcedMildOn|torusPhysicalVelocity|physical.*recover|recover.*physical|all.order|allOrder|Duhamel|duhamel|timeDerivative|pressure_gradient|pressure_poisson|PressureGaugeT|PeriodicLocalRegularity|ClassicalSolutionT' formalization/NSFormalization/Section4
```

It returned the analogues cited above (and existing `ClassicalSolutionR`/R42 fields), but no theorem with the U9d target binders.

4. **Hygiene note — minor.** The only concrete hygiene defect found is the extra blank line at EOF in `axioms_classical_assembly.lean:108`; remove it. The root checks also report pre-existing copied-source admission tokens (`BoundaryCorollary.lean:90`) and `source_hashes_match: false`; these are not in the lane diff and do not explain the rejection.

## 4. Commands and results

All Lean commands used `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, and ran from `verification/`; lake commands were run one at a time.

1. Module build (`lake build NSFormalization.Section3.T11.ClassicalAssembly`) exited 0. Exact beginning/end of the captured output:

```text
⚠ [8778/8930] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'
...
warning: NSFormalization/Paper1/PeriodicLocalLifespan.lean:587:13: Variable name `hS` is not explicitly referenced.
...
Build completed successfully (9978 jobs).
```

The warnings are replayed dependency warnings; none names `ClassicalAssembly.lean`.

2. Direct typechecks all exited 0 with no output:

```text
lake env lean ../formalization/NSFormalization/Section3/T11/ClassicalAssembly.lean
lake env lean ../research/T11/probes/classical_assembly_closes.lean
lake env lean ../research/T11/axioms_classical_assembly.lean
```

3. Reviewer negative mutation exited 1, as required:

```text
../research/T11/probes/rev320_negative_interval.lean:15:2: error: Type mismatch
  persistence_physical_sobolev h
has type
  ∀ (m : ℕ),
    ∃ G, ContinuousOn G (Ico 0 T) ∧ ∀ t ∈ Ico 0 T, IsPeriodicDatum (↑m) (fun x => torusPhysicalVelocity u (t, x)) (G t)
but is expected to have type
  ∀ (m : ℕ),
    ∃ G, ContinuousOn G (Ioo 0 T) ∧ ∀ t ∈ Ioo 0 T, IsPeriodicDatum (↑m) (fun x => torusPhysicalVelocity u (t, x)) (G t)
```

4. Root gates exited 0. `make check` ended with:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.043s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

`make test` exited 0 (the final replay reached `Tests.CompletedDensity`), and `make test-mutations` exited 0 with the exact final lines:

```text
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
```

Because `git diff --name-only origin/erenup/integration-section3...HEAD` contains no `verification/` path, the conditional `scripts/gates.sh` and `check_contracts.py --base-ref origin/erenup/integration-section3` reruns were not required; `make check` did run the ordinary contract policy check.

Fixes required:

- Prove the exact universal target from the one named `PersistenceInput`, including general pressure/gauge/Poisson, Duhamel time regularity, momentum and both structures; or revise the lane scope/brief before resubmission.
- Remove the trailing blank line in `research/T11/axioms_classical_assembly.lean:108`.

Verdict: REJECT
