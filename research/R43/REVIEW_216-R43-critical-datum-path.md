ACCEPT

## 1. What the lane claims

The worker claims a conditional construction of the exact lane-175
`CriticalDatumPath`, not an unconditional proof.  The report says that all six
slicewise homogeneous data and all four spatial compatibility fields are proved,
while the two time facts are isolated in one `CriticalDatumInputs` structure
(`research/R43/REPORT_216.md:5-19`, `research/R43/REPORT_216.md:41-58`).  It also
claims the no-`hcrit` corollary `rcritical1_of_classical` with the exact
eq:Rcritical1 conclusion (`research/R43/REPORT_216.md:15-19`).

These claims are faithful to the brief and the mathematics:

* The paper defines `y`, `z`, and `b` at the homogeneous half orders and states
  `1/2 (y²)' + (ν - C₀ y) z² ≤ b y` at
  `paper/sections/04-whole-space.tex:91-99`.  The local-theory appendix states
  the standard `C^j_t H^k_x` regularity for every `j,k` at
  `paper/sections/appendix-a-local-theory.tex:65-76`.
* The consumer has exactly the six paths, six datum fields, smoothness,
  momentum, order shift, Laplacian symbol, transverse velocity, and longitudinal
  pressure at `formalization/NSFormalization/Section4/R43/CriticalPairing.lean:161-201`.
* The delivered fallback has exactly the two missing consumer fields—
  `ContDiffOn` on `Ico 0 T` and the datum momentum equation on `Ioo 0 T`—at
  `formalization/NSFormalization/Section4/R43/CriticalDatumPath.lean:693-710`.
  It adds no spatial existence, sign, estimate, trilinear, or pairing premise.
  The unused `_hf` structure index is honest: `hf` is needed to construct the
  pressure and force fields, but the two isolated time statements themselves do
  not inspect its proof term.
* The assembly copies every consumer field without weakening it at
  `formalization/NSFormalization/Section4/R43/CriticalDatumPath.lean:714-737`.
  `exists_criticalDatumPath` has exactly the advertised conditional type at
  `formalization/NSFormalization/Section4/R43/CriticalDatumPath.lean:739-749`.
  No separate `0 < T` premise is needed because it is already the
  `ClassicalSolutionR.horizon_pos` field
  (`formalization/NSFormalization/Section4/A02/SolutionClass.lean:114-120`).
  Omitting `0 < ν` makes the carrier theorem stronger and does not weaken or
  vacuously discharge any obligation.
* `rcritical1_of_classical` has no `hcrit` binder and its conclusion is
  token-for-token the conclusion of `rcritical1_of_hcrit'`
  (`formalization/NSFormalization/Section4/R43/CriticalDatumPath.lean:751-767`,
  `formalization/NSFormalization/Section4/R43/Parseval.lean:138-151`).
  In particular, the dissipative sign is the paper's `ν - C₀ y` sign.

There is no `⊤.toReal = 0` escape.  Supplied homogeneous data make each infimum
equal to a finite Hilbert norm
(`formalization/NSFormalization/Section4/R43/CriticalPairing.lean:62-91`).  The
interval is nonempty because `0 < T`, and the conformance theorem constructs the
two-field fallback for the genuine `A04.zeroSol` and then instantiates
`Nonempty (CriticalDatumPath ...)`
(`research/R43/axioms_critical_datum.lean:53-107`).  This is the exact
non-vacuity instance requested by the brief.  The named input is also a standard
restriction for nonzero classical solutions: the appendix's
`C^j_t H^k_x` statement and the physical momentum equation are precisely the
two facts being transported, rather than a special zero-only or empty-interval
condition.

## 2. What is in Lean

The implementation matches the report field by field.

* The bounded multiplier is literally
  `|ξ|^s (1+|ξ|²)^(-s/2)`
  (`formalization/NSFormalization/Source/BesselFractionalData.lean:11-32`).
  Its real-subspace preservation and physical-distribution identification are
  proved at
  `formalization/NSFormalization/Section4/R43/CriticalDatumPath.lean:42-130`,
  and the vector/smooth-field constructors are at the same file's lines
  `132-161`.  Thus this is actual Fourier content, not an existential field
  restatement.
* The six definitions occur at
  `formalization/NSFormalization/Section4/R43/CriticalDatumPath.lean:193-226`;
  the six datum theorems occur at lines `228-293`.  The needed tree lemmas really
  state smooth square-integrable jets for velocity, Laplacian, advection, force,
  and pressure gradient
  (`formalization/NSFormalization/Section4/C01/VelocityJets.lean:83-89`,
  `formalization/NSFormalization/Section4/D01/Pressure.lean:220-239`,
  `formalization/NSFormalization/Section4/D01/Pressure.lean:289-309`,
  `formalization/NSFormalization/Section4/D01/PressureJets.lean:121-135`).
  In particular, `criticalForceHalf_isDatum` assumes only `MemForceR f` and
  `0 ≤ t`; G3 needs no extra premise for its slicewise claim.
* The exact order shift, negative Laplacian multiplier, transverse velocity,
  and longitudinal pressure statements are at
  `formalization/NSFormalization/Section4/R43/CriticalDatumPath.lean:318-356`,
  `:508-555`, `:557-624`, and `:626-691`.  Their conclusions match the consumer
  fields at `CriticalPairing.lean:189-201`, including the minus sign and the
  `Ioo` time interval.
* Every declaration in the new module is listed in the axiom audit
  (`research/R43/axioms_critical_datum.lean:15-51`), followed by the fallback
  witness (`research/R43/axioms_critical_datum.lean:53-99`).  All 38 outputs are
  exactly `[propext, Classical.choice, Quot.sound]`.

Hygiene is clean.  The forbidden-token scan found no declaration containing
`sorry`, `admit`, `axiom`, or `native_decide`; neither lane Lean file contains
`maxHeartbeats`.  The base diff adds one formalization module and research
records only; it modifies no existing Lean module.  The required split updates
accurately describe G3/S6 as slicewise-only
(`research/R43/R43_SPLIT.md:207-232`).

## 3. Gaps

The two declared residual gaps are honest and outside the theorem actually
claimed.

1. The tree does not export the homogeneous half-order `ContDiffOn` path and
   its physical momentum derivative for an arbitrary `ClassicalSolutionR`.
   Whole-`Section4` searches for homogeneous/momentum and for a time-regular
   `IsHomogeneousSliceDatum` found no theorem supplying those facts; apart from
   the consumer field, the only exact occurrence is this lane's
   `CriticalDatumInputs`.  The closest inhomogeneous A01 result differentiates a
   Duhamel carrier (`formalization/NSFormalization/Section4/A01/DatumPathDeriv.lean:344-420`)
   and leaves physical representative identification conditional
   (`formalization/NSFormalization/Section4/A01/DatumPathDeriv.lean:440-455`).
   This agrees with the earlier worker report
   (`research/A01/REPORT_169.md:105-120`).
2. Slicewise force data do not by themselves prove a strongly measurable,
   `L¹_t` homogeneous datum path.  The whole-tree search found only compact or
   separated-force measurability results and conditional homogeneous-norm
   equalities.  The canonical D01 module explicitly records strong
   measurability as missing
   (`formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean:21-29`)
   and defines the infimum over paths carrying that extra property at lines
   `621-630`.  Thus the report's remaining G2/G3/S6 path-level gap is accurate;
   it is not a hidden premise in `CriticalDatumPath`.

No additional gap, duplicated consumer structure, incorrect citation, or
vacuous hypothesis was found.

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`; every `lake` command
was run from `verification/` with `LEAN_NUM_THREADS=6`.

### Environment setup

```text
$ bash scripts/lean-install.sh
elan 4.2.4 (227caca13 2026-08-25)
info: toolchain 'leanprover/lean4:v4.34.0-rc2' is already installed
Lean (version 4.34.0-rc2, x86_64-unknown-linux-gnu, commit 6a10ac8c22beadecabdbb0919c2b50214762f91d, Release)
== lake exe cache get
Current branch: HEAD
Using cache from origin: (some leanprover-community/mathlib4)
No files to download
Already decompressed 8747 file(s)
== lake test
...
== OK
```

Exit 0.  The package directory was the expected shared symlink:

```text
verification/.lake/packages -> /data_8T/ping/blowup_density/verification/.lake/packages
```

### Target build and direct typecheck

```text
$ cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R43.CriticalDatumPath
[262 lines, 14979 bytes: replayed warnings from pre-existing dependencies]
...
Build completed successfully (10269 jobs).
```

Exit 0.  No output line names `CriticalDatumPath.lean`; the new module itself is
silent.  The exact beginning is a replayed warning from
`NSFormalization.Source.FiniteHilbertBochner`, and the exact last line is shown
above.

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/R43/CriticalDatumPath.lean
<no output>
```

Exit 0.

### Axioms and non-vacuity

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R43/axioms_critical_datum.lean
'NSFormalization.Section4.R43.CriticalHomogeneous.besselFractionalDatum_mem_realSubspace' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.CriticalHomogeneous.ofSobolevScalar' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.CriticalHomogeneous.ofSobolevScalar_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.CriticalHomogeneous.ofSobolevScalar_weight_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.CriticalHomogeneous.ofSobolevScalar_isHomogeneousDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.CriticalHomogeneous.ofSobolevVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.CriticalHomogeneous.ofSobolevVector_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.CriticalHomogeneous.ofSobolevVector_isHomogeneousSliceDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.CriticalHomogeneous.ofSmoothL2' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.CriticalHomogeneous.ofSmoothL2_isHomogeneousSliceDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.chosenHomogeneousDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.chosenHomogeneousDatum_isDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.exists_isHomogeneousSliceDatum_of_smoothL2' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalVelocityHalf' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalVelocityThreeHalf' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalLaplacianHalf' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalAdvectionHalf' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalPressureHalf' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalForceHalf' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalVelocityHalf_isDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalVelocityThreeHalf_isDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalLaplacianHalf_isDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalAdvectionHalf_isDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalPressureHalf_isDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalForceHalf_isDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.orderZeroDatum_angular_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalVelocity_order_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.componentLp_laplacianField' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.fourier_laplacianField_component_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.angular_laplacianField_component_ae' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalLaplacian_symbol' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalVelocity_transverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalPressure_longitudinal' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.CriticalDatumInputs' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalDatumPath' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.exists_criticalDatumPath' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.rcritical1_of_classical' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.zeroCriticalDatumInputs' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exit 0.  Lean wrapped some sets across physical output lines; the sets above are
the exact reflowed contents.  The final non-vacuity `example` is silent and
closes.

### Substantive negative mutation

The permitted scratch probe
`research/R43/probes/rev216_mutation_fail.lean:9-24` changes the main energy
coefficient from `ν - trilinearConst * y` to
`ν + trilinearConst * y`.  It does not drop an argument.

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R43/probes/rev216_mutation_fail.lean
../research/R43/probes/rev216_mutation_fail.lean:24:2: error: Type mismatch
  rcritical1_of_classical w hf hinputs
has type
  ... (ν - trilinearConst * criticalNormAt w.velocity t) *
        criticalDissipationAt w.velocity t ^ 2 ≤ ...
but is expected to have type
  ... (ν + trilinearConst * criticalNormAt w.velocity t) *
        criticalDissipationAt w.velocity t ^ 2 ≤ ...
```

Exit 1, exactly as expected.

### Repository and hygiene gates

```text
$ make check
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 532,
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
... generated closure JSON omitted (28234 output lines total) ...
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.048s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

Exit 0.  The copied `BoundaryCorollary.lean` and source-hash notices are the
pre-existing repository notices identified by the worker, not lane changes.
The exact first and last output blocks are pasted; the generated 1,159,606-byte
closure listing is intentionally not duplicated.

```text
$ git diff --name-status origin/erenup/integration...HEAD
A formalization/NSFormalization/Section4/R43/CriticalDatumPath.lean
A research/R43/ATTEMPTS_CRITICAL_DATUM.md
M research/R43/R43_SPLIT.md
A research/R43/REPORT_216.md
A research/R43/axioms_critical_datum.lean

$ git diff --name-only origin/erenup/integration...HEAD -- verification
<no output>

$ rg -n "\\b(sorry|admit|native_decide)\\b|^[[:space:]]*axiom[[:space:]]" formalization/NSFormalization/Section4/R43/CriticalDatumPath.lean research/R43/axioms_critical_datum.lean
<no output>

$ rg -n "maxHeartbeats" formalization/NSFormalization/Section4/R43/CriticalDatumPath.lean research/R43/axioms_critical_datum.lean
<no output>

$ git diff --check origin/erenup/integration...HEAD
<no output>
```

The explicit `scripts/gates.sh` and
`experiments/check_contracts.py --base-ref origin/erenup/integration` gates are
not applicable: the base diff contains no path under `verification/`.  The
ordinary contract architecture check nevertheless ran successfully as part of
`make check`.

Fixes: none.
