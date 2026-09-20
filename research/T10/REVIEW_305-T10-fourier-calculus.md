REJECT

## 1. What the lane claims

The worker reports 23 exported theorems, with literal statements, in
`NSFormalization.Section3.T10` (`research/T10/REPORT_305.md:13` through
`research/T10/REPORT_305.md:170`). It also says that all five deliverable files
are new and that there are no instances or heartbeat overrides
(`research/T10/REPORT_305.md:172-180`).

The report is candid about its restricted vector scope: it exports only
componentwise summability, inversion, and a component sup bound; it does not
export a packaged vector H² construction or a vector integrated gradient
identity (`research/T10/REPORT_305.md:184-193`). It nevertheless says that all
requested scalar conclusions are proved (`research/T10/REPORT_305.md:184`) and
records every gate as passing (`research/T10/REPORT_305.md:196-208`).

## 2. What is in Lean

### Exact declaration audit

Every theorem whose statement is printed in the worker report exists, and its
statement is exactly the printed statement. The declaration starts are:

| Report claim | Lean source |
|---|---|
| `periodicFourierCoeff_fderiv` (`REPORT_305.md:14`) | `formalization/NSFormalization/Section3/T10/FourierCalculus.lean:16` |
| `periodicFourierCoeff_secondPartial` (`REPORT_305.md:21`) | `FourierCalculus.lean:22` |
| `norm_periodicFourierCoeff_le` (`REPORT_305.md:28`) | `FourierCalculus.lean:33` |
| `summable_periodicFourierCoeff_of_h2` (`REPORT_305.md:33`) | `FourierCalculus.lean:43` |
| `summable_periodicFourierCoeff_of_smooth` (`REPORT_305.md:39`) | `FourierCalculus.lean:48` |
| `periodic_eq_tsum_mFourier` (`REPORT_305.md:45`) | `FourierCalculus.lean:53` |
| `norm_le_tsum_norm_periodicFourierCoeff` (`REPORT_305.md:52`) | `FourierCalculus.lean:61` |
| `periodicFrequencyWeight_eq_paper1` (`REPORT_305.md:59`) | `FourierCalculus.lean:67` |
| `summable_weighted_periodicFourierCoeff` (`REPORT_305.md:64`) | `FourierCalculus.lean:79` |
| `periodicFourierCoeff_rapid_decay` (`REPORT_305.md:70`) | `FourierCalculus.lean:86` |
| `summable_inverse_periodicFrequencyWeight` (`REPORT_305.md:76`) | `FourierCalculus.lean:103` |
| `tsum_norm_periodicFourierCoeff_le` (`REPORT_305.md:81`) | `FourierCalculus.lean:110` |
| `periodicFourierCoeff_iteratedFDeriv` (`REPORT_305.md:89`) | `FourierCalculus.lean:140` |
| `norm_periodicFourierCoeff_iterated_le` (`REPORT_305.md:97`) | `FourierCalculus.lean:156` |
| `periodic_component_eq_tsum` (`REPORT_305.md:105`) | `FourierCalculus.lean:165` |
| `periodicFourierCoeff_laplacian` (`REPORT_305.md:114`) | `FourierCalculus.lean:175` |
| `scalarSpatialLaplacianT_eq` (`REPORT_305.md:122`) | `FourierCalculus.lean:205` |
| `summable_periodicFourierCoeff_component_of_smooth` (`REPORT_305.md:128`) | `FourierCalculus.lean:211` |
| `spatialPartial_complexify` (`REPORT_305.md:135`) | `FourierCalculus.lean:218` |
| `periodicFourierCoeff_scalarSpatialLaplacianT` (`REPORT_305.md:141`) | `FourierCalculus.lean:228` |
| `norm_periodicFourierCoeff_coordinate_decay` (`REPORT_305.md:151`) | `FourierCalculus.lean:245` |
| `norm_component_le_tsum_norm_periodicFourierCoeff` (`REPORT_305.md:159`) | `FourierCalculus.lean:255` |
| `periodicFourierCoeff_gradient_sq` (`REPORT_305.md:166`) | `FourierCalculus.lean:265` |

The normalization is faithful. The canonical weight is literally
`1 + 4 * π^2 * ∑ k_i^2` (`Section3/T10/PeriodicData.lean:68-69`), matching
the paper's unit-torus Sobolev weight (`paper/sections/01-introduction.tex:76-89`),
and the derivative symbol is literally `2π i k_j`
(`Section3/T10/PeriodicData.lean:184-187`). The derivative wrapper uses the
existing cube integration-by-parts theorem
(`Paper1/PeriodicFourierDerivative.lean:101-105`); inversion and the pointwise
bound use the existing torus reconstruction results
(`Paper1/FourierReconstructionAdapter.lean:127-131,162-166`). The Laplacian
formula has the correct negative `4π²|k|²` multiplier
(`FourierCalculus.lean:175-202`), and its identification with T11's scalar
Laplacian is definitionally correct (`FourierCalculus.lean:205-209` and
`Section3/T11/LocalTheory.lean:37-43`).

The decay/summability route is mathematically legitimate: the exact Bessel
weight is bridged at `FourierCalculus.lean:67-77`, all real weighted orders at
`FourierCalculus.lean:79-83`, rapid pointwise decay at
`FourierCalculus.lean:86-101`, inverse-weight summability at
`FourierCalculus.lean:103-108`, and the requested weighted Cauchy–Schwarz bound
at `FourierCalculus.lean:110-138`. This matches the paper's
`ℓ1 ← H²` argument and inverse fourth-power lattice sum
(`paper/sections/appendix-a-local-theory.tex:40-50`). The reused lattice theorem
is proved rather than assumed (`Paper1/PeriodicH2Embedding.lean:265-268`).

There is no hidden `ENNReal.toReal`, empty interval, or `⊤.toReal = 0`
totalization in any exported statement. All smoothness and periodicity
hypotheses are used. The apparently arbitrary `t` in
`scalarSpatialLaplacianT_eq` is not a vacuity device: it is the time argument of
T11's Laplacian applied to the explicitly time-independent lift
(`FourierCalculus.lean:205-209`).

The shipped examples contain both a constant and a single Fourier character
(`research/T10/probes/fourier_calculus_examples.lean:5-27`). The reviewer probe
also applies the main derivative theorem to the nonzero frequency
`reviewerMode`, whose zeroth coordinate is one
(`research/T10/probes/rev305_nonvacuity.lean:7-21`); it typechecks with no
output. Thus the main hypotheses are satisfiable by a nonconstant field.

### Axioms and hygiene

`research/T10/axioms_fourier_calculus.lean:2-24` audits all 23 declarations.
Every line printed exactly the set `[propext, Classical.choice, Quot.sound]`.
There are no occurrences of `sorry`, `admit`, `axiom`, `native_decide`, or
`maxHeartbeats` in the new Lean module, conformance file, or worker example
probe. There are no instance declarations in the module.

Relative to `origin/erenup/integration-section3`, the committed diff is exactly:

```text
A formalization/NSFormalization/Section3/T10/FourierCalculus.lean
A research/T10/ATTEMPTS_FOURIER_CALCULUS.md
A research/T10/REPORT_305.md
A research/T10/axioms_fourier_calculus.lean
A research/T10/probes/fourier_calculus_examples.lean
```

No existing module is modified. The lane commit is `2f6471b [305-T10]
FourierCalculus`.

## 3. Gaps

### Blocking: the all-order coefficient-path obligation is absent

The lane brief explicitly directs this Fourier-calculus lane to the T10 items
requiring smooth periodic forces to have coefficient paths at every order. The
underlying reconciliation asks for smooth, continuous/strongly measurable
coefficient paths and finite `L¹_t H^m_x` and `L²_t H^m_x` norms for every
integer order (`research/T10/COMPARISON.md:132-138`). The canonical predicates
that such a theorem must discharge are already present:
`IsPeriodicSobolevPath` at `Section3/T10/PeriodicData.lean:218-230` and
`MemForceT` at `Section3/T10/PeriodicData.lean:237-245`.

`FourierCalculus.lean` contains no occurrence of `IsPeriodicSobolevPath`,
`MemForceT`, or `forceSobolevENormT`. It proves fixed-slice weighted summability
(`FourierCalculus.lean:79-83`) and one fixed component's absolute summability
(`FourierCalculus.lean:211-216`), but neither constructs a bundled datum path nor
proves its time regularity/measurability or its `L¹/L²` finiteness. Exact
absence check:

```text
$ rg -n 'IsPeriodicSobolevPath|MemForceT|forceSobolevENormT|energyGradientT|coefficientEnergyGradientT|energyENormT|coefficientEnergyENormT' formalization/NSFormalization/Section3/T10/FourierCalculus.lean
exit=1
```

This is not a one-line review note; it is a missing requested theorem family.

### Blocking: no canonical vector physical/coefficient gradient-energy identity

T10's stated dependency is the scalar and vector full-gradient identity with
the exact `2πk` factors (`research/T10/COMPARISON.md:105-107`) and the
physical/coefficient gradient and energy identities
(`research/T10/COMPARISON.md:136-138`). T13 names the same full-gradient/frequency
bridge as a required T10 dependency (`research/T13/COMPARISON.md:101-111`). The
paper uses precisely the full gradient and Laplacian Fourier identities in the
periodic estimates (`paper/sections/03-torus.tex:467-477,490-500`; the exact
unit-torus derivative normalization is also stated at
`paper/sections/appendix-b-embeddings.tex:8-9,96-103`).

The lane proves a correct scalar identity at one frequency
(`FourierCalculus.lean:265-276`). It does not assemble it with vector Parseval
into an identity involving the canonical physical and coefficient quantities
`energyGradientT` and `coefficientEnergyGradientT`, defined at
`Section3/T10/PeriodicData.lean:333-356`. The report itself acknowledges that
the physical integrated vector identity is not re-exported
(`research/T10/REPORT_305.md:188-193`). Paper1's scalar H¹ sum theorem
(`Paper1/PeriodicSobolev.lean:26-51`) is useful input, but it is not the requested
canonical vector/energy conclusion.

The final instruction also asks for componentwise `SpatialField` versions of
the scalar calculus. The only explicit vector exports are inversion
(`FourierCalculus.lean:165-172`), component summability
(`FourierCalculus.lean:211-216`), and the component sup bound
(`FourierCalculus.lean:255-263`), exactly as the report admits
(`research/T10/REPORT_305.md:188-190`). There is no exported vector derivative,
rapid-decay, Laplacian, or full-gradient/energy corollary.

### Tree search for declared gaps

The report says these objects are "not asserted here," rather than claiming
they do not exist anywhere. I nevertheless ran the required whole-Section4
search before accepting that they are gaps:

```text
$ grep -rnE 'IsPeriodicSobolevPath|MemForceT|periodicFourierCoeff|periodicFrequencyWeight|coefficientEnergyGradientT|energyGradientT|IsPeriodicLambda|lambda_exists|hTwo_le_laplacian|gradientLSix' formalization/NSFormalization/Section4
formalization/NSFormalization/Section4/A05/HessianLaplacian.lean:14:convention enters (`research/A05/COMPARISON.md:128`: "the `gradientLSix` clause

$ grep -rnE 'vector.*(H.?2|Laplacian)|Laplacian.*(vector|norm)|full.gradient.*(Fourier|frequency)|gradient.*frequency' formalization/NSFormalization/Section4
formalization/NSFormalization/Section4/A04/NonlinearColumns.lean:41:  (`LaplacianDatum.lean:96`) with a general column family; each column norm is `‖Cⱼ‖` by
formalization/NSFormalization/Section4/C01/EnstrophyBounds.lean:65:/-- The squared Laplacian norm is continuous on every closed solution slab,
```

These are unrelated whole-space/cylinder hits, not canonical T10 torus lemmas.
No contrary Section4 theorem was found.

### Negative mutation

The reviewer changed the Laplacian multiplier from negative to positive in
`research/T10/probes/rev305_negative_laplacian_sign.lean:7-14`. This is a
substantive sign mutation of a main statement, not a dropped argument. It fails
for the expected reason:

```text
../research/T10/probes/rev305_negative_laplacian_sign.lean:14:2: error: Type mismatch: After simplification, term
  periodicFourierCoeff_laplacian hp hs k
 has type
  periodicFourierCoeff (fun x => ∑ j, spatialPartial j (spatialPartial j f) x) k =
    -((4 * ↑Real.pi ^ 2 * ∑ x, ↑(k x) ^ 2) * periodicFourierCoeff f k)
but is expected to have type
  periodicFourierCoeff (fun x => ∑ j, spatialPartial j (spatialPartial j f) x) k =
    (4 * ↑Real.pi ^ 2 * ∑ x, ↑(k x) ^ 2) * periodicFourierCoeff f k
```

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, were invoked from
`verification/`, and used `LEAN_NUM_THREADS=6`.

1. `lake build NSFormalization.Section3.T10.FourierCalculus` exited 0. It was
   not globally silent because Lake replayed warnings from pre-existing
   dependencies; no warning names `FourierCalculus.lean`. Exact final line:

   ```text
   Build completed successfully (9909 jobs).
   ```

   The replayed modules were
   `NSFormalization.Source.FiniteHilbertBochner`,
   `NSFormalization.Paper1.PeriodicSobolevHilbert`,
   `NSFormalization.Paper1.PeriodicH2Embedding`,
   `NSFormalization.Source.RealSobolev`,
   `NSFormalization.Paper3.SpatiallyCompactTime`,
   `NSFormalization.Paper3.RealPositiveDensity`,
   `NSFormalization.Paper3.RealVectorPositiveDensity`,
   `NSFormalization.Source.PacketForceExtension`,
   `NSFormalization.Source.ViscosityPacket`,
   `NSFormalization.Source.PhysicalBesselSobolev`, and
   `NSFormalization.Paper3.SobolevDirectionalDerivative`.

2. `lake env lean ../formalization/NSFormalization/Section3/T10/FourierCalculus.lean`
   exited 0 with exactly zero output.

3. `lake env lean ../research/T10/probes/fourier_calculus_examples.lean`
   exited 0 with exactly zero output.

4. `lake env lean ../research/T10/axioms_fourier_calculus.lean` exited 0. The
   exact axiom result for each declaration was:

   ```text
   periodicFourierCoeff_fderiv: [propext, Classical.choice, Quot.sound]
   periodicFourierCoeff_secondPartial: [propext, Classical.choice, Quot.sound]
   norm_periodicFourierCoeff_le: [propext, Classical.choice, Quot.sound]
   summable_periodicFourierCoeff_of_h2: [propext, Classical.choice, Quot.sound]
   summable_periodicFourierCoeff_of_smooth: [propext, Classical.choice, Quot.sound]
   periodic_eq_tsum_mFourier: [propext, Classical.choice, Quot.sound]
   norm_le_tsum_norm_periodicFourierCoeff: [propext, Classical.choice, Quot.sound]
   periodicFrequencyWeight_eq_paper1: [propext, Classical.choice, Quot.sound]
   summable_weighted_periodicFourierCoeff: [propext, Classical.choice, Quot.sound]
   periodicFourierCoeff_rapid_decay: [propext, Classical.choice, Quot.sound]
   summable_inverse_periodicFrequencyWeight: [propext, Classical.choice, Quot.sound]
   tsum_norm_periodicFourierCoeff_le: [propext, Classical.choice, Quot.sound]
   periodicFourierCoeff_iteratedFDeriv: [propext, Classical.choice, Quot.sound]
   norm_periodicFourierCoeff_iterated_le: [propext, Classical.choice, Quot.sound]
   periodic_component_eq_tsum: [propext, Classical.choice, Quot.sound]
   periodicFourierCoeff_laplacian: [propext, Classical.choice, Quot.sound]
   scalarSpatialLaplacianT_eq: [propext, Classical.choice, Quot.sound]
   summable_periodicFourierCoeff_component_of_smooth: [propext, Classical.choice, Quot.sound]
   spatialPartial_complexify: [propext, Classical.choice, Quot.sound]
   periodicFourierCoeff_scalarSpatialLaplacianT: [propext, Classical.choice, Quot.sound]
   norm_periodicFourierCoeff_coordinate_decay: [propext, Classical.choice, Quot.sound]
   norm_component_le_tsum_norm_periodicFourierCoeff: [propext, Classical.choice, Quot.sound]
   periodicFourierCoeff_gradient_sq: [propext, Classical.choice, Quot.sound]
   ```

5. Root `make check` exited 0. Its complete output was 43,333 lines / 1,785,368
   bytes, so the exact head and tail are pasted rather than duplicating the
   generated contract-closure JSON:

   ```text
   python3 experiments/check_formalization_plan.py --check
   {
     "task_count": 45,
     "source_counts": {
       "formalization": 560,
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
   {
   ... generated closure JSON omitted (43,283 lines) ...
     "base_compatibility_checked": false,
     "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
   }
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.044s

   OK
   python3 experiments/check_work_queue.py
   45 work items: ownership, contract registration and task cards consistent.
   ```

   The copied-source `sorry` reported here is the pre-existing excluded
   `Paper1/BoundaryCorollary.lean:90`, not in this lane's import closure or diff.

6. Reviewer non-vacuity probe:
   `lake env lean ../research/T10/probes/rev305_nonvacuity.lean` exited 0 with
   exactly zero output.

7. Reviewer mutation probe:
   `lake env lean ../research/T10/probes/rev305_negative_laplacian_sign.lean`
   exited 1 with the exact expected error pasted in Part 3.

8. `git diff --check origin/erenup/integration-section3...HEAD` exited 0 with
   zero output. The forbidden-token/heartbeat scan also had zero output.

9. `scripts/gates.sh` and
   `check_contracts.py --base-ref origin/erenup/integration-section3` were not
   applicable: `git diff --name-only origin/erenup/integration-section3...HEAD -- verification`
   had exactly zero output, so `verification/` was not touched.

Required fixes before acceptance:

1. Export the all-integer-order periodic coefficient datum paths for
   `MemForceT`, including the continuous/strongly measurable path and finite
   `L¹` and `L²` conclusions required by T10 item 11.
2. Export the canonical vector physical/coefficient full-gradient (and energy)
   identity using `energyGradientT`/`coefficientEnergyGradientT`, with the exact
   `2πk` factors, rather than stopping at the scalar per-frequency identity.
3. Add the remaining requested componentwise `SpatialField` calculus
   corollaries (at least derivative symbol/decay/Laplacian/full gradient), then
   extend the conformance and axioms files to audit them.

