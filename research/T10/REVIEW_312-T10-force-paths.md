ACCEPT

## What the lane claims

The worker report claims an all-order coefficient-path construction for every
`MemForceT` force, including continuity, compact temporal support, strong
measurability, every-time `IsPeriodicDatum` (with the integrability conjunct),
and finite time `L^q` norms; it identifies `MemForceT` with Paper1's
`IsTestForce` (`research/T10/REPORT_312.md:5-16,19-41`).  It also claims the
vector Frobenius gradient Parseval identity, the homogeneous-gradient identity,
the physical/coefficient energy identity, and componentwise derivative,
decay, Laplacian, and gradient corollaries (`research/T10/REPORT_312.md:43-108`).
The report explicitly limits the path regularity to `Continuous`, and explicitly
does not claim the separate inhomogeneous intersection sum-norm comparison
(`research/T10/REPORT_312.md:133-140`).

The paper's force class is smooth and compactly supported in the positive-time
torus class (`paper/sections/02-preliminaries.tex:7-25`), while the paper's
time-norm convention is on `(0,∞)` and its fixed-positive-horizon energy is the
`L^∞_tL²_x + L²_t` full-gradient norm
(`paper/sections/01-introduction.tex:118-150`).  The unit-torus coefficient
normalization is the `(1+4π²|k|²)^s` weight and `2π` Fourier convention
(`paper/sections/01-introduction.tex:80-107`).

## What is in Lean

Statement fidelity checks passed.  The canonical predicates have exactly the
fields the lane uses: `IsPeriodicDatum` includes spatial periodicity,
Haar-integrability, and the component-then-frequency coefficient equation
(`formalization/NSFormalization/Section3/T10/PeriodicData.lean:104-114`);
`IsPeriodicSobolevPath` quantifies only over nonnegative time
(`formalization/NSFormalization/Section3/T10/PeriodicData.lean:218-223`);
`forceSobolevENormT` is the infimum over such paths and strongly measurable
representatives (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:224-230`);
and `MemForceT` is precisely global smoothness, periodicity on `univ`, and a
compact positive-time support (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:237-245`).
The Paper1 interface has the same three fields (`formalization/NSFormalization/Paper1/PeriodicForceSpace.lean:19-25`),
and `memForceT_iff_isTestForce` is proved by a direct fieldwise equivalence
(`formalization/NSFormalization/Section3/T10/ForcePaths.lean:14-16`).

The main path statements are exactly present at
`ForcePaths.lean:25-43` (`smooth_periodic_datum`), `:82-107`
(`continuous_datum_path`), `:109-142` (`force_coefficient_path`), and
`:144-148` (`forceSobolevENormT_ne_top`).  The latter ranges over every
`q : ℝ≥0∞`, hence includes the requested `1` and `2`; no `⊤.toReal` or
empty-interval totalization is used.  The probe supplies both the zero force
and a genuinely nonzero single Fourier mode with a smooth bump supported in
`[3/2,5/2]` (`research/T10/probes/force_paths_examples.lean:10-15,19-67`).

The componentwise calculus claimed in the report is present verbatim at
`ForcePaths.lean:150-187` (derivative, rapid decay, Laplacian, and frequencywise
vector-gradient square), `:410-439` (the T12 tensor-entry and vector-Laplacian
wrappers), and `:189-245` (tensor-entry identification and `MemLp`).  The
underlying scalar signs and constants agree with the existing calculus:
`periodicDerivativeSymbol` is `2π i k_j`
(`formalization/NSFormalization/Section3/T10/PeriodicData.lean:184-187`),
the scalar Laplacian multiplier is negative
(`formalization/NSFormalization/Section3/T10/FourierCalculus.lean:174-202`),
and the scalar gradient-square identity is the exact `4π²|k|²` identity
(`formalization/NSFormalization/Section3/T10/FourierCalculus.lean:265-276`).

The vector identity and energy bridge are also exactly the report's statements:
`gradientTensor` is the canonical T12 Frobenius tensor
(`formalization/NSFormalization/Section3/T12/MeanZeroCalculus.lean:82-90`),
`gradientTensor_parseval` is at `ForcePaths.lean:206-245`,
`gradient_eq_homogeneousENorm` at `:357-368`, and the energy theorem at
`:377-392`.  The energy definitions it unfolds are the canonical physical and
coefficient halves (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:327-356`).
Its hypotheses are only spatial smoothness and periodicity on `Ioo (0,T)`;
this is sufficient for the a.e. equalities under the restricted measure and is
strictly enough to instantiate the paper's smooth-on-`[0,T]`, `T>0` use case.
No time measurability hypothesis is silently needed.

For completeness, I matched every declaration listed by the report against
the source (the report's exact statement blocks are at
`research/T10/REPORT_312.md:19-115`):

| declarations | source lines |
|---|---|
| `memForceT_iff_isTestForce`, `memLp_torusLift_vector`, `smooth_periodic_datum`, `periodicSobolevENorm_eq`, `norm_scalar_datum_nat`, `datum_sub`, `continuous_datum_path` | `ForcePaths.lean:14-107` |
| `force_coefficient_path`, `forceSobolevENormT_ne_top` | `ForcePaths.lean:109-148` |
| `periodicFourierCoeff_component_derivative`, `periodicFourierCoeff_component_decay`, `periodicFourierCoeff_component_laplacian`, `periodicFourierCoeff_vector_gradient_sq` | `ForcePaths.lean:150-187` |
| `gradientTensor_component`, `memLp_gradientTensor`, `gradientTensor_parseval` | `ForcePaths.lean:189-245` |
| `angularFrequencySq_nonneg`, `homogeneousDatumWeight_one`, `summable_angular_component`, `norm_sqrt_angular_smul_sq` | `ForcePaths.lean:247-278` |
| `smooth_homogeneous_datum_one`, `homogeneousENorm_one_eq`, `angular_meanZeroPart`, `gradient_eq_homogeneousENorm`, `sobolevENorm_zero_eq` | `ForcePaths.lean:280-375` |
| `energyENormT_eq`, `memForceT_time_smul`, `periodicFourierCoeff_gradientTensor`, `periodicFourierCoeff_vector_laplacian` | `ForcePaths.lean:377-439` |

The committed source diff relative to the requested base is exactly the new
module and the lane records, plus the requested comparison note
(`git diff --name-only origin/erenup/integration-section3...HEAD`); no existing
Lean module, contract, registry, or status file is modified
(`research/T10/REPORT_312.md:117-131`).  The forbidden-declaration scan found
no `sorry`, `admit`, `axiom`, `native_decide`, or heartbeat override in the
module or worker probe.  The axioms file necessarily contains `#print axioms`
commands; all 29 audited declarations report exactly
`[propext, Classical.choice, Quot.sound]` (`research/T10/axioms_force_paths.lean:5-62`).

## Gaps

There is no acceptance-blocking gap.  The report's two scope notes are honest:
coefficient-valued `ContDiff` is not claimed (continuous paths are explicitly
allowed by the lane), and the broader inhomogeneous intersection norm
comparison is not part of the Goal-2 identity proved here
(`research/T10/REPORT_312.md:133-140`).  The universal `T : ℝ` energy theorem
also remains meaningful for the requested positive finite horizons; its proof
does not rely on an empty interval.

I performed the required whole-Section4 search before accepting those scope
claims.  The exact `grep -rn` search for all lane names produced no matching
Section4 theorem; the only broad gradient/Fourier hits were unrelated Leray
comments at `formalization/NSFormalization/Section4/D01/LeraySymbol.lean:137`,
`formalization/NSFormalization/Section4/D01/LerayMultiplier.lean:255`, and
`formalization/NSFormalization/Section4/A01/LerayBridge.lean:75`.

The substantive negative check was a sign mutation, not argument deletion.  In
`research/T10/probes/rev312_negative_laplacian_sign.lean:10-17`, the main
component Laplacian conclusion was changed from `-periodicAngularFrequencySq`
to `+periodicAngularFrequencySq`; Lean rejected it with:

```text
error: Type mismatch
  periodicFourierCoeff_component_laplacian hp hs i k
has type ... = -↑(periodicAngularFrequencySq k) * ...
but is expected to have type ... = ↑(periodicAngularFrequencySq k) * ...
```

## Commands and results

All commands sourced `. scripts/lean-env.sh`; Lake commands ran from
`verification/` with `LEAN_NUM_THREADS=6`.

* `LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T10.ForcePaths`:
  exit 0, exact final line `Build completed successfully (9945 jobs).`  The
  output only replayed dependency warnings; no warning named `ForcePaths`.
* `lake env lean ../formalization/NSFormalization/Section3/T10/ForcePaths.lean`:
  exit 0, zero output.
* `lake env lean ../research/T10/probes/force_paths_examples.lean`:
  exit 0, zero output.
* `lake env lean ../research/T10/axioms_force_paths.lean`:
  exit 0; all 29 `#print axioms` results are exactly
  `[propext, Classical.choice, Quot.sound]`.
* `make check`: exit 0.  Exact tail:

```text
.............
----------------------------------------------------------------------
Ran 13 tests in 0.051s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

  The check also reports the repository's pre-existing copied-source audit
  (11 admission tokens and `source_hashes_match: false`); none is in this lane.
* `BASE_REF=origin/erenup/integration-section3 LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T10.ForcePaths`:
  exit 0, exact tail ends `Mutation suite passed. This is an infrastructure
  check, not a PDE proof.`, `base_compatibility_checked: true`, and `== gates OK`.
  The direct `python3 experiments/check_contracts.py --base-ref
  origin/erenup/integration-section3` also exited 0.
* `LEAN_NUM_THREADS=6 make test-mutations`: exit 0; `implementation_refactor:
  accepted`, `admitted_proof: rejected as required`, `extra_axiom: rejected as
  required`, and `weakened_hypothesis: rejected as required`.
* `git diff --check`: exit 0.

No git state was changed by this review; the only added file is the permitted
negative probe and this review report.
