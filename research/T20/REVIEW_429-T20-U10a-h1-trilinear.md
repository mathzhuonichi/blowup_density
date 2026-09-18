ACCEPT-WITH-NOTES

## what the lane claims

The worker claims the mean-zero torus (H^1) trilinear estimate from
`paper/sections/03-torus.tex:467-477`, with
`h1TrilinearConst = CcriticalHalf * Csix`, the `ℝ≥0∞` form, the finite
`toReal` form, pairing/slice bridges, a nonzero cosine witness, and standard
axioms (`research/T20/REPORT_429.md:7-41`).  The claimed target is the theorem
printed in the report at `research/T20/REPORT_429.md:14-20`.

The paper says exactly
`|⟪(v·∇)v, Δv⟫| ≤ ‖v‖₃ ‖∇v‖₆ ‖Δv‖₂ ≤ C₁ y ‖Δv‖₂²`
(`paper/sections/03-torus.tex:467-477`).  The cited consumer defines
`laplacianSqT v` as `(periodicLpENorm 2 (laplacian v)).toReal ^ 2`
(`formalization/NSFormalization/Section3/T20/CriticalRegularity.lean:96-99`),
and the `hOneEnergy` field consumes precisely that spelling
(`formalization/NSFormalization/Section3/T20/CriticalRegularity.lean:330-342`).

## what is in Lean

The implementation theorem is present with the claimed binders and conclusion
at `formalization/NSFormalization/Section3/T20/H1Trilinear.lean:329-336`:
`SmoothPeriodicT v`, `MemPeriodicHomogeneous (1 / 2) v`, the lifted Haar
integral, and `h1TrilinearConst * (periodicHomogeneousENorm (1 / 2) v).toReal *
laplacianSqT v`.  The hypotheses are honest: `SmoothPeriodicT` is smoothness
plus spatial periodicity and `MemPeriodicHomogeneous` is periodicity, physical
`L²`, mean zero, and finite homogeneous norm
(`formalization/NSFormalization/Section3/T12/MeanZeroCalculus.lean:57-73`).
There is no empty interval, `⊤.toReal = 0` shortcut, unused named input, or
vacuous conclusion.

The constant and positivity are exactly at
`formalization/NSFormalization/Section3/T20/H1Trilinear.lean:250-257`;
the source constants and positivity are
`formalization/NSFormalization/Section3/T12/CriticalL3.lean:134-140`
and `formalization/NSFormalization/Section3/T12/GradientLSix.lean:611-620`.
The proof route is visible in the pointwise estimate
(`formalization/NSFormalization/Section3/T20/H1Trilinear.lean:121-140`), the
`(3,6,2)` Hölder instance
(`formalization/NSFormalization/Section3/T20/H1Trilinear.lean:142-218`), and
the physical integral estimate
(`formalization/NSFormalization/Section3/T20/H1Trilinear.lean:220-246`).  The
two embedding statements match the
produced norms exactly: `velocityCriticalL3` is
`formalization/NSFormalization/Section3/T12/CriticalL3Density.lean:515-524`,
and `gradientLSix` is
`formalization/NSFormalization/Section3/T12/GradientLSix.lean:639-644`; the
cited Fourier comparison is indeed
internal to `periodicLpENorm_gradientTensor_le_laplacian`
(`formalization/NSFormalization/Section3/T12/GradientLSix.lean:167-170`).

The `ℝ≥0∞` theorem and finite conversion are at
`formalization/NSFormalization/Section3/T20/H1Trilinear.lean:259-321`; the
pairing and exact U10b slice forms are at
`formalization/NSFormalization/Section3/T20/H1Trilinear.lean:340-371`.  The
positive non-vacuity probe proves a
nonzero smooth mean-zero cosine witness and finite Laplacian norm
(`research/T20/probes/h1_trilinear_closes.lean:115-208`), then checks the
`meanFreeVelocity` slice spelling required by U10b
(`research/T20/probes/h1_trilinear_closes.lean:210-231`).

## gaps

One upstream assembly note remains, accurately disclosed by the report: the
same theorem name `NSFormalization.Section3.T12.contDiff_dirDeriv` occurs in
`formalization/NSFormalization/Section3/T12/GradientLSix.lean:182-186` and
`formalization/NSFormalization/Section3/T12/GradientLambdaL3.lean:208-212`.
`CriticalTrilinear` imports the latter
(`formalization/NSFormalization/Section3/T20/CriticalTrilinear.lean:1-3`), so
the intended combined U10b/U13 import currently fails; the independent probe
`research/T20/probes/rev429_collision.lean:1-2` reproduces the exact error:

```
../research/T20/probes/rev429_collision.lean:1:0: error: import NSFormalization.Section3.T12.GradientLSix failed, environment already contains 'NSFormalization.Section3.T12.contDiff_dirDeriv' from NSFormalization.Section3.T12.GradientLambdaL3
```

This agrees with the report's recorded error (`research/T20/REPORT_429.md:47-58`).
This is not a defect in the delivered U10a theorem: this lane deliberately
uses only the `GradientLSix` side and repeats the four helpers under distinct
`H1` names
(`formalization/NSFormalization/Section3/T20/H1Trilinear.lean:94-140`).

Whole-tree grep of `formalization/NSFormalization/Section4` found no missing
torus `h1Trilinear`, `(3,6,2)` Hölder, or `gradientLSix` theorem (the only
`gradientLSix` hit is a distinct explanatory reference in
`Section4/A05/HessianLaplacian.lean:14`).  The exact one-line assembly fix is
upstream: remove/rename the duplicate specialized theorem at
`formalization/NSFormalization/Section3/T12/GradientLambdaL3.lean:210-212` and
reuse the general declaration from
`formalization/NSFormalization/Section3/T12/GradientLSix.lean:184-186` (or
move that general declaration to a shared module).  No lane-429 source change
is required.

The required substantive negative check was run in the added scratch probe
`research/T20/probes/rev429_negative_const.lean:13-24`: replacing `C₁` by
`C₁ - 1` causes the expected Lean type mismatch, not an argument-dropping
failure:

```
../research/T20/probes/rev429_negative_const.lean:24:2: error: Type mismatch
  h1Trilinear v hv hhalf
has type
  |∫ (y : PeriodicTorus),
        torusLift (fun x => inner ℝ (advection (lift v) 0 x) (laplacian v x)) y ∂periodicTorusMeasure| ≤
    h1TrilinearConst * (periodicHomogeneousENorm (1 / 2) v).toReal * laplacianSqT v
but is expected to have type
  |∫ (y : PeriodicTorus),
        torusLift (fun x => inner ℝ (advection (lift v) 0 x) (laplacian v x)) y ∂periodicTorusMeasure| ≤
    (h1TrilinearConst - 1) * (periodicHomogeneousENorm (1 / 2) v).toReal * laplacianSqT v
```

No forbidden implementation token occurs in the module; the only grep hits in
the implementation/probe/audit files are explanatory prose and `#print axioms`
commands
(`formalization/NSFormalization/Section3/T20/H1Trilinear.lean:60-76`,
`research/T20/axioms_u10a.lean:11-26`).  No existing module was modified:
`git diff --name-only origin/erenup/integration-section3...HEAD` lists only the
new H1Trilinear module and lane records; no pre-existing Lean module is in the
diff.

## commands and results

All commands were run after `. ../scripts/lean-env.sh`, with
`LEAN_NUM_THREADS=6`, and `lake` from `verification/`.

- `lake build NSFormalization.Section3.T20.H1Trilinear`: exit 0,
  `Build completed successfully (10646 jobs).`  The module itself is warning
  free; the cached dependency replay emits pre-existing warnings from unrelated
  modules.
- `lake env lean ../formalization/NSFormalization/Section3/T20/H1Trilinear.lean`:
  exit 0, 0 bytes of output.
- `lake env lean ../research/T20/probes/h1_trilinear_closes.lean`: exit 0, 0
  bytes of output.
- `lake env lean ../research/T20/probes/rev429_collision.lean`: exit 1 with
  the exact environment-collision error quoted in the gaps section (the
  intentional negative integration probe).
- `lake env lean ../research/T20/axioms_u10a.lean`: exit 0.  All 16 lines have
  exactly `[propext, Classical.choice, Quot.sound]` (the output is the 16
  standard `depends on axioms` lines).
- `rg -n -i 'sorry|admit|axiom|native_decide|maxHeartbeats'` over the module,
  positive probe, and axiom file found only documentation prose and the audit's
  `#print axioms` lines; no implementation occurrence.
- `make check`: exit 0.  Exact final checks were:

  ```
  Explicit axiom/admission tokens, all copied sources: 11
  .............
  ----------------------------------------------------------------------
  Ran 13 tests in 0.043s

  OK
  45 work items: ownership, contract registration and task cards consistent.
  ```

  The architecture checker also reported `task_count: 45`,
  `tracked_cache_free: true`, and `source_hashes_match: false`, but returned
  exit 0.  `verification/` was not
  touched (`git diff --name-only ...` above), so the conditional
  `scripts/gates.sh`/base-ref contract gate was not applicable.
