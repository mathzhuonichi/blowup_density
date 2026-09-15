REJECT

## 1. What the lane claims

The worker reports four substantive results:

1. `datumPath_contDiffOn` gives an order-`m` datum path which is `C^j` on `Icc 0 S`
   under `max 6 m + 2*j ≤ q+1` and a smooth cylinder force path
   (`research/A01/REPORT_178.md:5-31`).  The declaration exists with exactly that
   statement at `formalization/NSFormalization/Section4/A01/DatumPathSmooth.lean:615-629`.
2. `datumPath_contDiffOn_one` is claimed to give the *full* unconditional `C¹` range
   justified by the original Horizon inputs, namely `max 6 m + 2 ≤ q+1`
   (`research/A01/REPORT_178.md:33-42`).  The declaration exists with that statement at
   `DatumPathSmooth.lean:659-672`, but the claim that this is the exact/full range is false;
   this is the blocking finding below.
3. `datumPath_contDiffOn_all_orders` gives every `j,m` under the named compatible
   all-order supply `hall` (`research/A01/REPORT_178.md:44-49`).  Its exact statement is
   at `DatumPathSmooth.lean:734-753`.
4. `residualPath_hasDerivAt` differentiates the projected-residual datum path and uses
   the formula `νΔu_t + P(f_t-B(u_t,u)-B(u,u_t))` in the range `6 ≤ k`,
   `k+4 ≤ q+1` (`research/A01/REPORT_178.md:51-68`).  Its exact statement is at
   `DatumPathSmooth.lean:382-397`, and the displayed derivative is defined at
   `DatumPathSmooth.lean:283-300`.

The manuscript says that every time differentiation is obtained from the projected
equation after all spatial Sobolev orders are available
(`paper/sections/appendix-a-local-theory.tex:71-76`).  Thus a finite carrier should pay
two spatial orders for each Laplacian differentiation, while any algebra threshold must
be accounted for separately; it must not be reported as another Laplacian loss.

## 2. What is in Lean

### Blocking range-bookkeeping finding

The arbitrary-`j` proof as written chooses `k := max 6 m`, proves `C^j` at order `k`,
and lowers to `m` (`DatumPathSmooth.lean:630-653`).  Consequently the implemented
general theorem really has the stated sufficient range `max 6 m + 2*j ≤ q+1`.
For `m ≥ 6`, this is the sharp `m+2*j` loss forced by repeated use of `Δ`.  For
`m < 6`, however, the `6` is the vendor product's algebra floor
(`DatumPathSmooth.lean:65-82`), not an order lost by the Laplacian.

More importantly, no product differentiation is needed for the first time derivative.
R2's cylinder residual is already a continuous order-`m` path whenever
`m+2 ≤ q+1` (`formalization/NSFormalization/Section4/A01/DatumPathDeriv.lean:88-96`),
and `cylinderVelocity_hasDerivWithinAt` has exactly that unrestricted target order
(`DatumPathSmooth.lean:160-169`).  The general datum descent then applies at order `m`
itself (`DatumPathSmooth.lean:467-476`).

The reviewer theorem
`research/A01/probes/rev178_sharp_c1.lean:18-63` combines exactly those three existing
lemmas and compiles with the strictly sharper hypothesis

```lean
m + 2 ≤ q + 1.
```

It does not assume `hfs`.  In particular, the delivered theorem loses the entire minimal
case `q=6`: at `m=0`, its premise reduces to the false proposition `8 ≤ 7`.
`research/A01/probes/rev178_range_repro.lean:18-32` reproduces that failure, while the
general sharper reviewer theorem compiles.  Therefore
`research/A01/REPORT_178.md:40-42` and `research/A01/B1_LADDER.md:16` do not state the
sharpest range the existing proof machinery supports.  This violates the brief's explicit
exact-range requirement.

The sharpest statements actually Lean-verified in this review are therefore:

- general `j`: the delivered proof proves `max 6 m + 2*j ≤ q+1`;
- `j=1`: the stronger range is exactly `m+2 ≤ q+1`, with no `max 6 m` floor;
- R1 (`j=0`): `m ≤ q+1`, as already recorded by lane 161.

An optimized higher-`j` proof may also lower the order-six nonlinear term after forming it,
rather than bootstrapping the entire velocity at order six, but no stronger all-`j` theorem
is delivered or claimed here without a checked Lean proof.

### Force smoothness and the named all-order hypothesis

The extra `hfs` is genuinely absent from the inputs of `Horizon.lean`.
`HasAprioriBound` receives only
`hF : ∀ n, Continuous (fun t => (F t).jetLp n)`
(`formalization/NSFormalization/Section4/A01/Horizon.lean:106-114`), and
`localTheory_on_prescribed_horizon` has the same input and inserts
`sobolevPath F hF q` in the Duhamel equation
(`Horizon.lean:137-153`).  Lane 167's `forcePath_of_memForceR` likewise returns only jet
continuity for `C01.forcePath hf` (`formalization/NSFormalization/Section4/A01/ForceBridge.lean:64-70`).

`D01.MemForceR` does provide, at every order, a *datum* path `G` which is `C∞` on
`futureTimes` (`formalization/NSFormalization/Section4/D01/ForceClass.lean:158-164`), and
`C01.forcePath_jetLp_continuous` uses that witness to reconstruct continuous spatial jets
(`formalization/NSFormalization/Section4/C01/JetPaths.lean:99-110`).  But no searched
declaration identifies this datum-valued smooth path, through a continuous-linear
reconstruction, with the cylinder-valued `sobolevPath (C01.forcePath hf) hF q`.
Thus lane 167 does not by itself discharge `hfs`; a new datum-to-cylinder time-smoothness
bridge is still needed.  This part of the worker's gap report is honest.

`datumPath_contDiffOn_one` itself has no `hfs` binder (`DatumPathSmooth.lean:659-672`) and
uses only continuity of the restricted force path (`DatumPathSmooth.lean:678-693`).
The issue with it is only the unnecessarily weak range.

The four conjuncts of `hall` are audited as follows
(`DatumPathSmooth.lean:736-745`):

- `hfs`: a `C∞` order-`q` cylinder force path;
- `hU`: the same fixed `U` is realized at every order;
- `hu`: angle invariance;
- `hduh`: the exact order-`q` Duhamel equation.

For a fixed `q`, `localTheory_on_prescribed_horizon` supplies `hU`, `hu`, and that exact
Duhamel equation, with `u₀ := ordinarySobolev (q+1) a...` and
`f := sobolevPath F hF q` (`Horizon.lean:143-153`).  It supplies additional norm,
initial-value, and divergence clauses which `hall` does not demand.  Hence, modulo
identifying the separately constructed `U` paths across orders, the only stronger
conjunct is precisely `hfs`.  No conjunct states datum-path time regularity or otherwise
encodes the conclusion.  The hypothesis is not logically empty: the all-zero family in
`research/A01/probes/rev178_hall_zero.lean:17-36` instantiates `hall` and compiles.

### Differentiated residual and datum identity

The residual derivative has the correct signs and orders.  In
`reducedResidualDerivativePath`, `d₁` is the order-`k+1` velocity derivative used in
the two bilinear terms, while `d₂` is the order-`k+2` velocity derivative to which
`laplacianOperator 1 k` is applied (`DatumPathSmooth.lean:286-300`).  The hypothesis
`k+4 ≤ q+1` is exactly what makes the order-`k+2` R2 derivative available.

The product rule actually invoked is
`ContinuousLinearMap.hasDerivWithinAt_of_bilinear`
(`DatumPathSmooth.lean:342-352`), producing
`B(u_t,u)+B(u,u_t)`.  It is subtracted inside the Leray source
(`DatumPathSmooth.lean:353-360`), so the final formula is exactly
`νΔu_t + P(f_t-B(u_t,u)-B(u,u_t))`.

No restriction silently changes the datum.  `reducedResidualPath_eq` identifies the
target-order rewritten residual with R2's original `cylinderResidualPath`
(`DatumPathSmooth.lean:111-153`); `residualPath_hasDerivAt` assumes `R` is a datum of the
ordinary descent of that original residual (`DatumPathSmooth.lean:391-395`); and the
proof explicitly uses `reducedResidualPath_eq` before descending
(`DatumPathSmooth.lean:424-440`).  The remaining lift back to order `k` is by datum
uniqueness and `lowerVectorL_injective` (`DatumPathSmooth.lean:400-456`).

### Non-vacuity, axioms, and hygiene

The worker's zero example really invokes the main theorem `datumPath_contDiffOn`, not the
one-derivative corollary (`research/A01/axioms_b1_r3.lean:35-63`), although it chooses
`j=0`.  The stronger reviewer probe invokes that same main theorem at `j=2` and compiles
(`research/A01/probes/rev178_zero_j2.lean:17-44`).  The substantive mutation from the
same `C²` conclusion to `C³`, without adding the required spatial orders, fails at the
expected type boundary (`research/A01/probes/rev178_negative_c3.lean:16-40`).

All 18 declarations listed at `research/A01/axioms_b1_r3.lean:14-31` print exactly
`[propext, Classical.choice, Quot.sound]`.  The lane files contain no
`sorry`, `admit`, `axiom`, or `native_decide`.  The six heartbeat overrides are all local
to one declaration, all exactly `400000`, and each has an immediately preceding reason
comment (`DatumPathSmooth.lean:60-61,108-109,232-233,302-303,376-377,461-462`).

The committed diff adds only the new proof module and research records; no pre-existing
Lean module or `verification/` file was changed.  The paper quotation at
`research/A01/B1_LADDER.md:135-137` agrees with the opened manuscript lines
`appendix-a-local-theory.tex:71-76`.

## 3. Gaps and required fixes

The force-smoothness bridge and cross-order compatibility gap are real and properly named;
they are not rejection reasons.  The whole-tree searches found no theorem closing either
gap.  The strongest relevant inputs are the smooth datum path in `ForceClass.lean:158-164`,
the merely continuous force carrier in `ForceBridge.lean:64-70`, and the fixed-order
Horizon result in `Horizon.lean:137-154`.

The rejection is for the exact-range defect:

1. Change `datumPath_contDiffOn_one` at `DatumPathSmooth.lean:659-672` to assume
   `hm : m + 2 ≤ q + 1`; replace its order-six detour with the compiling proof in
   `research/A01/probes/rev178_sharp_c1.lean:32-63`.
2. Update `research/A01/REPORT_178.md:33-42` and
   `research/A01/B1_LADDER.md:16` to state the sharp `C¹` range.  Do not call
   `max 6 m + 2*j` the exact mathematical range at low `m`; call it the range of the
   current all-`j` implementation unless a stronger mixed-order induction is proved.

Reproducing error from the delivered `datumPath_contDiffOn_one` at the valid R2 case
`q=6, m=0`:

```text
../research/A01/probes/rev178_range_repro.lean:32:19: error: unsolved goals
ν S : ℝ
hν : 0 < ν
hS : 0 < S
u₀ : ↥(SobolevSpace 1 7)
f : C(↑(Icc 0 S), ↥(SobolevSpace 1 6))
u : C(↑(Icc 0 S), ↥(SobolevSpace 1 7))
U : C(↑(Icc 0 S), ↥EulerMeanSolenoidal.L2)
hU : ∀ (t : ↑(Icc 0 S)), ordinaryLift (U t) = value 1 (u t)
hu : ∀ (θ : AddCircle 1) (t : ↑(Icc 0 S)), (sobolevTranslation 1 7 (0, θ)) (u t) = u t
hduh : ∀ (t : ↑(Icc 0 S)), u t = quadraticDuhamel 1 ν hν ⋯ ⋯ (coefficients 1 ⋯ f) u₀ u t
⊢ False
```

## 4. Commands and results

All Lean commands were run after sourcing `scripts/lean-env.sh`; every `lake` command
was run from `verification/` with `LEAN_NUM_THREADS=6`.

### Module build and direct check

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.DatumPathSmooth
[exit 0]
… 205 lines, all replayed warnings/info from pre-existing dependencies …
Build completed successfully (10026 jobs).

$ set -o pipefail; LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.DatumPathSmooth 2>&1 | sha256sum
d72ce572b980faad5752754b12f4dcf5a926f3f9b1fc110ab6e1d8a55f02f638  -
[exit 0]

$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A01/DatumPathSmooth.lean
[no output]
[exit 0]
```

The build stream contains no diagnostic from `DatumPathSmooth.lean` itself.

### Axiom/conformance file: exact output

```text
'NSFormalization.Section4.A01.restrictPath' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.restrictPath_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.restrict_leray' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.restrict_advection' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.reducedAdvectionPath' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.reducedResidualPath' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.reducedResidualPath_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderVelocity_hasDerivWithinAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.reducedResidualPath_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderPath_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.reducedResidualDerivativePath' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.reducedResidualPath_hasDerivWithinAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.reducedResidualDerivativeOrdinaryPath' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.residualPath_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.exists_contDiff_datumPath_of_cylinder' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.datumPath_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.datumPath_contDiffOn_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.datumPath_contDiffOn_all_orders' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[exit 0]
```

### Repository check

The raw successful `make check` stream had 25,428 lines.  Its exact opening was:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 482,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
```

It retained the pre-existing copied-source notice for
`formalization/NSFormalization/Paper1/BoundaryCorollary.lean:90: token "sorry"` and
`source_hashes_match: false`.  Its exact tail was:

```text
      "NavierStokes.R3.SchwartzCompactApproximation",
      "NavierStokes.R3.WeakFourierUniqueness",
      "NavierStokes.R3CompactIntegration",
      "NavierStokes.ResidualCalculus",
      "NavierStokes.SpatialCurl",
      "TestSupport.Axioms",
      "Tests.HomogeneousNorm"
    ]
  },
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.041s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
[exit 0]
```

A second complete successful stream was fingerprinted exactly as:

```text
$ set -o pipefail; make check 2>&1 | sha256sum
9bf69a041063d6f764a7299eb21793896b31876c6a6f237c0d000d5f242570e1  -
[exit 0]
```

No `verification/` path was touched, so the brief's conditional `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration` gates were not applicable.

### Reviewer probes: exact outputs

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/A01/probes/rev178_sharp_c1.lean
[no output]
[exit 0]

$ LEAN_NUM_THREADS=6 lake env lean ../research/A01/probes/rev178_zero_j2.lean
[no output]
[exit 0]

$ LEAN_NUM_THREADS=6 lake env lean ../research/A01/probes/rev178_hall_zero.lean
[no output]
[exit 0]

$ LEAN_NUM_THREADS=6 lake env lean ../research/A01/probes/rev178_negative_c3.lean
../research/A01/probes/rev178_negative_c3.lean:40:12: error: Application type mismatch: The argument
  hG
has type
  ContDiffOn ℝ (↑2) G (Icc 0 1)
but is expected to have type
  ContDiffOn ℝ 3 G (Icc 0 1)
in the application
  And.intro hG
[exit 1, expected]
```

The last probe is a substantive mutation of the main conclusion, not an omitted argument.

### Hygiene, diff, and gap-search outputs

```text
$ rg -n --glob '*.lean' '\b(sorry|admit|axiom|native_decide)\b' \
    formalization/NSFormalization/Section4/A01/DatumPathSmooth.lean \
    research/A01/axioms_b1_r3.lean
[no output]

$ git diff --check origin/erenup/integration...HEAD
[no output]

$ git diff --name-status origin/erenup/integration...HEAD
A formalization/NSFormalization/Section4/A01/DatumPathSmooth.lean
A research/A01/ATTEMPTS_B1_R3.md
M research/A01/B1_LADDER.md
A research/A01/REPORT_178.md
A research/A01/axioms_b1_r3.lean

$ git diff --name-only origin/erenup/integration...HEAD -- verification
[no output]

$ grep -rnE --include='*.lean' 'ContDiff(On)?.*sobolevPath|sobolevPath.*ContDiff(On)?|forcePath.*ContDiff(On)?|ContDiff(On)?.*forcePath' formalization/NSFormalization/Section4
[no output]

$ grep -rnE --include='*.lean' 'SobolevTower|cross-order|cross.order|compatible.*carrier|carrier.*compatible|same ordinary path' formalization/NSFormalization/Section4
formalization/NSFormalization/Section4/D01/RealPairing.lean:136:order-independence step 3b needs to identify lowering data across orders (the lowering analogue of
formalization/NSFormalization/Section4/A01/DatumPathSmooth.lean:731:the same ordinary path `U`, an exact Duhamel equation, angle invariance, and a smooth
formalization/NSFormalization/Section4/A01/DatumPathSmooth.lean:733:cross-order compatibility and force-smoothness facts. -/
```

These searches were also run over `Source/`, `Paper1/`, `Paper3/`, `vendor/`, and
`formalization/FormalPatched/`; the only nearby constructions were the compact-support
Sobolev-time results and vendor `SobolevTower`, neither of which supplies the missing
`MemForceR → ContDiffOn (sobolevPath ...)` or compatible-Horizon theorem.
