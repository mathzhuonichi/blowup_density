ACCEPT

## 1. What the lane claims

The lane claims unconditional uniqueness, on every positive finite horizon, of
two order-seven fixed points of the same forced quadratic Duhamel map.  This is
the uniqueness component of the paper's unique maximal smooth solution
(`paper/sections/02-preliminaries.tex:105-115`); the appendix writes the mild
equation and explains uniqueness and patching on compact common intervals
(`paper/sections/appendix-a-local-theory.tex:109-124`).

I compared every signature printed in the worker report with its declaration:

- `volterra_window_bound`: report `research/A01/REPORT_188.md:37-45`, Lean
  `formalization/NSFormalization/Section4/A01/MildUniqueness.lean:23-30`.
- `volterra_eq_zero`: report `research/A01/REPORT_188.md:48-54`, Lean
  `formalization/NSFormalization/Section4/A01/MildUniqueness.lean:99-104`.
- `quadratic_mild_unique`: report `research/A01/REPORT_188.md:57-62`, Lean
  `formalization/NSFormalization/Section4/A01/MildUniqueness.lean:144-148`.
- `mildUniqueness`: report `research/A01/REPORT_188.md:65-66`, Lean
  `formalization/NSFormalization/Section4/A01/MildUniqueness.lean:185-188`.
- `compatible_carriers_of_boundsInv'`, `compatible_carriers_of_bounds'`, and
  `compatible_carriers_hall'`: report `research/A01/REPORT_188.md:69-131`, Lean
  `formalization/NSFormalization/Section4/A01/MildUniqueness.lean:191-253`.

All seven exist and the reported types match.  `mildUniqueness` has exactly the
predicate defined in `CommonHorizon.lean:156-162`; it is not a weakened local
restatement.  The complete `CommonHorizon.lean` has the identical SHA-256
`7a5bc1527e62a25e140026f0248cafb5ac3538482484f05426835074fe91b426`
in `HEAD^`, the current lane worktree, and the subsequently advanced lane-186
ref.  Thus the predicate is token-for-token the reviewed base definition.

No smallness, ball, regularity, divergence, or invariance premise was added to
`MildUniqueness`.  Its `hnu` and `hS` premises are strict positivity premises;
the datum and force are arbitrary, and both fixed-point equations are used in
the subtraction at `MildUniqueness.lean:172-179`.  There is no `ENNReal.toReal`,
top-valued norm, or empty main time interval.  The auxiliary window theorem has
one deliberately underscored, proof-redundant premise `_hb : 0 <= b`
(`MildUniqueness.lean:27`), disclosed by the worker
(`ATTEMPTS_MILD_UNIQUENESS.md:83-87`).  It describes a genuine prefix and is
instantiated by `hb : 0 <= min ((n+1)*delta) S` at
`MildUniqueness.lean:116-124`; it neither weakens nor vacuously discharges the
main theorem.

## 2. What is in Lean

### Causality and the short-window mass

The vendor convolution is genuinely causal.  Its integrand is
`1_{r <= t} K r (f (t-r))` (`VolterraConvolution.lean:32-35`), integrated over
`r in (0,S]` (`VolterraConvolution.lean:107-110`), and is equal to the usual
interval integral from `0` to `t` (`VolterraConvolution.lean:138-145`).  In the
heat application the kernel is explicitly zero at nonpositive lag
(`SobolevHeatKernel.lean:89-94`).  This is exactly the change of variables from
`K (t-s) (f s)` over `s in [0,t]`.

For `t <= b <= a+delta`, the new proof splits the positive lag `r`.  If
`r <= delta`, then `t-r` lies in the current prefix and the uniform prefix norm
bounds the source (`MildUniqueness.lean:44-61`).  If `r > delta`, then
`t-r <= a`, so `hpast` gives `d(t-r)=0`, and the source bound gives
`f(t-r)=0` (`MildUniqueness.lean:62-69`).  The indicator-domain identity is
literally `Iic delta intersect Ioc 0 S = Ioc 0 delta`, and the final integral is
literally `kernelMass delta k`, not `kernelMass S k`
(`MildUniqueness.lean:76-96`).

The counterexample-shaped specialization in
`research/A01/probes/rev188_tiny_parabolic_window.lean:15-37` uses the singular
inverse-square-root parabolic majorant and an arbitrarily tiny
`delta <= S/100`; it typechecks with exactly `kernelMass delta`.  This directly
tests the requested near-zero-concentrated-kernel case.

### Time budget and the quadratic Lipschitz estimate

`exists_positive_time_budget` states
`exists T, 0 < T and T <= Tmax and ... and
(T + 2*parabolicConstant nu*sqrt T)*L < 1`
(`VolterraUniqueness.lean:68-72`).  The lane takes its last conjunct after
calling it with `M := 0`, `margin := 1`, and `Tmax := S`
(`MildUniqueness.lean:180`).  The exact kernel integral is
`integral_(0,T] parabolicKernelBound = T + 2*parabolicConstant nu*sqrt T`
(`SobolevHeatKernel.lean:144-146`), so the rewrite at
`MildUniqueness.lean:181-182` produces precisely
`kernelMass delta (parabolicKernelBound nu) * L < 1`, with `0 < delta <= S`.

The radius is `max ||u|| ||v||`, so every point of both continuous paths lies
in that ball (`MildUniqueness.lean:149-165`).  The vendor's
`Coefficients.apply_sub_bound` is the actual uniform difference estimate for
the linear-plus-bilinear source (`QuadraticCoefficients.lean:50-70`); its
underlying bilinear difference identity and estimate are proved in
`QuadraticSource.lean:29-69`.  At order six the concrete coefficient has
`X = SobolevSpace 1 7`, `Y = SobolevSpace 1 6`, and its quadratic map is the
bounded order-six advection map (`ForcedCylinderLocal.lean:43-58`).  Thus the
Lipschitz estimate used is valid for both full-horizon competitors and is the
requested order-six estimate.

### Finite propagation and consumers

The induction hypothesis is exactly vanishing on the closed prefix
`t <= n*delta` (`MildUniqueness.lean:105`).  The successor uses
`b := min ((n+1)*delta) S`, passes that hypothesis unchanged as `hpast`, and
proves the closed prefix through `b` is zero (`MildUniqueness.lean:114-130`).
Finally `exists_nat_gt (S/delta)` gives `S < n*delta`; every `t in Icc 0 S`,
including `S`, is covered (`MildUniqueness.lean:131-135`).  No point is skipped
when `S` is not an integer multiple of `delta`.

The three primed results are literal applications of the existing consumer to
`mildUniqueness`: `compatible_carriers_of_boundsInv` at
`MildUniqueness.lean:209`, `compatible_carriers_of_bounds` at `:230`, and
`compatible_carriers_hall` at `:253`.  The conformance example is an actual
`exists!` with witness the zero path and uses `mildUniqueness` for uniqueness
(`research/A01/axioms_mild_uniqueness.lean:18-28`), so existence and uniqueness
are both instantiated on a positive horizon.

## 3. Gaps, negative check, and hygiene

There is no remaining mathematical or Lean gap.  The worker does not make a
"not in the tree" claim: it explicitly says the alternative restart route was
not proved missing (`ATTEMPTS_MILD_UNIQUENESS.md:46-62`).  Nevertheless I ran
the requested whole-tree searches over `formalization/NSFormalization/Section4`
and vendor `Euler/` for `restart|shift|translate|concat|mild_solution_unique`.
They find the classical restart infrastructure, the bounded restart uniqueness
use in `ContinuationInvariant.lean:140`, and the vendor theorem, but no result
that undercuts or invalidates the causal proof.  Therefore there is no negative
tree claim to accept.

The substantive mutation in
`research/A01/probes/rev188_halved_mass_mutation.lean:11-25` replaces
`kernelMass delta` by `kernelMass (delta/2)`, without dropping an argument.
The original proof then fails exactly at the changed conclusion:

```text
../research/A01/probes/rev188_halved_mass_mutation.lean:24:2: error: Type mismatch
  volterra_window_bound hS K k hK hk hk0 hbound d f L hL hf hd hb hbS hdeltaS hbdelta hpast
has type
  ||d.comp (timeInclusion hbS)|| <= kernelMass delta k * L * ||d.comp (timeInclusion hbS)||
but is expected to have type
  ||d.comp (timeInclusion hbS)|| <= kernelMass (delta / 2) k * L * ||d.comp (timeInclusion hbS)||
```

(The actual Lean output uses Unicode `delta`, `<=`, and norm brackets; it is
quoted verbatim in part 4.)

There is no `sorry`, `admit`, declaration of an `axiom`, `native_decide`, or
heartbeat override in the implementation.  The only matches for the word
`axioms` are the seven audit commands in
`research/A01/axioms_mild_uniqueness.lean:10-16`.  No pre-existing Lean module
was modified relative to the lane's immutable parent `HEAD^ = 6af395e`; the
only Lean implementation delta is the new `MildUniqueness.lean`.  The exact
parent diff is five files: one new implementation, three new records/audit
files, and the requested one-line record update.

During this review the mutable local ref
`erenup/186-A01-a3-common-horizon` advanced externally from `6af395e` to
`7efd3e4`.  I made no git state change.  The required historical comparison was
therefore repeated against immutable `HEAD^`; `CommonHorizon.lean` has the same
hash in both refs and the worktree.  Relative to
`origin/erenup/integration...HEAD`, every Lean file is added (`A`), not modified.
No `verification/` file is in the lane delta, so the conditional
`scripts/gates.sh` and `check_contracts.py --base-ref ...` gates do not apply.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`; every `lake` command ran from
`verification/` with `LEAN_NUM_THREADS=6`.

```text
$ lake build NSFormalization.Section4.A01.MildUniqueness
Build completed successfully (3946 jobs).

$ lake -q build NSFormalization.Section4.A01.MildUniqueness
<zero output; exit 0>

$ lake env lean ../formalization/NSFormalization/Section4/A01/MildUniqueness.lean
<zero output; exit 0>
```

The axiom audit output was exactly:

```text
'NSFormalization.Section4.A01.volterra_window_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.volterra_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.quadratic_mild_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.mildUniqueness' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.compatible_carriers_of_boundsInv'' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.compatible_carriers_of_bounds'' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.compatible_carriers_hall'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The positive adversarial probe gave zero output and exit 0:

```text
$ lake env lean ../research/A01/probes/rev188_tiny_parabolic_window.lean
<zero output; exit 0>
```

The negative mutation gave exit 1 and exactly:

```text
$ lake env lean ../research/A01/probes/rev188_halved_mass_mutation.lean
../research/A01/probes/rev188_halved_mass_mutation.lean:24:2: error: Type mismatch
  volterra_window_bound hS K k hK hk hk0 hbound d f L hL hf hd hb hbS hδS hbδ hpast
has type
  ‖d.comp (timeInclusion hbS)‖ ≤ kernelMass δ k * L * ‖d.comp (timeInclusion hbS)‖
but is expected to have type
  ‖d.comp (timeInclusion hbS)‖ ≤ kernelMass (δ / 2) k * L * ‖d.comp (timeInclusion hbS)‖
```

`make check` exited 0.  Its raw repo-wide architecture JSON was 25,427 lines;
the exact terminal suffix from a second `set -o pipefail; make check | tail -n
24` run was:

```text
.............
----------------------------------------------------------------------
Ran 13 tests in 0.041s

OK
      "NavierStokes.PeriodicIntegration",
      "NavierStokes.PeriodicUniqueness",
      "NavierStokes.ProblemStatement",
      "NavierStokes.R3.CompactSchwartz",
      "NavierStokes.R3.ComparisonCutoffs",
      "NavierStokes.R3.ComparisonFourierSetup",
      "NavierStokes.R3.ComparisonSetup",
      "NavierStokes.R3.FourierTestDerivatives",
      "NavierStokes.R3.ProblemStatement",
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
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

`lake test` exited 0.  It replayed only pre-existing linter warnings; its final
test output was exactly:

```text
ℹ [10526/10528] Replayed Tests.InsertionLifespanV2
info: Tests/InsertionLifespanV2.lean:32:0: Contract BlowupDensity.Tests.checkedInsertionLifespanV2: checked; standard logical axioms only
ℹ [10527/10528] Replayed Tests.TameProduct
info: Tests/TameProduct.lean:14:0: Contract BlowupDensity.Tests.checkedTameProduct: checked; standard logical axioms only
ℹ [10528/10528] Replayed Tests.EnergyAbsorptionPartialV3
info: Tests/EnergyAbsorptionPartialV3.lean:41:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionPartialV3: checked; standard logical axioms only
```

The immutable parent comparison was exactly:

```text
$ git diff --stat HEAD^..HEAD
 .../Section4/A01/MildUniqueness.lean               | 255 +++++++++++++++++++++
 research/A01/A3_SPLIT.md                           |   2 +-
 research/A01/ATTEMPTS_MILD_UNIQUENESS.md           |  97 ++++++++
 research/A01/REPORT_188.md                         | 175 ++++++++++++++
 research/A01/axioms_mild_uniqueness.lean           |  30 +++
 5 files changed, 558 insertions(+), 1 deletion(-)

$ git diff --name-status HEAD^..HEAD
A formalization/NSFormalization/Section4/A01/MildUniqueness.lean
M research/A01/A3_SPLIT.md
A research/A01/ATTEMPTS_MILD_UNIQUENESS.md
A research/A01/REPORT_188.md
A research/A01/axioms_mild_uniqueness.lean

$ git diff --check HEAD^..HEAD
<zero output; exit 0>
```

Fixes required: none.
