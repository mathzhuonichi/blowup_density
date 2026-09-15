ACCEPT-WITH-NOTES

Exact fixes are listed at the end.  The conditional theorem is sound and the
single residual is honest; the notes concern the solenoidal API recut, one
order-index explanation, and rebasing the stale branch onto current integration.

## 1. What the lane claims

The report accurately says that this is a **conditional** delivery, not an
unconditional proof of A3-M2 (`research/A01/REPORT_196.md:5-12`).  Its one named
analytic input is `FiniteMildEnergy`; the worker does not claim to prove that
input for general data.  All 15 production declarations named in the report
exist.  The reported principal signatures agree exactly with
`formalization/NSFormalization/Section4/A01/MildGronwall.lean:22-229`:

- the norm definitions/comparisons and continuity are at `:22-67`;
- the regularized metric limit and word PDE are at `:72-101`;
- the tame/Young/inner-product reductions are at `:105-140`;
- `FiniteMildEnergy` is at `:149-166`;
- `mildGronwall`, `hb_of_base'`, and `hb_of_base_inv'` are at `:170-229`.

The four declarations omitted from the report's displayed signature blocks are
indeed exactly the four names it lists at `REPORT_196.md:148-152`.

### Fidelity of `FiniteMildEnergy`

The named input is a restriction of the standard finite-order squared-energy
inequality, not the final Gronwall conclusion.  It fixes `E,A` before every
window and competitor (`MildGronwall.lean:149-157`), supplies a nonnegative
continuous squared-energy envelope `x`, the majorization
`‖u t‖ ≤ sqrt (x t)`, and the initial comparison
`sqrt (x 0) ≤ E‖u₀‖` (`:157-161`).  Its full interior right-hand side is exactly

```lean
A * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq)
  (extendPath T hT u t)‖) * Real.sqrt (extendPath T hT x t) * g t +
  (E * ‖sobolevPath F hF (q+1)‖) * Real.sqrt (extendPath T hT x t)
```

(`MildGronwall.lean:163-166`).  It contains no integral bound, no
`aprioriRadius`, and no upper bound on `x`; those are derived in
`mildGronwall` at `:175-198`.  Thus it encodes the missing differential energy
estimate, not the desired conclusion.

The driver is genuinely lowered to base index six: `Nat.succ_le_succ hq` is
`7 ≤ q+1`, so the restricted value lies in `SobolevSpace 1 7`.  This is the
same lowering used by `lower_identification`
(`formalization/NSFormalization/Section4/A01/AprioriFamily.lean:85-102`) and the
same `16`, hence `256=16^2`, proved in the physical order-two cap
(`formalization/NSFormalization/Section4/A01/OrderTwoCap.lean:195-207`).

The absorption algebra is exact.  Young gives

```text
A·16·l·sqrt(x)·g
  ≤ ν·g² + (A²·256·l²/(4ν))·x.
```

After cancelling `νg²` and doubling, the coefficient multiplying the lane-193
driver is `C=A²/(4ν)`, exactly the conclusion of
`mild_energy_absorption` (`MildGronwall.lean:105-110`) and exactly what
`mildGronwall` installs at `:174,183-193`.

For solenoidal smooth data, the paper's solution would satisfy this kind of
input.  Appendix A gives one common interval with all spatial Sobolev orders and
time smoothness at `paper/sections/appendix-a-local-theory.tex:66-76`, and the
actual differential inequality is

```text
1/2 d/dt ‖u‖_{H^m}² + ν‖∇u‖_{H^m}²
  ≤ C_m‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m}
    + ‖f‖_{H^m}‖u‖_{H^m}
```

at `paper/sections/appendix-a-local-theory.tex:127-140`.  Taking the finite
full-word energy for `x`, its gradient energy for `g`, and enlarging one fixed
comparison constant `E` gives the stated input.  The paper explicitly uses
solenoidality to remove pressure (`:138`), which leads to the API note below.

No `ENNReal.toReal` loophole occurs in `FiniteMildEnergy`.  The separate tame
transport retains both necessary finiteness hypotheses
(`MildGronwall.lean:114-119`).  Every selected `Icc 0 T` is nonempty because
`hT : 0 ≤ T`; the singleton window is legitimate.  There is one inherited
scope caveat: if the outer horizon `S<0`, there is no admissible `T`, so both
lane-193's `MildGronwall` and this residual are vacuous.  All actual family
consumers carry `hS : 0 ≤ S` (`AprioriFamily.lean:177-186` and
`MildGronwall.lean:202-215`), so this does not affect the paper application,
but a standalone API recut may also bind `hS` explicitly.

## 2. What is in Lean

### Genuine vendor specializations

`SobolevWord (q+1)` really is the complete finite family of coordinate words
through length `q+1`: the vendor defines it as
`Σ n : Fin ((q+1)+1), Fin n.val → Fin 4`
(`vendor/NavierStokesAndEuler/Euler/CylinderSobolevSpace.lean:14-15`).
The local `euclideanWordNorm` is the vendor's actual `familyMetricNorm` at the
identity (`MildGronwall.lean:27-35`), whose definition is the square root of a
sum of metric inner products
(`vendor/NavierStokesAndEuler/Euler/FiniteMetricEnergy.lean:20-24`).  The lower
and upper comparisons at `MildGronwall.lean:38-55` are proved from the cylinder
max norm and finite sum; they are not assumptions.  The constant is exactly

```lean
Real.sqrt (Fintype.card (SobolevWord (q+1)) : ℝ).
```

`continuous_euclideanWordNorm` proves continuity of the norm function itself
(`MildGronwall.lean:58-67`), which is stronger than continuity after composing
with any continuous word path.

`euclidean_full_word_limit` is a genuine specialization of the vendor's
regularized system: `regularizedValueFamily` and its strong uniform limit are
defined/proved at
`vendor/NavierStokesAndEuler/Euler/RegularizedEnergyFamily.lean:19-49`, while
the actual metric path and its uniform-limit theorem are at
`vendor/NavierStokesAndEuler/Euler/MetricPathConvergence.lean:26-44`.  The lane
instantiates both with the full `SobolevWord (q+1)` index and identity metric
(`MildGronwall.lean:72-84`); it is not a reformulation of a hypothesis.

Likewise `quadratic_regularized_word` applies the vendor theorem that every
regularized word, including `m=q+1`, satisfies the time PDE without a top-order
differentiability premise
(`vendor/NavierStokesAndEuler/Euler/RegularizedWordEquation.lean:54-70`).  The
source is the genuine `sourcePath` (`Euler/QuadraticSourceLimit.lean:16-18`) of
the time-restricted quadratic coefficients, not an abstract supplied PDE
identity (`MildGronwall.lean:88-101`).

The tame steps are also real theorem applications.  `outer_tame_low` consumes
`A03.outerProductTame`
(`formalization/NSFormalization/Section4/A03/OuterTameProduct.lean:165-179`)
through `A04.outerSobolevNormAt_le`
(`formalization/NSFormalization/Section4/A04/HighEnergy.lean:157-179`), and
`inner_mild_energy` consumes the generic Hilbert-space assembly
`A04.inner_energy_Rhigh` (`HighEnergy.lean:125-146`).  They do not pretend to
construct the missing carrier/forcing identifications.

### Solenoidal interface mismatch and exact recut

The worker correctly flags a real mismatch at `REPORT_196.md:185-188`:
`MildGronwall` and `FiniteMildEnergy` quantify over arbitrary
`SmoothL2Field` data, while the vendor energy theorem requires a
divergence-free state (`vendor/NavierStokesAndEuler/Euler/MildMajorantEnergy.lean:39-46`).
The paper also removes pressure by solenoidality.

The exact recommended recut is to insert, immediately after `a`,

```lean
(ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
```

in both `AprioriFamily.MildGronwall` and `FiniteMildEnergy`, and thread the same
argument through `mildGronwall`, `hb_of_base`, `hb_of_base_inv`,
`hb_of_base'`, and `hb_of_base_inv'`.  In particular the family input becomes

```lean
hMG : ∀ q (hq : 6 ≤ q), MildGronwall hq hν a ha F hF (E q) (C q)
```

and the residual premise becomes

```lean
henergy : FiniteMildEnergy hq hν a ha F hF E A.
```

This is harmless for the intended consumers.  Lane 186's unrestricted and
invariant common-carrier theorems already bind `ha`
(`formalization/NSFormalization/Section4/A01/CommonHorizon.lean:202-221` and
`:224-245`), and current integration's lane-192 constructor export binds it at
`formalization/NSFormalization/Section4/A01/CylinderWiring.lean:139-143`
(read from `origin/erenup/integration`).  Zero data still discharges it by
`simp`.

### Non-vacuity, axioms, and hygiene

The zero instance is genuine.  `zero_energy` quantifies over every admissible
window and every competitor, identifies the competitor with zero using actual
quadratic mild uniqueness, and constructs `x=d=g=0`
(`research/A01/axioms_mild_gronwall.lean:55-74`).  The public example then
applies `hb_of_base'` with `E=1`, `A=C=0` and obtains the all-order family
without assuming `FiniteMildEnergy` (`:76-85`).  This is stronger than merely
exhibiting a stationary scalar inequality.  The separate nonstationary scalar
check is correctly labelled as non-PDE (`:93-100`).

The audit prints the 15 production declarations plus four private zero helpers,
19 reports total (`axioms_mild_gronwall.lean:5-19,102-105`), each exactly
`[propext, Classical.choice, Quot.sound]`.  The new production and audit files
contain no `sorry`, `admit`, declaration `axiom`, or `native_decide`, and no
`maxHeartbeats` override.  The imported lane-193 module's sole override is
per-declaration, exactly `400000`, with the reason immediately above it
(`AprioriFamily.lean:173-176`).

The worker commit itself modifies exactly five paths: one new production
module, three new records/audit files, and the authorized A3-M2 row update.
No pre-existing Lean module was modified.  However the branch is stale relative
to current `origin/erenup/integration`: its lane-193 parent `d7c66a8` is not an
ancestor of the integrated/rebased lane-193 commit.  Consequently the required
current-base two-dot diff presently reports 50 paths rather than only lane 196.
This is a branch-cut hygiene issue, not a proof defect, and requires the rebase
listed below.

## 3. Gaps

The sole analytic gap is indeed construction of the general-data envelope in
`FiniteMildEnergy`, uniformly in window and competitor.  Whole-tree searches of
`formalization/NSFormalization/Section4` for `FiniteMildEnergy`,
`mild_majorized_energy_subinterval`, `regularized_word_hasDerivAt`,
`quadraticDuhamel` plus energy, and mild/energy combinations found no second
Section4 theorem with this conclusion.  The only `FiniteMildEnergy` occurrence
is the new module; the nearby Section4 interfaces are fixed-point/regularity
lemmas or the classical-solution energy chain.  Therefore the worker's
"not in the tree" claim is accepted.

The next lane must specialize
`EulerMildMajorantEnergy.mild_majorized_energy_subinterval`
(`vendor/NavierStokesAndEuler/Euler/MildMajorantEnergy.lean:24-65`) to the
identity metric and a full word family through `q+1`, but first construct the
premises it exposes: divergence-free velocity/transport paths and a gradient
pressure (`hu`, `hz`, `hp` at `:43-46`); a maximal-regularity state
`U : TimeLp T (SobolevSpace 1 (q+2))` and source/pressure representatives
`F,P : TimeLp T (SobolevSpace 1 (q+1))` with the required approximation and
truncation identities (`:47-50`); and a quantitative bound for the limiting
forcing-family norm `Z`, which remains explicitly in the conclusion (`:54-65`).
`A01.ForcedMaximalRegularity.forced_mild_maximal_regularity`
(`formalization/NSFormalization/Section4/A01/ForcedMaximalRegularity.lean:28-42`)
supplies the first Bochner state, but the full-order source, pressure, and their
restriction identities still need Navier--Stokes-specific analogues of
`sourceTime_restriction`/`signedPressureTime_restriction`.  After identifying
the word forcing with the physical tensor pairing, A03's `outerProductTame`,
A04's `outerSobolevNormAt_le`, and `inner_energy_Rhigh` provide exactly the
tame low-order factor and Young algebra; they do **not** by themselves supply
the representatives or forcing-family identification.  Finally the integrated
root-energy estimate must be converted to an everywhere-interior differentiable
majorant `x` (or the signed limit strengthened to retain the dissipative term).

The correction wrapper's order explanation needs one correction.  Its premise
is `N+6 ≤ q+1` (`vendor/NavierStokesAndEuler/Euler/CorrectionMildEnergy.lean:41-42`),
but `N` is the external order added to the six-word base, not the final Sobolev
order: `energyLength = baseLength + externalLength`
(`vendor/NavierStokesAndEuler/Euler/EnergyWordCoordinates.lean:39-52`).  For
`q≥6`, the full cutoff `q+1` is reached with `N=q-5`, not `N=q+1`.  Thus this
inequality is not itself a full-order obstruction.  The wrapper still cannot be
quoted directly because it is for `CorrectionData`/`SpatialBudget` and its own
constructed nonlinear source and pressure
(`Euler/CorrectionMildEnergy.lean:32-82`), not this lane's canonical
`coefficients` system.

### Required negative check

The reviewer changed the sharp `256` in the main Young-absorption conclusion to
`255` in
`research/A01/probes/rev196_absorption_255_fail.lean:6-15`, retaining all
arguments and the original proof route.  Lean fails at the expected final
arithmetic step:

```text
../research/A01/probes/rev196_absorption_255_fail.lean:15:2: error: linarith failed to find a contradiction
nu A l x g b d : ℝ
hnu : 0 < nu
hx : 0 ≤ x
h : 1 / 2 * d + nu * g ^ 2 ≤ A * (16 * l) * √x * g + b * √x
ha : 1 / 2 * d ≤ A ^ 2 / (4 * nu) * (16 * l) ^ 2 * x + b * √x
a✝ : 2 * (A ^ 2 / (4 * nu) * (255 * l ^ 2) * x + b * √x) < d
⊢ False
failed
```

This is a false mutation, not tactic fragility.  The passing counterexample
`research/A01/probes/rev196_absorption_255_counterexample.lean:6-17` takes
`ν=A=l=x=1`, `g=8`, `b=0`, `d=128`: the input inequality is equality, while
the mutated conclusion is `128 ≤ 255/2`.  Lean checks both facts with zero
output.

## 4. Commands and results

Every Lean command sourced `. scripts/lean-env.sh`; every Lake command ran from
`verification/` with `LEAN_NUM_THREADS=6`.  The package directory is the shared
symlink:

```text
lrwxrwxrwx 1 ping ping 56 Sep 15 19:08 verification/.lake/packages -> /data_8T/ping/blowup_density/verification/.lake/packages
```

1. Module build:

```text
$ cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.MildGronwall
```

Exit 0.  Lake replayed inherited warnings from dependencies; none names
`MildGronwall.lean`.  Its exact final line was:

```text
Build completed successfully (10067 jobs).
```

Thus the target module is silent even though the complete Lake invocation is
not globally output-free.

2. Direct module check:

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A01/MildGronwall.lean
```

Exit 0, exactly 0 bytes of output.

3. Axiom/non-vacuity audit:

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/A01/axioms_mild_gronwall.lean
'NSFormalization.Section4.A01.mildNormConstant' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.mildNormConstant_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.euclideanWordNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.euclideanWordNorm_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.euclideanWordNorm_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.continuous_euclideanWordNorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.euclidean_full_word_limit' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.quadratic_regularized_word' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.mild_energy_absorption' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.outer_tame_low' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.inner_mild_energy' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.FiniteMildEnergy' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.mildGronwall' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.hb_of_base'' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.hb_of_base_inv'' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_sob' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_mild' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private._stdin.0.NSFormalization.Section4.A01.zero_energy' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exit 0; exactly 19 reports, all the required three axioms.

4. Repository check:

```text
$ LEAN_NUM_THREADS=6 make check
```

Exit 0.  The command emits the large contract-closure JSON; the exact terminal
tail was:

```text
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.042s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

5. Negative and counterexample probes:

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/A01/probes/rev196_absorption_255_fail.lean
```

Exit 1 with the exact expected error pasted in section 3.

```text
$ cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/A01/probes/rev196_absorption_255_counterexample.lean
```

Exit 0, exactly 0 bytes of output.

6. Hygiene/search results:

```text
$ rg -n -w 'sorry|admit|axiom|native_decide' formalization/NSFormalization/Section4/A01/MildGronwall.lean research/A01/axioms_mild_gronwall.lean research/A01/probes/rev196_*.lean
NO_FORBIDDEN_TOKENS
```

There are no `set_option maxHeartbeats` matches in either new lane Lean file.
`git diff --check HEAD^ HEAD` exits 0.  The worker commit paths are exactly:

```text
formalization/NSFormalization/Section4/A01/MildGronwall.lean
research/A01/A3_SPLIT.md
research/A01/ATTEMPTS_MILD_GRONWALL.md
research/A01/REPORT_196.md
research/A01/axioms_mild_gronwall.lean
```

No `verification/` path was touched, so the conditional `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration` gates are not
applicable.  The required current-base diff presently ends with:

```text
50 files changed, 795 insertions(+), 5313 deletions(-)
```

and `git merge-base --is-ancestor HEAD^ origin/erenup/integration` exits 1,
confirming that the lane must be rebased before merge.

## Exact fixes

1. Recut `MildGronwall` and `FiniteMildEnergy` with
   `ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0` immediately after `a`,
   and thread `ha` through the five family/corollary theorems named above.
2. Replace the correction-wrapper order sentence by: “At full cutoff `q+1`,
   choose external order `N=q-5`, so `N+6=q+1`; the wrapper remains unusable
   directly because it is specific to `CorrectionData`/`SpatialBudget`."
3. Rebase lane 196 onto current `origin/erenup/integration`, retain only the
   five worker paths plus this review/probes, and rerun the four mandatory gates.
