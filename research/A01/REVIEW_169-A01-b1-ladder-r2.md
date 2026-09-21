ACCEPT-WITH-NOTES

## 1. What the lane claims

The report claims a route-α R2 theorem at every natural order `m ≤ q - 1`: a
closed-interval continuous datum path for the velocity, a closed-interval continuous
datum path for the projected momentum residual, and a Hilbert-space `HasDerivAt`
identity at every `t ∈ Ioo 0 S`.  The report's displayed conclusion is the actual
conclusion of `exists_differentiable_datumPath` at
`formalization/NSFormalization/Section4/A01/DatumPathDeriv.lean:402`; its datum clauses
and derivative clause are at `DatumPathDeriv.lean:415-420`.  The hypotheses are the
Horizon data, not a substituted classical-solution assumption: force jet continuity is
at `DatumPathDeriv.lean:405-406`, angle invariance and ordinary descent are at
`:407-411`, and the exact Duhamel identity is at `:412-414`.  These agree with the
corresponding output of `localTheory_on_prescribed_horizon` at
`formalization/NSFormalization/Section4/A01/Horizon.lean:143-153`.

The claimed residual is exact.  `projectedResidualPath_eq` states

```lean
ν • laplacianOperator 1 m (restrictOperator 1 _ (u t)) +
  restrictOperator 1 _
    (leray 1 q (sobolevPath F hF q t - advection 1 hq (u t) (u t)))
```

at `DatumPathDeriv.lean:247-254`.  `source_eq` identifies the coefficient source as
`P(f-(u·∇)u)` at
`formalization/NSFormalization/Source/ForcedCylinderLocal.lean:51-68`.
`ordinaryResidualPath_eq_ordinaryDerivative` then identifies its ordinary descent with
the derivative used by the Duhamel theorem at `DatumPathDeriv.lean:178-189`, and
`realization_hasDerivAt` derives that ordinary derivative from the exact mild equation at
`formalization/NSFormalization/Source/OrdinaryForcedTime.lean:50-67`.  Thus the reported
derivative is genuinely the order-`m` datum of
`νΔu + P(F-(u·∇)u)`, not a merely named path.

This is the mathematics requested by the brief.  The manuscript's mild equation has
exactly the heat, projected-advection, and projected-force terms at
`paper/sections/appendix-a-local-theory.tex:109-113`; its regularity discussion says the
projected equation first gives `W^{1,∞}_t H^k_x`, then a continuous right-hand side and
repeated time differentiation at `appendix-a-local-theory.tex:71-76`.

The report's other named declarations also exist with the claimed types:

- `datumPath_hasDerivAt` has the reusable `m+2 ≤ q+1` statement, continuous-map
  inputs `A,R`, the two honest datum hypotheses, and interior `HasDerivAt` conclusion at
  `DatumPathDeriv.lean:346-360`.
- `ordinaryLift_projectedResidualOrdinaryPath` proves exact recovery of the cylinder
  residual at every point of `Icc 0 S` at `DatumPathDeriv.lean:268-282`.
- `residualDatum_is_timeDerivative` has exactly the conditional hypothesis
  `∀ x, HasDerivAt (fun r => v (r,x)) ((ordinaryResidualPath …) x) t` at
  `DatumPathDeriv.lean:442-451` and concludes that `R t` is the datum of
  `x ↦ deriv (fun r => v (r,x)) t` at `:452-455`.  This is an honest isolated R3
  bridge: it assumes precisely the representative-side identification still to be
  constructed and is not being passed off as an unconditional representative theorem.

No hypothesis makes the flagship statement vacuous.  In particular `hS : 0 < S` at
`DatumPathDeriv.lean:403` makes `Ioo 0 S` nonempty, and `hν`, `hU`, `hduh`, `hu`, and
`hF` are all consumed in the proof at `:421-438`.  There is no ENNReal `.toReal`
statement or empty-interval trick.

## 2. What is in Lean

The selection differentiated is literally a selection returned by lane 161's theorem:
`exists_differentiable_datumPath` invokes `exists_continuous_datumPath` at
`DatumPathDeriv.lean:422`; that theorem's velocity datum property and continuity are at
`formalization/NSFormalization/Section4/A01/DatumPathContinuous.lean:82-105`.
Wrapping the chosen function as `Ac` at `DatumPathDeriv.lean:433` does not change the
path.  Thus this is the same lane-161 continuous selection in the precise existential
sense requested by the brief, not an unrelated path lacking its defining property.

The derivative is in the requested Hilbert space.  Both `A` and `R` have codomain
`RealVectorSobolev (m : ℝ)` at `DatumPathDeriv.lean:415`, and the conclusion is a
genuine `HasDerivAt` of the clamped real extension at every interior time at `:419-420`.
Because `R` is a continuous map on `Icc 0 S`, this supplies the asserted continuous
interior derivative (with no endpoint derivative claim).

The order bookkeeping is sound:

- the reusable residual needs `m + 2 ≤ q + 1` at `DatumPathDeriv.lean:89-96`;
- the flagship derives this from `m ≤ q - 1` at `DatumPathDeriv.lean:421`;
- the two lost orders are exactly those needed to apply `Δ` to the order-`q+1`
  cylinder velocity, while the nonlinear source is still available at order `q`;
- consequently `m=q` and `m=q+1` are excluded because the available velocity does not
  put `Δu` in those spaces.  The injectivity of order lowering is not the source of
  that exclusion.  `lowerDatumL_injective` and `lowerVectorL_injective` hold for every
  `r ≤ s` at `DatumPathDeriv.lean:59-79`; they are used later to lift the already
  identified weak derivative from order zero at `:361-398`.

The heartbeat exception is acceptable.  It is the proof module's only override, is
per-declaration, is exactly `400000`, and the preceding comment identifies the two
dependent restriction rewrites as the reason at `DatumPathDeriv.lean:137-139`.  The
verbatim default-budget probe is
`research/A01/probes/rev169_default_heartbeats.lean:14-44`; at its existing explicit
`rw [laplacianOperator_translation_local]` on line 42 Lean deterministically reaches the
default 200000-heartbeat limit.  The proof contains no `decide`, and the hot operation is
already a targeted `rw`, not a broad `simp` that should simply be replaced by rewriting.

The module contains 23 declarations, listed at `DatumPathDeriv.lean:59-455`, and the
axioms file prints all 23 at `research/A01/axioms_b1_r2.lean:18-40`.  Every printed set
is exactly `[propext, Classical.choice, Quot.sound]`.

The negative mutation is substantive.  In
`research/A01/probes/rev169_negative_sign.lean:17-27` I flipped the viscous term from
`νΔu` to `-νΔu` without removing any argument.  The original formula proof fails with
the expected type mismatch between `ν • laplacianOperator …` and
`-ν • laplacianOperator …`.

The main theorem is non-vacuous on the zero pair.  The lane's conformance file really
sets `q=6`, `m=0`, `S=ν=1`, zero force, `u := 0`, and `U := 0` at
`axioms_b1_r2.lean:53-94`, and derives the exact zero Duhamel equation at `:78-87`.
A stronger reviewer probe proves that the projected residual path itself is zero and
uses datum uniqueness to derive that the selected `R` equals zero at
`research/A01/probes/rev169_zero_residual.lean:70-88`; it compiles successfully.

Hygiene is otherwise clean.  A token scan of `DatumPathDeriv.lean` and
`axioms_b1_r2.lean` found no `sorry`, `admit`, `axiom`, or `native_decide`.  The only
changed formalization module is the newly added `DatumPathDeriv.lean`; the sole modified
pre-existing path is the brief-mandated record `research/A01/B1_LADDER.md`.  No
`verification/` path changed.  The manuscript citation used in the ladder at
`research/A01/B1_LADDER.md:117-119` matches the paper lines cited above.

## 3. Gaps and required note

R2 itself has no Lean or statement-fidelity gap in the proved range.  The remaining
representative/pressure bridge is accurately reported as downstream work.  I ran the
required whole-tree search over `formalization/NSFormalization/Section4` for
`residualDatum`, `timeDerivative`, `timeDeriv`, `projectedResidual`, `ordinaryResidual`,
physical residual/Leray-pressure combinations, and smooth-representative combinations.
The relevant hits do not close this R2 input shape:

- `A04.timeDeriv_isSobolevDatum` assumes an already constructed
  `ClassicalSolutionR`, a smooth datum path, and joint velocity smoothness at
  `formalization/NSFormalization/Section4/A04/TimeDerivative.lean:181-205`;
- `C01.residualPath` and its jet continuity assume `ClassicalSolutionR` at
  `formalization/NSFormalization/Section4/C01/JetPaths.lean:242-263`;
- the strongest pressure assembly found, including
  `isSobolevDatum_pressureGradient_lerayComplement`, also starts from
  `ClassicalSolutionR` and `MemForceR` at
  `formalization/NSFormalization/Section4/D01/PressureJets.lean:87-108`.

The corresponding search over `Source/`, `Paper1/`, and `Paper3/` found ordinary
Duhamel differentiation (`Source/OrdinaryForcedTime.lean`) and unrelated physical
residual/periodic representative results, but no theorem constructing the B1 smooth
representative or proving its pointwise time derivative from these Horizon inputs.
Thus the report's circularity/gap claim survives the mandated negative search.

One exact record fix is required before treating the conformance witness as satisfying
the lead's stronger non-vacuity checkpoint:

1. In `research/A01/axioms_b1_r2.lean:47-52`, strengthen the conclusion to expose the
   zero derivative residual, retain `hR` instead of `_` at `:88`, and derive `R = 0` by
   the zero-residual calculation plus datum uniqueness; the compiling replacement is
   `research/A01/probes/rev169_zero_residual.lean:22-88`.

As written, the axioms example applies the theorem to `u=U=0`, but it drops the
residual-datum fact at `axioms_b1_r2.lean:88` and never establishes `R=0`.  This is a
conformance-evidence omission, not a defect in the theorem: the reviewer probe confirms
that `R=0` is derivable.

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`; all `lake` commands were run
from `verification/` with `LEAN_NUM_THREADS=6`.

1. Module build:

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.DatumPathDeriv
[exit 0]
… replayed warnings only from pre-existing dependency files …
Build completed successfully (10006 jobs).
```

There was no warning from `DatumPathDeriv.lean`.  Because Lake's replayed dependency
warning stream was 205 lines, I also reran the exact combined stream through SHA-256:

```text
$ set -o pipefail; LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.DatumPathDeriv 2>&1 | sha256sum
d4459ce084088f0d98f3e958b75113734565942fdf083501be8204fd3959ab66  -
[exit 0]
```

2. Direct module check:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A01/DatumPathDeriv.lean
[no output]
[exit 0]
```

3. Axiom/conformance check (exact output):

```text
'NSFormalization.Section4.A01.lowerDatumL_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.lowerVectorL_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderSourcePath' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderResidualPath' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderResidual' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.cylinderResidual_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.laplacianOperator_translation_local' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.cylinderResidual_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.ordinaryResidualPath' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.ordinaryResidualPath_eq_ordinaryDerivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.ordinaryLift_adjoint_of_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.ordinaryLift_ordinaryResidualPath' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.sobolevPath_angle_invariant' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.projectedResidualPath' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.projectedResidualOrdinaryPath' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.projectedResidualPath_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.ordinaryLift_projectedResidualOrdinaryPath' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.weakDerivsBound_cylinder' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.datum_sub_norm_sq_le_general' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.exists_continuous_datumPath_general' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.datumPath_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.exists_differentiable_datumPath' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.A01.residualDatum_is_timeDerivative' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
[exit 0]
```

4. Repository check:

```text
$ make check
[exit 0; 25367 output lines]
python3 experiments/check_formalization_plan.py --check
…
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
…
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.047s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

The architecture output retains the pre-existing
`NSFormalization.Paper1.BoundaryCorollary:90` copied-source `sorry` notice and
`source_hashes_match: false`; neither is in this lane's closure or diff.  An exact
combined-stream fingerprint from a second successful run is:

```text
$ set -o pipefail; make check 2>&1 | sha256sum
ee40f18d2c99e89ad41e2fddd2c16d978545ce58c833d17cca0841642f2ec2c6  -
[exit 0]
```

5. Default-heartbeat probe (exact output):

```text
../research/A01/probes/rev169_default_heartbeats.lean:42:6: error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000) has been reached

Note: Use `set_option maxHeartbeats <num>` to set the limit.

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
[exit 1, expected]
```

6. Negative sign mutation (exact output):

```text
../research/A01/probes/rev169_negative_sign.lean:27:2: error: Type mismatch
  projectedResidualPath_eq hq hm ν F hF u t
has type
  (projectedResidualPath hq hm ν F hF u) t =
    ν • (laplacianOperator 1 m) ((restrictOperator 1 ⋯) (u t)) +
      (restrictOperator 1 ⋯) ((leray 1 q) ((sobolevPath F hF q) t - ((advection 1 hq) (u t)) (u t)))
but is expected to have type
  (projectedResidualPath hq hm ν F hF u) t =
    -ν • (laplacianOperator 1 m) ((restrictOperator 1 ⋯) (u t)) +
      (restrictOperator 1 ⋯) ((leray 1 q) ((sobolevPath F hF q) t - ((advection 1 hq) (u t)) (u t)))
[exit 1, expected]
```

7. Strong zero-residual non-vacuity probe:

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/A01/probes/rev169_zero_residual.lean
[no output]
[exit 0]
```

8. Hygiene/diff checks:

```text
$ rg -n --glob '*.lean' '\b(sorry|admit|axiom|native_decide)\b' formalization/NSFormalization/Section4/A01/DatumPathDeriv.lean research/A01/axioms_b1_r2.lean
[no output]

$ git diff --name-only origin/erenup/integration...HEAD -- verification
[no output]

$ git diff --name-status origin/erenup/integration...HEAD
A formalization/NSFormalization/Section4/A01/DatumPathDeriv.lean
A research/A01/ATTEMPTS_B1_R2.md
M research/A01/B1_LADDER.md
A research/A01/REPORT_169.md
A research/A01/axioms_b1_r2.lean
```

Because the diff contains no `verification/` path, the brief's conditional
`scripts/gates.sh` and `check_contracts.py --base-ref origin/erenup/integration` gates
do not apply and were not run.

9. Paper and whole-tree gap checks:

```text
$ sed -n '71,76p' paper/sections/appendix-a-local-theory.tex
More explicitly, the bounds in every spatial Sobolev order and the
projected equation first give $u\in W^{1,\infty}_tH^k_x$ for each $k$,
hence continuity into every $H^k$. The equation then has a continuous
right-hand side in every $H^k$; repeated time differentiation gives
$C^j_tH^k_x$ regularity for all $j,k$, including one-sided derivatives
at the initial time. We apply the projected formulation with force $\PP f$; the pressure

$ sed -n '109,113p' paper/sections/appendix-a-local-theory.tex
In either domain, the resulting velocity satisfies the mild equation
\begin{align}
 u(t)={}&e^{\nu t\Delta}a
 -\int_0^t e^{\nu(t-r)\Delta}\PP\nabla\cdot(u\otimes u)(r)\dd r\nonumber\\
 &+\int_0^t e^{\nu(t-r)\Delta}\PP f(r)\dd r.\label{eq:mild}

$ grep -rnE --include='*.lean' 'residualDatum|timeDerivative|timeDeriv|pointwise time derivative|projectedResidual|ordinaryResidual|physical.*residual|residual.*physical|pressure.*Leray|Leray.*pressure|smooth representative|representative.*smooth' formalization/NSFormalization/Section4 | wc -l
45
```

The 45 matches include the three strongest candidates cited in part 3; opening those
declarations confirms their `ClassicalSolutionR` hypotheses at the cited lines.
