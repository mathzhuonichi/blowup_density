ACCEPT-WITH-NOTES

## 1. What the lane claims

The report claims an actual assembled `ClassicalSolutionT`, the three explicit
finite-sum formulas, `solution_pin`, `force_mem`, and `rest`, with no additional
analytic input (`research/T24/REPORT_468.md:5-9`).  It also claims the precise
cross term

```lean
spatialDerivative (d.component j).velocity t x
  ((d.component i).velocity (t, x)) = 0
```

for `i ≠ j`, `t ∈ Ico 0 d.T` (`research/T24/REPORT_468.md:11-19`).  These are
exactly the Ub4 targets in the split (`research/T24/T24_SPLIT.md:308-317`) and
the canonical record fields (`formalization/NSFormalization/Section3/T24/Multiple.lean:138-174`).

The mathematics matches the paper.  The paper defines `u`, `p`, and `f` as the
three finite sums at `paper/sections/03-torus.tex:707-710`, kills every
off-diagonal transport term and concludes the exact momentum equation at
`:711-712`, obtains compact positive-time force support and rest at `:712`,
and records the torus pressure-gauge adjustment at `:719`.  Thus this is the
assembled-solution part of the prescribed multi-region construction, not a
repackaged residual proposition.

The one note is citation hygiene only.  The new module header at
`formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:3` cites
`03-torus.tex:710-716`; source line 710 is only the closing display delimiter
and lines 714-716 start the later regional/energy argument.  Replace that one
line's range by `03-torus.tex:707-712,719`.  No Lean statement or proof changes.

## 2. What is in Lean

All reported declarations exist with the claimed statements.

- The three definitions and formula theorems are literal finite sums at
  `formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:41-51`.
- `rest` and `force_mem` have exactly the canonical types at `:69-74`.
- `component_nonoverlap` uses the common floor-lattice representative,
  `component_support`, and `regions_disjoint` at `:83-96`.  No support-closure
  strengthening is assumed.
- `crossTransport_eq_zero` has exactly the statement reported at `:100-102`.
  Its zero-advector branch is linearity (`:103-104`); its nonzero branch uses
  continuity to obtain a neighbourhood on which the advector stays nonzero,
  pointwise non-overlap to make the other component locally zero, and
  `EventuallyEq.fderiv_eq` (`:105-111`).  This is sufficient even when closures
  of disjoint open balls touch.
- The derivative, divergence, Sobolev-path, pressure-gradient, and pressure
  gauge fields are proved at `:113-173`; the temporal derivative, Laplacian,
  pressure gradient, advection, and momentum equation are proved at `:175-241`.
  In particular the double sum is reduced to its diagonal at `:218-229`.
- `solution` fills all thirteen fields at `:243-257`, matching the canonical
  structure field-for-field at
  `formalization/NSFormalization/Section3/T10/PeriodicData.lean:265-299`.
  `solution_pin` is definitionally true at `:259-260`.

The residual sign and ordering are correct: the registered residual is
`∂ₜu + (u·∇)u - νΔu + ∇p` at
`vendor/NavierStokesAndEuler/NavierStokes/R3/ProblemStatement.lean:54-63`,
and the assembled proof unfolds exactly that definition at
`formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:231-241`.
The force-class report is also honest: `MemForceT` consists only of global
smoothness, unit periodicity, and compact positive-time support at
`formalization/NSFormalization/Section3/T10/PeriodicData.lean:237-245`; it has
no mean-zero clause.  Its finite-sum proof is at
`formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:12-35`.

There is no vacuity from an empty family or empty evolution interval.  The
input record carries `0 < d.T` and `0 < d.N` at
`formalization/NSFormalization/Section3/T24/MultipleComponents.lean:28-31`.
The added review probe explicitly constructs both `Nonempty (Fin d.N)` and
`d.T / 2 ∈ Ioo 0 d.T` at
`research/T24/probes/rev468_nonvacuity.lean:15-20`; it elaborates with zero
output.  There is no `⊤.toReal`, empty-interval trick, named analytic premise,
or unused theorem binder in the delivered declarations.

## 3. Gaps and hygiene

There is no Ub4 proof gap.  The report says only that Ub5-Ub7 and final
30-field API assembly are out of this lane (`research/T24/REPORT_468.md:47-51`),
which agrees with the split's next units (`research/T24/T24_SPLIT.md:318-329`).
It makes no “missing from the tree” claim.  For completeness, the requested
whole-Section4 name search was run:

```text
$ grep -rnE 'crossTransport_eq_zero|forceClassT_finset_sum|assembled_momentum' formalization/NSFormalization/Section4 || true
<no output>
```

The lane commit adds the implementation module rather than modifying an
existing Lean module.  `git diff --name-status HEAD^ HEAD` reports
`A formalization/NSFormalization/Section3/T24/MultipleAssembled.lean` plus the
new research files and one `M research/T24/T24_SPLIT.md`; no pre-existing
`.lean` file is `M`.  The mandated comparison against the now-advanced
integration ref has two merge bases and currently prints the following; its
only Lean paths are additions, not modifications:

```text
$ git diff --name-status origin/erenup/integration-section3...HEAD
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using 84cbedb39e289aaafdd85cc42b42139dfc66e615
M NEXT_SESSION.md
M PLAN.md
M collaboration/briefs/465-T19-U13-U14-closure.md
M collaboration/briefs/466-T19-U10-U11-U12-projection.md
A collaboration/briefs/467-T24-UbCAN-Ub1-Ub3-multiple-regions.md
A formalization/NSFormalization/Section3/T19/Threading.lean
A formalization/NSFormalization/Section3/T24/MultipleAssembled.lean
M logs/AGENT_RUNS.csv
A research/T19/ATTEMPTS_U0.md
A research/T19/REPORT_461.md
A research/T19/REVIEW_461-T19-U0-insertion-from-reference.md
M research/T19/T19_SPLIT.md
A research/T19/axioms_u0.lean
A research/T19/probes/rev461_negative_lifespan.lean
A research/T19/probes/rev461_nonvacuity.lean
A research/T19/probes/threading_closes.lean
A research/T24/ATTEMPTS_UB4.md
A research/T24/REPORT_468.md
M research/T24/T24_SPLIT.md
A research/T24/axioms_ub4.lean
A research/T24/probes/assembled_closes.lean
```

`git diff --name-only origin/erenup/integration-section3...HEAD -- verification`
and `git diff --name-only HEAD -- verification` both produced no paths, so the
conditional `scripts/gates.sh` and `check_contracts.py --base-ref
origin/erenup/integration-section3` gates do not apply.  The token scan over
the delivered module, conformance/axiom files, and reviewer probes found no
`sorry`, `admit`, `axiom`, `native_decide`, or `set_option maxHeartbeats`.
`git diff --check HEAD^ HEAD` and `git diff --check` both produced no output.

The substantive negative check widens the momentum equation from `Ioo 0 d.T`
to `Ico 0 d.T` at `research/T24/probes/rev468_mutation.lean:13-19`.  It fails
for the expected load-bearing boundary mismatch, rather than because an
argument was removed:

```text
../research/T24/probes/rev468_mutation.lean:19:2: error: Type mismatch
  RegionsData.assembled_momentum d
has type
  ∀ t ∈ Ioo 0 d.T,
    ∀ (x : Space),
      NavierStokesR3.ProblemStatement.navierStokesResidual ν d.assembledVelocity d.assembledPressure t x =
        d.assembledForce (t, x)
but is expected to have type
  ∀ t ∈ Ico 0 d.T,
    ∀ (x : Space),
      NavierStokesR3.ProblemStatement.navierStokesResidual ν d.assembledVelocity d.assembledPressure t x =
        d.assembledForce (t, x)
```

Exit code: `1`, as required.

## 4. Commands and results

Every Lean command sourced `scripts/lean-env.sh`, used
`LEAN_NUM_THREADS=6`, and ran Lake from `verification/`.

```text
$ lake build NSFormalization.Section3.T24.MultipleComponents
[only replayed dependency lints]
Build completed successfully (10050 jobs).

$ lake build NSFormalization.Section3.T24.MultipleAssembled
[only replayed dependency lints]
Build completed successfully (10051 jobs).
```

Both exited `0`; there was no diagnostic from either target module itself.

```text
$ lake env lean ../formalization/NSFormalization/Section3/T24/MultipleAssembled.lean
<zero output>
exit 0

$ lake env lean ../research/T24/probes/assembled_closes.lean
<zero output>
exit 0

$ lake env lean ../research/T24/probes/rev468_nonvacuity.lean
<zero output>
exit 0
```

The implementation axiom audit exited `0` with this exact declaration list;
every entry is exactly `[propext, Classical.choice, Quot.sound]` (line wrapping
is cosmetic):

```text
'NSFormalization.Section3.T24.forceClassT_finset_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.assembledVelocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.assembledPressure' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.assembledForce' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.assembled_velocity_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.assembled_pressure_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.assembled_force_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.assembled_velocity_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.assembled_pressure_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.velocity_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.pressure_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.rest' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.force_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.component_slice' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.component_nonoverlap' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.crossTransport_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.assembled_spatialDerivative' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.assembled_divergence' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.assembled_sobolev' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.assembled_pressure_gradient' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.assembled_pressure_gauge' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.component_temporal' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.assembled_temporalDerivative' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.assembled_spatialLaplacian' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.assembled_pressureGradient' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.assembled_advection' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.assembled_momentum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.RegionsData.solution_pin' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The separate seven-declaration conformance axiom audit also exited `0`; each
printed exactly the same three axioms.

```text
$ make check
...
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
exit 0
```

The omitted middle is the command's very large machine-generated source and
50-contract closure JSON; it reported `registered_contracts: 50`, no missing
copied imports, and no failing policy check.  The terminal returned exit `0`.

Fixes: one documentation-only line — at
`formalization/NSFormalization/Section3/T24/MultipleAssembled.lean:3`, replace
`03-torus.tex:710-716` with `03-torus.tex:707-712,719`.
