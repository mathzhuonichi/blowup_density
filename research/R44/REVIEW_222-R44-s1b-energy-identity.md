ACCEPT-WITH-NOTES

# 1. What the lane claims

The worker claims the exact S1b identity for every positive viscosity, admissible
force, classical solution, and interior time, with derivative value

```text
-2 * ν * Z(u(t))^2 - 2 * ⟪datum₋½((u·∇)u), Ju⟫
  + 2 * forceJPairing(...).
```

This is the statement actually printed in the report
(`research/R44/REPORT_222.md:3-12`) and actually declared as
`energy_identity` (`formalization/NSFormalization/Section4/R44/EnergyIdentity.lean:286-299`).
The coefficient and signs agree with the requested testing calculation: the
paper defines `Y`, `Z`, and `B` at `paper/sections/04-whole-space.tex:146-150`
and says that testing against `Ju` gives dissipation `ν Z²` at
`paper/sections/04-whole-space.tex:152`; solving
`(1/2)(Y²)' + νZ² + advection = force` for `(Y²)'` gives exactly the displayed
Lean value.  The split's S1 target and S1b row are at
`research/R44/R44_SPLIT.md:53-73`.

The report's inventory is also accurate.  The module contains canonical slice
data and lowering (`EnergyIdentity.lean:23-53`), the smooth half-order velocity
path (`EnergyIdentity.lean:55-61`), the slice `JWeightDatum` and order-six force
pin (`EnergyIdentity.lean:63-90`), norm differentiation
(`EnergyIdentity.lean:92-102`), exact lowered momentum
(`EnergyIdentity.lean:104-123`), weight redistribution
(`EnergyIdentity.lean:125-136`), Laplacian and pressure evaluations
(`EnergyIdentity.lean:138-233`), energy assembly (`EnergyIdentity.lean:235-299`),
and the zero-solution check (`EnergyIdentity.lean:301-332`).  These are exactly
the declarations summarized at `research/R44/REPORT_222.md:14-26`.

There is no silent analytic hypothesis in the final theorem: its only explicit
inputs are `0 < ν`, `MemForceR f`, `ClassicalSolutionR ν a f T`, and
`t ∈ Ioo 0 T` (`EnergyIdentity.lean:286-293`).  The four temporary datum
hypotheses in `energy_identity_of_data` are discharged in the public theorem by
the smooth-slice existence results (`EnergyIdentity.lean:294-299`).  They are
honest realizability hypotheses, not estimates.  The `.toReal` norms are not
using the `⊤.toReal = 0` escape: `jWeightDatumPath` supplies actual half-order,
three-half-order, gradient, and negative-half-order data
(`EnergyIdentity.lean:64-81`), while `Y_eq_norm` and `Z_sq_eq_sum_norm` identify
the physical norms with finite Hilbert data
(`formalization/NSFormalization/Section4/R44/JWeight.lean:149-165`).
The interval is demonstrably inhabited in the checked instance `T = 1`,
`t = 1/2` (`research/R44/axioms_s1b.lean:30-39`).

The cited upstream statements have the shapes the proof needs:

* `Jmul` is the stored-data realization of physical
  `(I-Δ)^(1/2)` (`JWeight.lean:37-63`), and the datum package and physical
  pairings are defined at `JWeight.lean:97-134`.
* Smooth integer-order solution paths are supplied at
  `formalization/NSFormalization/Section4/A04/RestartFixedForce.lean:144-183`,
  squared-norm differentiation at
  `formalization/NSFormalization/Section4/A04/DerivNorm.lean:106-122`, and the
  exact momentum sign pattern `ν • L - N - P + F` at
  `formalization/NSFormalization/Section4/A04/MomentumDatum.lean:123-151`.
* `lowerVectorL` really is a continuous linear order-lowering map
  (`formalization/NSFormalization/Section4/D01/HalfOrder.lean:91-113`).
* Velocity solenoidality and Leray self-adjointness are the exact pressure-drop
  ingredients (`formalization/NSFormalization/Section4/A04/PressureDrop.lean:150-186`),
  and the pressure datum is pinned to the Leray complement at
  `formalization/NSFormalization/Section4/D01/PressureJets.lean:110-119`.
* The cited homogeneous twins do have the stated Laplacian, transverse, and
  longitudinal meanings at
  `formalization/NSFormalization/Section4/R43/CriticalDatumPath.lean:508-517`,
  `:557-624`, and `:626-634`.

Finally, the sibling-name disclosure is correct.  Read-only `git show` of
`erenup/220-R44-s1c-trilinear` shows `AdvectionJDatum.advectionNegHalf` and
`advectionJPairing h ha := ⟪ha.advectionNegHalf, Jmul h.velocityThreeHalf⟫` in
`formalization/NSFormalization/Section4/R44/TrilinearJ.lean:252-273` on that
branch.  The local `energyAdvectionJPairing h N` is the same expression with an
explicit datum argument (`EnergyIdentity.lean:235-237`).

# 2. What is in Lean

The public API proves the requested mathematics without a residual named
hypothesis:

* `hasDerivAt_Y_sq` differentiates the actual lane-218 `Y²`, not a replacement
  norm (`EnergyIdentity.lean:93-102`).
* `energyVelocity_momentum` lowers the exact order-two momentum identity to
  order `1/2` (`EnergyIdentity.lean:105-123`).
* `inner_eq_jPairing` converts the half-order inner product into the
  `H^{-1/2}`/`Ju` pairing (`EnergyIdentity.lean:126-136`).
* `laplacian_jPairing` proves the raw equality `⟪Δu,Ju⟫ = -Z²`
  (`EnergyIdentity.lean:160-205`); scalar multiplication by `ν` is performed in
  the assembly (`EnergyIdentity.lean:262-281`).
* `pressure_jPairing_zero` proves the pressure equality, rather than assuming
  it (`EnergyIdentity.lean:207-233`).
* `energy_identity` constructs every auxiliary datum and exposes only the four
  intended inputs (`EnergyIdentity.lean:286-299`).

The conformance file lists all 20 declarations and gives the closed zero-force,
zero-solution instance (`research/R44/axioms_s1b.lean:9-39`).  Its actual output
shows exactly `[propext, Classical.choice, Quot.sound]` for each declaration.

Hygiene is clean.  The changed implementation contains no
`sorry`/`admit`/`axiom`/`native_decide`.  The only heartbeat overrides are local,
commented, and exactly 400000 (`EnergyIdentity.lean:157-159` and `:239-241`).
The integration diff adds one new formalization module; it does not modify an
existing Lean module.  The other changes are the requested records and
conformance file.  `git diff --check origin/erenup/integration...HEAD` is clean.

The reviewer mutation is
`research/R44/probes/rev222_flip_dissipation.lean:13-21`.  It changes the
substantive main-statement coefficient from `-2 * ν` to `+2 * ν` while keeping
every argument and hypothesis.  Lean rejects the proof precisely because the
proved derivative has the negative coefficient.  The non-vacuity instance was
already present, so no duplicate was added.

# 3. Gaps

There is no S1b analytic proof gap.  There is one minor API-fidelity note: the
brief asked for the final nonlinear term to be spelled literally with lane
220's `AdvectionJDatum`/`advectionJPairing`, whereas this branch necessarily
exposes the extensionally identical `energyAdvectionJPairing` because lane 220
is not in its base (`EnergyIdentity.lean:235-237`, `:283-293`).  The worker
discloses this accurately rather than hiding it (`research/R44/REPORT_222.md:32-36`).
It does not change the proved mathematics, but the direct rewrite should be
added when both sibling modules coexist.

The other disclosed follow-up work at
`research/R44/REPORT_222.md:28-36` is accurate after whole-tree searches:

* `grep -rn` for `advectionJPairing|AdvectionJDatum` in all of
  `formalization/NSFormalization/Section4` finds only the explanatory reference
  in `EnergyIdentity.lean:285`; lane 220's API is not yet in this tree.  Thus the
  sibling adapter really is an integration step.
* Searches for the R44 trilinear/absorption conclusion find no S1c or S1d
  theorem.  `R44/Pieces.lean` explicitly describes the PDE inequality as a
  separate obligation (`formalization/NSFormalization/Section4/R44/Pieces.lean:7-21`).
* The existing scalar closure still *assumes* both
  `IntervalIntegrable E'` and the pointwise energy inequality
  (`Pieces.lean:153-166`); it does not construct the time-integrable derivative
  path.  This confirms the time-assembly gap rather than contradicting it.
* Searches of `verification/contracts.json`, `verification/Contracts`,
  `verification/Bindings`, and `verification/Tests` find only general R44
  consumer/scope prose, not an EnergyIdentity contract or binding.  Contract
  registration therefore remains open as reported.

The current branch is behind the moving integration ref, but the required
merge-base diff is confined to the five lane deliverables, and every gate below
passes in this worktree.  This is not a lane defect.

# 4. Commands and results

All Lean/Lake commands were run after sourcing `scripts/lean-env.sh`, with
`LEAN_NUM_THREADS=6`, and Lake was invoked only from `verification/`.

## Diff and hygiene

```text
$ git diff --name-only origin/erenup/integration...HEAD
formalization/NSFormalization/Section4/R44/EnergyIdentity.lean
research/R44/ATTEMPTS_S1B.md
research/R44/R44_SPLIT.md
research/R44/REPORT_222.md
research/R44/axioms_s1b.lean

$ rg -n '\b(sorry|admit|axiom|native_decide)\b' \
    formalization/NSFormalization/Section4/R44/EnergyIdentity.lean \
    research/R44/axioms_s1b.lean \
    research/R44/probes/rev222_flip_dissipation.lean
[no output; exit 1, meaning no match]

$ rg -n 'maxHeartbeats|set_option' \
    formalization/NSFormalization/Section4/R44/EnergyIdentity.lean \
    research/R44/axioms_s1b.lean \
    research/R44/probes/rev222_flip_dissipation.lean
formalization/NSFormalization/Section4/R44/EnergyIdentity.lean:158:set_option maxHeartbeats 400000 in
formalization/NSFormalization/Section4/R44/EnergyIdentity.lean:240:set_option maxHeartbeats 400000 in

$ git diff --check origin/erenup/integration...HEAD
[no output; exit 0]
```

## Required build and direct typechecks

```text
$ cd verification && . ../scripts/lean-env.sh && \
    LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.R44.EnergyIdentity
...
Build completed successfully (10537 jobs).
[exit 0]
```

The omitted build lines are replayed warnings from existing dependency files
(the first is `NSFormalization.Source.FiniteHilbertBochner`); there is no warning
from `EnergyIdentity.lean`.  In accordance with the repository lesson against
pasting thousands of unrelated lines, only the exact terminal result is shown.

```text
$ cd verification && . ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 \
    lake env lean ../formalization/NSFormalization/Section4/R44/EnergyIdentity.lean
[no output; exit 0]
```

The conformance command exited 0 and printed the following audit (the one
wrapped entry is reproduced as Lean printed it):

```text
'NSFormalization.Section4.R44.energyDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.energyDatum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.energyDatum_isDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.energyDatum_eq_lower' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.energyVelocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.energyVelocity_isDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.energyVelocity_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.jWeightDatumPath' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.jWeightDatumPath_force_eq_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R44.hasDerivAt_Y_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.energyVelocity_momentum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.inner_eq_jPairing' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.half_laplacian_component' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.laplacian_jPairing' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.pressure_jPairing_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.energyAdvectionJPairing' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.energy_identity_of_data' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.energy_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.energyDatum_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.zero_energy_terms' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Repository gates

`make check` exited 0.  Its full output is about 290 KB because the existing
contract checker prints complete module closures.  The exact relevant head and
tail are:

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 536,
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
...
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.044s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

The displayed source-manifest diagnostics concern existing copied sources, not
this diff; the command's exit status is 0.

The two additional gates claimed by the worker were also rerun:

```text
$ . scripts/lean-env.sh && LEAN_NUM_THREADS=6 make test
lake -d verification test
...
info: Tests/EnergyAbsorptionV4.lean:18:0: Contract BlowupDensity.Tests.checkedEnergyAbsorptionV4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:19:0: Contract BlowupDensity.Bindings.energyAbsorptionPartialV3_of_v4: checked; standard logical axioms only
info: Tests/EnergyAbsorptionV4.lean:100:0: Contract BlowupDensity.Tests.energyAbsorptionV4_terminalFinite: checked; standard logical axioms only
[exit 0]

$ . scripts/lean-env.sh && LEAN_NUM_THREADS=6 make test-mutations
...
implementation_refactor: accepted
admitted_proof: rejected as required
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
[exit 0]
```

No file under `verification/` is in the lane diff, so the review request makes
`scripts/gates.sh` and
`python3 experiments/check_contracts.py --base-ref origin/erenup/integration`
conditional and they are not applicable here.

## Negative mutation

```text
$ cd verification && . ../scripts/lean-env.sh && LEAN_NUM_THREADS=6 \
    lake env lean ../research/R44/probes/rev222_flip_dissipation.lean
../research/R44/probes/rev222_flip_dissipation.lean:21:2: error: Type mismatch
  energy_identity hν hf w ht
has type
  HasDerivAt (fun r => (Y fun x => w.velocity (r, x)) ^ 2)
    (-2 * ν * (Z fun x => w.velocity (t, x)) ^ 2 -
        2 *
          energyAdvectionJPairing (jWeightDatumPath w hf t ⋯) (energyDatum (-1 / 2) fun x => advection w.velocity t x) +
      2 * forceJPairing (jWeightDatumPath w hf t ⋯))
    t
but is expected to have type
  HasDerivAt (fun r => (Y fun x => w.velocity (r, x)) ^ 2)
    (2 * ν * (Z fun x => w.velocity (t, x)) ^ 2 -
        2 *
          energyAdvectionJPairing (jWeightDatumPath w hf t ⋯) (energyDatum (-1 / 2) fun x => advection w.velocity t x) +
      2 * forceJPairing (jWeightDatumPath w hf t ⋯))
    t
[exit 1, expected]
```

Fixes:

1. After lane 220 is in the same base, add the direct datum-uniqueness bridge
   `energyAdvectionJPairing ... (energyDatum ...) = advectionJPairing ... ha`
   and expose the companion `energy_identity` statement using lane 220's
   literal pairing name.
