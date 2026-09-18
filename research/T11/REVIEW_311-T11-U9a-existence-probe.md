ACCEPT

## 1. What the lane claims

The lane claims a route decision and a first analytic rung, not the missing
arbitrary-data local-existence theorem.  The report says that R2 (native torus
coefficient paths, using A01's causal-window/common-horizon strategy) is selected,
that the unconditional output is the real-vector heat layer, and that the
convolution estimate and `PeriodicQuantitativeLocalInput` remain open
(`research/T11/REPORT_311.md:5-11`, `research/T11/EXISTENCE_ROUTE.md:3-7`).  That is
an accurate description of the delivered Lean.

Statement fidelity checks:

- The named input at
  `formalization/NSFormalization/Section3/T11/LocalExistenceProbe.lean:35-41` is
  token-for-token the input mandated by the reviewed brief and by
  `research/T11/T11_SPLIT.md:81-90`: `K` is chosen before `a` and `g`, `K != top`,
  the same `K` bounds the datum and every force order, and one positive `delta`
  precedes all data.  No support, higher-order datum, or fixed-force hypothesis
  was inserted.
- The manuscript asks for forced local existence with one common interval for all
  Sobolev orders (`paper/sections/02-preliminaries.tex:105-120` and
  `paper/sections/appendix-a-local-theory.tex:60-77`), and its continuation
  argument specifically invokes an H1-controlled restart duration
  (`paper/sections/appendix-a-local-theory.tex:127-155`).  The lane does not claim
  that its H3/H2 Picard contract proves this stronger H1 statement
  (`research/T11/EXISTENCE_ROUTE.md:33-36`, `:179-186`).
- The coefficient weights and phantom-index convention are the canonical ones:
  `PeriodicSobolev s` is the real weighted Fourier submodule and the represented
  coefficient is `W(k)^(s/2) zhat(k)`
  (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:66-114`).  The
  H3 x H3 -> H2 convection formula removes two H3 weights and restores the H2
  weight, then applies the canonical Leray symbol
  (`formalization/NSFormalization/Section3/T11/LocalExistenceProbe.lean:202-231`).
  This agrees with the paper's Leray convention, including identity at the torus
  zero mode (`paper/sections/02-preliminaries.tex:75-88`).
- `TorusTwoSpaceContract` has exactly the upstream roles: same-space linear
  evolution, positive-time rough-to-strong smoothing, continuous bilinear source,
  locally integrable kernel, and coherence.  Compare the identifying fields at
  `formalization/NSFormalization/Section3/T11/LocalExistenceProbe.lean:220-232`
  with the upstream contract at
  `vendor/HeliCorgi/Formal/EndpointSafeTwoSpaceDuhamel.lean:393-444`.
  `TorusForcedPicard`, `TorusForcedMildOn`, and `TorusPicardConstants` then record
  the forced Duhamel operator, actual-vector integrability, self-map inequality,
  and strict contraction constant
  (`formalization/NSFormalization/Section3/T11/LocalExistenceProbe.lean:234-268`).
- All 17 theorem signatures printed in the worker report exist with the claimed
  statements.  Their source starts are:
  `torusMultiplier_norm_le` at `LocalExistenceProbe.lean:61`,
  `torus_weight_eq` at `:83`, `torus_weight_neg` at `:90`,
  `torusHeatSymbol_neg` at `:98`, `torusHeat_norm_le` at `:118`,
  `torusHeatSmoothing_norm_le` at `:137`, `torusHeatSmoothing_apply` at `:143`,
  `torusHeat_zero` at `:151`, `torusHeat_add` at `:161`,
  `torusHeatSmoothing_coherent` at `:173`, `torusHeat_solenoidal` at `:189`,
  `torus_bilinear_bound` at `:271`, `torusConstantDatum_isDatum` at `:287`,
  `torusConstantDatum_smul` at `:300`,
  `torusHomogeneousSolution_regularity` at `:352`,
  `quantitative_lifespan_lower_bound` at `:374`, and
  `nonzero_forced_witness` at `:392`.  These match the report list at
  `research/T11/REPORT_311.md:16-91`.
- The existing scalar heat theorem really does supply the advertised coefficient
  bound, including the zero mode
  (`formalization/NSFormalization/Paper1/PeriodicHeatMultiplier.lean:94-163`).
  The lane's vector lift, semigroup, smoothing coherence, and solenoidal
  preservation are unconditional (`LocalExistenceProbe.lean:107-200`).  By
  contrast, `torus_bilinear_bound` is honestly only the generic operator-norm
  estimate conditional on a `TorusTwoSpaceContract`; the report explicitly says
  it is not the missing convolution proof (`research/T11/REPORT_311.md:10-11`).
- There is no vacuity through `top.toReal`, an empty time interval, or an unused
  datum.  The non-vacuity theorem chooses a finite `K`, proves all exact datum and
  force premises, constructs a solution on the positive horizon `T = 1`, and
  proves both solution and force nonzero at `(0,0)`
  (`LocalExistenceProbe.lean:387-445`).  The copied conformance structure uses the
  required `Ico 0 T` and `Ioo 0 T` intervals
  (`research/T11/probes/existence_probe.lean:20-43`).

The route-source citations are also accurate.  `FlowMapUniformRestartPackage`
assumes `restart_past_terminal` rather than creating a PDE solution
(`vendor/HeliCorgi/Formal/UniformRestartContinuation.lean:29-49`); the abstract
Picard theorems are genuinely conditional on a two-space contract and a linear
contraction (`vendor/HeliCorgi/Formal/EndpointSafeTwoSpacePicard.lean:714-730`,
`:879-894`); and `ClassicalPeriodicLocalTheory.local_flow` and
`.finite_h2_extension` are structure fields
(`formalization/NSFormalization/Paper1/PeriodicLocalLifespan.lean:64-82`).

## 2. What is in Lean

The delivered module contains 33 named declarations and the axiom audit contains
33 matching guarded `#print axioms` commands
(`research/T11/axioms_existence_probe.lean:3-137`).  The important concrete
content is:

- bounded even real vector multipliers and exact canonical heat/smoothing symbols
  (`LocalExistenceProbe.lean:43-147`);
- heat identity, semigroup, smoothing coherence, and incompressibility
  preservation (`LocalExistenceProbe.lean:150-200`);
- an exact H3/H2 torus two-space construction specification and forced Picard
  semantics (`LocalExistenceProbe.lean:202-268`);
- a genuine spatially homogeneous, nonzero forced `ClassicalSolutionT` and all
  three unmodified `PeriodicLocalRegularity` clauses
  (`LocalExistenceProbe.lean:276-371`);
- the conditional lifespan lower bound from the exact named input
  (`LocalExistenceProbe.lean:373-385`); and
- a finite-`K`, nonzero force/nonzero solution satisfiability instance
  (`LocalExistenceProbe.lean:387-451`).

The report's future U9b/U9c/U9d statements are not theorem claims, but their exact
text does elaborate.  They are recorded at
`research/T11/EXISTENCE_ROUTE.md:127-177`; the retained scratch check is at
`tmp/311/route-statements.lean:13-34` and independently exited 0.

The reviewer mutation is at
`research/T11/probes/rev311_heat_constant_mutation.lean:12-25`: changing the heat
contraction constant from `1` to `1/2` makes direct reuse of the proof fail with
the expected type mismatch.  The probe additionally proves that the tightened
claim is actually false on a nonzero constant zero mode at time zero (`:27-42`),
and repeats the nonzero forced instance (`:44-53`).  Thus the negative check is
substantive and is not obtained by dropping an argument.

Hygiene is clean:

- `git diff --name-only origin/erenup/integration-section3...HEAD` lists one new
  Lean module, two new Lean research probes/audits, three new records, and the
  required two-line append to `T11_SPLIT`; no pre-existing Lean module is modified.
  The append is exactly the U9a status line
  (`research/T11/T11_SPLIT.md:136`).
- The changed Lean files contain no `sorry`, `admit`, `axiom`, or `native_decide`.
- The only heartbeat override is declaration-local, commented, and exactly
  `400000` (`LocalExistenceProbe.lean:387-392`).
- Both local instances are explicitly named
  (`LocalExistenceProbe.lean:28-33`).
- `git diff --check origin/erenup/integration-section3...HEAD` is empty.

## 3. Gaps

The lane correctly leaves `PeriodicQuantitativeLocalInput` unproved and does not
claim an inhabitant of `TorusTwoSpaceContract`
(`research/T11/REPORT_311.md:118-125`).  The remaining mathematical obligations
are the H3 x H3 -> H2 convolution bound, concrete continuous linear heat maps and
joint continuity, kernel integrability, forced fixed point, physical/pressure
reconstruction on a common horizon, and ultimately an H1-uniform lifespan.

I reran a whole-tree `grep -rnE` over
`formalization/NSFormalization/Section4` for the contract names and for forced
Picard, convolution bounds, strong continuity, common horizons, pressure recovery,
and H1 local theory.  It found similarly named Section4 results, but none closes
the torus coefficient gap:

- A01's `HasAprioriBound` is an explicit hypothesis on ordinary cylinder
  `SobolevSpace` paths (`formalization/NSFormalization/Section4/A01/Horizon.lean:97-114`),
  and its prescribed-horizon theorem consumes that hypothesis
  (`Horizon.lean:130-154`).
- A01's common-carrier theorem still assumes both `MildUniqueness` and a family of
  high-order a-priori bounds and uses the ordinary cylinder carrier
  (`formalization/NSFormalization/Section4/A01/CommonHorizon.lean:153-183`).
- The found `pressure_recovery_of_classicalSolution` is for
  `ClassicalSolutionR` and an `IsLerayComplement` on R3, not periodic Haar-gauged
  pressure recovery from torus coefficients
  (`formalization/NSFormalization/Section4/A01/ManuscriptRegularity.lean:172-181`).
- The genuine Section4 local solution theorem likewise has `initialClassR`,
  `MemForceR`, and `ClassicalSolutionR` types
  (`formalization/NSFormalization/Section4/A01/LocalSolution.lean:81-104`).

The worker's additional force-quantifier warning is correct: one finite bound for
each Sobolev order does not imply one common finite bound over all orders
(`research/T11/EXISTENCE_ROUTE.md:100-120`).  After this lane was committed, the
integration branch adopted the downstream primed input with a family
`M : Nat -> ENNReal`; that post-lane amendment assigns the one-line lifespan
reduction update to U9b
(`origin/erenup/integration-section3:research/T11/LEAD_AMENDMENTS.md:3-23`).
It does not make this lane unfaithful to the supplied
brief, whose exact unprimed input is what was reviewed here.  At the final status
check the lane was five commits behind `origin/erenup/integration-section3`; this is integration
sequencing, not a defect in the reviewed proof.

## 4. Commands and results

All Lean invocations sourced `scripts/lean-env.sh`; all Lake invocations ran from
`verification/` with `LEAN_NUM_THREADS=6`.

1. `lake build NSFormalization.Section3.T11.LocalExistenceProbe`

   Exit 0.  The command replayed warnings only from pre-existing dependencies
   (`FiniteHilbertBochner`, `PeriodicSobolevHilbert`,
   `EndpointSafeTwoSpacePicard`, `RealSobolev`, `SpatiallyCompactTime`,
   `RealPositiveDensity`, `RealVectorPositiveDensity`, `PacketForceExtension`,
   `ViscosityPacket`, `PhysicalBesselSobolev`, and
   `SobolevDirectionalDerivative`).  There was no warning from
   `LocalExistenceProbe`.  Exact terminal line:

   ```text
   Build completed successfully (9905 jobs).
   ```

2. Direct typechecks:

   ```text
   lake env lean ../formalization/NSFormalization/Section3/T11/LocalExistenceProbe.lean
   exit 0
   output: <empty>

   lake env lean ../research/T11/probes/existence_probe.lean
   exit 0
   output: <empty>

   lake env lean ../research/T11/axioms_existence_probe.lean
   exit 0
   output: <empty>

   lake env lean ../research/T11/probes/rev311_heat_constant_mutation.lean
   exit 0
   output: <empty>
   ```

3. Independent unguarded axiom-print pass.  Exit 0; exact output:

   ```text
   'NSFormalization.Section3.T11.torusProbeNormedGroup' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torusProbeNormedSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.PeriodicQuantitativeLocalInput' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torusMultiplier' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torusMultiplier_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torus_weight_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torus_weight_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torusHeatSymbol' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torusHeatSymbol_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torusSmoothingKernel' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torusHeat' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torusHeat_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torusHeatSmoothing' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torusHeatSmoothing_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torusHeatSmoothing_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torusHeat_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torusHeat_add' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torusHeatSmoothing_coherent' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torusHeat_solenoidal' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torusConvectionSymbol' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torusProjectedConvectionSymbol' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.TorusTwoSpaceContract' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torusForcedPicard' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.TorusForcedMildOn' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.TorusPicardConstants' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torus_bilinear_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torusConstantDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torusConstantDatum_isDatum' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torusConstantDatum_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torusHomogeneousSolution' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.torusHomogeneousSolution_regularity' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T11.quantitative_lifespan_lower_bound' depends on axioms: [propext,
    Classical.choice,
    Quot.sound]
   'NSFormalization.Section3.T11.nonzero_forced_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
   ```

4. Negative mutation, before wrapping it in `#guard_msgs`; exact failing output:

   ```text
   ../research/T11/probes/rev311_heat_constant_mutation.lean:16:2: error: Type mismatch
     torusHeat_norm_le s hν ht A
   has type
     ‖torusHeat s hν ht A‖ ≤ ‖A‖
   but is expected to have type
     ‖torusHeat s hν ht A‖ ≤ 1 / 2 * ‖A‖
   ```

   The checked-in reviewer probe preserves this expected failure under
   `#guard_msgs`, so its final typecheck is silent and exits 0
   (`research/T11/probes/rev311_heat_constant_mutation.lean:13-25`).

5. `make check` from the worktree root: exit 0.  The JSON closure dump is very
   large, so the exact command head and tail are reproduced per the repository's
   review-log size rule:

   ```text
   python3 experiments/check_formalization_plan.py --check
   ...
   python3 experiments/check_contracts.py
   ...
   python3 experiments/test_contract_policy.py
   .............
   ----------------------------------------------------------------------
   Ran 13 tests in 0.045s

   OK
   python3 experiments/check_work_queue.py
   45 work items: ownership, contract registration and task cards consistent.
   ```

6. Hygiene commands, exact relevant output:

   ```text
   $ git diff --name-only origin/erenup/integration-section3...HEAD
   formalization/NSFormalization/Section3/T11/LocalExistenceProbe.lean
   research/T11/ATTEMPTS_EXISTENCE_PROBE.md
   research/T11/EXISTENCE_ROUTE.md
   research/T11/REPORT_311.md
   research/T11/T11_SPLIT.md
   research/T11/axioms_existence_probe.lean
   research/T11/probes/existence_probe.lean

   $ rg -n --glob '*.lean' '\b(sorry|admit|axiom|native_decide)\b' <changed Lean files>
   <empty>

   $ git diff --check origin/erenup/integration-section3...HEAD
   <empty>
   ```

`verification/` was not touched, so the brief's conditional
`scripts/gates.sh` and `check_contracts.py --base-ref
origin/erenup/integration-section3` gates do not apply.  `make check` nevertheless
ran the ordinary architecture `check_contracts.py` successfully.

Required fixes: none.
