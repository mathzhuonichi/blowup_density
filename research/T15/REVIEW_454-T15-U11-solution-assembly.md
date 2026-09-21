ACCEPT

## 1. What the lane claims

The lane claims one explicit `ClassicalSolutionT` constructor and the literal
`ScalingAPI.solution` conclusion.  This is accurate.

1. The manuscript chooses one fixed placement and every sufficiently small
   positive scale, defines the parabolically rescaled fields, periodizes the
   spatial variables, and states that the result solves Navier--Stokes at the
   unchanged viscosity, starts from zero, and has mean-zero pressure
   (`paper/sections/03-torus.tex:101`, `paper/sections/03-torus.tex:105`,
   `paper/sections/03-torus.tex:112`, `paper/sections/03-torus.tex:120`,
   `paper/sections/03-torus.tex:122`, `paper/sections/03-torus.tex:123`,
   `paper/sections/03-torus.tex:141`).  The definitions used by the lane have
   exactly the paper's factors `eps^-1`, `eps^-2`, and `eps^-3`, the start time
   `T-eps^2`, and the pinned periodized/normalized fields
   (`formalization/NSFormalization/Section3/T15/Bridges.lean:56`,
   `formalization/NSFormalization/Section3/T15/Bridges.lean:59`,
   `formalization/NSFormalization/Section3/T15/Bridges.lean:64`,
   `formalization/NSFormalization/Section3/T15/Bridges.lean:69`,
   `formalization/NSFormalization/Section3/T15/Bridges.lean:74`,
   `formalization/NSFormalization/Section3/T15/Bridges.lean:81`,
   `formalization/NSFormalization/Section3/T15/Bridges.lean:97`).

2. The main theorem's conclusion at
   `formalization/NSFormalization/Section3/T15/Solution.lean:151`--`174` is
   statement-for-statement the canonical field at
   `formalization/NSFormalization/Section3/T15/Scaling.lean:301`--`305`:
   scale first, membership in `Ioc 0 place.ε₀`, then one
   `ClassicalSolutionT ν 0 (periodizedScaledForce ...) place.T`, followed by
   both field-pinning equalities.  There is no changed viscosity, endpoint, or
   quantifier order.

3. The nine explicit raw packet hypotheses are exactly those printed in the
   worker report and in the theorem
   (`formalization/NSFormalization/Section3/T15/Solution.lean:153`--`168`).
   Each occurs in the constructor proof: carrier/support and both smoothness
   assumptions feed regularity, Sobolev, pressure-gradient, and gauge fields;
   force support, force zero, and the equation feed momentum; divergence feeds
   incompressibility
   (`formalization/NSFormalization/Section3/T15/Solution.lean:128`--`147`).
   There is no named `Prop` input or hidden analytic premise.

4. The conclusion is not vacuous.  `PlacementData.eps_pos` makes the scale
   interval nonempty and `eps_time` forces a positive horizon
   (`formalization/NSFormalization/Section3/T15/Scaling.lean:169`--`183`); the
   constructor derives `0 < place.T` explicitly
   (`formalization/NSFormalization/Section3/T15/Solution.lean:125`--`127`).
   The canonical solution structure requires smoothness on `[0,T)`, initial
   data, divergence on `[0,T)`, momentum on `(0,T)`, Sobolev paths,
   pressure-gradient membership, both periodicities, and the pressure gauge
   (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:265`--`299`).
   The velocity and pressure fields are definitionally the requested fields
   (`formalization/NSFormalization/Section3/T15/Solution.lean:121`--`124`), and
   the theorem exposes both pins (`formalization/NSFormalization/Section3/T15/Solution.lean:170`--`178`).

## 2. What is in Lean

Finding 1 (pass, statement fidelity): all eight declarations claimed in
`REPORT_454.md` exist.  The six supporting results are at
`formalization/NSFormalization/Section3/T15/Solution.lean:30`, `:40`, `:58`,
`:72`, `:80`, and `:89`; the constructor is at `:102`; the main theorem is at
`:151`.  The implementation agrees with the report:

- Haar normalization is identified with the established cube normalization by
  `Paper1.integral_torusLift`
  (`formalization/NSFormalization/Section3/T15/Solution.lean:30`--`37`,
  `formalization/NSFormalization/Paper1/TorusCube.lean:39`--`52`).
- Raw pressure slab smoothness is proved from scaled smoothness and support,
  then normalization preserves it through time zero
  (`formalization/NSFormalization/Section3/T15/Solution.lean:40`--`69`,
  `formalization/NSFormalization/Paper1/PeriodicPressureNormalization.lean:121`--`135`).
- Velocity and normalized pressure have the required unit periods
  (`formalization/NSFormalization/Section3/T15/Solution.lean:72`--`96`), using
  the genuine lattice reindexing theorem
  (`vendor/NavierStokesAndEuler/NavierStokes/PeriodicLocalization.lean:191`--`210`).
- U8 supplies initial data, divergence, and momentum
  (`formalization/NSFormalization/Section3/T15/Equation.lean:35`--`41`,
  `formalization/NSFormalization/Section3/T15/Equation.lean:267`--`279`,
  `formalization/NSFormalization/Section3/T15/Equation.lean:281`--`314`); U9
  supplies the Sobolev and pressure-gradient fields
  (`formalization/NSFormalization/Section3/T15/SobolevPath.lean:56`--`88`,
  `formalization/NSFormalization/Section3/T15/SobolevPath.lean:90`--`116`); U10
  supplies the honest integrability-backed gauge
  (`formalization/NSFormalization/Section3/T15/Pressure.lean:123`--`156`).

Finding 2 (pass, non-vacuity): the delivered positive probe instantiates the
theorem with the registered viscosity-one packet
(`research/T15/probes/solution_closes.lean:128`--`137`), proves a nonzero
periodized velocity at an interior time (`research/T15/probes/solution_closes.lean:148`--`181`),
and transfers it to the velocity of the constructed solution
(`research/T15/probes/solution_closes.lean:183`--`195`).  This rules out an
empty scale interval, empty evolution interval, zero-field shortcut, or an
unrelated witness solution.

Finding 3 (pass, axioms and hygiene): the audit covers every declaration
(`research/T15/axioms_u11.lean:3`--`10`) and every result prints exactly
`[propext, Classical.choice, Quot.sound]`.  The lane commit adds
`Solution.lean`; it does not modify an existing Lean module.  The other five
lane files are a probe/audit and records, as shown by the exact `HEAD^..HEAD`
name-status output in part 4.  No forbidden proof primitive or heartbeat
override occurs in the delivered Lean files.

## 3. Gaps

No correctness, statement, axiom, build, or non-vacuity gap remains.

The worker report and attempts make no "not in the tree" or missing-lemma
claim (`research/T15/REPORT_454.md:81`--`104`,
`research/T15/ATTEMPTS_U11.md:72`--`75`), so the Section 4 missing-lemma grep
obligation is not applicable.  A whole-tree grep produced only unrelated
historical comments in Section 4 and no claimed U11 dependency.

The required negative check is substantive.  The scratch probe at
`research/T15/probes/rev454_negative_pressure_sign.lean:31`--`37` retains all
nine hypotheses and every proof argument but flips the sign of the required
pressure pin.  Lean rejects the unchanged proof with exactly the expected
positive-versus-negative pressure-field mismatch (full output below).

The requested triple-dot base diff emits a multiple-merge-base warning because
the integration branch advanced and this lane had merged an earlier integration
snapshot.  Its long output contains parallel integrated work, but its
modified-Lean-only query is empty.  More decisively, the lane's sole work
commit has the six-file output printed below and adds, rather than modifies,
the only formalization module.  This is a history-shape note, not a lane defect.

`verification/` is absent from both the lane commit and the requested base
diff.  Therefore the brief's conditional `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` gates do not
apply.

## 4. Commands and results

All Lake commands below ran from `verification/` after
`. ../scripts/lean-env.sh`, with `LEAN_NUM_THREADS=6`.

### Build and direct checks

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.Solution
[exit 0; Lake replayed pre-existing warnings from imported modules and no
 Solution.lean warning or error]
Build completed successfully (10012 jobs).
```

The replayed warnings were from existing files only:
`Source/FiniteHilbertBochner.lean`, `Paper1/PeriodicSobolevHilbert.lean`,
`Paper1/PeriodicH2Embedding.lean`, `Paper1/LocalizationBoundary.lean`,
`Formal/EndpointSafeTwoSpacePicard.lean`, `Paper1/PeriodicWeightShift.lean`,
`Source/RealSobolev.lean`, `Paper3/SpatiallyCompactTime.lean`,
`Paper3/RealPositiveDensity.lean`, `Paper3/RealVectorPositiveDensity.lean`,
`Source/PacketForceExtension.lean`, `Source/ViscosityPacket.lean`,
`Source/PhysicalBesselSobolev.lean`, `Paper3/SobolevDirectionalDerivative.lean`,
`Paper1/PeriodicScalarForceEndpoints.lean`,
`Paper1/PeriodicForceConvergence.lean`,
`Paper1/PeriodicInsertionSupport.lean`,
`Paper1/PeriodicPacketEndpointRates.lean`,
`Paper1/PeriodicCorrectionEndpointRates.lean`,
`Paper1/PeriodicDensityFiber.lean`, and `Paper1/PeriodicLocalLifespan.lean`.

```text
$ LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T15/Solution.lean
[no output]
[exit 0]

$ LEAN_NUM_THREADS=6 lake env lean ../research/T15/probes/solution_closes.lean
[no output]
[exit 0]
```

### Axiom audit

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/T15/axioms_u11.lean
'NSFormalization.Section3.T15.normalizePressureT_eq_normalizedPressure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T15.periodizedPressure_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.normalizedScaledPressure_contDiffOn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T15.isPeriodicOn_normalizePressureT' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T15.periodizedVelocity_periodic' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.normalizedScaledPressure_periodic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section3.T15.periodizedSolution' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T15.solution' depends on axioms: [propext, Classical.choice, Quot.sound]
[exit 0]
```

### Negative mutation

```text
$ LEAN_NUM_THREADS=6 lake env lean ../research/T15/probes/rev454_negative_pressure_sign.lean
../research/T15/probes/rev454_negative_pressure_sign.lean:37:2: error: Type mismatch
  solution hK hu hp hf hf0 hus hps heq hdiv place
has type
  ∀ ε ∈ Ioc 0 place.ε₀,
    ∃ S,
      S.velocity = periodizedScaledVelocity u place.x₀ place.T ε ∧
        S.pressure = normalizedScaledPressure p place.x₀ place.T ε
but is expected to have type
  ∀ eps ∈ Ioc 0 place.ε₀,
    ∃ S,
      S.velocity = periodizedScaledVelocity u place.x₀ place.T eps ∧
        S.pressure = -normalizedScaledPressure p place.x₀ place.T eps
[exit 1, expected]
```

### Repository gates

```text
$ make check
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 45,
  "source_counts": {
    "formalization": 683,
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
[the checker printed its 46-contract closure JSON; the command runner elided
 1,120,836 bytes of that mechanical list]
{
  "registered_contracts": 46,
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
[exit 0]
```

The copied-source `BoundaryCorollary.lean` token is the repository's known
unreachable historical token reported by the plan checker, not in this lane's
imported closure; the checker itself exits successfully.

### Hygiene and changed files

```text
$ rg -n "\b(sorry|admit|axiom|native_decide)\b|maxHeartbeats" \
    formalization/NSFormalization/Section3/T15/Solution.lean \
    research/T15/probes/solution_closes.lean \
    research/T15/probes/rev454_negative_pressure_sign.lean || true
[no output]
[exit 0 after `|| true`]

$ git diff --check
[no output]
[exit 0]

$ git diff --diff-filter=M --name-only origin/erenup/integration-section3...HEAD -- '*.lean'
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using 9171f6d9c69f391a13b2836d6c25496d43a08785
[no paths]
[exit 0]

$ git show --format= --name-status HEAD
A formalization/NSFormalization/Section3/T15/Solution.lean
A research/T15/ATTEMPTS_U11.md
A research/T15/REPORT_454.md
M research/T15/T15_SPLIT.md
A research/T15/axioms_u11.lean
A research/T15/probes/solution_closes.lean
[exit 0]

$ git diff --name-only origin/erenup/integration-section3...HEAD -- verification
warning: origin/erenup/integration-section3...HEAD: multiple merge bases, using 9171f6d9c69f391a13b2836d6c25496d43a08785
[no paths]
[exit 0]
```

No fixes are required.
