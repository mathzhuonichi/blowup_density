# Lane 340 (T11 / U17) — assembly, contract, binding, tests; `T01.torus_local_theory` registered

## 1. Which theorem was proved

Proposition `prop:local` on the unit three-torus
(`paper/sections/02-preliminaries.tex:28-36,75-120`,
`paper/sections/appendix-a-local-theory.tex:60-157`) in the four-API form reconciled in
`research/T11/RECONCILIATION.md` and stated in `research/T11/Spec.lean`:

* **Local theory** (8 fields) — one common horizon `horizon ν a f` for every
  admissible `(ν, a, f)`, a classical periodic solution on it, all three
  regularity clauses (smooth datum path at every integer order, the pressure
  Poisson equation, the projected equation), velocity and normalized-pressure
  uniqueness on the common interval, `ofReal horizon ≤ T_max`, existence of a
  maximal pair and its uniqueness at every presingular time.
* **Continuation** (5 fields) — restart uniformly over a compact restart window,
  the Grönwall higher-order bound at every integer order from a finite squared
  `H²` integral, endpoint restart with exact overlap agreement, concrete
  extension beyond `S`, and "locally finite criterion ⟹ infinite lifespan"
  (with the load-bearing non-strict endpoint).
* **Galilean mean reduction** (6 fields) — `m(t) = ∫a + ∫₀ᵗ ∫f`, `m' = ∫f`, the
  data-defined transformed solution with its regularity, class preservation,
  the three mean-zero identities and the translation isometry of every
  `H^s(T³)`.
* **Viscosity rescaling** (4 fields) — class preservation, the inverse
  identities, and both directions of the `ν ↦ 1`, `T ↦ νT` change of variables
  with regularity carried.

**One narrowing, explicit and registered as such.**  The manuscript's `restart`
and `restartBeyond` quantify over an `H¹` ball of data.  What is proved and
registered is the same package with those two balls at `H³`
(`PeriodicContinuationH3API`); the manuscript's two sentences are kept verbatim
as the named, documented, **unproved** predicates `PeriodicRestartH1` and
`PeriodicRestartBeyondH1`, exactly as Section 4 kept
`ManuscriptHorizonLowerBoundH1` next to `RestartFixedForce`.  Lead amendment 2
(`research/T11/LEAD_AMENDMENTS.md`), gap analysis and consumer checklist in
`research/T11/H1_GAP.md`.

## 2. What is in Lean now

New files:

| file | contents |
|---|---|
| `formalization/NSFormalization/Section3/T11/Assembly.lean` (569 lines) | the unconditional horizon/solution selection (`periodicLocalChoiceU`, `periodicLocalHorizon`, `periodicLocalHorizon_eq`, `periodicLocalSolution`, `periodicLocalHorizon_pos`); the five spec structures; `periodicLocalTheoryAPI`, `periodicContinuationH3API`, `periodicMeanReductionAPI`, `periodicViscosityRescalingAPI`; the named `PeriodicRestartH1` / `PeriodicRestartBeyondH1` and `periodicContinuationAPI_of_h1`; `periodicLocalTheoryAPI_nonvacuous` |
| `verification/Contracts/V1/TorusLocalTheory.lean` | the deferred T10 solution-class tier + the T11 vocabulary + `PeriodicLocalRegularity` + the four API structures + `PeriodicContinuationAPI` (stated, not registered) + the two named `H¹` predicates + the bundling `TorusLocalTheoryAPI`; module docstring carries the "registered narrowing" note |
| `verification/Bindings/TorusLocalTheory.lean` | 34 `rfl` drift guards; the `ClassicalSolutionT` structure exception (`toContract`/`ofContract`, both round trips `rfl`, four field lemmas); seven proved bridges for the declarations that mention the structure; the four transported API terms, `torusContinuationAPI_of_h1`, and `torusLocalTheory` |
| `verification/Tests/TorusLocalTheory.lean` | `checkedTorusLocalTheory`, `run_cmd TestSupport.checkAxioms`, six conformance `example`s against `Spec.lean`, and the residue example `(h₁ h₂) → PeriodicContinuationAPI` |
| `research/T11/probes/assembly_closes.lean` | all 23 specification fields closed by name; the two `H¹` fields only from the named predicates; non-vacuity |
| `research/T11/axioms_assembly.lean` | the 11 public `Assembly.lean` declarations, each `[propext, Classical.choice, Quot.sound]` |

Registry: `T01.torus_local_theory`, version 1, parent task `T01`, declaration
`BlowupDensity.Tests.checkedTorusLocalTheory` (39 contracts total).  Ledger:
`T11` claimed by `erenup`, state `in-progress`, contract recorded; task cards
re-rendered.

Every field of every API comes from a named theorem of a merged unit:
`Restart`/`ExistenceInputH3` (U9e/U10/U11), `ClassicalRegularity` (U6b),
`Uniqueness` (U5), `Maximal` (U15), `PairingBound` (U12), `MeanIdentity` (U7),
`GalileanClasses` (U3), `Rescaling` (U4), `Transport` (U6).  No named input
survives in any registered field.

## 3. Gaps

1. **The two `H¹` manuscript sentences** (`H1_GAP.md` G2, G3), kept as
   `PeriodicRestartH1` and `PeriodicRestartBeyondH1`.  They are the only
   residue: `periodicContinuationAPI_of_h1` derives the whole manuscript
   package from exactly those two, and the last `Tests` example machine-checks
   it.  Their common root is `PeriodicQuantitativeLocalInput'` (G1), the
   `H¹`-ball local-existence input, i.e. the subcritical Fujita–Kato theory.
2. **Consumer checklist** (`H1_GAP.md` §3), unchanged by this lane: every
   T11-internal use is fine at `H³` because `higherOrderBound` is finite at
   every order; T18/T19 carry no ball; **T20 must be re-read when its proof
   lane starts** — its `Spec.lean:402,437` copy of `PeriodicContinuationAPI`
   still spells `periodicSobolevENorm 1`, and its own route produces `H²`
   bounds.  T20 appears to consume only the ball-free `extendsBeyond` and the
   criterion, in which case the narrowing costs nothing; if it genuinely needs
   the `H¹` ball, that is an owner-level gap, not something a lane may weaken.
3. `PeriodicContinuationAPI` is stated in the contract but deliberately **not**
   a field of the registered `TorusLocalTheoryAPI`.
4. The ledger item `T10` still records no contract although `T01.torus_data`
   is registered (lane 293 omission); this lane recorded only its own.

## 4. Commands and results

```
cd verification && LEAN_NUM_THREADS=6 lake build \
  NSFormalization.Section3.T11.Assembly Contracts.V1.TorusLocalTheory \
  Bindings.TorusLocalTheory Tests.TorusLocalTheory
  -> Build completed successfully
  -> info: Tests/TorusLocalTheory.lean:33:0: Contract
     BlowupDensity.Tests.checkedTorusLocalTheory: checked; standard logical axioms only

cd verification && lake env lean ../research/T11/probes/assembly_closes.lean
  -> no output (all 23 fields + non-vacuity elaborate)

cd verification && lake env lean ../research/T11/axioms_assembly.lean
  -> 11 declarations, each: [propext, Classical.choice, Quot.sound]

BASE_REF=origin/erenup/integration-section3 scripts/gates.sh
  == make check              -> ok (registered_contracts 39)
  == make test               -> 39 contracts, all "checked; standard logical axioms only"
  == make test-mutations     -> extra_axiom: rejected as required
                                weakened_hypothesis: rejected as required
                                Mutation suite passed.
  == check_contracts --base-ref origin/erenup/integration-section3
                             -> registered_contracts 39, base_compatibility_checked true
  == gates OK

git diff --stat verification/contracts.json -> 1 file changed, 11 insertions(+)
```
