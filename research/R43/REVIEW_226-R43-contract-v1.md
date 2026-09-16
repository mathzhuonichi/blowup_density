ACCEPT

## 1. What the lane claims

The worker claims that Proposition 4.3 is the 30th registered contract,
`R43.critical_regularity` V1, with exactly the four fields `c`, `hc`,
`universal`, and `inhomogeneousAtZero` (`research/R43/REPORT_226.md:5-24`).  It
also claims that the witness uses one explicit positive constant for both
clauses (`research/R43/REPORT_226.md:27-37`), that all vocabulary bridges are
definitional except the existing equality between the two maximal-lifespan
definitions (`research/R43/REPORT_226.md:41-53`), and that Proposition 4.3 has
no remaining gap or additional analytic hypothesis (`research/R43/REPORT_226.md:61-66`).

Those are the right claims for the brief.  The paper says that one universal
`c > 0` works for every `a ∈ 𝒳_ℝ` and `f ∈ 𝓕_ℝ` under strict
`Ḣ^{1/2} + L¹_tḢ^{1/2}` smallness and concludes infinite maximal lifespan
(`paper/sections/04-whole-space.tex:82-87`); its same-constant zero-datum
inhomogeneous consequence is stated at `paper/sections/04-whole-space.tex:88-89`.
Positive viscosity is the standing equation convention
(`paper/sections/01-introduction.tex:1-3`), so the Lean `0 < ν` binder is a
domain condition rather than an extra analytic rider.
The proof text independently confirms the critical estimate, the two constant
shrinkings, the finite H² budget, continuation, and the homogeneous-to-
inhomogeneous comparison (`paper/sections/04-whole-space.tex:96-132`).

## 2. What is in Lean

### Statement fidelity

The registered structure is token-for-token the research structure.  Compare
`research/R43/Spec.lean:165-173,211-217,243-247` with
`verification/Contracts/V1/CriticalRegularity.lean:35-43,52-58,65-69`:

- `c : ℝ` is stored before all viscosity, datum, and force binders, and `hc :
  0 < c` makes `ENNReal.ofReal (c * ν)` positive whenever `0 < ν`.
- `universal` quantifies in the required order over `ν`, `a`, and `f`, uses
  `initialClassR`, `MemForceR`, the strict ENNReal sum with
  `forceHomogeneousENorm 1 (1/2)`, and concludes `maximalLifespanR ν a f = ⊤`.
- `inhomogeneousAtZero` retains the same structure field `c`, uses
  `forceSobolevENormL1 (1/2)`, fixes only the datum to zero, and concludes the
  genuine infinite-lifespan equality.

The sole permitted substitution is exact: the spec-local definition at
`research/R43/Spec.lean:142-143` and the registered definition at
`verification/Contracts/V1/HomogeneousNorm.lean:31-32` have identical bodies.
The contract contains no `.toReal`, no interval that could be empty, no finite-
horizon weakening, and no extra named analytic hypothesis.  Its domain
hypotheses are precisely the paper's positive viscosity, initial class, force
class, and strict smallness hypotheses.

The implementation constant is
`min (1/(8*trilinearConst))
     (1/(4*(A05.gradientL6Const*A05.criticalL3Const)))`, and its positivity is
proved at `formalization/NSFormalization/Section4/R43/Endpoint.lean:16-25`.
The exact implementation endpoints are
`universal_of_memForceR` at
`formalization/NSFormalization/Section4/R43/Universal.lean:192-203` and
`inhomogeneousAtZero_of_memForceR` at
`formalization/NSFormalization/Section4/R43/Endpoint.lean:133-140`.

The binding records all five definitional vocabulary equalities at
`verification/Bindings/CriticalRegularity.lean:31-55`, selects the documented
constant and positivity proof at `verification/Bindings/CriticalRegularity.lean:61-64`,
and fills the two fields directly at
`verification/Bindings/CriticalRegularity.lean:65-72`.  Its only non-`rfl`
transport is honest: `maximalPartial_maximalLifespanR_eq` proves the double-`iSup`
equality across the two distinct `ClassicalSolutionR` types at
`verification/Bindings/MaximalPartial.lean:113-138`.

The public test definition and the two exact conformance examples are present at
`verification/Tests/CriticalRegularity.lean:15-41`.  The registry entry has the
claimed id, parent, version, module names, declaration, and honest scope at
`verification/contracts.json:323-332`; the checked registry count is 30.

### Non-vacuity and negative mutation

The worker report did not contain its own contract-level satisfiable instance,
so `research/R43/probes/rev226_nonvacuity.lean:9-45` supplies two.  For every
positive viscosity, zero force belongs to `MemForceR`, both registered zero
force norms reduce to zero, the zero datum belongs to `initialClassR`, the
stored `hc` makes the strict radius positive, and both checked fields yield
infinite lifespan.  The probe typechecks with zero output.

`research/R43/probes/rev226_mutation.lean:12-20` substantively widens the
universal ball from `c * ν` to `2 * c * ν`.  Assigning the checked theorem then
fails exactly because the available premise has threshold `ofReal (c * ν)`, not
`ofReal (2 * c * ν)`; no argument was dropped.

### Historical gap audit and hygiene

The report declares no missing-tree lemma.  Nonetheless, a full-tree `rg` over
`formalization/NSFormalization/Section4` checked the historical G1--G8 list in
`research/R43/COMPARISON.md:105-114`.  It found G1 at
`formalization/NSFormalization/Section4/D01/HomogeneousNorm.lean:26-44`; G2
and homogeneous G3 at
`formalization/NSFormalization/Section4/R43/ForcePath.lean:65-93`;
inhomogeneous G3 at
`formalization/NSFormalization/Section4/D01/HalfOrder.lean:175-180`; the force
primitive comparison at
`formalization/NSFormalization/Section4/R43/ForcePath.lean:256-273`; G5/G6 at
`formalization/NSFormalization/Section4/R43/MaximalEndpoint.lean:15-53`; G7 at
`formalization/NSFormalization/Section4/R43/CriticalMomentum.lean:327-347`;
and G8 at `formalization/NSFormalization/Section4/R43/Endpoint.lean:16-44`.
Thus the closing statement in
`research/R43/COMPARISON.md:145-167` is supported, not an unchecked “not in the
tree” assertion.

`git diff --name-only origin/erenup/integration...HEAD` lists only new Lean
modules plus permitted registry/record changes; `git diff --diff-filter=M
--name-only origin/erenup/integration...HEAD -- '*.lean'` has no output.  No
pre-existing Lean module or frozen test was modified.  The declaration-token
scan over the new Lean and reviewer probes found no `sorry`, `admit`, `axiom`,
or `native_decide`, and found no `set_option maxHeartbeats`.  `git diff --check`
also has no output.  The paper and spec citations used by the contract are
correct (`verification/Contracts/V1/CriticalRegularity.lean:28-34,44-69`).

## 3. Gaps

No blocking or corrective gap was found.  The raw `lake build` commands replay
warnings from pre-existing dependencies, so their aggregate output is not
literally empty; there is no diagnostic from `Universal.lean`,
`CriticalRegularity.lean`, or `Bindings/CriticalRegularity.lean`, and direct
`lake env lean` on each of those target files exits 0 with exactly zero output.
This is repository build-log replay, not a lane-local warning or a required
fix.

There are no accepted “not in the tree” claims and no fixes required.

## 4. Commands and results

All Lean invocations sourced `scripts/lean-env.sh`, used
`LEAN_NUM_THREADS=6`, and ran Lake only from `verification/`.  Large
`check_contracts.py` closure arrays are omitted in accordance with the
repository lesson limiting raw JSON dumps; the command heads/tails and every
non-enumerative result are reproduced exactly.

Focused implementation and contract checks:

```text
$ lake build NSFormalization.Section4.R43.Universal
[pre-existing dependency warnings replayed; no Universal.lean diagnostic]
Build completed successfully (10545 jobs).
exit 0

$ lake env lean ../formalization/NSFormalization/Section4/R43/Universal.lean
[no output]
exit 0

$ lake build Contracts.V1.CriticalRegularity
[pre-existing dependency warnings replayed; no CriticalRegularity.lean diagnostic]
Build completed successfully (8818 jobs).
exit 0

$ lake env lean Contracts/V1/CriticalRegularity.lean
[no output]
exit 0

$ lake build Bindings.CriticalRegularity
[pre-existing dependency warnings replayed; no CriticalRegularity.lean diagnostic]
Build completed successfully (10557 jobs).
exit 0

$ lake env lean Bindings/CriticalRegularity.lean
[no output]
exit 0

$ lake build Tests.CriticalRegularity
info: Tests/CriticalRegularity.lean:20:0: Contract BlowupDensity.Tests.checkedCriticalRegularity: checked; standard logical axioms only
Build completed successfully (10559 jobs).
exit 0
```

Axiom audit, exit 0:

```text
'NSFormalization.Section4.R43.criticalConst' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.criticalConst_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.universal_of_memForceR' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R43.inhomogeneousAtZero_of_memForceR' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.criticalRegularity_initialClassR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.criticalRegularity_memForceR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.criticalRegularity_dotHomogeneousENorm_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.criticalRegularity_forceHomogeneousENorm_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.criticalRegularity_forceSobolevENormL1_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.maximalPartial_maximalLifespanR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.criticalRegularity' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedCriticalRegularity' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalRegularityContractConformance.universal' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalRegularityContractConformance.inhomogeneousAtZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalRegularityContractConformance.constant_value' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Standalone `make check` exited 0.  Its exact non-enumerative tail was:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.046s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

`scripts/gates.sh` exited 0.  Selected exact lines from its final sections were
(the other already-registered contract info lines are omitted):

```text
== make test
info: Tests/CriticalRegularity.lean:20:0: Contract BlowupDensity.Tests.checkedCriticalRegularity: checked; standard logical axioms only
== make test-mutations
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
```

The separately rerun architecture check exited 0; its exact relevant fields
were:

```text
{
  "registered_contracts": 30,
  "closures": {
    ... closure module arrays only ...
  },
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

Reviewer probes:

```text
$ lake env lean ../research/R43/probes/rev226_nonvacuity.lean
[no output]
exit 0

$ lake env lean ../research/R43/probes/rev226_mutation.lean
../research/R43/probes/rev226_mutation.lean:20:2: error: Type mismatch
  BlowupDensity.Tests.checkedCriticalRegularity.universal
has type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ a ∈ initialClassR,
        ∀ (f : SpaceTimeField),
          MemForceR f →
            dotHomogeneousENorm (1 / 2) a + forceHomogeneousENorm 1 (1 / 2) f <
                ENNReal.ofReal (BlowupDensity.Tests.checkedCriticalRegularity.c * ν) →
              maximalLifespanR ν a f = ∞
but is expected to have type
  ∀ (ν : ℝ),
    0 < ν →
      ∀ a ∈ initialClassR,
        ∀ (f : SpaceTimeField),
          MemForceR f →
            dotHomogeneousENorm (1 / 2) a + forceHomogeneousENorm 1 (1 / 2) f <
                ENNReal.ofReal (2 * BlowupDensity.Tests.checkedCriticalRegularity.c * ν) →
              maximalLifespanR ν a f = ∞
exit 1 (expected)
```

Registry and hygiene commands:

```text
$ git diff --stat verification/contracts.json
[no output: the lane changes are committed]

$ git diff --stat origin/erenup/integration...HEAD -- verification/contracts.json
 verification/contracts.json | 11 +++++++++++
 1 file changed, 11 insertions(+)

$ git diff --diff-filter=M --name-only origin/erenup/integration...HEAD -- '*.lean'
[no output]

$ git diff --check origin/erenup/integration...HEAD
[no output]

$ rg <forbidden declaration tokens and maxHeartbeats> <new Lean files and probes>
[no output]
```

Fixes required: none.
