ACCEPT

## 1. What the lane claims

The worker claims that Proposition 4.4 is registered as the 31st contract,
`R44.critical_finite_horizon` V1, with the nine fields of `RCritical2API`
token-for-token except for the structure name
(`research/R44/REPORT_231.md:5-20`).  It further claims that the witness fixes
`c = R44.theta / 20`, `C = 3`, and `radius = R44.radius`, binds the unconditional
`R44.main` and `R44.nonDensityBallZero`, and transports the lifespan through the
existing non-definitional `ClassicalSolutionR` bridge
(`research/R44/REPORT_231.md:24-42`).  Finally, it claims that there is no
remaining Proposition 4.4/registration gap and no extra analytic premise
(`research/R44/REPORT_231.md:44-50`).

Those are the right claims for the brief.  The paper says that for every
`nu,S > 0` there is a positive radius such that an `F_R` force with strict
inhomogeneous `L^2(0,infinity;H^(-1/2))` norm below that radius has zero-datum
maximal lifespan greater than `S`, and it permits the universal formula
`c*nu^(3/2)*exp(-C*nu*S)` with positive `c,C`
(`paper/sections/04-whole-space.tex:136-143`).  The proof confirms that force
class membership supplies the finite unscaled norms used for continuation and
that the inhomogeneous negative-half norm is essential
(`paper/sections/04-whole-space.tex:169-173`).  The stated non-density
consequence is exactly how Theorem 4.1 consumes the proposition at `S = T`
(`paper/sections/04-whole-space.tex:176-179`).

## 2. What is in Lean

### Statement fidelity and binding

A mechanical comparison of the complete structure text, after replacing only
`RCritical2API` by `CriticalFiniteHorizonAPI`, prints
`structure_token_match: True`.  The source fields are at
`research/R44/Spec.lean:181-304`, and their registered copies are at
`verification/Contracts/V1/CriticalFiniteHorizon.lean:31-154`.  In particular:

- `c`, `C`, `hc`, and `hC` are stored before all viscosity, horizon, and force
  binders (`verification/Contracts/V1/CriticalFiniteHorizon.lean:31-54`).
- `radius` is a named field, while `radiusFormula` alone pins it to the exact
  real exponent `3/2` and decaying exponential
  (`verification/Contracts/V1/CriticalFiniteHorizon.lean:66-75`).
- `radiusPos` retains the paper's `0 < nu` and `0 < S` regime
  (`verification/Contracts/V1/CriticalFiniteHorizon.lean:76-87`).
- `main` has the exact binder order, zero datum, `MemForceR`, strict
  `forceSobolevENormL2 (-1 / 2)` ENNReal smallness, and strict finite-horizon
  conclusion (`verification/Contracts/V1/CriticalFiniteHorizon.lean:116-120`).
- `nonDensityBallZero` uses the same named radius and the exact registered
  breakdown set (`verification/Contracts/V1/CriticalFiniteHorizon.lean:150-154`).

The public statement has no `.toReal`, no interval binder that could be empty,
and no abstract proposition or added differential/local-existence/continuation
hypothesis.  The force norm is the fail-safe measurable-path infimum in
`Contracts.V1.Data`, and its `L2` abbreviation really is the `q = 2` case
(`verification/Contracts/V1/Data.lean:215-236`).  `MemForceR` is the manuscript
smooth force class (`verification/Contracts/V1/Data.lean:540-550`), and the
lifespan is the supremum of horizons carrying an actual classical solution
(`verification/Contracts/V1/Data.lean:650-658`).  Thus neither a missing datum
path nor `top.toReal = 0` can make the smallness premise spuriously true.

The positivity proof does not use `hS`, but this is honest rather than vacuous:
the formula is positive for every real `S` because `Real.exp` is positive, while
the theorem retains `0 < S` because that is the paper's domain.  Both `S` and
the radius depending on it remain present in `main`.  Where the implementation
does use `.toReal` internally, it first proves the lifespan is not top and then
uses `ENNReal.ofReal_toReal` (`formalization/NSFormalization/Section4/R44/Endpoint.lean:278-286`).

The implementation constants and positivity facts are present exactly as
claimed: `theta`, `radiusCoefficient`, `radiusRate`, `radius`, and their
positivity theorems are at
`formalization/NSFormalization/Section4/R44/Endpoint.lean:22-41`.
The unconditional endpoint theorem has precisely the public theorem binders
(`formalization/NSFormalization/Section4/R44/Prop44.lean:14-21`), and `R44.main`
is exactly that theorem (`formalization/NSFormalization/Section4/R44/Prop44.lean:23-29`).
The same-radius breakdown exclusion is at
`formalization/NSFormalization/Section4/R44/Prop44.lean:31-38`.  No differential
hypothesis leaks into these declarations: the implementation constructs it
from only positive viscosity and `MemForceR`
(`formalization/NSFormalization/Section4/R44/Absorption.lean:281-291`).

The binding records the two definitional force-vocabulary equalities
(`verification/Bindings/CriticalFiniteHorizon.lean:24-35`), proves the advertised
constant reductions (`verification/Bindings/CriticalFiniteHorizon.lean:38-45`),
and fills all nine fields at
`verification/Bindings/CriticalFiniteHorizon.lean:61-80`.  Its non-`rfl`
transport is honest: the double-supremum equality between the two distinct
`ClassicalSolutionR` structures is proved at
`verification/Bindings/MaximalPartial.lean:113-138`, and breakdown membership is
transported in both directions at
`verification/Bindings/CriticalFiniteHorizon.lean:47-59`.

The public checked witness and all nine field checks are present at
`verification/Tests/CriticalFiniteHorizon.lean:14-65`.  The registry entry has
the claimed id, parent, version, files, declaration, and scope at
`verification/contracts.json:335-343`; the parsed registry has 31 unique ids.

### Non-vacuity and negative mutation

The worker's conformance audit already contains a zero-force instance
(`research/R44/axioms_contract.lean:64-70`).  The independent reviewer probe
`research/R44/probes/rev231_nonvacuity.lean:9-21` additionally derives the zero
force norm as exactly zero, uses the registered `radiusPos`, and applies the
checked `main`; it typechecks with exactly zero output.

The negative probe at `research/R44/probes/rev231_mutation.lean:11-18`
substantively widens the main theorem's force ball from `radius nu S` to
`2 * radius nu S`.  Reusing the checked theorem fails at the intended threshold
mismatch, without dropping any argument:

```text
../research/R44/probes/rev231_mutation.lean:18:2: error: Type mismatch
  BlowupDensity.Tests.checkedCriticalFiniteHorizon.main
has type
  ∀ (ν S : ℝ),
    0 < ν →
      0 < S →
        ∀ (f : SpaceTimeField),
          MemForceR f →
            forceSobolevENormL2 (-1 / 2) f <
                ENNReal.ofReal (BlowupDensity.Tests.checkedCriticalFiniteHorizon.radius ν S) →
              ENNReal.ofReal S < maximalLifespanR ν (fun x => 0) f
but is expected to have type
  ∀ (ν S : ℝ),
    0 < ν →
      0 < S →
        ∀ (f : SpaceTimeField),
          MemForceR f →
            forceSobolevENormL2 (-1 / 2) f <
                ENNReal.ofReal (2 * BlowupDensity.Tests.checkedCriticalFiniteHorizon.radius ν S) →
              ENNReal.ofReal S < maximalLifespanR ν (fun x => 0) f
```

### Hygiene and tree audit

`git diff --diff-filter=M --name-only origin/erenup/integration...HEAD -- '*.lean'`
has no output: every lane Lean file is new, so no existing module or frozen test
was modified.  The only modified non-Lean files are the append-only registry,
the work-item registration plus its two generated views, and research records.
The declaration-token scan over all new Lean files and reviewer probes finds no
`sorry`, `admit`, `axiom`, or `native_decide`, and no `set_option maxHeartbeats`.
The broad textual scan finds only the harmless word `transitive-axiom` in the
test module comment (`verification/Tests/CriticalFiniteHorizon.lean:5`).

The worker declares no missing-tree lemma; its gap statement is explicitly
"None" (`research/R44/REPORT_231.md:44-50`), so there is no "not in the tree"
claim to accept.  As a positive cross-check, whole-tree `grep -rn` finds the
unconditional provider and final declarations at
`formalization/NSFormalization/Section4/R44/Absorption.lean:281` and
`formalization/NSFormalization/Section4/R44/Prop44.lean:14,24,32`; the underlying
unconditional maximal-solution and continuation declarations are at
`formalization/NSFormalization/Section4/A02/MaximalWiring.lean:14-19` and
`formalization/NSFormalization/Section4/A04/ShiftedExtension.lean:247-253`.

## 3. Gaps

No blocking or corrective gap was found.  The raw `lake build` commands replay
warnings from pre-existing dependencies, so their aggregate output is not
literally empty; there is no diagnostic from `Prop44.lean`,
`CriticalFiniteHorizon.lean`, or `Bindings/CriticalFiniteHorizon.lean`, and
direct `lake env lean` on each target exits 0 with exactly zero output.  This is
repository build-log replay, not a lane-local warning.

There are no accepted "not in the tree" claims and no fixes required.

## 4. Commands and results

All Lean commands sourced `scripts/lean-env.sh`, used `LEAN_NUM_THREADS=6`, and
ran Lake only from `verification/`.  In accordance with the repository rule
against pasting enormous closure arrays, the exact emitted build first/last
lines and exact gate tails are shown; omitted text consists only of pre-existing
dependency warnings or module-closure arrays.

Focused implementation and contract checks:

```text
$ lake build NSFormalization.Section4.R44.Prop44
⚠ [8781/9212] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'
[pre-existing dependency warnings replayed; no Prop44.lean diagnostic]
Build completed successfully (10552 jobs).
exit 0

$ lake env lean ../formalization/NSFormalization/Section4/R44/Prop44.lean
[no output]
exit 0

$ lake build Contracts.V1.CriticalFiniteHorizon
⚠ [8779/8817] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'
[pre-existing dependency warnings replayed; no CriticalFiniteHorizon.lean diagnostic]
Build completed successfully (8817 jobs).
exit 0

$ lake env lean Contracts/V1/CriticalFiniteHorizon.lean
[no output]
exit 0

$ lake build Bindings.CriticalFiniteHorizon
⚠ [8778/8912] Replayed NSFormalization.Source.FiniteHilbertBochner
warning: NSFormalization/Source/FiniteHilbertBochner.lean:24:19: try 'simp' instead of 'simpa'
[pre-existing dependency warnings replayed; no CriticalFiniteHorizon.lean diagnostic]
Build completed successfully (10562 jobs).
exit 0

$ lake env lean Bindings/CriticalFiniteHorizon.lean
[no output]
exit 0

$ lake build Tests.CriticalFiniteHorizon
⚠ [8778/9593] Replayed NSFormalization.Source.FiniteHilbertBochner
[pre-existing dependency warnings replayed]
info: Tests/CriticalFiniteHorizon.lean:19:0: Contract BlowupDensity.Tests.checkedCriticalFiniteHorizon: checked; standard logical axioms only
Build completed successfully (10564 jobs).
exit 0
```

The axiom audit exited 0.  Every `#print axioms` result is exactly the required
three-element set (line wraps are Lean's output):

```text
'NSFormalization.Section4.R44.theta' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.theta_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.radiusCoefficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.radiusCoefficient_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.radiusRate' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.radiusRate_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.radius' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.radius_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.rcritical2_endpoint_unconditional' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.R44.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.R44.nonDensityBallZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.criticalFiniteHorizon_memForceR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.criticalFiniteHorizon_forceSobolevENormL2_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.criticalFiniteHorizon_radiusCoefficient_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.criticalFiniteHorizon_radiusRate_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.maximalPartial_maximalLifespanR_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Bindings.criticalFiniteHorizon_breakdownSetRZero_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'BlowupDensity.Bindings.criticalFiniteHorizon' depends on axioms: [propext, Classical.choice, Quot.sound]
'BlowupDensity.Tests.checkedCriticalFiniteHorizon' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalFiniteHorizonContractConformance.c_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalFiniteHorizonContractConformance.C_value' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalFiniteHorizonContractConformance.radiusFormula' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalFiniteHorizonContractConformance.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalFiniteHorizonContractConformance.nonDensityBallZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'CriticalFiniteHorizonContractConformance.zeroForceMain' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Standalone `make check` exited 0.  Its exact final non-enumerative section was:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.045s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

`scripts/gates.sh` exited 0.  Its exact lane-relevant tail was:

```text
== make test
info: Tests/CriticalFiniteHorizon.lean:19:0: Contract BlowupDensity.Tests.checkedCriticalFiniteHorizon: checked; standard logical axioms only
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

The separately rerun architecture check exited 0 with these exact fields:

```text
$ python3 experiments/check_contracts.py --base-ref origin/erenup/integration
  "registered_contracts": 31,
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
```

Reviewer probes:

```text
$ lake env lean ../research/R44/probes/rev231_nonvacuity.lean
[no output]
exit 0

$ lake env lean ../research/R44/probes/rev231_mutation.lean
../research/R44/probes/rev231_mutation.lean:18:2: error: Type mismatch
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
