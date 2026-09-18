ACCEPT

# Lane 387-T22-UA4-orderzero-isometry review

## 1. What the lane claims

The worker claims the new `NSFormalization.Section3.T22` module proves the order-0
identity

```lean
theorem norm_orderZeroDatum_eq {z : Space → Space} (hz : MemLp z 2 volume) :
  ‖orderZeroDatum hz‖ₑ = eLpNorm z 2 volume
```

This is the requested `SpatialField` statement: `SpatialField` is definitionally
`Space → Space` (`formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean:223-224`).
The cited D01 source explicitly says that this Plancherel identity is not proved there
(`formalization/NSFormalization/Section4/D01/OrderZeroDatum.lean:40-53`), while its
constructor is exactly the componentwise Fourier/projection/vector expression used by
the lane (`formalization/NSFormalization/Section4/D01/OrderZeroDatum.lean:89-99`).
The paper's order-zero convention is the usual `L²(Ω)` norm and its vector norm is the
sum of squared component norms (`paper/sections/03-torus.tex:606-607,630-631`).

The report also claims these supporting declarations:

* `cyclesToAngular_zero_norm` (`formalization/NSFormalization/Section3/T22/OrderZeroIsometry.lean:62-73`);
* the two definitional coercion bridges `norm_coe_realSobolev` and
  `coe_cyclesToAngularReal_zero`
  (`formalization/NSFormalization/Section3/T22/OrderZeroIsometry.lean:75-85`);
* `cyclesToAngularReal_zero_norm`
  (`formalization/NSFormalization/Section3/T22/OrderZeroIsometry.lean:87-93`); and
* the vector lift `cyclesToAngularRealVector_zero_norm`
  (`formalization/NSFormalization/Section3/T22/OrderZeroIsometry.lean:95-108`).

The brief suggested a `symm`-named vector helper if needed, but the delivered
forward equality is a genuine order-0 isometry and is the form actually used by the
target proof (`research/T22/T22_SPLIT.md:125-143`).  No downstream contract in this
lane requires the suggested name.

## 2. What is in Lean

The target theorem is present with exactly the claimed binders and conclusion at
`formalization/NSFormalization/Section3/T22/OrderZeroIsometry.lean:113-118`.  Its proof
uses the honest load-bearing hypothesis `hz : MemLp z 2 volume`, component reality
(`formalization/NSFormalization/Section3/T22/OrderZeroIsometry.lean:120-127`), the vector
norm square identity and the existing component Pythagoras lemma
(`formalization/NSFormalization/Section3/T22/OrderZeroIsometry.lean:128-143`).  The final
conversion to extended norm is explicit
(`formalization/NSFormalization/Section3/T22/OrderZeroIsometry.lean:144-145`).  There are no
extra smoothness, support, interval, or finiteness hypotheses.

The supporting tree statements match their use: `norm_toLp_component_sq_sum` is the
real `L²` Pythagoras identity (`formalization/NSFormalization/Section4/D01/FiniteOrderNorm.lean:96-108`),
`enorm_sq_piLp` is the Euclidean `WithLp 2` squared-component identity
(`formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean:402-413`), and
the scalar reverse angular bound used by the worker is exactly the existing theorem
(`formalization/NSFormalization/Paper3/AngularTameProduct.lean:20-23`).  The only
real-subspace reverse bound in the tree is the scalar one cited by the brief
(`formalization/NSFormalization/Paper3/AngularRealSobolev.lean:84-86`).

The non-vacuity probe is substantive: it defines a `ContDiffBump` field along a
coordinate axis (`research/T22/probes/orderzero_isometry_closes.lean:18-23`), proves
compact support, continuity, `MemLp`, and nonzero value at the centre
(`research/T22/probes/orderzero_isometry_closes.lean:24-40`), and proves equality with
both sides `< ⊤` (`research/T22/probes/orderzero_isometry_closes.lean:42-50`).

The module has six declarations, each wrapped in a commented
`set_option maxHeartbeats 400000 in`
(`formalization/NSFormalization/Section3/T22/OrderZeroIsometry.lean:62-114`).  An
executable-token scan found no `sorry`, `admit`, `axiom`, or `native_decide` in the
module, probe, or axioms file.  The lane diff against
`origin/erenup/integration-section3` contains no `verification/` path and introduces
the new module rather than modifying an existing Lean module.

## 3. Gaps

No U-A4 gap remains: the D01-open norm identity is proved verbatim.  The report
correctly leaves U-A5 downstream (the bounded-domain quotient/restriction calculation
and the off-`L²(Ω)` `⊤ = ⊤` edge), rather than silently adding those obligations to this
theorem (`research/T22/REPORT_387.md:56-62`).

I searched the whole Section 4 tree with `grep -rnE` for `domainL2Sq`,
`domainSobolevENorm`, `restrictField`, `zeroExtension`, and
`orderZeroDatum_eq.*eLpNorm`; all five searches returned no matches.  Thus no exact
Section-4 lemma contradicts the report's downstream-gap claim.  (There are unrelated
order-zero datum construction lemmas, but no domain quotient identity.)

The required substantive mutation is in
`research/T22/probes/rev387_mutation_constant.lean`: changing the right side to
`2 * eLpNorm z 2 volume` and applying the delivered theorem fails with exactly:

```text
error: Type mismatch
  norm_orderZeroDatum_eq hz
has type
  ‖orderZeroDatum hz‖ₑ = eLpNorm z 2 volume
but is expected to have type
  ‖orderZeroDatum hz‖ₑ = 2 * eLpNorm z 2 volume
```

The mutation exits with status `1`; it changes the constant, not merely an argument.

## 4. Commands and results

All Lean commands were run after `. scripts/lean-env.sh`, with
`LEAN_NUM_THREADS=6`, and `lake` from `verification/`.

* `lake build NSFormalization.Section3.T22.OrderZeroIsometry`: exit `0`, ending with
  `Build completed successfully (9928 jobs).`  The replay emitted only pre-existing
  dependency linter warnings; the module itself has no warning/error output.
* `lake env lean ../formalization/NSFormalization/Section3/T22/OrderZeroIsometry.lean`:
  exit `0`, no output.
* `lake env lean ../research/T22/probes/orderzero_isometry_closes.lean`: exit `0`, no output.
* `lake env lean ../research/T22/axioms_ua4.lean`: exit `0`; the exact axiom results
  are `[propext, Classical.choice, Quot.sound]` for all six declarations:

  ```text
  'NSFormalization.Section3.T22.cyclesToAngular_zero_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T22.norm_coe_realSobolev' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T22.coe_cyclesToAngularReal_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T22.cyclesToAngularReal_zero_norm' depends on axioms: [propext, Classical.choice, Quot.sound]
  'NSFormalization.Section3.T22.cyclesToAngularRealVector_zero_norm' depends on axioms: [propext,
   Classical.choice,
   Quot.sound]
  'NSFormalization.Section3.T22.norm_orderZeroDatum_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
  ```

* `make check`: exit `0`; the exact final checks included `.............`, `OK`, and
  `45 work items: ownership, contract registration and task cards consistent.`
* `make test-mutations`: exit `0`; exact tail:

  ```text
  extra_axiom: rejected as required
  weakened_hypothesis: rejected as required
  Mutation suite passed. This is an infrastructure check, not a PDE proof.
  ```

* The aggregate `scripts/gates.sh NSFormalization.Section3.T22.OrderZeroIsometry`
  completed its `make check`, module build, `make test`, and mutation stages, then
  stopped in `check_contracts` with:

  ```text
  AssertionError: Removed stable specification: verification/Contracts/V1/Localization.lean
  ```

  This is a base-state mismatch, not a lane change: `verification/` is untouched and
  the lane's three-dot diff contains no contract deletion.  Checking the actual lane
  base (`python3 experiments/check_contracts.py --base-ref c2747324`) passed with
  `"base_compatibility_checked": true`.  The `origin/erenup/integration-section3`
  ref has advanced to contain `Localization.lean`, while this lane's base does not.

* The mutation probe command exited `1` with the type-mismatch text reproduced in §3,
  as required for the negative check.

Verdict: ACCEPT
Fixes: none.
