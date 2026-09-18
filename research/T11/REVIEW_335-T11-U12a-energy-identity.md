REJECT

## 1. What the lane claims

The worker claims an unconditional periodic high-order energy identity for every
`ClassicalSolutionT`, at every `m` and every `t ∈ Ioo 0 T`, with the pressure
term removed by solenoidality (`research/T11/REPORT_335.md:5-21`).  It also claims
that `hRhigh_of_pairingBound` and
`higherOrderBound_of_pairingBound` provide the exact downstream binders from
lane 322, with U12b's pairing estimate as an explicit argument
(`research/T11/REPORT_335.md:23-26`, `research/T11/REPORT_335.md:65-85`).

The report correctly cites the paper's high-order argument
(`paper/sections/appendix-a-local-theory.tex:127-141`), including the displayed
`eq:Rhigh` inequality and the pressure cancellation at line 138.  It also
correctly identifies the residual pairing estimate as a pointwise-in-time
estimate rather than a restatement of the uniform continuation conclusion.

However, the lane explicitly declined one obligation in the brief: its attempts
record says the requested projected coefficient equation was rejected and that
the module deliberately proves only an unprojected equation with an explicit
pressure coefficient (`research/T11/ATTEMPTS_ENERGY_IDENTITY.md:56-68`).

## 2. What is in Lean

The scalar coefficient differentiation theorem is present and well-formed:
`hasDerivAt_velocityCoeffT` differentiates the coefficient under the integral
(`formalization/NSFormalization/Section3/T11/EnergyIdentity.lean:196-243`).
The submitted momentum theorem is instead exactly

```
d/dt ûᵢ = -ν|2πk|² ûᵢ + (f̂ᵢ - Q̂ᵢ) - 2π i kᵢ p̂.
```

This is the statement of `velocityDerivCoeffT_momentum`
(`formalization/NSFormalization/Section3/T11/EnergyIdentity.lean:519-528`); the
module has no `periodicLeray`, `lerayAt`, or projected coefficient theorem (the
only occurrence is a docstring saying that no Leray projector is used,
`formalization/NSFormalization/Section3/T11/EnergyIdentity.lean:30-37`).  The
tree does contain the sibling projected form for a mild solution
(`formalization/NSFormalization/Section3/T11/MildMomentum.lean:255-264`) and the
Leray fixed-point coefficient fact for solenoidal data
(`formalization/NSFormalization/Section3/T10/Leray.lean:149-153`), but the
classical-solution bridge required by this lane is absent.

The energy theorem itself does typecheck.  Its exact pointwise statement is
`energyIdentity_of_classical` (`formalization/NSFormalization/Section3/T11/EnergyIdentity.lean:853-887`),
and the explicit U12b-to-`hRhigh` theorem is present at
`formalization/NSFormalization/Section3/T11/EnergyIdentity.lean:891-938`.
The composition to the canonical `higherOrderBound` field is present at
`formalization/NSFormalization/Section3/T11/EnergyIdentity.lean:940-964` and
matches the canonical field (`research/T11/probes/api_on_canonical.lean:112-120`).
The energy identity therefore supplies useful partial mathematics, but it does
not satisfy the brief's required projected coefficient statement.

## 3. Gaps and hygiene

1. **Blocker — statement fidelity.**  The requested coefficient equation is the
   Leray-projected form
   `d/dt û = -ν4π²|k|² û + P̂(f̂-Q̂)`.  The only submitted theorem has an
   additional pressure-gradient term instead (`formalization/NSFormalization/Section3/T11/EnergyIdentity.lean:522-528`),
   and the attempts file expressly confirms this substitution
   (`research/T11/ATTEMPTS_ENERGY_IDENTITY.md:58-68`).  Fix by adding a theorem
   in this module (or an explicitly cited bridge theorem) with the exact
   projected coefficient statement, using the existing Leray symbol and the
   pressure-gradient complement; retain the current unprojected theorem only as
   an auxiliary lemma.

2. **Major — required negative check was absent from the submitted deliverables.**
   `research/T11/probes/energy_identity_closes.lean:1-154` contains conformance
   and non-vacuity checks but no substantive mutation.  I added the allowed
   scratch probe `research/T11/probes/rev335_mutation_sign.lean`, changing only
   the diffusion sign, and ran it with `lake env lean`.  The exact reproducing
   error was:

   ```
   ../research/T11/probes/rev335_mutation_sign.lean:30:2: error: Type mismatch
     energyIdentity_of_classical w hf m ht hGm hFm hNm
   has type
     HasDerivAt (fun r => torusSobolevNormAt (↑m) w.velocity r ^ 2)
       (-2 * ν * torusGradientNormAt (↑m) w.velocity t ^ 2 + 2 * torusRealPairing Gm Fm - 2 * torusRealPairing Gm Nm) t
   but is expected to have type
     HasDerivAt (fun r => torusSobolevNormAt (↑m) w.velocity r ^ 2)
       (2 * ν * torusGradientNormAt (↑m) w.velocity t ^ 2 + 2 * torusRealPairing Gm Fm - 2 * torusRealPairing Gm Nm) t
   ```

   Record this mutation and its expected failure in the lane's attempts/report
   when resubmitting.

3. **Gap search (“not in the tree”).**  A whole-tree grep of
   `formalization/NSFormalization/Section4` found the whole-space analogues
   `outerProductTame` (`formalization/NSFormalization/Section4/A03/OuterTameProduct.lean:172-179`)
   and the generic `inner_energy_Rhigh`
   (`formalization/NSFormalization/Section4/A04/HighEnergy.lean:125-146`),
   plus the R³ advection/tensor-divergence bridge
   (`formalization/NSFormalization/Section4/A01/ConvectionDivergence.lean:111-118`).
   None has the torus `torusRealPairing`/`torusGradientNormAt` statement claimed
   as U12b's missing fact, so the residual-gap claim is honest but those
   declarations should be named as non-matching analogues rather than omitted.

4. **Report/diff precision.**  The worker says that only three new files plus
   records were added (`research/T11/REPORT_335.md:112-113`).  The mandated
   `git diff --name-only origin/erenup/integration-section3...HEAD` also lists
   the merged dependency modules `HighOrder.lean` and `MildMomentum.lean` and
   their records.  They are additions (`A`), not modifications of pre-existing
   files, so this is not a proof defect, but the report should state the exact
   diff rather than the narrower summary.

## 4. Commands and results

All commands used `. scripts/lean-env.sh`; Lake commands ran from `verification/`
with `LEAN_NUM_THREADS=6`.

Successful typechecking gates:

```text
cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T11/EnergyIdentity.lean
(no output, exit 0)

cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/probes/energy_identity_closes.lean
probe_exit=0

cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/axioms_energy_identity.lean
axioms_exit=0
```

The axiom file has `51` `#print axioms`/`#guard_msgs` pairs, and all 51 expected
lines are exactly `[propext, Classical.choice, Quot.sound]`.  The module build
also succeeded:

```text
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.EnergyIdentity
Build completed successfully (9993 jobs).
```

The build replayed existing upstream linter/deprecation warnings, but none came
from the submitted module.  `make check` exited 0; its exact tail was:

```text
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.047s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

I also ran the full lane gate with the Section 3 base:

```text
BASE_REF=origin/erenup/integration-section3 scripts/gates.sh NSFormalization.Section3.T11.EnergyIdentity
extra_axiom: rejected as required
weakened_hypothesis: rejected as required
Mutation suite passed. This is an infrastructure check, not a PDE proof.
== check_contracts
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
== gates OK
```

The direct contract check also exited 0 with:

```text
python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3
  "base_compatibility_checked": true,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
```

Hygiene checks found no forbidden proof tokens in the submitted module and no
`maxHeartbeats`; the only grep hits in the audit file are explanatory comments.
The required diff-name command (which also warned about multiple merge bases)
printed exactly:

```text
formalization/NSFormalization/Section3/T11/EnergyIdentity.lean
formalization/NSFormalization/Section3/T11/HighOrder.lean
formalization/NSFormalization/Section3/T11/MildMomentum.lean
research/T11/ATTEMPTS_ENERGY_IDENTITY.md
research/T11/ATTEMPTS_HIGH_ORDER.md
research/T11/ATTEMPTS_MILD_MOMENTUM.md
research/T11/EXISTENCE_ROUTE.md
research/T11/REPORT_322.md
research/T11/REPORT_327.md
research/T11/REPORT_335.md
research/T11/T11_SPLIT.md
research/T11/axioms_energy_identity.lean
research/T11/axioms_high_order.lean
research/T11/axioms_mild_momentum.lean
research/T11/probes/energy_identity_closes.lean
research/T11/probes/high_order_closes.lean
research/T11/probes/mild_momentum_closes.lean
```

All module entries there are additions rather than modifications.  `git status
--short` remained clean apart from the allowed untracked review probe and this
review file.

Verdict: REJECT — fixes: add the exact Leray-projected classical coefficient theorem/bridge; record the substantive sign-flip negative probe in the lane records; correct the report's exact diff summary.
