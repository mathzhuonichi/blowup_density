# Lane 224 — Theorem 4.1(ii), q = 1 non-density

## 1. Theorem proved

For ν,T > 0 and s ≥ 1/2, the zero-datum breakdown set is not relatively
dense in F_R in the L¹_t H^s metric. The excluded ball is centred at zero
and has radius `R43.criticalConst * ν`.

`nonDensityZero_L1` gives the positive radius and lower bound on every
breakdown force. `not_breakdownDenseR_zero_L1` proves the exact negation of
`BreakdownDenseR ν (fun _ => 0) T 1 s`.

## 2. What is in Lean

New module `formalization/NSFormalization/Section4/R41/NonDensityL1.lean`
contains 13 declarations: scalar and vector contraction, general
`forceSobolevENorm_mono_order`, six canonical local definitions, the explicit
radius lower bound, both requested conclusions, and ambient zero membership.
Order monotonicity holds for every q and every pair of real orders s ≤ s'.
Non-vacuity examples include ν = T = 1 and s = 1/2.

`research/R41D/axioms_nondensity_l1.lean` audits all 13 declarations and six
bridge/conformance theorems: all 19 have exactly
`[propext, Classical.choice, Quot.sound]`. It checks force-class and relative
density equality by rfl, and bridges lifespan-dependent definitions through
the existing maximal-lifespan equality (the local and contract solution
structures are distinct). Both final theorems are checked in Data vocabulary.

## 3. Remaining gaps

None for this clause; no additional hypothesis, forbidden proof construct,
or heartbeat override is used. The q = 2 obstruction and subcritical density
are outside this lane. R41D/Spec.lean uses literal thresholds, so no exponent
record copy is needed; the module cites ThresholdAPI.l1/energy.

The requested COMPARISON.md update is delivered in the new companion
`COMPARISON_NONDENSITY_L1.md` to obey the explicit new-files-only rule.
No existing file was edited. No contract registration or full RMainAPI
witness is claimed.

## 4. Commands and results

All Lean commands ran from verification after sourcing scripts/lean-env.sh,
with LEAN_NUM_THREADS=6.

- `lake build NSFormalization.Section4.R41.NonDensityL1`: exit 0; the new
  module has no warnings. Aggregate Lake output replays pre-existing
  dependency warnings and is therefore not literally silent.
- `lake env lean ../formalization/NSFormalization/Section4/R41/NonDensityL1.lean`:
  exit 0, zero bytes of output.
- `lake env lean ../research/R41D/axioms_nondensity_l1.lean`: exit 0;
  all 19 audits have the exact standard three axioms, all examples pass.
- `make check`: exit 0, policy tests and all 30 work items pass.
- `lake test`: exit 0 (the make-test recipe run inside verification).
- `make test-mutations`: exit 0; all three prohibited mutations rejected.
- `git diff --check` and forbidden-token scan: clean.

Committed on erenup/224-R41-nondensity-q1. No push, merge, or rebase.
