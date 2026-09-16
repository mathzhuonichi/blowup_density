# Lane 229 — Proposition 4.4 and q = 2 non-density

## 1. Theorem proved

Proposition 4.4 is unconditional at zero initial datum: for ν,S > 0 and
MemForceR f, the strict bound
`forceSobolevENormL2 (-1/2) f < ofReal (radius ν S)` implies
`ofReal S < maximalLifespanR ν (fun _ => 0) f`.
The explicit radius remains `(theta/20)*ν^(3/2)*exp(-3*ν*S)`, with lane 227's
fixed theta and coefficients 2,4. At S=T this proves Theorem 4.1(ii)'s
q = 2 non-density clause for every s ≥ -1/2, in the exact BreakdownDenseR
vocabulary, with excluded radius ρ = radius ν T.

## 2. What Lean contains

Three new modules: `R44.Absorption` (25 declarations), `R44.Prop44`
(4 declarations), and `R41.NonDensityL2` (3 declarations).
Absorption credits and preserves lane 228's analytic proof, renames its
constants, removes its duplicate structure, and proves the monotonicity
adapter `rCritical2Differential_of_classical`. Endpoint.lean is unchanged.
The required TrilinearJ dependency was absent from this base; it is included
unchanged, byte-identical to origin/erenup/integration (lane 220).

Prop44 supplies the exact main and nonDensityBallZero binders. All nine
RCritical2API field values/proofs are now available with c=theta/20, C=3;
the audit checks the conclusions in Contracts.V1.Data vocabulary and pins
the radius formula and positivity. NonDensityL2 imports lane 224's general
order monotonicity and local definitions without duplicating them.

The two audits contain 56 and 19 axiom reports, respectively, all exactly
`[propext, Classical.choice, Quot.sound]`. This includes the unchanged
TrilinearJ dependency. Non-vacuity examples verify the actual strict
smallness premise for f=0, apply the unconditional endpoint, instantiate
the differential package on zeroSol, and exclude density at ν=T=1.
ATTEMPTS_PROP44.md records the missing dependency and naming correction;
R44_SPLIT.md and R41D/COMPARISON.md record closure of S1–S6 and both
nonDensityZero instances.

## 3. Remaining gaps

No analytic gap remains for Proposition 4.4 or this q = 2 non-density clause.
Formal contract registration and a registered RCritical2API witness remain
separate work; no full RMainAPI or subcritical-density result is claimed.
The derivative is integrable on each closed presingular window S<T, exactly
as required by the endpoint assembly, with no claim at a singular endpoint.
No existing implementation module, contract, binding, or test was edited.

## 4. Validation and commit

All Lean commands ran after `. scripts/lean-env.sh`, from verification,
with LEAN_NUM_THREADS=6.

- `lake build NSFormalization.Section4.R44.Absorption NSFormalization.Section4.R44.Prop44 NSFormalization.Section4.R41.NonDensityL2`: exit 0.
  The three modules emit no warnings. Aggregate Lake output is not literally
  silent because it replays pre-existing dependency warnings.
- `lake env lean` on each of the three modules: exit 0, exactly zero bytes
  of output for each.
- `lake env lean ../research/R44/axioms_prop44.lean` and
  `lake env lean ../research/R41D/axioms_nondensity_l2.lean`: exit 0;
  all 75 axiom reports have exactly the standard three axioms.
- `make check`: exit 0, including all 13 policy tests and 30 work-item checks.
- `lake test` (make-test recipe, run inside verification): exit 0.
- `make test-mutations`: exit 0; implementation refactoring accepted and
  all three prohibited mutations rejected.
- `git diff --check`: clean; no prohibited proof construct or heartbeat
  override in the delivered implementation files.

Committed on erenup/229-R44-prop44; no push, merge, or rebase.
Local validation logs are in tmp/ and are not committed.
