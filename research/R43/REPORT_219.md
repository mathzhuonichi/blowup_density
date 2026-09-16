# Lane 219 — critical momentum

## 1. Theorem proved

`criticalDatumInputs_of_classical (hν : 0 < ν) (hf : A02.MemForceR f)
(w : ClassicalSolutionR ν a f T) : CriticalDatumInputs w hf` closes both
lane 216 time-path fields for an arbitrary classical solution.

Consequently `exists_criticalDatumPath'` constructs the exact critical carrier,
and `rcritical1_of_classical'` proves lane 214's `eq:Rcritical1` without a
`CriticalDatumInputs`, `hcrit`, or momentum binder. On every `0 < t < T`, it
supplies the derivative E′ of the squared critical norm and

`E′/2 + (ν - trilinearConst * criticalNormAt w.velocity t)
  * criticalDissipationAt w.velocity t ^ 2
  ≤ criticalForceAt f t * criticalNormAt w.velocity t`.

## 2. What is in Lean

New module: `formalization/NSFormalization/Section4/R43/CriticalMomentum.lean`,
19 explicit declarations, all under `NSFormalization.Section4.R43`.

The bounded real continuous linear Bessel-to-homogeneous map agrees with lane
216's constructor. Existing homogeneous uniqueness identifies the chosen path
with the converted smooth integer-order path. The local-carrier covering
argument transfers smoothness to arbitrary classical solutions. At order two,
`A04.momentum_datum` already provides the exact derivative identity; D01's
pressure-gradient jets supply its pressure datum. Continuous linear lowering
and homogeneous conversion transport the equation to half order.

Lane 215's module/report are absent from this baseline. Its seven supporting
declarations through `classical_hasSmoothSobolevPath` were inspected at local
branch commit `1768cd0871fc50566514c82b439eed7baf9bca18` and reproduced under
`R43.CarrierWindow`, avoiding a dependency on an absent module and avoiding
namespace collisions when lane 215 later lands. No existing Lean module was
edited, and no merge, rebase, or push was performed.

`axioms_critical_momentum.lean` audits every declaration and includes a genuine
`A04.zeroSol`/zero-force instance. `ATTEMPTS_CRITICAL_MOMENTUM.md` records the
route and failed elaboration attempts. `R43_SPLIT.md` marks S1/G7 closed.

## 3. Remaining gaps

None in the requested time smoothness, momentum identity, or `eq:Rcritical1`
under positive viscosity and force membership. No fallback hypothesis remains.
The proof uses smoothness on `[0,T)` and differentiates only at interior times.

The separate G2/G3/G4 time-integrated homogeneous force-path obligations and
later R43 bootstrap/continuation work remain outside this result. Lane 216's
G3 slicewise note is preserved unchanged. No new contract registration is
claimed.

## 4. Commands and results

All Lean commands ran from `verification/`, after `. scripts/lean-env.sh`,
with `LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section4.R43.CriticalMomentum` — exit 0.
  The new module has no warnings. Lake replayed pre-existing dependency linter
  messages, so the aggregate build log is not literally empty.
- `lake env lean ../formalization/NSFormalization/Section4/R43/CriticalMomentum.lean`
  — exit 0, exactly zero output.
- `lake env lean ../research/R43/axioms_critical_momentum.lean` — exit 0.
  All 19 module declarations and the zero-solution witness print exactly
  `[propext, Classical.choice, Quot.sound]`; the non-vacuity example compiles.
- `make check` — exit 0; 13 policy tests pass and 30 work items are consistent.
  The architecture output retains pre-existing copied-source admission notices
  and `source_hashes_match: false`.
- `lake test` (the `make test` recipe, run directly inside `verification/`)
  — exit 0; registered contract checks pass.
- `make test-mutations` — exit 0; all three mutations rejected as required.
- Forbidden-proof-token scan of both new Lean files and `git diff --check`
  — clean. The only heartbeat override is a documented, declaration-local
  `400000` on the momentum transport theorem; no global override is used.
