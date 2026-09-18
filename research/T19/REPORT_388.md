# Lane 388 report — T19 U1--U6 bookkeeping

## 1. Proved theorem

Added canonical proofs for all six wave-1 units from `T19_SPLIT.md`:
`thresholdValue`, `mixedRegionArithmetic`, `regionExamples`,
`energyTimeEmbedding`, `referenceFiniteEnergy`, and the two U6 zero-norm
helpers `torusForceSobolevENorm_zero` and
`torusMixedLebesgueENormT_zero`.  Their statements are the U1--U5 Spec fields
verbatim modulo the required canonical vocabulary, plus the two exact U6 helper
targets.  No named input or residual assumption remains.

## 2. What Lean now has

`formalization/NSFormalization/Section3/T19/Bookkeeping.lean` provides the
T19-local canonical vocabulary and all seven public theorems without importing
`Contracts.*`.  U4 proves the finite-time `L²_tL²_x`/essential-sup embedding
directly.  U5 proves finite coefficient energy for a classical reference by
compact bounds on its continuous Sobolev datum paths and a Fourier-coefficient
proof that taking the mean-zero part does not increase the order-one Sobolev
norm.

`research/T19/probes/bookkeeping_closes.lean` imports the registered contracts,
copies the Spec-local mixed and space-time definitions, records the
registered/canonical definitional equalities, and closes every U1--U5 field and
both U6 helpers by `exact`.  It also checks the requested numeric arithmetic
instances and converts the contract classical solution to the canonical one in
U5.  `research/T19/axioms_u1_6.lean` audits every public theorem; each prints
exactly `[propext, Classical.choice, Quot.sound]`.

## 3. Remaining gap

There is no remaining gap in U1--U6.  The later T19 units U7 onward remain
outside this lane and retain the dependencies documented in `T19_SPLIT.md`, in
particular the constructive density units' dependency on the registered T18
insertion result.

## 4. Commands and results

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T19.Bookkeeping`:
  exit 0, `Build completed successfully (9980 jobs)`; only pre-existing
  warnings from upstream replayed modules.
- `lake env lean` on `Bookkeeping.lean`, `bookkeeping_closes.lean`, and
  `axioms_u1_6.lean`: all exit 0 with no errors; the audit printed the required
  three axioms for all seven theorems.
- Forbidden-token scan over the three Lean deliverables: no `sorry`, `admit`,
  `native_decide`, `axiom`/`opaque` declaration, or heartbeat override.
- `git diff --check`: exit 0.
- `make check`: exit 0; formalization-plan, contract-policy, contract
  architecture, and work-queue checks passed.
