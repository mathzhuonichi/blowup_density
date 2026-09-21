# Lane 485 — T23 U6 rates and convergence

## 1. Statements

All eight U6 field components are proved, with the authorized parallel-lane
facts threaded explicitly: `energyConst`, `energyConst_nonneg`, `energyRate`,
`forceDiffSobolevConst`, `forceDiffSobolevConst_pos`,
`forceDifference_sobolev_bound`, `forceDifference_negativeSobolev_tendsto`,
and `forceDifference_convergence`.

The path bridge first bounds the slice infimum by every admissible measurable
path and then takes the path infimum. It remains valid when there is no path.
The triangle inequality uses actual realizing paths and derives integrable
Schwartz pairings from their continuous, nonnegative-order slices. It neither
identifies path and slice norms nor assumes addition of totalized integrals.

Energy restriction contracts each spatial velocity/gradient norm, then the
essential supremum, lower integral, and positive square root. The rate retains
`(M + E) * ε^(1/2) + C * ε^(3/2)`. The probe consumes the actual
`Bindings.scaling C th` implementation's `perturbationEnergyBound`, checks
its correction is exactly `C`, and transports the matching center, time,
and correction family. Its nonnegative correction constant is not replaced
by a coarser single-power rate.

The force constant is `2 * (|A s| + |B s|) + 1`, chosen before ε. Separate
q=1 packet/correction path estimates combine using ε≤1 and s≥0, followed by
the support identity and U5's left comparison. The probe also normalizes
both registered I03 positive-scaling clauses at q=1.

Inhomogeneous order lowering is contractive on whole-space slice infima and
on domain extension infima. Integrating the latter gives the all-negative
convergence field from the proved order-zero rate. The former additionally
proves the literal zero-extension estimate against its L² norm, using T22's
order-zero identification for square-integrable zero extensions. No negative
I03 endpoint restriction is used. Both limits squeeze along `𝓝[>] 0`, using
eventual membership in `(0, ε₀]` and the two positive real-power exponents.

## 2. Files

- `formalization/NSFormalization/Section3/T23/NormBridge.lean`: path bridge,
  whole-space and domain order contraction, measurable-path triangle
  inequality, and zero-extension negative-order L² estimate (five declarations).
- `formalization/NSFormalization/Section3/T23/Rates.lean`: energy restriction,
  constants, absorption, actual-family rates, and both convergence fields
  (thirteen declarations).
- `research/T23/probes/T23-U6-rates-convergence_closes.lean`: exact consumers
  for all eight canonical field components at the threaded hypotheses;
  actual registered I03 energy and q=1 rate consumers; norm definition bridges.
- `research/T23/axioms_T23-U6-rates-convergence.lean` and `.log`: all 18
  production declarations print exactly `[propext, Classical.choice, Quot.sound]`.
- `research/T23/ATTEMPTS_T23-U6-rates-convergence.md`: development errors and fixes.
- `research/T23/T23_SPLIT.md`: U6 status line.

Skeleton committed as `12e17ada`; subsequent proof checkpoints were committed
incrementally. No existing production module, contract, registry, or parallel
lane module was edited. No push, merge, rebase, or sub-agent work was performed.

## 3. Gaps and error text

No open U6 proof or compiler error remains. This is the requested conditional
unit delivery, not a construction of a complete `BoundaryInsertionAPI`.
U9 must supply U2b's matching whole-space energy and separate Sobolev estimates,
the actual insertion formulas, correction/packet slice regularity and support,
and U5's left comparison on one common threshold. These premises are explicit;
no replacement record, named-input bundle, or assumption of a U6 conclusion is
used to produce its own rate. The convergence theorems consume the proved rate,
and their probes instantiate it from the separate suppliers.

G0's owner-pending statement wording and G1's unrestricted smooth-domain IBP
remain outside U6. The domain contraction is stronger than the requested
zero-extension route and needs no smooth-domain uniqueness theorem.

Nine resolved development failures are recorded verbatim in ATTEMPTS. Examples:

```text
Unknown identifier `enorm_le_enorm`
Unknown identifier `nnnorm_le_nnnorm_iff`
(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```

The timeout was fixed by explicitly typing the infimum witness and intermediate
norm bound, without a heartbeat override. Other failures were definitional
projection spelling, addition-side convention, and probe namespace/import
resolution. A checkpoint containing the timeout was repaired immediately in
`771c3953`; all final files pass.

## 4. Commands and results

Every Lean shell sourced `. scripts/lean-env.sh`. All Lake invocations ran
from `verification/` with `LEAN_NUM_THREADS=6`.

| Check | Result |
|---|---|
| Build Boundary, LocalCorrectionBridge, StatementRepair, NoSlipEnergy, DifferenceEnergy, BoxIntegration before proof work | Exit 0; 10087 jobs |
| Build consumed R41.NonDensityL1, T24.AffineEnergy, Paper1.ScalingLimits, T22.OrderZero, Bindings.Scaling closures | Exit 0 |
| `lake build NSFormalization.Section3.T23.NormBridge NSFormalization.Section3.T23.Rates` | Exit 0; 10677 jobs; dependency diagnostics only |
| `lake env lean` on each new production module | Exit 0; zero output bytes each |
| `lake env lean ../research/T23/probes/T23-U6-rates-convergence_closes.lean` | Exit 0; zero output bytes |
| `lake env lean ../research/T23/axioms_T23-U6-rates-convergence.lean` | Exit 0; all 18 lists exactly the standard three |
| `make check` | Exit 0; 54 contracts, 13 policy tests, 45 consistent work items |
| `lake test` | Exit 0; registered tests pass |
| `make test-mutations` | Exit 0; refactor accepted, three invalid mutations rejected |
| Source import traversal from both modules | 2226 module names visited; no BoundaryCorollary path |
| New production/probe forbidden-token scan | No matches |
| `git diff --check` | Exit 0 |

`make check` still prints the pre-existing umbrella BoundaryCorollary token and
`source_hashes_match: false`, while returning success. Neither belongs to this
lane's source import closure. The test and mutation gates certify their existing
registered scope; the new unit is certified separately by its builds and probe.
