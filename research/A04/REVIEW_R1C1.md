# Lane 160 R1/C1 source review — 2026-09-15

## Result

The reviewed `A04/Continuation.lean` preserves the statement of R1
(`research/A04/Spec.lean:574`) after its explicit analytic input hypotheses,
and C1 (`Spec.lean:657`) after `Restart` and `HigherOrderBound`. No statement-fidelity blocker
was found. This is a source review only; Luna records compilation separately.

## Evidence

- `Restart` matches A02 `Spec.lean:550`: the same `δ(ν,K)` is selected before
  the data, forcing and restart time. The endpoint proof retains the full δ.
- All three force premises of R1 remain. The local `BoundedIntoHOne` premise
  is unused because the assumed A02 restart only consumes the shifted L1 bound;
  this is not a weakening of the conclusion's contract.
- The maximal field construction obtains positivity from an existing shorter
  solution and uses the existing normalized-pressure gluing, without assuming
  A01 local existence.
- C1 preserves both lifespan positivity and the endpoint guard
  `ofReal S ≤ maximalLifespanR`. Substitution of the finite lifespan's `toReal`
  gives the guarded criterion at equality and a strict self-inequality.

## Force translation and final export

Reviewed the added `ForceShift.lean` and final `restartBeyond` wrapper.
Positive translation sends positive times to positive times; each measurable
Sobolev datum path therefore translates to an admissible path for the shifted
force. Its half-line L1 norm is the norm on a tail, bounded by the original
half-line integral. Taking the infimum over all original datum paths preserves
the inequality, including the empty-witness case. No unsupported existence of a
minimizer or force regularity is assumed.

The final `restartBeyond` supplies this proved estimate to the internal assembly:
its only analytic hypothesis is `Restart`. Its conclusion and quantifier order
remain the Spec R1 statement. The internal C1 reduction remains conditional on `extendsBeyond`. No source-level blocking finding remains.

## G3 and final C1 assembly

The added `HigherOrderBound` matches Spec's full G3 statement (`Spec.lean:534`):
`MemL1Hm`, `SolvesBelow`, the finite squared H2 integral and all integer orders
are retained. No `HasSmoothSobolevPath` rider was added.

`extendsBeyond` uses G3 only at order 1, obtains the compact force bound on
`Icc 0 (S+1)`, and sets `K = max M (max F ‖f‖L1H1)`.
All three caps are finite (`M` from G3, `F` from F1, L1 cap from `MemL1Hm` at 1),
and dominate the matching R1 premises on their exact intervals. The positive
uniform δ then yields a strict lifespan extension. The final
`lifespanInfiniteOfLocallyFinite` invokes the already reviewed finite-supremum
contradiction with this derived criterion. Its only analytic inputs are
**A02 Restart and G3 HigherOrderBound**, not a free continuation-criterion input.
These inputs are still unproved by this lane. No source-level blocking finding.

## Verification scope

Luna subsequently compiled both modules and `axioms_r1c1.lean` successfully:
all nine audited declarations use only the standard three logical axioms, and
the concrete zero-solution / zero-shift examples typecheck. This reviewer did
not run Lean; the commands and logs are recorded in the session validation report.
