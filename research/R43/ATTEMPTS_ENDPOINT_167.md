# R43 G5 maximal endpoint (lane 167)

## Statement

`MaximalEndpoint.maximal_h2TimeIntegral` (namespace `NSFormalization.Section4.R43`)
extends the C01 bound to every real `0 < S` with `ofReal S ≤ maximalLifespanR`.
It retains positive viscosity, the initial class, actual `MemForceR`, the actual
`A02.IsMaximalSolution` family, and the C01 absorption bound on `Ico 0 S`.
The integrand is the canonical angular `D01.sobolevENorm 2`, on the supplied
velocity and original data/force. No classical solution at S is requested.

## Proof route

For each `0 < t < S`, choose `t < r < S`. The actual maximal-family predicate
supplies a classical solution of the same data through horizon r, with velocity
literally equal to u. `C01.h2TimeIntegral_Ioc` gives the closed-right t integral
with the already uniform budget S. `C01.lintegral_Ioo_le_of_Ioc` passes to the
open interval using its countable directed union of rational endpoints. This
reuses the existing monotonicity and force-regularity proof instead of repeating
the budget comparison for each r.

The natural-square corollary rewrites by the existing G6 power equality and
deduces finiteness from the real-valued bound. The research consumer transports
the frozen V2 maximal-family predicate using the existing binding iff and
lifespan bridge; its smallness constant is the actual V4 witness's C₁.

## Scope and remaining gaps

This closes only the G5 endpoint passage, conditional on the stated genuine
absorption bound. It supplies neither critical-energy G7, the absorption
bootstrap, nor unconditional A04 continuation. No new contract or registry entry.

## Verification

Source written by Astra low. All Lean compilation was executed by the
parent-selected Luna high compiler; no Lean compilation was run by this writer.

Luna's first build found only the final slice eta equality in the natural-square
bridge. The proof now closes that definitional equality explicitly with `rfl`
after rewriting the power; the unused slice simp argument was removed.

The second source build passed. The first consumer's `simpa ... using` did not
close the source `gradientSq` against the expanded frozen gradient bridge.
Changed it to the existing V4 binding's pattern: simplify the goal with the
Frobenius bridge, then `exact` the source theorem, permitting definitional
reduction of `C01.gradientSq`. The other three axiom reports were standard;
the failed consumer was not counted as validated.

Final local evidence, confirmed by Luna and reviewed by the parent:

- Source module rebuild r2: exit 0, 10,389 jobs.
- `axioms_endpoint167.lean` probe r3: exit 0; all four declarations depend only
  on `propext`, `Classical.choice`, and `Quot.sound`.
- Full `lake test`: exit 0; 27 registered contracts and 29 checked witnesses.
- Contract mutation checks: exit 0.

The two fixes affected proof elaboration only; the endpoint statement and its
original hypotheses were unchanged. These are local checks, not cloud CI.
