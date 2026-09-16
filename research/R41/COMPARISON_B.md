# Independent draft B: Theorem 4.1

This draft was written from the permitted manuscript passages and registered
`Data`, `Thresholds`, and `CriticalRegularity` vocabulary/template only. No other
R41 draft, implementation, binding, statement ledger, or lane brief was read.
References in registered vocabulary comments were not followed. Only this lane's
new deliverables are inspected under `research/R41/`.

## Paper-clause correspondence

| Paper clause | Lean field | Quantifiers / conclusion |
| --- | --- | --- |
| `04-whole-space.tex:8,10`, fixed-initial-velocity density (i) | `fixedInitialDensity` | ∀ ν>0, ∀ T>0, ∀ q∈{1,2}, ∀ s∈ℝ, ∀ a∈X_R, s<s_q → density |
| `04-whole-space.tex:8,11`, zero-velocity equivalence (ii) | `zeroInitialDensityIff` | ∀ ν>0, ∀ T>0, ∀ q∈{1,2}, ∀ s∈ℝ, density at a=0 ↔ s<s_q |
| `04-whole-space.tex:13`, numerical thresholds | `thresholdValues` | Real arithmetic: s₁=1/2 and s₂=−1/2 |
| `04-whole-space.tex:13`, around every regular reference | `regularReferenceApproximation` | After ν,T,q,s<s_q: ∀ a∈X_R, ∀ g∈F_R, ∀ δ>0, ∀ reference v on [0,T+δ), ∃ ε₀>0, ∃ one family (f,u) |
| Same line, same initial velocity | Same field, `ClassicalSolutionR ν a (f ε) T` | Every sufficiently small positive ε gives a solution with precisely datum a, through its registered `initial` field |
| Same line, same earlier history | Same field, pointwise equality on `Icc 0 (T - 2 * ε ^ 2)` | ∀ sufficiently small ε>0, ∀ t in that interval, ∀ x, u_ε(t,x)=v(t,x) |
| Same line, singularity exactly at T | Same field, `maximalLifespanR ... = ENNReal.ofReal T` | Equality, together with a classical solution on [0,T); not just membership in the breakdown set |
| Same line, velocity difference tending to zero in E_T | Same field, second `Tendsto` | The same family's registered `energyENorm` tends to zero as ε↓0 |
| Same line, “approximating” around reference in the stated topology | Same field, first `Tendsto` | The same family's `forceSobolevENorm q s (f ε - g)` tends to zero as ε↓0 |

The rider is one field with shared existential witnesses. Splitting its conclusions
into independent existence fields would lose simultaneity. Clause (ii) is one iff
field, matching the paper literally and keeping the endpoint converse visible.
The forward direction intentionally overlaps clause (i) at a=0.

## Representation choices

- `q : ℝ` with the explicit restriction `q = 1 ∨ q = 2`; `s : ℝ`.
  All divisions in `2 / q - 3 / 2` are real divisions. Norm exponents use
  `ENNReal.ofReal q`, which is exactly 1 or 2 under the restriction. There is
  no integer division, and no exceptional q=0 case in any assertion.
- `ThresholdAPI` is imported as registered vocabulary. Its `formula` is
  `exponent q s = 2/q - 3/2 - s`. The threshold is written directly as
  `2/q - 3/2`; no arbitrary arithmetic API instance is required as a hypothesis
  of the PDE theorem. `thresholdValues` records the explicit “Thus” sentence,
  redundant with the registered arithmetic obligations.
- `BreakdownDenseR` is the registered `RelativelyDense` predicate for
  `forceClassR` and `breakdownSetR`. Clause (ii) spells out the same predicate
  with `breakdownSetRZero`. It quantifies over reference forces in the smooth
  class and positive ENNReal radii, asking for strict norm approximation.
  It is relative norm density, not density in the full Bochner completion or
  the topology of smooth test functions. Radii may include infinity as in the
  registry; finite positive radii already characterize the topology.
- Density concerns `T_max ≤ T`. The rider asserts the strictly more specific
  `T_max = ENNReal.ofReal T`. Positivity of T is always present, so the cast
  does not collapse a negative time to zero. Infinite lifespan remains `⊤`.
- A regular reference is a named `ClassicalSolutionR ν a g (T+δ)` with δ>0.
  This unpacks the existential in registered `RegularThrough` while keeping
  the actual reference velocity available for comparison. Quantifying over
  every such extension is the natural meaning of “every reference.” The
  registered half-open convention is equivalent to the manuscript's closed
  extension after shrinking δ.
- The families f and u are total functions of real ε. Only small positive ε
  carry PDE and force-class assertions. Their one-sided limits use
  `nhdsWithin 0 (Ioi 0)`, so arbitrary other values are irrelevant. The harmless
  choice `2*ε₀² < T` keeps the whole history interval inside [0,T).
- Energy convergence uses `energyENorm T`, the sum of the two norms in
  `01-introduction.tex:143-145`, with no viscosity factor. All norms remain
  ENNReal-valued; no `.toReal` totalization occurs.
- No local definitions are needed and nothing needs registration. The draft
  imports only `Contracts.V1.Data` and `Contracts.V1.Thresholds`. The registry's
  existing transitive imports are not changed.

## What is inherited from Theorem 4.2

The rider restates the consequences of the manuscript's insertion theorem:
force membership and solution existence (`04-whole-space.tex:32`), identical
datum and exact lifespan and history (`:32-35`), energy convergence from the
bound (`:37-40`), force convergence and common witnesses (`:41`). The density
proof explicitly invokes these at `:177,181`. This is a statement-level
re-export; no Lean insertion contract or implementation was inspected/imported.

Theorem 4.1 does not itself quantify a spatial ball, promise compact support of
the force correction, state an L-infinity limsup, give constants M,D,C or an
energy rate, or demand one family for all q,s simultaneously. Those additional
Theorem 4.2 assertions (`:32-41`) are therefore not added to this API. In
particular, “singularity exactly at T” is interpreted using exact classical
lifespan, not a new independently specified blowup norm.

## Manuscript ambiguities / elaborations requiring comparison

1. **s is not explicitly introduced in line 8.** It is universally quantified
   over real Sobolev orders immediately after q in this draft.
2. **The final rider does not repeat s<s_q.** This draft scopes force/energy
   approximation to the subcritical range. Reading force approximation as
   unconditional would contradict clause (ii) near the zero reference at and
   above the threshold. Insertion without force-smallness is a distinct claim
   available in Theorem 4.2, not a further field here.
3. **“Same earlier history” has no cutoff in line 13.** The explicit
   [0,T−2ε²] cutoff is taken from line 35, justified by line 181. It implies
   preservation on any prescribed compact earlier interval for sufficiently
   small ε, rather than preservation all the way up to T.
4. **No approximation parameter is named in line 13.** This draft uses the
   ε↓0 family supplied by Theorem 4.2. For each fixed q,s it shares all
   witnesses; it does not strengthen the rider to uniformity over q,s.
5. **“Singularity” is informal in line 13.** Exact maximal lifespan is used.
   Theorem 4.2 additionally supplies unbounded speed, and
   `02-preliminaries.tex:47-48` highlights this stronger feature of inserted
   solutions. A lead may choose to expose that extra insertion conclusion,
   but it is not an explicit separate clause of Theorem 4.1.
6. **“Regular through T” is stronger than existence up to T.** The δ>0
   extension in `02-preliminaries.tex:34-36` is essential. It is not replaced
   by existence on [0,T), or by the inequality T_max≥T.
7. **The sentence after the theorem (line 16) is explanatory.** Smooth force
   classes with relative topology are already represented. The T-dependent
   radius for the q=2 converse is not separately quantified by Theorem 4.1;
   the iff gives non-density without choosing or asserting a uniform radius.
8. **Line 13's numeric thresholds are redundant.** They are included as an
   arithmetic field to account for every sentence, rather than proved here.

There are no other identified statement ambiguities. The principal review point
is the scope and precision of the final rider, not the two density clauses.
