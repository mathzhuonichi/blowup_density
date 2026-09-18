# REPORT 356 — T18 Draft A

## 1. The theorem rendered

`research/T18/DraftA.lean` renders the torus `thm:insertion`
(`03-torus.tex:287-346`) as the Type-valued `PeriodicInsertionAPI` and the
quantified `periodicInsertionStatement`.  The record fixes one packet,
placement, scaling package, cutoff/correction package, reference classical
solution, and one threshold.  It has separate fields for the three
`eq:insertion` formulas, force/initial class membership, a pinned classical
solution, exact `maximalLifespanT = T`, `breakdownSetT` membership, the
pointwise blow-up clause, unchanged history, support and divergence-free
clauses, both cross-transport identities, the exact momentum equation, and the
three rates `eq:Eclose`, `eq:Fclose`, and `eq:Hsclose`.  Negative-order force
convergence is also exported explicitly.

## 2. Lean contents

The file is 2,160 lines.  It imports the registered T10/T11 contracts and
copies the needed T13/T14/T15/T16/T17/T12 declarations in delimited blocks
with provenance comments.  The copied blocks include `LocalizationAPI`,
`PacketEnergyAPI`, `PacketImportAPI`, `PlacementData`, `ScalingAPI`,
`CutoffData`, `LocalPotentialAPI`, `CorrectionAPI`, mixed-norm carriers, and
`MeanZeroSobolevCalculusAPI`.  Every totalized norm in the insertion record is
paired with an explicit `MemLp`/Sobolev path guard.  `ν>0`, `δ>0`, and
`ε∈Ioc 0 ε₀` are explicit hypotheses, and `ε₀` is a parameter so the
statement has the requested `∃ ε₀>0, Nonempty (…)` order.

`research/T18/COMPARISON_A.md` contains the paper-clause/R42-field table,
parameter choices, ambiguity resolutions, the T11/T12/T13/T15/T16/T17 lemma
consumption list, and the requested implementation grep candidates.

## 3. Remaining proof gap

This is a statement-only contract draft.  The cross-term identities,
maximal-lifespan equality, and all finite-scale inequalities are fields to be
discharged by the future T18 proof.  The proof will consume the T11 uniqueness
and continuation APIs, T12 `boundedRepresentative`, T13 localization and
endpoint transfers, T15 packet scaling identities, and T17 correction bounds;
the exact mapping is recorded in the comparison table.

## 4. Commands and results

The required elaboration command succeeds with zero errors:

```text
cd verification && lake env lean ../research/T18/DraftA.lean
```

The quality-clause placeholder scan was run as requested:

```text
grep -nE ': *True|:= *0$|→ *True' research/T18/DraftA.lean
```

It produced no output.  No `sorry`, `admit`, `axiom`, or `native_decide` was
added.  The implementation-candidate grep from `COMPARISON_A.md` was recorded
for the next proof lane; this draft does not modify formalization modules.
