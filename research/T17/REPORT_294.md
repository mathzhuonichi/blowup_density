# 294-SPEC-t17-draft-a

## 1. Theorem specified

Draft A now states every clause of `lem:correction`: the explicit `H_epsilon`, fixed-cylinder profile hypothesis, both derivative bounds, `eq:wE`, endpoint-inclusive `eq:Hmixed`, and T13-transferred `eq:HHs`, with constants uniform in one small-scale range.

## 2. Lean now

`DraftA.lean` is self-contained over copied T10/T13/T16 vocabulary. Its Type-valued `CorrectionAPI` uses periodic Haar/mixed/Sobolev norms, explicit `MemLp` and datum-path witnesses, and distinguishes the single-chart profile from the globally periodized correction. `COMPARISON_A.md` maps every clause to its `I02.correction` counterpart and records implementation candidates.

## 3. Remaining gap

This is statement-only. Registration still needs the affine rescaling/chain-rule lemmas, periodic support and mixed-norm scaling, and the single-copy T13 localization adapter (including `s=0,1` endpoints).

## 4. Checks

- `cd verification && lake env lean ../research/T17/DraftA.lean` — passed.
- `make check` — passed.
