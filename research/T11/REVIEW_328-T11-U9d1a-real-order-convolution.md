ACCEPT

## What the lane claims

The worker claims an unconditional real-order extension of lane 317: for every
`r : ℝ` with `3 ≤ r`, a real bounded bilinear map `H^r × H^r → H^(r-1)`, its
projected-symbol coefficient formula, the explicit `9 * sqrt (2 * 4^r *
∑' W^(-r))` bound, order reweighting compatibility, the order-three
`TorusConvolutionInput` bridge, and nonzero constant-mode examples.  The report
also explicitly records the nested-index elaborator timeout and says that no
named input or weaker theorem was used (`research/T11/REPORT_328.md:5-43,57-76`).

## What is in Lean

The claimed object really has the requested type.  Although its source
definition uses the elaboration workaround `torusConvolutionCLM_realAt r t`,
the exported declaration prints as
`PeriodicSobolev r →L[ℝ] PeriodicSobolev r →L[ℝ] PeriodicSobolev (r - 1)`:
`formalization/NSFormalization/Section3/T11/ConvolutionBoundReal.lean:538-602`.
The source-level application witness pins the output to `PeriodicSobolev
(r - 1)` at
`formalization/NSFormalization/Section3/T11/ConvolutionBoundReal.lean:604-606`;
an independent `#print` in the review probe gave the same full type
(`research/T11/probes/rev328_statement.lean:10-21`).

The real scalar convolution uses exactly the input weights `W^(-r/2)`, output
weight `W^((r-1)/2)`, and derivative symbol
(`formalization/NSFormalization/Section3/T11/ConvolutionBoundReal.lean:121-129`),
and the Peetre/kernel comparison and summability are proved rather than
assumed
(`formalization/NSFormalization/Section3/T11/ConvolutionBoundReal.lean:149-209`).
This matches the paper's real-order Fourier convolution
route (`paper/sections/appendix-a-local-theory.tex:33-50`).  The projected
symbol keeps the zero mode and uses the same Leray formula
(`formalization/NSFormalization/Section3/T11/ConvolutionBoundReal.lean:330-347`), in
agreement with the paper's torus projection convention
(`paper/sections/02-preliminaries.tex:76-87`) and with the order-three tree
implementation (`formalization/NSFormalization/Section3/T11/ConvolutionBound.lean:347-360`).

The coefficient, operator norm, and applied norm statements are exactly the
report's claims
(`formalization/NSFormalization/Section3/T11/ConvolutionBoundReal.lean:620-634`).
The transport identity
has the requested `.1 i k` form and the weight `W^((r-3)/2)`
(`formalization/NSFormalization/Section3/T11/ConvolutionBoundReal.lean:727-742`);
it correctly uses `persistenceDown`, whose defining ratio and
reweight theorem are in
`formalization/NSFormalization/Section3/T11/Persistence.lean:57-68`, and the canonical relation is
exactly `B.1 i k = W(k)^((t-s)/2) • A.1 i k`
(`formalization/NSFormalization/Section3/T10/PeriodicData.lean:209-214`).
The general compatibility theorem is present and in fact does not need the
brief's extra `r ≤ r'` hypothesis
(`formalization/NSFormalization/Section3/T11/ConvolutionBoundReal.lean:714-725`).

The order-three bridge and the constant-mode annihilation theorem are present
at `formalization/NSFormalization/Section3/T11/ConvolutionBoundReal.lean:744-788`.
The supplied probe checks the general target, `r = 3`, and
`r = 7/2` (`research/T11/probes/convolution_bound_real_closes.lean:17-72,92-110`),
and proves two genuinely nonzero constant-mode data at both orders
(`research/T11/probes/convolution_bound_real_closes.lean:74-90,112-128`) plus
cross-order transport
(`research/T11/probes/convolution_bound_real_closes.lean:130-141`).

No hypothesis is silently vacuous: the only main-order hypothesis is the
honest `3 ≤ r`; no `⊤.toReal`, empty interval, or unused analytic binder is
introduced.  The sole heartbeat increase is local, commented, and within the
limit
(`formalization/NSFormalization/Section3/T11/ConvolutionBoundReal.lean:420-423`).
A whole-tree Section 4 grep found
no competing real-order convolution declaration, so there is no unsupported
“not in the tree” gap claim to accept.

## Gaps

There is no mathematical gap for this lane.  The report's stated limits—no
`r < 3`, no optimality claim, no order-`r` Picard contract, and no U9d1
half-step theorem—are explicit scope exclusions, not silently weakened fields
(`research/T11/REPORT_328.md:73-76`).  The phantom-index elaborator timeout is
real and documented; it does not change the exported type (the independent
`#print` above confirms this).  No `sorry`, `admit`, `axiom`, or
`native_decide` occurs in the new module, and no existing Lean module is
modified relative to `origin/erenup/integration-section3`.

The required substantive negative check was run separately: flipping the sign
of the coefficient identity in `research/T11/probes/rev328_mutation.lean:11-16`
fails with the expected type mismatch, not by dropping an argument:

```
error: Type mismatch
  torusConvolutionCLM_real_coeff r hr A B i k
has type
  ... = torusProjectedConvectionSymbolReal r A B i k
but is expected to have type
  ... = -torusProjectedConvectionSymbolReal r A B i k
```

## Commands and results

All commands used `. scripts/lean-env.sh`; Lean commands ran from
`verification/` with `LEAN_NUM_THREADS=6`, one Lake process at a time.

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.ConvolutionBoundReal` — exit 0; final line `Build completed successfully (9978 jobs).`  The run replayed dependency linter warnings, but none from the new module.
- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section3/T11/ConvolutionBoundReal.lean` — exit 0, no Lean output.
- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/probes/convolution_bound_real_closes.lean` — exit 0, no output.
- `cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/T11/axioms_convolution_bound_real.lean` — exit 0.  All 34 public declarations and both named local instances print exactly `[propext, Classical.choice, Quot.sound]`; all 29 private-helper audit lines print the same list.
- `make check` — exit 0; `test_contract_policy` reports `Ran 13 tests ... OK`, and `check_work_queue` reports `45 work items: ownership, contract registration and task cards consistent.`
- `. scripts/lean-env.sh && LEAN_NUM_THREADS=6 scripts/gates.sh NSFormalization.Section3.T11.ConvolutionBoundReal` — exit 0; mutation suite reports `extra_axiom: rejected as required`, `weakened_hypothesis: rejected as required`, `Mutation suite passed`, and final line `== gates OK`.
- `. scripts/lean-env.sh && python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3` — exit 0; final JSON has `"base_compatibility_checked": true`.
- `rg` for `sorry|admit|axiom|native_decide` in the new module — no matches.  `git diff --name-only origin/erenup/integration-section3...HEAD` shows only the new module/records and the appended T11 status row; `git diff --check` is clean.
