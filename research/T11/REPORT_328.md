# REPORT 328 — T11 / U9d1a: the projected convection convolution at every real order `r ≥ 3`

## 1. What was proved

For **every real `r ≥ 3`** (not just integers), on the canonical T10 carriers:

- `torusConvolutionCLM_real (r : ℝ) (hr : 3 ≤ r) : PeriodicSobolev r →L[ℝ] PeriodicSobolev r →L[ℝ] PeriodicSobolev (r-1)`
  — a genuine bounded **real bilinear** map, built by `LinearMap.mkContinuous₂`, no residual input.
- **Coefficient identity (intrinsic).** `torusConvolutionCLM_real_coeff`:
  `(torusConvolutionCLM_real r hr A B).1 i k = torusProjectedConvectionSymbolReal r A B i k`,
  where `torusConvectionSymbolReal r A B i k = W(k)^((r-1)/2) · ∑ⱼ (2πi kⱼ) · ∑'_l W(l)^(-r/2) A_j(l) · W(k-l)^(-r/2) B_i(k-l)`
  and `torusProjectedConvectionSymbolReal` applies the same Leray formula as at order three
  (`W(k) = 1 + 4π²|k|²`; the zero mode is kept).
- **Coefficient identity (transported, the form the brief asked for).**
  `torusConvolutionCLM_real_coeff_transport`:
  `(torusConvolutionCLM_real r hr A B).1 i k = W(k)^((r-3)/2) · torusProjectedConvectionSymbol (persistenceDown r 3 hr A) (persistenceDown r 3 hr B) i k`
  — literally lane 317's projected convection symbol of the order-three reweighted data,
  transported by the weights.
- **Explicit norm bound.** `torusConvolutionCLM_real_norm_le`:
  `‖torusConvolutionCLM_real r hr‖ ≤ torusConvolutionConstant_real r = 9 · sqrt (2 · 4^r · ∑'_k W(k)^(-r))`,
  plus the applied form `‖Q A B‖ ≤ C · ‖A‖ · ‖B‖`. No optimality is claimed (at `r = 3` the
  constant is `√2` times lane 317's, see ATTEMPTS).
- **Reweighting compatibility between orders.** `torusConvolutionCLM_real_reweight`: if
  `IsPeriodicReweight r r' A A'` and `IsPeriodicReweight r r' B B'`, then
  `IsPeriodicReweight (r-1) (r'-1) (Q_r A B) (Q_{r'} A' B')`. The brief's hypothesis `r ≤ r'`
  is not needed and was dropped. Its symbol-level form
  (`torusConvectionSymbolReal_reweight`, `torusProjectedConvectionSymbolReal_reweight`) is the
  single lemma from which the transport identity above also follows.
- **Backward compatibility.** `torusScalarConvectionReal_three`, `torusConvectionSymbolReal_three`,
  `torusProjectedConvectionSymbolReal_three` prove that at `r = 3` the new symbols are *equal* to
  lane 317's, and `torusConvolutionInput_ofReal : TorusConvolutionInput` re-discharges lane 313's
  residual input from the new construction.
- **Non-vacuity.** `torusConvolutionCLM_real_constants`: two constant-mode data are annihilated;
  the probe exhibits two nonzero data at `r = 3` and at `r = 7/2`, and transports the order-3
  value to the order-7/2 value through the compatibility lemma.

Mathematical content of the estimate: the kernel squared is
`W(k)^(r-1)‖2πikⱼ‖² W(l)^(-r) W(k-l)^(-r) ≤ W(k)^r W(l)^(-r) W(k-l)^(-r)`, then the real-exponent
Peetre inequality `W(k)^r ≤ 4^r (W(l)^r + W(k-l)^r)` (from `W(k) ≤ 4 max (W l) (W (k-l))` and
`rpow` monotonicity) turns it into `4^r (W(l)^(-r) + W(k-l)^(-r))`, whose `l`-sum is
`2·4^r ∑ W^(-r) < ∞` because `W ≥ 1` makes `W^(-r) ≤ W^(-3)` summable. Discrete Cauchy–Schwarz on
`ℓ²` and the reindexing `(k,l) ↦ (l, k-l)` then give the product of the two energies, exactly as at
order three: no cutoff, no density argument, no analytic assumption.

## 2. Files

- `formalization/NSFormalization/Section3/T11/ConvolutionBoundReal.lean` (new, 803 lines):
  34 public declarations, 2 named local instances, 29 private helpers.
- `research/T11/probes/convolution_bound_real_closes.lean` (new): every target closes — general
  `r ≥ 3`, then `r = 3` (including lane 313's verbatim `∃ Q : H³→L H³→L H², …` target) and
  `r = 7/2`, two constant-mode data at each, and the cross-order transport.
- `research/T11/axioms_convolution_bound_real.lean` (new): `#guard_msgs`-checked `#print axioms`
  for all 36 named declarations and a `run_cmd` audit for the 29 private helpers.
- `research/T11/ATTEMPTS_CONVOLUTION_BOUND_REAL.md` (new), this report, and one appended status
  line in `research/T11/T11_SPLIT.md` §1.

## 3. Gaps

- **No named input remains**; every statement in the module is unconditional. The lane's theorem is
  proved outright.
- **One elaborator obstacle, worked around without weakening anything.** The nested bilinear type
  `PeriodicSobolev r →L[ℝ] PeriodicSobolev r →L[ℝ] PeriodicSobolev (r-1)` cannot be elaborated
  directly: instance search reports
  `failed to synthesize MulAction ℝ ↥(PeriodicSobolev (r - 1)) … timeout at typeclass (20000) … timeout at whnf (200000)`
  and raising both limits (200000/400000) does not help. Cause: the phantom index makes the two
  instances interchangeable, so the elaborator tests `r =?= r - 1` and `whnf` on real subtraction
  diverges; literal indices, two free indices, or an opaque index all elaborate. The map is
  therefore built as `torusConvolutionCLM_realAt (r t : ℝ) (hr : 3 ≤ r) : … →L[ℝ] PeriodicSobolev t`
  and the lane's object is `torusConvolutionCLM_real r hr := torusConvolutionCLM_realAt r (r-1) hr`,
  whose *inferred* type is the one asked for; a source-level `example` pins the codomain to
  `PeriodicSobolev (r-1)`, and all unbundled statements (datum, coefficients, norms) are at the
  honest index. Full measurements in `ATTEMPTS_CONVOLUTION_BOUND_REAL.md`.
- **Out of scope / not claimed.** No result for `r < 3`; no optimality of the constant; the
  two-space Picard contract (`TorusTwoSpaceContract`) is still an order-three object — this lane
  supplies its convolution input, not an order-`r` contract; and the `H^r` half-step of U9d1
  (`TorusHalfStepInput`) is a *different* unit (329/330), untouched here.

## 4. Commands and results

```
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.ConvolutionBoundReal
  → ✔ [9978/9978] Built … Build completed successfully (0 errors)
cd verification && lake env lean ../formalization/NSFormalization/Section3/T11/ConvolutionBoundReal.lean
  → no output (0 errors, 0 warnings)
cd verification && lake env lean ../research/T11/probes/convolution_bound_real_closes.lean
  → no output (0 errors)
cd verification && lake env lean ../research/T11/axioms_convolution_bound_real.lean
  → exit 0; 29 private helpers reported `[propext, Classical.choice, Quot.sound]`;
    the 36 `#guard_msgs` prints matched exactly the same three axioms (no diagnostics)
make check
  → check_formalization_plan / check_contracts / test_contract_policy (13 tests OK) /
    check_work_queue (45 work items consistent) — all pass
```

`grep` over the module: no `sorry`, `admit`, `axiom`, `native_decide`; one
`set_option maxHeartbeats 400000 in` (on `torusConvectionDatumReal_norm_le`, the nested
`PiLp`/`lp` vector-norm computation, as in lane 317).
