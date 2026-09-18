# Lane 342-T12-tame-product — T12 the scalar tame product `tameProduct` of `MeanZeroSobolevCalculusAPI` (`eq:Rproduct` on the torus)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/342-T12-tame-product` (git branch `erenup/342-T12-tame-product`, based on `origin/erenup/integration-section3`: canonical modules
`formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray,FourierCalculus}.lean` (FourierCalculus only if lane 305 has landed — check `ls`),
`Section3/T12/{MeanZeroCalculus,SpectralGap}.lean` (the T12 vocabulary and the proved spectral-gap fields), `Section3/T10/{PeriodicData,FourierCalculus,ForcePaths,Parseval,DatumBasics}.lean`, `Section3/T11/{ClassicalRegularity,PairingBound,ConvolutionBoundReal,MildPressure,MildMomentum,EnergyIdentity}.lean` (lane 339's Bernstein bound `W(k)^N‖ĝ(k)‖ ≤ 2^N(sup|g| + sup|Δ^N g|)` and slab machinery; lane 336's `torusInverseWeight_summable` (`∑ W^{-r} < ∞` for real `r > 3/2`), `torusWeightPeetre`, trilinear convolution; the periodic convolution theorem `periodicFourierCoeff_mul`), and the target statements `research/T12/probes/api_on_canonical.lean` (the Type-valued `MeanZeroSobolevCalculusAPI`: constants as data fields; read every field's exact statement and docstring in `research/T12/Spec.lean`), the registered contract `verification/Contracts/V1/TorusData.lean` (`T01.torus_data`), and the proof targets
`research/T12/probes/api_on_canonical.lean`). Read `CLAUDE.md` (hard rules; "结构体例外"), **`research/T12/RECONCILIATION.md` §0–§3 and `research/T12/COMPARISON.md` §"Proof dependencies"**,
`research/T11/RECONCILIATION.md` §0–§3, `research/T11/IMPLEMENTATION_CANDIDATES.md`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; no anonymous `local instance`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- **Satisfiability / peeling rule** (`T11_SPLIT.md` §0): if your unit must assume something not yet proved, name exactly ONE input hypothesis with its exact statement as a `def … : Prop`
  (the split names it where applicable), prove everything else from it, and record it; never weaken a target statement. Target statements are the fields of
  `research/T12/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T12/probes/tame_product_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Prove the `tameProduct` field of `research/T12/probes/api_on_canonical.lean` verbatim with an explicit constant family `Cproduct m` (positivity included): for `m ≥ 2` and scalar `a, b ∈ H^m(T³)` (the field's exact hypotheses — `MemPeriodicHmScalar m` / `IsPeriodicScalarDatum`, read `Spec.lean`), `‖ab‖_{H^m} ≤ Cproduct m (‖a‖_{H²}‖b‖_{H^m} + ‖b‖_{H²}‖a‖_{H^m})` in the `periodicScalarSobolevENorm` spelling. Route (Fourier side, the same machinery as lane 336's `PairingBound.lean`): the product's coefficient is the convolution (`MildPressure.periodicFourierCoeff_mul`, extended from smooth to `H^m` functions — for `m ≥ 2` both factors are continuous with absolutely summable coefficients, so the product's coefficients are the convolution: prove this extension via the `L²` representation or by density; say which), then split `W(k)^{m/2} ≤ 2^{m/2}(W(l)^{m/2} + W(k−l)^{m/2})` (`torusWeightPeetre`), and in each half bound the low-order factor by `‖·‖_{H²}` through `∑ W(l)^{-2} < ∞` (`torusInverseWeight_summable`) and Cauchy–Schwarz (Young `ℓ¹ * ℓ² ⊂ ℓ²` on the lattice). Existence of the product's datum (`ab` has an order-`m` datum) is part of the claim: construct it from the convolution bound. **No named input**; honest partial with the exact obstacle if stuck. (L, Opus.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T12/TameProduct.lean` (namespace `NSFormalization.Section3.T12`); the probe; conformance `research/T12/axioms_tame_product.lean`.
2. Records `research/T12/ATTEMPTS_TAME_PRODUCT.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T12/REPORT_342.md`; update your unit's row in
   `research/T12/COMPARISON.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T12.TameProduct` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[342-T12] TameProduct`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
