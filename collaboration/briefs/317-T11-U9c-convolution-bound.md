# Lane 317-T11-U9c-convolution-bound — T11 U9c: discharge `TorusConvolutionInput` (bounded bilinear H³×H³→H² realization of the projected convection convolution)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/317-T11-U9c-convolution-bound` (git branch `erenup/317-T11-U9c-convolution-bound`, based on `origin/erenup/integration-section3`: canonical modules
`formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray,FourierCalculus}.lean` (FourierCalculus only if lane 305 has landed — check `ls`),
`Section3/T11/{LocalTheory,FlowConversion,CriterionBridge,LocalExistenceProbe,LocalExistence}.lean` (lane 313's `LocalExistence.lean` defines the target `TorusConvolutionInput` and `torusProjectedConvectionSymbol`, and proves `torusConvolution_summable`), `Section3/T12/{MeanZeroCalculus,SpectralGap}.lean` (`reweightDatum`, weight comparisons), the registered contract `verification/Contracts/V1/TorusData.lean` (`T01.torus_data`), and the proof targets
`research/T11/probes/api_on_canonical.lean`). Read `CLAUDE.md` (hard rules; "结构体例外"), **`research/T11/T11_SPLIT.md` (binding: §0 ground rules, your unit's entry in §1, §3 risks, §4 conversions)**,
`research/T11/RECONCILIATION.md` §0–§3, `research/T11/IMPLEMENTATION_CANDIDATES.md`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; no anonymous `local instance`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- **Satisfiability / peeling rule** (`T11_SPLIT.md` §0): if your unit must assume something not yet proved, name exactly ONE input hypothesis with its exact statement as a `def … : Prop`
  (the split names it where applicable), prove everything else from it, and record it; never weaken a target statement. Target statements are the fields of
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/convolution_bound_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Unit **U9c** (`research/T11/EXISTENCE_ROUTE.md` §"U9b status" and §"Subsequent sub-lanes"): **discharge lane 313's single residual input**, verbatim
```lean
def TorusConvolutionInput : Prop :=
  ∃ Q : PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 2,
    ∀ A B i k, (Q A B).1 i k = torusProjectedConvectionSymbol A B i k
```
i.e. the projected convection symbol `torusProjectedConvectionSymbol` (read its definition in `LocalExistence.lean`/`LocalExistenceProbe.lean`: coefficientwise `P_k ∑_j (2πi k_j)`-type convolution
of two order-3 data) is a **bounded real bilinear map `H³ × H³ → H²`** on the weighted coefficient carrier. Route: the discrete Sobolev product estimate — for `A, B ∈ ℓ²` with weights `W(k)^{3/2}`
(`W = 1 + 4π²|k|²`), the convolution `∑_{k'} a(k') b(k−k')` is controlled in the `W^{1}`-weighted `ℓ²` norm (order 2 with one derivative from the symbol `|2πk| ≤ W^{1/2}`) via the Peetre inequality
`W(k) ≤ 2 (W(k') + W(k−k'))`, Cauchy–Schwarz, and the lattice summability `∑_{k} W(k)^{-3/2} … ` — the standard `H^s` algebra proof for `s > 3/2`; Mathlib pieces: `lp`/`Memℓp` API, `tsum` Cauchy–Schwarz
(`inner_mul_le_norm_mul_norm` on `lp 2`), `Finset`/`tsum` reindexing by `k ↦ k − k'` (`Equiv.addLeft`/`tsum_equiv`), `summable_of_nonneg_of_le`; existing local pieces: `Section3/T12/SpectralGap.lean`
(`reweightDatum`, weight comparison lemmas), lane 313's `torusConvolution_summable`, `torusMultiplierCLM`, `torus_realSubmodule_closed`. Build `Q` as a `ContinuousLinearMap` in two steps
(`LinearMap.mkContinuous₂` with the explicit bound), prove the coefficient identity, hence `theorem torusConvolutionInput : TorusConvolutionInput`, and the corollary
`torusTwoSpaceContract_nonempty'` (instantiate lane 313's `torusTwoSpaceContract_nonempty`). If the projection `P_k` or the derivative symbol needs a separate bound, prove it as a lemma
(`|P_k v| ≤ |v|` is in `Section3/T10/Leray.lean`'s contraction). No named input expected: this is the analytic core — do not stop at a partial bound; if genuinely stuck, name exactly ONE input
(e.g. the scalar weighted convolution inequality with its exact statement) and finish the rest. (L, astra.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/ConvolutionBound.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_convolution_bound.lean`.
2. Records `research/T11/ATTEMPTS_CONVOLUTION_BOUND.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_317.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.ConvolutionBound` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[317-T11] ConvolutionBound`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
