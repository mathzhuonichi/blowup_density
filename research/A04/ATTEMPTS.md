# A04 — attempts and revision record

## Review fixes (revision 1 → revision 2)

Applied against [`REVIEW.md`](REVIEW.md) (verdict **ACCEPT-WITH-NOTES**,
reviewed at `78b0b99`), on the lane branch after the lead merged
`erenup/integration` (merge commit `f2937e8`, which brings
`verification/Contracts/V1/TameProduct.lean`).

| finding | severity | what changed |
|---|---|---|
| **1** | MAJOR | `lifespanInfiniteOfLocallyFinite`: the criterion hypothesis is now guarded by the manuscript's own range, `∀ S, 0 < S → ENNReal.ofReal S ≤ maximalLifespanR ν a f → squaredHTwoIntegral S u ≠ ⊤` (`04-whole-space.tex:121`, "within or at the maximal lifespan"). Revision 1 quantified over *all* `S`, which C01 cannot discharge past a hypothetical finite lifespan — `u` is unconstrained there and `sobolevENorm` is fail-safe to `⊤`. The derivation is unaffected: contradiction at a finite supremum instantiates the hypothesis only at `S = T^ν_{max,R}`, where the guard holds with equality. |
| **2** | MAJOR | Same field: added `0 < maximalLifespanR ν a f`, `IsMaximalSolution`'s first clause (`research/A02/Spec.lean:212-215`, rationale `:180-183`). Without it the reviewer's `u = p = 0` at a datum with empty lifespan makes the inline family vacuous, the integral `0 ≠ ⊤` at every `S`, and the conclusion assert `0 = ⊤`. **Swept every other field for the same omission:** `higherOrderBound`, `restartBeyond` and `extendsBeyond` are stated on `SolvesBelow`, which at `0 < S` produces a `ClassicalSolutionR ν a f (S/2)` and hence positivity on its own; no other field inlines an `IsMaximalSolution`-style family. Recorded in `SolvesBelow`'s docstring so the asymmetry is visible at the definition. |
| **3** | MODERATE | Added `import Contracts.V1.TameProduct`. Deleted the seven `⟪A03:…⟫` mirror `def`s (`lift`, `partialDeriv`, `outerColumn`, `columnsSobolevENorm`, `outerSobolevENorm`, `gradientSobolevENorm`, `MemHmVector`) and the `outerProductTame` field; added `tame : Contracts.V1.TameProduct.TameProductAPI`, carried whole like `boundedRepresentative`. `gradientSobolevNormAt` now calls `Contracts.V1.TameProduct.gradientSobolevENorm` (`TameProduct.lean:192`). Net −77 lines of mirrors. |
| **3** sub-note | — | **Constant decision: keep `Chigh` opaque**, state `energyIdentityHigh` with it, not with `tame.Ctame`. Reason: eq:Rhigh's Cauchy–Schwarz step contributes a factor one, so an implementation *may* take them equal, but `appendix-a:131` says only "using eq:Rproduct gives"; pinning them would oblige an implementer to prove a sharper identity than the manuscript states, for no gain, since `R43`/`R44` use the criterion qualitatively and never see either constant. The revision-1 docstring claim "`Chigh` above may be taken to be `Ctame`" is rewritten as a permission rather than an identification. Recorded in `COMPARISON.md` §2, `Chigh` row. |
| **4** | MODERATE | Split by whether a field *asserts* the input — the smaller change of the two the reviewer offered. (a) The `C^∞`-in-time datum path **is** asserted (the three differential fields say `r ↦ ‖u(r)‖²_{H^m}` is differentiable, while `ClassicalSolutionR.sobolev` gives only `ContinuousOn`), so A01's `ManuscriptLocalRegularity.sobolev_smooth` (`research/A01/Spec.lean:230`) is restated verbatim as the new `def HasSmoothSobolevPath` and is an explicit hypothesis of `energyIdentityHigh`, `regularizedNormDerivative` and `highContinuationIntegral`; those three are now self-contained. (b) A02's `restart`/`uniqueness` are **not** asserted by any field — they are proof inputs of `restartBeyond` — so they stay out; restating `restart` would drag in `IsMaximalSolution`, `presingularTimes` and `timeShift`, the duplication `DEPENDENCY_GRAPH.md:205-209` and `COMPARISON.md` §3 tell this lane to avoid, and the review itself praised the draft for avoiding. (c) A new header section, "How the inputs of the other lanes enter — and why asymmetrically", states the rule actually applied: **importability**. A03's contracts are registered Lean modules, hence fields; A01/A02 live under `research/`, which is not a Lean library and cannot be imported by `lake env lean`, so `maximal : MaximalSolutionAPI` is not available to this draft at all. Unit **D1** in `COMPARISON.md` §4 is narrowed accordingly: producing the smooth path is now A01's, and D1 keeps only the inner-product derivative step. |
| **5** | MINOR | `MemL1Hm` and `BoundedIntoHOne` **kept**, with the justification moved to where a reader meets them. Each `def` docstring now says outright that `MemForceR` (`Data.lean:544`) supplies it — the `MemLp G 1` clause and the `ContDiffOn ℝ ∞ G futureTimes` clause respectively — that the derivation is unit **F1**, and why it is still listed (to display the manuscript's own hypothesis, to show which half of `F_R` each field consumes, and — for `BoundedIntoHOne` — because `restartBeyond` needs the bound to be *the same* `K` as the velocity's, which `MemForceR` alone does not give). Every use site now carries the "(free from `MemForceR`, unit **F1**)" pointer. |
| **6** | MINOR | `highContinuationIntegral` no longer writes an inequality against Mathlib's interval-integral junk `0`. It now **asserts** `IntervalIntegrable (fun s => …) volume t₀ t` as a conjunct of the conclusion, alongside the bound. Chosen over adding it as a hypothesis: on a classical solution the integrand is continuous on a compact interval (unit **N1**), so the implementer pays nothing and every consumer is spared a side condition. The module docstring's conventions section now documents this totality caveat next to the existing `ℝ≥0∞`/`toReal` one, and notes that `squaredHTwoIntegral`, being an `∫⁻`, has no such caveat. |
| **7** | MINOR | `COMPARISON.md`: `integer_energy_uniform` corrected to `Euler/OrdinaryEulerHigherEnergy.lean:84` (was `:82`); the `tame` row now cites `verification/Contracts/V1/TameProduct.lean:215,345` instead of the `026-A03-tame-contract` worktree path; every "PR #31 has not landed / not yet on `erenup/integration`" sentence removed from both `Spec.lean` and `COMPARISON.md`. |

### Not changed, and why

* **`energyIdentityHigh`'s constant is not `tame.Ctame`** — see the finding 3
  sub-note row above.  This is a deliberate decision, not an oversight.
* **`higherOrderBound`, `extendsBeyond` and `lifespanInfiniteOfLocallyFinite`
  carry no `HasSmoothSobolevPath` rider.**  These three transcribe manuscript
  sentences (`appendix-a:146-147`, `02-preliminaries.tex:108-114`,
  `04-whole-space.tex:121`); their hypotheses are `prop:local`'s, and a
  regularity rider would make them weaker than the proposition.  A01's clause
  reaches them through the three differential fields, which already carry it.
* **No A02 field is restated.**  `restartBeyond` remains A02's `restart` cashed
  at the endpoint, which is the whole point of the `A04 ← A02` edge.
* The ten checks `REVIEW.md` listed as clean — `squaredHTwoIntegral`'s measure
  and convention, the absence of any spectral-gap/Poincaré/mean-zero content,
  eq:Rhigh term-for-term, the `ζ`-step algebra, `extendsBeyond`,
  `restartBeyond`'s non-duplication, `higherOrderBound`, the five COMPARISON
  spot-checks and the Mathlib Grönwall survey — were not touched.

### Verification after the fixes

```
$ cd /data_8T/ping/blowup_density/.claude/worktrees/030-A04-spec
$ . scripts/lean-env.sh; export LEAN_NUM_THREADS=6
$ cd verification && lake build Contracts.V1.TameProduct
✔ [8817/8817] Built Contracts.V1.TameProduct (2.6s)
Build completed successfully (8817 jobs).                      # exit 0

$ lake env lean ../research/A04/Spec.lean
                                                               # no output, exit 0

$ make check                                                   # worktree root
python3 experiments/check_formalization_plan.py --check         → exit 0
python3 experiments/check_contracts.py                          → exit 0
python3 experiments/test_contract_policy.py                     → Ran 13 tests … OK
python3 experiments/check_work_queue.py                         → 30 work items … consistent
```

`#check` of every changed field (scratch file in `/tmp`, deleted afterwards)
confirms the elaborated statements: the two new hypotheses on
`lifespanInfiniteOfLocallyFinite`, the `IntervalIntegrable … ∧ …` conclusion on
`highContinuationIntegral`, `tame : …Contracts.V1.TameProduct.TameProductAPI`,
and `HasSmoothSobolevPath : ℝ → SpaceTimeField → Prop`.

## Earlier attempts (revision 1)

No dead ends worth recording: the draft was written once against
`appendix-a-local-theory.tex:127-157` and typechecked on the first
`lake env lean`.  Two modelling choices were weighed and are recorded in
`Spec.lean` rather than here — stating eq:Rhigh on the **squared** norm (so that
no regularization is needed where none is needed) and stating the `ζ↓0` limit in
**integrated** form (because `‖u‖_{H^m}` need not be differentiable at a zero).
Both survived review.

One environment failure, unrelated to A04: the final `lake test` stage of
`scripts/lean-install.sh` failed once on
`NavierStokes.ActualSignedPhysicalCoherence` with
`failed to open file … ActualSignedCurrentSupport.olean`, while the same log
shows that olean built two jobs earlier.  A targeted rebuild succeeded and a full
`lake test` re-run passed 9406/9406 with all three registered contract tests
reporting "checked; standard logical axioms only".  Transient lake race; recorded
so the next lane does not chase it.
