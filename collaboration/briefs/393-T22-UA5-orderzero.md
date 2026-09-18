# Lane 393-T22-UA5-orderzero — T22 U-A5: the `orderZero` field of `BoundedDomainNormAPI` verbatim (order-0 domain Sobolev norm = `L²(Ω)` norm of the restricted field), on top of lanes 387 (U-A4) and 383 (U-B1)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/393-T22-UA5-orderzero` (git branch `erenup/393-T22-UA5-orderzero`, based on lane 387's branch merged with `origin/erenup/integration-section3`:
`Section3/T22/{Domain,RestrictBridge,WeightRatio,OrderZeroIsometry}.lean` — lane 387's `norm_orderZeroDatum_eq : ‖orderZeroDatum hz‖ₑ = eLpNorm z 2 volume`; lane 383's
`restrictDatum_eq_restrictField`, `domainSobolevENorm_le_sobolevENorm`; the canonical `BoundedDomainNormAPI` restatement). Read `CLAUDE.md`, **`research/T22/T22_SPLIT.md` §0 and unit U-A5
(target verbatim, inputs with file:line, route)**, `research/T22/Spec.lean` (`orderZero` field of `BoundedDomainNormAPI` — token-for-token target — and the definitions `restrictDatum`,
`domainSobolevENorm`, `restrictField`, `zeroExtension`), `research/T22/REPORT_{383,387}.md`, `Section4/D01/OrderZeroDatum.lean` (`orderZeroDatum`, `isSobolevDatum_orderZeroDatum`-type
realization lemma — grep), `Section4/D01/FiniteOrderNorm.lean`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; the `maxHeartbeats` note of lane 387).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging** (hard analytic unit). An honest partial with the exact residual statement and error text beats a stub.
- Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
New module `formalization/NSFormalization/Section3/T22/OrderZero.lean` (namespace `NSFormalization.Section3.T22`): `theorem orderZero` — the `orderZero` field of the canonical
`BoundedDomainNormAPI` verbatim (read it: the order-0 domain norm `domainSobolevENorm Ω 0 (restrictField Ω z)` equals the `L²(Ω)` norm `eLpNorm z 2 (volume.restrict Ω)` of the restricted
field, under the field's exact hypotheses; the `⊤ = ⊤` edge off `L²(Ω)` if the field includes it). Route (T22_SPLIT U-A5): `≤`: the zero extension `E₀z ∈ L²(ℝ³)` gives the order-0 datum
`orderZeroDatum` whose norm is `eLpNorm (E₀z) 2 volume = eLpNorm z 2 (volume.restrict Ω)` (lane 387's isometry + `zeroExtension` a.e./support facts), and it restricts to `restrictField Ω z`
(lane 383's `restrictDatum_eq_restrictField`), so the `⨅` is `≤`; `≥`: every datum `A` of an extension realizing `restrictField Ω z` has `‖A‖ₑ = eLpNorm (its field) 2 volume ≥ eLpNorm z 2 (volume.restrict Ω)`
(the field agrees with `z` on `Ω`; monotonicity of `eLpNorm` under `restrict`) — the quotient-norm identity; handle the `⨅` over the empty family (`⊤`) and the `MemLp`-or-not split.

## Deliverables
1. `Section3/T22/OrderZero.lean`; 2. probe `research/T22/probes/orderzero_closes.lean` (the canonical field closed by `exact`; non-vacuity: a nonzero `ContDiffBump` field with `Ω = ball 0 1`,
both sides finite and equal); 3. `research/T22/ATTEMPTS_UA5.md`, `research/T22/axioms_ua5.lean`, status in `research/T22/T22_SPLIT.md` U-A5, report `research/T22/REPORT_393.md` (if a guard
blocks the write, put the full report in your final message).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T22.OrderZero` (0 errors), `lake env lean` on module / probe / axioms file; `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with exact error text / commands and results).
