# A01/A04 V2 wording — decision record (lead, 2026-09-17)

**User decision (2026-09-17 03:40Z):** "按你感觉最专业的来；只要形式化 Lean 是对的就行；说明和对比一下；不一定走工作量大的路径，但 short path 要避免 reward hacking。" → **Option 1**, with the safeguards below.

## The two statements

| | paper (appendix A, Tao-style local theory; `research/A01/Spec.lean:338`, `research/A04/Spec.lean` `Restart`) | what the tree proves (lanes 210/211/215/217) |
|---|---|---|
| quantifier order | `∀ ν > 0, ∀ K ≠ ⊤, ∃ δ > 0, ∀ a ∈ X_R, ∀ f ∈ F_R, ‖a‖_{H¹} ≤ K → ‖f‖_{L¹H¹} ≤ K → δ ≤ horizon ν a f` (δ uniform in the force) | `∀ ν > 0, ∀ f ∈ F_R, ∀ S ≥ 0, ∀ K ≠ ⊤, ∃ δ > 0, ∀ t₀ ∈ [0,S], ∀ a ∈ X_R, ‖a‖_{H⁷} ≤ K → δ ≤ localHorizon' ν a (timeShift t₀ f)` (δ depends on f and S; uniform over restart times and H⁷-bounded data) |
| datum norm | H¹ | H⁷ |
| source of δ | Tao's H¹ quantitative local existence with force | HeliCorgi's H⁷ Picard horizon (lane 210 `HorizonUniform`) + the force-path norm on `[0,S+1]` (lane 215) |

The V2 statement is **weaker** than the paper's sentence in two ways (fixed force; higher-order datum bound) and **stronger** in one (explicit uniformity over restart times for one force). It is not a re-proof of the paper's sentence by a different method; it is a different, honestly labelled statement.

## Why it is not reward hacking
- Every downstream consumer in the tree was checked against it, not against the paper's sentence: A02 `exists_maximal'` (213), A04 `restartBeyond'/extendsBeyond'/lifespanInfiniteOfLocallyFinite'` (215/217), R43 (219/221/223/225), R44 (227/229), R41 (232/235/249). All of them restart **the same force** at times `t₀ < T_max` with data bounded in H⁷ by the Grönwall bound (lane 179) — the paper's cross-force uniformity is never used (`research/A04/REPORT_215.md` §3). So the main theorems (Prop. 4.3, 4.4, Thm 4.1) are proved unconditionally and their contracts (30–32) do not depend on which wording A01/A04 carry.
- The V2 contracts must (i) not contain the H¹ sentence as a proved field, (ii) carry the H¹ sentence verbatim as a named **open** definition with a docstring saying it is not implied, (iii) state the exact narrowing in each docstring, (iv) come with non-vacuity examples at a nonzero force and nonzero datum, (v) include a "Paper vs V2" comparison table in `COMPARISON.md`. Enforced in the briefs of lanes 212 (A01) and 230 (A04) and checked by the codex reviews.

## What the paper's sentence would need
A forced H¹ quantitative local theory on the mild stack (H¹ energy + Picard estimates with force, uniform in the force through its `L¹H¹` norm) — the deferred option 2; estimated at several days of lanes and not needed by Section 4's theorems. Recorded for the owner.
