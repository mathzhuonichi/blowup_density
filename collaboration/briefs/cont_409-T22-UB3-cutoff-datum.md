# Lane 409-T22-UB3-cutoff-datum — CONTINUATION (the previous run died with HTTP 429 mid-way)

Your previous run on this lane was cut off by an API rate limit. The worktree `/data_8T/ping/blowup_density/.claude/worktrees/409-T22-UB3-cutoff-datum` (branch `erenup/409-T22-UB3-cutoff-datum`)
may contain **uncommitted partial work** (`git status --short`, `git diff`): read it first and continue from it rather than starting over — keep what elaborates, fix or
delete what does not. Then follow the original brief below to the end (all deliverables, gates, commit, four-part report to `research/T22/REPORT_409.md`).

---

# Lane 409-T22-UB3-cutoff-datum — T22 U-B3: cutoff existence + cutoff datum realizes the zero extension (bookkeeping)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/409-T22-UB3-cutoff-datum` (git branch `erenup/409-T22-UB3-cutoff-datum`, based on `origin/erenup/integration-section3`, which contains
`Section3/T22/{Domain,RestrictBridge,WeightRatio,OrderZeroIsometry,CutoffKernel,OrderZero}.lean`). Read `CLAUDE.md`, **`research/T22/T22_SPLIT.md` §0 and unit U-B3** (`:95-104`),
`Section3/T22/Domain.lean` (`IsCutoffDatum`, `angularRealization`, `restrictDatum`, `restrictField`, `DomainTest`, `zeroExtension`, `smulLeftCLM`), `Section3/T22/RestrictBridge.lean`
(lane 383: `restrictDatum`/`restrictField` bridges), `Section3/T22/OrderZero.lean` (lane 393: `restrictDatum_eq_restrictField_of_datum`), the Mathlib smooth-Urysohn/bump lemmas
(`exists_contDiff_one_nhds_of_subset` / `exists_smooth_tsupport_subset` / `IsCompact.exists_isOpen_lt_of_lt`, `ContDiffBump`), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- No named inputs. Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
New module `formalization/NSFormalization/Section3/T22/CutoffDatum.lean` (namespace `NSFormalization.Section3.T22`), the U-B3 targets consumed by U-Z1:
(a) `theorem exists_cutoff (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) : ∃ χ : Space → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ω ∧ (∀ᶠ x in 𝓝ˢ K, χ x = 1)`
(state the "`χ = 1` on a neighbourhood of `K`" clause in whatever form U-Z1's split text uses — `∃ V, IsOpen V ∧ K ⊆ V ∧ ∀ x ∈ V, χ x = 1` is acceptable; say which);
(b) `theorem isCutoffDatum_realizes_zeroExtension {s χ A B} (hcut : IsCutoffDatum s χ A B) (hA : restrictDatum Ω s A = restrictField Ω z) (hsupp : tsupport (zeroExtension Ω z) ⊆ K)
(hχ : χ = 1 on a nbhd of K, same form as (a)) (hχΩ : tsupport χ ⊆ Ω) : IsSobolevDatum s (zeroExtension Ω z) B`. Route: unfold `IsCutoffDatum` (`angularRealization s (B i) ψ =
angularRealization s (A i) (smulLeftCLM ℂ (χ·) ψ)`); `χ·ψ` is a Schwartz test with compact support inside `tsupport χ ⊆ Ω`, hence a `DomainTest`, so the right side is
`restrictField Ω z i (χψ) = ∫ x in Ω, χ x · ψ x · z x i`; `χ = 1` on `supp (E₀z) ⊆ K` collapses it to `∫ ψ · (E₀z) i`, which is the `IsSobolevDatum` pairing. Read the exact
definitions before writing statements; if `IsSobolevDatum` is phrased through a different pairing, prove the bridge.
Deliverables: the module, `research/T22/probes/cutoff_datum_closes.lean` (instantiate (a) on `Ω = ball 0 1`, `K = closedBall 0 (1/2)`), `research/T22/axioms_ub3.lean`,
`research/T22/ATTEMPTS_UB3.md`, U-B3 status line in `T22_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T22.CutoffDatum` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands and results). Also write it to `research/T22/REPORT_409.md`.
