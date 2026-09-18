# Lane 409-T22-UB3-cutoff-datum — Opus continuation after a failed codex run

The codex run of this lane (see `research/T22/REPORT_409.md`, `research/T22/ATTEMPTS_UB3.md`, `research/T22/T22_SPLIT.md` U-B3 status "blocked") delivered **no theorem**: it
claimed that `exists_smooth_tsupport_subset` and `exists_contDiff_one_nhds_of_subset` are unknown identifiers under this Mathlib pin, that "the T22 import tree has no bridge for
the zero-extension pairing", and it never built the closure ("missing prebuilt `Domain.olean`" — that just means it did not run `lake build NSFormalization.Section3.T22.Domain`
first). Treat those claims as unverified. Your job: deliver U-B3 per the original brief below. Notes: (1) build the closure first (`lake build NSFormalization.Section3.T22.Domain
NSFormalization.Section3.T22.RestrictBridge NSFormalization.Section3.T22.OrderZero`); (2) for the cutoff existence search Mathlib for the smooth Urysohn lemma on a normed space —
candidates `exists_smooth_zero_one_of_isClosed` / `exists_contMDiff_zero_one_of_isClosed` (manifold form, applies to `ℝ³` with `𝓘(ℝ, Space)`; grep `Mathlib/Geometry/Manifold/PartitionOfUnity.lean`),
`IsOpen.exists_smooth_support_eq`, `exists_smooth_support_subset`, `ContDiffBump` + a finite cover of the compact `K` by balls inside `Ω` (sum of bumps normalised, or
`SmoothPartitionOfUnity`) — whichever exists under the pin; report the exact name used; (3) for (b) read `IsCutoffDatum`, `angularRealization`, `restrictDatum`, `restrictField`,
`IsSobolevDatum` in `Section3/T22/Domain.lean` and the lane-383/393 bridges before deciding the pairing route. Rewrite `ATTEMPTS_UB3.md`/`REPORT_409.md`/the U-B3 status with the
truth (keep the codex text as a struck-through or "superseded" section). Commit on the same branch `erenup/409-T22-UB3-cutoff-datum`.

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
