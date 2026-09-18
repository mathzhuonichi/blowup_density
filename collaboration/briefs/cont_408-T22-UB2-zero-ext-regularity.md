# Lane 408-T22-UB2-zero-ext-regularity — CONTINUATION (the previous run died with HTTP 429 mid-way)

Your previous run on this lane was cut off by an API rate limit. The worktree `/data_8T/ping/blowup_density/.claude/worktrees/408-T22-UB2-zero-ext-regularity` (branch `erenup/408-T22-UB2-zero-ext-regularity`)
may contain **uncommitted partial work** (`git status --short`, `git diff`): read it first and continue from it rather than starting over — keep what elaborates, fix or
delete what does not. Then follow the original brief below to the end (all deliverables, gates, commit, four-part report to `research/T22/REPORT_408.md`).

---

# Lane 408-T22-UB2-zero-ext-regularity — T22 U-B2: zero-extension regularity (bookkeeping)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/408-T22-UB2-zero-ext-regularity` (git branch `erenup/408-T22-UB2-zero-ext-regularity`, based on `origin/erenup/integration-section3`,
which contains `Section3/T22/{Domain,RestrictBridge,WeightRatio,OrderZeroIsometry,CutoffKernel,OrderZero}.lean`). Read `CLAUDE.md`, **`research/T22/T22_SPLIT.md` §0 and unit U-B2**
(`:86-93`), `Section3/T22/Domain.lean` (`zeroExtension`, `restrictField`, `DomainTest`, the canonical `BoundedDomainNormAPI`), `Section3/T22/RestrictBridge.lean` (lane 383),
`Section3/T22/OrderZero.lean` (lane 393: how `Ω.indicator z` is handled), the datum constructors (`grep -rn "smoothJets_exists_datum\|SmoothSquareIntegrableJets" formalization/NSFormalization/Section4/D01`),
and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- No named inputs. Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
New module `formalization/NSFormalization/Section3/T22/ZeroExtRegularity.lean` (namespace `NSFormalization.Section3.T22`), the U-B2 targets consumed by U-Z1:
`theorem contDiff_zeroExtension (hΩ : IsOpen Ω) (hz : ContDiffOn ℝ ∞ z Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) (hsupp : tsupport (zeroExtension Ω z) ⊆ K) : ContDiff ℝ ∞ (zeroExtension Ω z)`,
`theorem hasCompactSupport_zeroExtension (…same…) : HasCompactSupport (zeroExtension Ω z)`, and the consequences `memLp_zeroExtension : MemLp (zeroExtension Ω z) 2 volume`,
`smoothJets_zeroExtension : SmoothSquareIntegrableJets (zeroExtension Ω z)` (or whatever the D01 datum constructor's hypothesis is named — read it) and
`exists_datum_zeroExtension (s : ℝ) : ∃ A, IsSobolevDatum s (zeroExtension Ω z) A` via the existing D01 constructor. Route: `zeroExtension Ω z = Ω.indicator z` (check the
definition — use the exact spelling) agrees with `z` on the open `Ω` (`ContDiffOn` there) and vanishes on the open `(tsupport)ᶜ`; the two opens cover `ℝ³` because `tsupport ⊆ K ⊆ Ω`;
glue with `contDiff_iff_contDiffAt` + `ContDiffOn.contDiffAt` on each open (`IsOpen.mem_nhds`), or `ContDiffOn.congr` on `Ω` plus `contDiffAt_of_eventuallyEq zero` off the support.
Deliverables: the module, `research/T22/probes/zero_ext_regularity_closes.lean` (a nonzero `ContDiffBump` instance on `Ω = ball 0 1`, `K = closedBall 0 (1/2)`), `research/T22/axioms_ub2.lean`,
`research/T22/ATTEMPTS_UB2.md`, U-B2 status line in `T22_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T22.ZeroExtRegularity` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands and results). Also write it to `research/T22/REPORT_408.md`.
