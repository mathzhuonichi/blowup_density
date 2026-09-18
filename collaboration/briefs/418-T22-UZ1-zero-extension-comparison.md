# Lane 418-T22-UZ1-zero-extension-comparison — T22 U-Z1: `zeroExtensionComparison` assembly (two-sided bound from the U-A3 constant and the U-B units)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/418-T22-UZ1-zero-extension-comparison` (git branch `erenup/418-T22-UZ1-zero-extension-comparison`, based on lane 409's branch merged with
`origin/erenup/integration-section3`: `Section3/T22/{Domain,RestrictBridge,WeightRatio,OrderZeroIsometry,CutoffKernel,OrderZero,CutoffMultiplier,CutoffMultiplierField,ZeroExtRegularity,CutoffDatum}.lean`).
Read `CLAUDE.md`, **`research/T22/T22_SPLIT.md` §0 and unit U-Z1** (`:164-173`: left conjunct from U-B1's `domainSobolevENorm_le_sobolevENorm`, right conjunct from
`cutoffMultiplier` (406) applied to a datum of `E₀z` obtained through U-B2 (`exists_datum_zeroExtension`) and U-B3 (`exists_cutoff`, `isCutoffDatum_realizes_zeroExtension` — note
it needs `HasCompactSupport χ` and does **not** need `K ⊆ Ω`, see `REPORT_409.md` §3)), the canonical field `BoundedDomainNormAPI.zeroExtensionComparison` in
`Section3/T22/Domain.lean` (read its exact quantifier order: `∃ C > 0` chosen before `z`), `research/T22/REPORT_{383,406,408,409}.md`, and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line.

## Goal
New module `formalization/NSFormalization/Section3/T22/ZeroExtensionComparison.lean` (namespace `NSFormalization.Section3.T22`): `theorem zeroExtensionComparison` whose type is
literally the canonical field (probe `example : <field type> := zeroExtensionComparison`). Route: fix `Ω, K, s`; pick the cutoff `χ` from `exists_cutoff` (`K ⋐ Ω`); take
`C := cutoffFieldConst s χ` (positive) from `cutoffMultiplier`; for each `z` smooth on `Ω` with `tsupport (E₀z) ⊆ K`: the left inequality `domainSobolevENorm Ω s (restrictField Ω z) ≤
sobolevENorm s (E₀z)` is U-B1's restriction bound; for the right, `E₀z` has a datum `A₀` (U-B2) — but the field's right side is `‖E₀z‖_{H^s} ≤ C·domainSobolevENorm …`: unfold the domain
norm as an infimum over data `A` with `restrictDatum Ω s A = restrictField Ω z`, apply `cutoffMultiplier` to each such `A` to get `B` with `IsCutoffDatum s χ A B` and
`‖B‖ₑ ≤ C‖A‖ₑ`, then U-B3 (b) says `B` is a datum of `E₀z`, so `sobolevENorm s (E₀z) ≤ ‖B‖ₑ ≤ C‖A‖ₑ`; take the infimum over `A` (handle `⊤` when no datum exists: then the
inequality is trivial). Deliverables: the module, `research/T22/probes/zero_extension_comparison_closes.lean` (type match + a nonzero bump instance on `ball 0 1` with
`K = closedBall 0 (1/2)`), `research/T22/axioms_uz1.lean`, `research/T22/ATTEMPTS_UZ1.md`, U-Z1 status line in `T22_SPLIT.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T22.ZeroExtensionComparison` (0 errors), `lake env lean` on the module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorem with exact statement / files / gaps with error text / commands and results). Also write it to `research/T22/REPORT_418.md`.
