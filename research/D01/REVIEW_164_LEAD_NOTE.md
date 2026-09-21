# Lead note on REVIEW_164 (2026-09-15)

The codex review of lane 164 returned **REJECT solely because `Contracts/V2/HomogeneousNorm.lean` is absent**,
judging the lane against the *original* brief (which suggested a V2 file). That brief was superseded by the
lead's fix brief (`collaboration/briefs/fix_164-D01-g1-homogeneous-norm.md`): a **new** component registered at
`version: 1` lives under `Contracts/V1/` (the freeze in `CLAUDE.md` applies to *existing* V1 files; cf.
`Contracts/V1/GradientL6.lean`, lane 019), and the registrar's version-path rule requires it. The review's
own findings — statements, axioms (9/9 standard), gates, hygiene, non-vacuity, mutation — all PASS on the
V1 layout. Decision: merge with the V1 layout; the review's "restore V2" fix is not applied.
Process fix: `scripts/codex_review.sh` now appends any later fix brief to the reviewer's prompt.
