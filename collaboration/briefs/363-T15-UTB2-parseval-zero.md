# Lane 363-T15-UTB2-parseval-zero — T15 U-TB2: the Parseval-at-0 norm bridge `periodicSobolevENorm 0 z = eLpNorm (torusLift z) 2 periodicTorusMeasure`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/363-T15-UTB2-parseval-zero` (git branch `erenup/363-T15-UTB2-parseval-zero`, based on `origin/erenup/integration-section3`).
Read `CLAUDE.md`, **`research/T15/T15_SPLIT.md` §0 and unit U-TB2**, `Section3/T10/PeriodicData.lean` (`periodicSobolevENorm :119`, `torusLift`, `IsPeriodicDatum`),
`Section3/T10/Parseval.lean` (`parseval_forward :116` — `‖A‖ₑ = eLpNorm (torusLift z) 2 periodicTorusMeasure` for the datum `A`; check its exact hypotheses incl. lead amendment 1's
`MemLp 2` / Haar integrability), `Section3/T10/DatumBasics.lean` (`datum_unique`, existence of the order-0 datum for smooth periodic fields), `Section3/T13/LocalizationKernel.lean`
(lane 353 used `periodicSobolevENorm 0` as the `L²` term — this bridge is what lane 359 needs), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No placeholders, no aliases, no named inputs, no goal repackaging.** A `def X : Prop := <goal>` or a hypothesis equal to the target is a stub and will be discarded without review;
  an honest partial with the exact residual statement and error text is fine.
- Before claiming a lemma is "not in the tree", `grep -rn` `Section3/T10`, `Section3/T13`, `Section4/I03`, `verification/Contracts/V1/Scaling.lean`, `verification/Bindings/Scaling.lean`.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal
`theorem periodicSobolevENorm_zero_eq (z : SpatialField) (hz : SmoothPeriodicT z) : periodicSobolevENorm 0 z = eLpNorm (torusLift z) 2 periodicTorusMeasure`
(exact T10 spellings; if the natural hypothesis is weaker — e.g. `IsPeriodicSpatial z ∧ MemLp (torusLift z) 2 periodicTorusMeasure` — prove the stronger, more general version and derive
the smooth one). Route: `periodicSobolevENorm 0 z` is the infimum of `‖A‖ₑ` over order-0 data `A` (`PeriodicData.lean:119`); for smooth periodic `z` the datum exists and is unique
(`DatumBasics`), and `parseval_forward` identifies `‖A‖ₑ` with the physical `L²` norm; conclude by `iInf` over a singleton-like subtype (`datum_unique`). Also the vector/scalar companions
if `periodicSobolevENorm` has both, and the lemma `periodicSobolevENorm 0 z ≠ ⊤` for smooth periodic `z`.

## Deliverables
1. `formalization/NSFormalization/Section3/T15/ParsevalZero.lean` (namespace `NSFormalization.Section3.T15`); 2. probe `research/T15/probes/parseval_zero_closes.lean` (non-vacuity: a
nonzero smooth periodic mode with both sides computed or at least the identity instantiated); 3. `research/T15/ATTEMPTS_UTB2.md`, `research/T15/axioms_utb2.lean`, status in
`research/T15/T15_SPLIT.md` U-TB2, report `research/T15/REPORT_363.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T15.ParsevalZero` (0 errors), `lake env lean` on module / probe / axioms file; `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/T15/REPORT_363.md`.
