# Lane 370-T17-U3-correction-profile — T17 U3: the fixed-cylinder correction profile fields of `CorrectionAPI` (`correction_profile_smooth/_support/Const/_nonneg/_uniform/_identity`) by Euclidean reuse

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/370-T17-U3-correction-profile` (git branch `erenup/370-T17-U3-correction-profile`, based on `origin/erenup/integration-section3`).
Read `CLAUDE.md`, **`research/T17/T17_SPLIT.md` §0 and unit U3**, **`research/T17/Spec.lean:752-830`** (the `CorrectionAPI` structure and the six target fields, verbatim, with the definitions
they use: `rescaledCorrectionProfile`, `fixedProfileCylinder`, `correctionChartPoint`, `rescaledPotential`, …), `research/T17/RECONCILIATION.md` §3–§4 (esp. §4 ① on the potential display),
the T16 canonical modules `Section3/T16/{LocalPotential,BallPotential,LatticeLift}.lean` (`CutoffData`, `LocalPotentialAPI.potential_formula`, `timePotential`, `eta_support`/`theta_support`),
the Euclidean profile modules `formalization/NSFormalization/Paper1/CorrectionProfile.lean` (`profile_smooth :49`, `profile_support :187`, `profile_uniform_global_derivative_bound :201`,
`physicalCorrection_eq_profile :223`; grep the exact names) and `Section4/I02/Reference.lean` (`jointPotential`/`cutPotential`, `centeredPotential_eq_integral`), and the top 40 lines
of `logs/LESSONS.md` (**name every instance explicitly**).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No placeholders, no aliases, no named inputs, no goal repackaging.** A `def X : Prop := <goal>` or a hypothesis equal to the target is a stub and will be discarded without review;
  an honest partial with the exact residual statement and error text is fine.
- Before claiming a lemma is "not in the tree", `grep -rn` `Section3/T16`, `Section3/T10`, `Section4/I02`, `Paper1/Correction*.lean`. Every declaration must print exactly
  `[propext, Classical.choice, Quot.sound]`.

## Goal
New module `formalization/NSFormalization/Section3/T17/CorrectionProfile.lean` (namespace `NSFormalization.Section3.T17`): restate over the canonical T10/T15/T16 vocabulary the T17 Spec
definitions these fields use (copy verbatim from `research/T17/Spec.lean`, only the namespace changes; import T16's canonical `CutoffData` — do not copy it), prove the `def` bridge
`rescaledCorrectionProfile v place ε D z = CorrectionProfile.profile v place.x₀ place.T D.θ D.η (ε, z)` (unfold `rescaledPotential` — the literal display `∫₀¹ ρ v(…) × z` — against
`jointPotential`/`cutPotential`, via `LocalPotentialAPI.potential_formula` / `centeredPotential_eq_integral`), then the six fields **as theorems with exactly the Spec's statements**:
`correction_profile_smooth`, `correction_profile_support` (`fixedProfileCylinder D = Icc (−2) 2 ×ˢ closedBall 0 D.θRadius ⊇ tsupport (profile)` by `eta_support`/`theta_support`),
`correctionProfileConst` (a `def`, the uniform derivative constant), `correctionProfileConst_nonneg`, `correction_profile_uniform` (from `profile_uniform_global_derivative_bound`),
`correction_profile_identity` (from `physicalCorrection_eq_profile` via `inverseScale`, matching `correctionChartPoint`). If a T15 `PlacementData` field is needed, take `place : PlacementData P`
as a parameter in the canonical spelling of `research/T15/Spec.lean` (no T15 canonical module exists yet except lane 362's `Bridges.lean`, in progress — copy `PlacementData` verbatim into a
delimited block of your module if 362 has not landed; say which).

## Deliverables
1. `Section3/T17/CorrectionProfile.lean`; 2. probe `research/T17/probes/correction_profile_closes.lean` restating the six Spec fields token-for-token and closing each by `exact`, plus a
non-vacuity instance (a nonzero smooth divergence-free `v`, e.g. a constant field, with T16's cutoff data from `exists_originCutoff`/`exists_timeCutoff`); 3. `research/T17/ATTEMPTS_U3.md`,
`research/T17/axioms_u3.lean`, status in `research/T17/T17_SPLIT.md` U3, report `research/T17/REPORT_370.md` (if a guard blocks the write, put the full report in your final message).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T17.CorrectionProfile` (0 errors), `lake env lean` on module / probe / axioms file; `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with exact error text / commands and results).
