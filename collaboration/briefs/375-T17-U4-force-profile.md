# Lane 375-T17-U4-force-profile — T17 U4: the fixed-cylinder force profile fields of `CorrectionAPI` (`force_profile_smooth/_support/Const/_nonneg/_uniform/_identity`) by Euclidean reuse, on top of lane 370

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/375-T17-U4-force-profile` (git branch `erenup/375-T17-U4-force-profile`, based on lane 370's branch merged with
`origin/erenup/integration-section3`: it contains `Section3/T17/CorrectionProfile.lean` (lane 370: `rescaledCorrectionProfile_eq_profile` — the potential/profile def bridge,
`correction_profile_*`, `correctionProfileConst`, `correction_eq_physicalCorrection`, `profile_eq_curl_slice`) and the T16 modules incl. `Section3/T16/Assembly.lean` (#330,
`localPotential`, `localPotentialData`)). Read `CLAUDE.md`, **`research/T17/T17_SPLIT.md` §0 and unit U4**, `research/T17/REPORT_370.md` / `ATTEMPTS_U3.md` (G1: the profile lemmas need
global `ContDiff ℝ ∞ v` — take the same `hv` premise; G3: bare `(x₀, T)` instead of `place`), **`research/T17/Spec.lean:805-837`** (the six target fields verbatim, with
`rescaledForceProfile`, `correctionForce` and the `ε⁻²` rescaling under `correctionChartPoint`), `research/T17/RECONCILIATION.md` §4 ②, the Euclidean modules
`formalization/NSFormalization/Paper1/CorrectionForceProfile.lean` (`forceProfile`, `forceProfile_smooth :57`, `forceProfile_support :75`, `forceProfile_uniform_derivative_bound :204`,
`physicalForce_eq_profile :185` — grep exact names) and `Source/`'s `correctionForce`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging.** Honest partial with the exact residual statement and error text beats a stub.
- Before claiming a lemma is "not in the tree", `grep -rn` `Section3/T17`, `Section3/T16`, `Paper1/Correction*.lean`, `Source/`. Every declaration must print exactly
  `[propext, Classical.choice, Quot.sound]`.

## Goal
New module `formalization/NSFormalization/Section3/T17/ForceProfile.lean` (namespace `NSFormalization.Section3.T17`): restate the Spec's `rescaledForceProfile` and the T17
`correctionForce` verbatim (if lane 373's `Transport.lean` has landed on your base with `correctionForce`, import it instead of restating; say which), prove the def bridge
`rescaledForceProfile_eq_forceProfile : rescaledForceProfile ν v x₀ T ε D z = CorrectionForceProfile.forceProfile ν v x₀ T D.θ D.η (ε, z)` (shares lane 370's potential bridge), then the
six fields **as theorems with exactly the Spec's statements** (`place.x₀ ↦ x₀`, `place.T ↦ T`, the `hv : ContDiff ℝ ∞ v` premise as in lane 370): `force_profile_smooth`,
`force_profile_support`, `forceProfileConst` (`def`), `forceProfileConst_nonneg`, `force_profile_uniform` (from `forceProfile_uniform_derivative_bound`), `force_profile_identity`
(from `physicalForce_eq_profile`: `Source.correctionForce … p = (ε²)⁻¹ • forceProfile ν … (ε, inverseScale ε (p − (T, x₀)))`, i.e. the affine `ε⁻²` rescaling under `correctionChartPoint`,
combined with `correction_eq_physicalCorrection` (370) and, for the lift, lane 373's `force_eq` if available — otherwise state the identity for the chart force `Source.correctionForce ν v (physicalCorrection …)`
and leave the lifted form to U12 with the exact residual statement).

## Deliverables
1. `Section3/T17/ForceProfile.lean`; 2. probe `research/T17/probes/force_profile_closes.lean` (restate the six Spec fields token-for-token and close each by `exact`; non-vacuity as in 370's
probe with a nonzero constant reference); 3. `research/T17/ATTEMPTS_U4.md`, `research/T17/axioms_u4.lean`, status in `research/T17/T17_SPLIT.md` U4, report `research/T17/REPORT_375.md`
(if a guard blocks the write, put the full report in your final message).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T17.ForceProfile` (0 errors), `lake env lean` on module / probe / axioms file; `make check`.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with exact error text / commands and results).
