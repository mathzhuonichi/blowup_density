# Lane 180-A01-b2-assembly — A01 unit B2: assemble the conditional classical constructor from the landed pieces

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working
directory `/data_8T/ping/blowup_density/.claude/worktrees/180-A01-b2-assembly` (git branch
`erenup/180-A01-b2-assembly`, based on `origin/erenup/integration`). Read `CLAUDE.md`, `collaboration/HANDOFF.md`
§0 and §2 P7/P8, `research/A01/REVIEW_SLICE_WIRING.md` §3(b) and `research/A01/REVIEW_CONSTRUCTOR_SPLIT.md` §3
(the target `CarrierConstructorFull`, verified to close the consumer loop), `research/A01/B1_LADDER.md`, and the
top 40 lines of `logs/LESSONS.md` first.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`,
  commented. No edits to existing modules; new files only. Named hypotheses are allowed **only** for the rungs
  listed below as open, each stated exactly and documented as such (no placeholder `Prop` fields).
- Before claiming a lemma is "not in the tree", `grep -rn` all of `Section4/{A01,A02,D01,C01}`. Before citing a
  paper line, `sed -n` it. Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`;
  include a non-vacuity `example` (zero pair ⇒ the zero solution `A04.zeroSol`).

## The pieces on `origin/erenup/integration` (all merged; use them, do not re-prove)
- Cylinder pair with all seven clauses: `Section4/A01/Horizon.lean:137` `localTheory_on_prescribed_horizon`, and
  the invariant-bound version `Section4/A01/AprioriInvariance.lean` `localTheory_on_prescribed_horizon_of_boundInv` (173).
- Data of the velocity slices: per-time all-order data (`ConstructorPieces.exists_isSobolevDatum_slice_of_cylinder`
  and lane 153's `L2Descent.word_descent_ae_top`), **continuous** selection at every order `m ≤ q+1`
  (`DatumPathContinuous.exists_continuous_datumPath`, 161), **time-differentiable** paths with the projected residual
  as derivative for `m ≤ q−1` (`DatumPathDeriv.exists_differentiable_datumPath`, 169).
- Smooth representative of each slice: `Section4/D01/DatumToJets.lean` `exists_smoothL2Field_of_memHInfty`;
  `SliceWiring.velocitySliceSmoothL2` (157).
- Divergence: `ConstructorDivergence.divergence_ae_of_cylinder` and `divergence_of_cylinder_pointwise_of_contDiff` (162).
- Pressure: `ConstructorPressure.pressureOfVelocity`, `pressure_gradient_memLp`, `pressure_smooth_of_velocity_smooth`,
  `momentum_of_projected` (168; open input: `HasSymmetricJacobian` of the Leray complement — check whether
  `Section4/D01/OrderZeroCurl.lean` / `LerayDatum.lean` gives curl-freeness of `lerayComplement` at datum level).
- Force/datum: `ForceBridge.forcePath_of_memForceR`, `initialClassR_of_smoothL2` (167).
- Two-sided norm comparisons: `OrderTwoCap`, `AprioriRows`, `SliceWiring.apriori_rows_of_hslice`.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/ConstructorAssembly.lean` (namespace
   `NSFormalization.Section4.A01`):
   - `def constructedVelocity` — a **single** pointwise field `velocity : SpaceTimeField` whose slice at each
     `t ∈ Icc 0 S` is a smooth representative of `⇑(U t)` (choose it so that the slice identity `hslice :
     ∀ t, (fun x => velocity (↑t, x)) =ᵐ ⇑(U t)` holds by construction), extended beyond `S` (e.g. constant);
     horizon `T := S` with the solution class on `Ico 0 T` (check whether `S < T` is needed as in
     `REVIEW_SLICE_WIRING.md` §3(b) and pick `T := S + 1` with a continuation only if the class demands it — say
     which and why).
   - `theorem carrierConstructor_of_localTheory` : from the seven-clause output of
     `localTheory_on_prescribed_horizon` (or `_of_boundInv`) plus **named hypotheses only for the open rungs**:
     `hc3 : ContDiffOn ℝ ∞ velocity (Ico 0 T ×ˢ univ)` (joint smoothness, B1 R3/R4) and, if not discharged from the
     tree, `hcurl` (symmetric Jacobian of the pressure-gradient field) — produce
     `w : ClassicalSolutionR ν a' f T` with `a' := velocity (0,·)`, `f` the paper's force, and `hslice`. Every
     other field (`horizon_pos`, `initial`, `divergence`, `momentum`, `sobolev` — the **continuous** datum path from
     161 with the existential the structure wants, `pressure_gradient`, `pressure_smooth`) must be discharged from
     the pieces above, not assumed.
   - `theorem carrierConstructorFull_of_hc3` : the review-157 target shape (`CarrierConstructorFull`, copy its
     `def` from `research/A01/probes/rev158_ctor_restated.lean` or `REVIEW_CONSTRUCTOR_SPLIT.md` §3) proved under
     the same named hypotheses, so the consumer loop `rows_from_constructor` (`rev157_constructor_loop.lean`) closes
     end-to-end conditional on `hc3` (write a probe that closes it).
2. Records `research/A01/ATTEMPTS_B2_ASSEMBLY.md` (which fields closed unconditionally, which needed which
   hypothesis and why, the exact residual statements), update `research/A01/CONSTRUCTOR_SPLIT.md` (or append a
   lane-180 note to `A3_SPLIT.md` if that file is absent), conformance `research/A01/axioms_b2_assembly.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.ConstructorAssembly` (silent),
`lake env lean` on the module (0 output), the axioms file, the consumer-loop probe, `make check` from the
worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements and the exact named hypotheses /
files / gaps with error text / commands). Also write it to `research/A01/REPORT_180.md`.
