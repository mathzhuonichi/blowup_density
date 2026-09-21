# Lane 190-A01-b1-r4-joint-smooth — B1 rung R4: a jointly smooth space-time representative of the cylinder solution (supply `hc3`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/190-A01-b1-r4-joint-smooth` (git branch `erenup/190-A01-b1-r4-joint-smooth`,
based on `origin/erenup/integration`, which now contains lane 178's `Section4/A01/DatumPathSmooth.lean`
(`datumPath_contDiffOn_all_orders`: `∀ j m, ∃ G : ℝ → RealVectorSobolev m, ContDiffOn ℝ j G (Icc 0 S) ∧ ∀ t : Icc 0 S, IsSobolevDatum m (⇑(U t)) (G t.1)`
under `hall`), lanes 186/188 (`CommonHorizon.lean`, `MildUniqueness.lean`: `compatible_carriers_hall'` supplies `hall`), and lane 180's
target shape (branch `erenup/180-A01-b2-assembly`, being re-cut to horizon `T := S`: the consumer needs
`hc3 : ContDiffOn ℝ ∞ velocity (Ico (0:ℝ) S ×ˢ univ)` for a field `velocity : SpaceTimeField` with the slice identity
`∀ t : Icc 0 S, (fun x => velocity (↑t, x)) =ᵐ[volume] ⇑(U t)`). Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P8,
`research/A01/B1_LADDER.md` (R4 row and §R3/R4), `research/A01/REPORT_178.md`, `Section4/D01/DatumToJets.lean`
(`exists_smoothL2Field_of_memHInfty`: a single slice with data at every order has a smooth `L²` representative; `jetOfDatum`,
`jetOfDatum_continuous` — jets are continuous-linear in the datum), `Section4/D01/SmoothDatum.lean`, `Section4/A03/SmoothJets.lean`,
`Section4/B01/*.lean` (separated space/time embeddings, if relevant), `Section4/A01/SliceWiring.lean:velocitySliceSmoothL2` (157),
and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented.
  No edits to existing modules; new files only.
- Before claiming a lemma is "not in the tree", `grep -rn` all of `Section4/{A01,A03,B01,B02,D01}`, `Source/`, `Paper1/`, the vendor
  `Euler/` directory. Before citing a paper line, `sed -n` it (`appendix-a-local-theory.tex:66-80`). Every declaration must print exactly
  `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example` (`U := 0`).
- **Satisfiability rule (new, mandatory):** every named input you introduce must be a restriction of a standard property that a nonzero
  solution has; write one sentence per input saying why (the clamped-carrier mistake of lane 180 must not recur).

## Goal
From the all-order, all-time-derivative datum paths (178's output shape — take it as the named input
`hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m:ℝ), ContDiffOn ℝ j G (Icc (0:ℝ) S) ∧ ∀ t : Icc (0:ℝ) S, IsSobolevDatum (m:ℝ) (⇑(U t)) (G t.1)`)
construct **one** field `u : SpaceTimeField` with
1. `∀ t : Icc 0 S, (fun x => u (↑t, x)) =ᵐ[volume] ⇑(U t)` (slice identity), and
2. `ContDiffOn ℝ ∞ u (Ico (0:ℝ) S ×ˢ (univ : Set Space))` (joint smoothness on the open slab; if the proof gives it on `Icc 0 S ×ˢ univ`, state
   that stronger version too).
Route (paper: the representative is `u(t,x) := ` the pointwise evaluation of the datum's smooth representative; Sobolev embedding
`H^m ⊂ C^k` for `m > k + 3/2`): pick a canonical representative per slice via the jets — e.g. define `u (t,x)` through the order-`m`
datum path's continuous representative (`jetOfDatum`/the tree's `SmoothL2Field` construction, `exists_smoothL2Field_of_memHInfty`
gives existence per slice; you need a **uniform, canonical** choice across `t` so that time-regularity transfers: prefer an explicit
evaluation map `RealVectorSobolev m → (Space → ℝ³)` that is continuous-linear for `m` large (`Section4/D01/…` bounded-representative /
`A03/BoundedRepresentative.lean` — grep `BoundedRepresentative`, `evalCLM`, `continuous_eval`), so `u (t,x) = eval_x (G_m t)` and then
`ContDiffOn` in `(t,x)` follows from `ContDiffOn ℝ j G_m` in `t` and the spatial jets' control, order by order (`contDiffOn_of_all_orders`,
`ContDiffOn.prod`, `contDiff_iff_forall_nat`). Handle the compatibility of the choices across orders `m` (the order-`m` and order-`m'`
representatives agree a.e. hence everywhere by continuity). If one uniform-evaluation lemma is genuinely missing, prove it in your module.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/JointRepresentative.lean` (namespace `NSFormalization.Section4.A01`):
   the evaluation/representative construction, `jointRepresentative`, `jointRepresentative_slice`, `jointRepresentative_contDiffOn`,
   and the packaged `theorem exists_joint_smooth_representative (hpaths) : ∃ u : SpaceTimeField, (slice identity) ∧ ContDiffOn ℝ ∞ u (Ico 0 S ×ˢ univ)`;
   plus the composition with 178: `exists_joint_smooth_representative_of_hall (hall) : …` via `datumPath_contDiffOn_all_orders`.
2. Records `research/A01/ATTEMPTS_B1_R4.md`; update `research/A01/B1_LADDER.md` row R4; conformance `research/A01/axioms_b1_r4.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.JointRepresentative` (silent), `lake env lean` on the
module (0 output), the axioms file, `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements and named inputs / files / gaps with error text / commands).
Also write it to `research/A01/REPORT_190.md`.
