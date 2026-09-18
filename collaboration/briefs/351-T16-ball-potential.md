# Lane 351-T16-ball-potential — T16 gap 1: the radial vector potential on the chart ball (`potential_smooth`, `potential_curl` for a reference that is only smooth/divergence-free on `Ioo 0 (T+δ) ×ˢ ball x₀ r`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/351-T16-ball-potential` (git branch `erenup/351-T16-ball-potential`, based on lane 347's
branch: it contains `formalization/NSFormalization/Section3/T16/LocalPotential.lean` (the canonical T16 module: `CutoffData`,
`LocalPotentialAPI`, `localPotentialStatement`, `exists_originCutoff`, `exists_timeCutoff`, `exists_threshold`, `localPotential_zero`) and
`research/T16/{ATTEMPTS.md,SPEC_ISSUES.md,REPORT_347.md,probes/api_on_canonical.lean}`). Read `CLAUDE.md` (hard rules),
**`research/T16/ATTEMPTS.md` §"Gap 1"** (the two residual statements and the proof route — this lane is exactly that gap),
`research/T16/Spec.lean` fields `potential_smooth`/`potential_formula`/`potential_curl`, the I02 sources
`formalization/NSFormalization/Section4/I02/Reference.lean` (`exists_local_truncation`, `timePotential_contDiffOn`,
`spatialCurl_timePotential_on`, `timePotential_congr_slice`) and the modules they import for `RadialPotential.timePotential` /
`centeredPotential_eq_integral` / `SpatialCurl.curl` (grep `Paper1/` and `Source/`), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented.
  No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging** (hard analytic unit). Honest partial with exact residual statements and error
  text beats a stub; a `def X : Prop := <goal>` or a hypothesis equal to the target will be discarded without review.
- Before claiming a lemma is "not in the tree", `grep -rn` `Section4/I02`, `Paper1/`, `Source/`, `Section3/T16`. Every declaration must
  print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal — the two residual lemmas of `ATTEMPTS.md` §Gap 1, verbatim
```
theorem timePotential_contDiffOn_ball {v : VelocityField} {x₀ : Space} {r : ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hv : ContDiffOn ℝ ∞ v (I ×ˢ Metric.ball x₀ r)) :
    ContDiffOn ℝ ∞ (RadialPotential.timePotential v x₀) (I ×ˢ Metric.ball x₀ r)

theorem spatialCurl_timePotential_on_ball {v : VelocityField} {x₀ : Space} {r : ℝ} {I : Set ℝ}
    (hv : ContDiffOn ℝ ∞ v (I ×ˢ Metric.ball x₀ r))
    (hdiv : ∀ t ∈ I, ∀ x ∈ Metric.ball x₀ r, spatialDivergence v t x = 0)
    {t : ℝ} (ht : t ∈ I) {x : Space} (hx : x ∈ Metric.ball x₀ r) :
    SpatialCurl.curl (fun y => RadialPotential.timePotential v x₀ (t, y)) x = v (t, x)
```
(if `I` must be open in the second one too, add `hI` and say so). Route: for `x ∈ ball x₀ r` the radial segment
`{x₀ + ρ • (x − x₀) | ρ ∈ [0,1]}` is compact inside the open ball; take a smooth bump `χ` (`ContDiffBump`/`exists_smooth_tsupport_subset`)
equal to `1` on a neighbourhood of it with `tsupport χ ⊆ ball x₀ r`, set `V (t,y) := χ y • v (t,y)` extended by `0` (globally smooth on
`I ×ˢ univ` — note `χ` kills the non-smooth region; for the time direction use I02's time truncation `exists_local_truncation` if `I ≠ univ`),
apply the global I02 lemmas to `V`, and transfer with `timePotential_congr_slice` (the potential at `(t,x)` only reads `v` on the segment).
For the curl, `V` is divergence-free on a neighbourhood of the segment? — **no**: `div (χ v) = ∇χ·v + χ div v`, which is nonzero on the
annulus where `χ` varies. So either (a) choose the bump `= 1` on a slightly larger ball `ball x₀ r'` with `‖x − x₀‖ < r' < r` and note the
segment lies in `ball x₀ r'` where `V = v` is divergence-free — then check whether `spatialCurl_timePotential_on` needs global divergence-freeness
or only on the segment/ball (read its proof; if it needs `univ`, prove the pointwise identity by re-running its derivative computation on the
ball where `V = v`, using `timePotential_congr_slice` and the fact that the curl at `x` only involves derivatives of the potential at `x`, i.e.
of `v` on a neighbourhood of the segment); or (b) if the I02 proof of the curl identity is genuinely global, re-derive it locally. Report which.

Then the T16 fields: `theorem exists_potential_on_ball … : ∃ A : SpaceTimeField, ContDiffOn ℝ ∞ A (Ioo 0 (T+δ) ×ˢ ball x₀ r) ∧
(∀ t x, A (t,x) = <potential_formula's right side>) ∧ (∀ t ∈ Ioo 0 (T+δ), ∀ x ∈ ball x₀ r, curl (A t) x = v (t,x))` in exactly the
spellings of `LocalPotentialAPI.potential_smooth/potential_formula/potential_curl` (`Section3/T16/LocalPotential.lean`) so lane 353 (assembly)
can fill those three fields by `exact`.

## Deliverables
1. New module `formalization/NSFormalization/Section3/T16/BallPotential.lean` (namespace `NSFormalization.Section3.T16`) with the lemmas above.
2. Probe `research/T16/probes/ball_potential_closes.lean`: `example`s instantiating the three T16 fields from `exists_potential_on_ball`
   against the canonical `LocalPotentialAPI` field types (copy the field statements verbatim), plus a non-vacuity instance (a nonzero smooth
   divergence-free `v`, e.g. a constant field, on some ball).
3. Records: `research/T16/ATTEMPTS_BALL_POTENTIAL.md`, conformance `research/T16/axioms_ball_potential.lean`, status line in
   `research/T16/COMPARISON.md`, report `research/T16/REPORT_351.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T16.BallPotential` (0 errors), `lake env lean` on the module,
probe and axioms file; `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with exact error text / commands and results).
Also write it to `research/T16/REPORT_351.md`.
