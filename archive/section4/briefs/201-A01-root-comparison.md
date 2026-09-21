# Lane 201-A01-root-comparison — `CylinderRootComparison`: the limiting energy root of the mild competitor is bounded by the comparison ODE solution (given `ForcingFamilyBound`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/201-A01-root-comparison` (git branch `erenup/201-A01-root-comparison`, based on branch `erenup/199-A01-envelope`
= `origin/erenup/integration` + lane 199's `Section4/A01/MildEnergyEnvelope.lean` (the signed regularized energy identity retaining dissipation — the review
calls it "M:72" — the ODE envelope `energyComparison`, `cylinderEnvelopeDriver`, `energyRootPath`, `def CylinderRootComparison`, and the conditional chain
`finiteMildEnergy_of_rootComparison`-style theorems at "M:214/:243/:253")). On integration: lane 198's `MildEnergyPremises.lean` (`def ForcingFamilyBound`,
`mild_energy_estimate_of_cylinder`, the maximal-approximation limit and all vendor premises). Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P7,
`research/A01/REPORT_199.md`, `research/A01/REVIEW_199-A01-envelope.md` §"Lanes 200/201" (your route) and §2 (what is proved), `research/A01/REPORT_198.md`,
and the top 40 lines of `logs/LESSONS.md`. Lane 200 (running concurrently on the same base) proves `ForcingFamilyBound` — **take it as a hypothesis**
(`hFB : ForcingFamilyBound hq hν a ha F hF E A`, lane 198's exact `def`) and do not prove it here.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules;
  new files only. Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` on zero data.
- **Satisfiability rule:** if one genuinely missing analytic fact remains, isolate it as ONE named hypothesis with the exact statement; never route through
  the all-order constructor; never use `ClassicalSolutionR`-level lemmas on a mild path.

## Goal
`theorem cylinderRootComparison_of_forcingBound (hFB : ForcingFamilyBound …) : CylinderRootComparison hq hν a F hF E A` — token-for-token lane 199's `def`
(`∀ T hT hTS u, mild ⇒ ∀ t, energyRootPath u t ≤ energyComparison (fun s => (cylinderEnvelopeDriver hq hT A u s)^2/(4ν)) (E‖F‖_{q+1}) (E‖u₀‖) t`).
Route (reviewer 199): (1) from the signed regularized identity (lane 199) and the forcing bound `hFB`, derive the signed differential inequality for the
regularized root `r_ε` (Young absorption of the tame term into `ν g²` — lane 196's algebra), then pass to the **signed integrated limit** along lane 198's
maximal-approximation family (the same word family, constants and maximal limit); (2) scalar regularized-root comparison: a nonnegative continuous `r` with
`r(0) ≤ y₀` and the integrated inequality `r(t) ≤ r(0) + ∫₀ᵗ (α r + b)` satisfies `r ≤ y` for the comparison solution `y' = αy + b`, `y(0) = y₀`
(Grönwall: Mathlib `gronwallBound`/`le_gronwallBound_of_liminf_deriv_right_le` or an explicit integrating-factor argument), including the zero-root limit
and the endpoints `t = 0`, `t = T`; (3) supply `CylinderRootComparison` and compose with lane 199's chain to export
`finiteMildEnergy_of_forcingBound (hFB) : FiniteMildEnergy hq hν a ha F hF E A` (and, once lane 200 lands, the unconditional version is one application).
Also add the scalar ODE uniqueness lemma if lane 199's fix has not already (check the branch).

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/RootComparison.lean` (namespace `NSFormalization.Section4.A01`).
2. Records `research/A01/ATTEMPTS_ROOT_COMPARISON.md` (negative examples), update `research/A01/A3_SPLIT.md` A3-M2 sub-row "envelope", conformance
   `research/A01/axioms_root_comparison.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.RootComparison` (silent), `lake env lean` on the module (0 output), the axioms
file, `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands). Also write it to `research/A01/REPORT_201.md`.
