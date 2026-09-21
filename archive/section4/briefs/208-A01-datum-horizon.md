# Lane 208-A01-datum-horizon — toward the A01 contract: the solution with the datum `a` itself, a total `horizon` function, and the `solution` field of `LocalTheoryAPI`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/208-A01-datum-horizon` (git branch `erenup/208-A01-datum-horizon`, based on `origin/erenup/integration`, which now contains
lane 207's `Section4/A01/TameAssembly.lean` (`hb_of_base''`: the all-order a-priori bound family with no analytic input; `constructor_of_base`; the milestone probe
`research/A01/probes/a01_constructor_unconditional.lean`: `∃ S > 0, ∃ velocity, ∃ w : ClassicalSolutionR ν (velocity(0,·)) f S, w.velocity = velocity` from `hf : MemForceR f`,
`ha`, positivity), `CylinderWiring.lean` (lane 192: `U 0 = a.toLp`), `JointRepresentative.lean` (190: slice identity `∀ t : Icc 0 S, velocity(t,·) =ᵐ ⇑(U t)`), `ConstructorAssembly.lean`
(180), `PressureRegularity.lean` (189), `ForceBridge.lean` (167: `initialClassR_of_smoothL2`)). Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P7, **`research/A01/Spec.lean`**
(the target contract `LocalTheoryAPI`: `:270-300` the fields `horizon : ℝ → SpatialField → SpaceTimeField → ℝ` and `solution : ∀ ν a f, 0 < ν → a ∈ initialClassR → MemForceR f →
ClassicalSolutionR ν a f (horizon ν a f)`), `research/A01/REVIEW_207-A01-tame-assembly.md` §5 (the registration list), `research/A01/REPORT_207.md`, `verification/Contracts/V1/Data.lean`
(`initialClassR`, `ClassicalSolutionR`), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]` (`Classical.choice` is allowed: the total `horizon` may use `Classical.choose`).
- **Satisfiability rule:** no named analytic input is expected in this lane (pure wiring); if one appears, isolate it exactly and say why.

## Goal
1. **Datum identification:** from the milestone's `velocity` with `hslice` at `t = 0` and lane 192's `U 0 = a.toLp` derive `velocity (0, x) = a.field x` for every `x` (both sides
   continuous — `a : SmoothL2Field Space` is smooth, `velocity` is slab-smooth — and a.e. equal ⇒ equal), then transport the `ClassicalSolutionR ν (velocity(0,·)) f S` to
   `ClassicalSolutionR ν a.field f S` (the structure's `initial` field is about `velocity (0,·) = a`; the other fields are unchanged — write the transport lemma).
2. **Initial class:** state the constructor for `a ∈ initialClassR` (the contract's hypothesis, `Contracts/V1/Data.lean`): bridge `initialClassR` ↔ (`SmoothL2Field` + solenoidal `ha`)
   in the direction needed (lane 167's `initialClassR_of_smoothL2` is the other direction — prove the converse: every `a ∈ initialClassR` is (a.e./pointwise) a smooth `L²`
   solenoidal field, i.e. produce the `SmoothL2Field` and `ha` from `a ∈ initialClassR`, or explain exactly why not and what `initialClassR` contains).
3. **Total horizon and the `solution` field:** define `def localHorizon (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) : ℝ` (the existential positive horizon via `Classical.choose`
   under the hypotheses, `1` otherwise — or `Classical.epsilon`), prove `localHorizon_pos` under the hypotheses, and `theorem localSolution : ∀ ν a f, 0 < ν → a ∈ initialClassR → MemForceR f →
   ClassicalSolutionR ν a f (localHorizon ν a f)` — exactly the `solution` field's type. Keep the chosen solution accessible (`def localSolution` as data), because lanes 209/210 need
   *the same* solution and horizon.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/LocalSolution.lean` (namespace `NSFormalization.Section4.A01`).
2. Records `research/A01/ATTEMPTS_LOCAL_SOLUTION.md`, `research/A01/A3_SPLIT.md` new section "Contract registration" with rows 208/209/210/211, conformance `research/A01/axioms_local_solution.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.LocalSolution` (silent), `lake env lean` on the module (0 output), the axioms file, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/A01/REPORT_208.md`.
