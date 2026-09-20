# Lane 209-A01-manuscript-regularity — `ManuscriptLocalRegularity` for the constructed local solution (the `regularity` field of `LocalTheoryAPI`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/209-A01-manuscript-regularity` (git branch `erenup/209-A01-manuscript-regularity`, based on `origin/erenup/integration`, which contains
lane 207's `TameAssembly.lean` and the whole constructor pipeline: `CylinderWiring.lean` (192: all-`j` all-`m` datum paths of the carrier `U`), `JointRepresentative.lean` (190:
`velocity`, `hslice`, `hc3`), `PressureRegularity.lean` (189: `pressureSupply_of_pieces` — the gradient field `G` with `G = residual − ∂ₜvelocity` on `Ioo`, slab smooth, per-time `L²`
and symmetric Jacobian; built as the joint representative of the Leray-complement path of the residual, `ComplementPath.lean` 194), `ConstructorAssembly.lean` (180:
`pressure := RadialPotential.pressurePotential G`), lane 208 (`LocalSolution.lean`, running concurrently: the chosen solution `localSolution ν a f …` on `localHorizon` —
**take its exported solution as the object; if 208 has not landed when you start, state your theorems for an arbitrary solution produced by `carrierConstructor_of_localTheory` with
the pipeline's inputs, so 208 can instantiate them**). Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P7, **`research/A01/Spec.lean:160-240`** (the target
`structure ManuscriptLocalRegularity ν a f T u` with its four fields `sobolev_smooth`, `pressure_recovery`, `projected`, `pressure_potential` — copy them token-for-token),
`research/A01/REVIEW_207-A01-tame-assembly.md` §5, `research/D01/RECONCILIATION.md` (unit L9(c): eq:Rpressure ⟺ `momentum` given `divergence` and `∇p ∈ L²`), and the top 40 lines
of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.
- **Satisfiability rule:** no new analytic input is expected (the pieces exist); if one genuinely appears, isolate it exactly.

## Goal: `theorem manuscriptLocalRegularity_of_pipeline … : ManuscriptLocalRegularity ν a f S w` for the constructed `w`, field by field
1. `sobolev_smooth : ∀ m, ∃ G, (∀ t ∈ Ico 0 T, IsSobolevDatum m (fun x => w.velocity (t,x)) (G t)) ∧ ContDiffOn ℝ ∞ G (Ico 0 T)` — from lane 192's all-`j` datum paths of `⇑(U t)`
   (`ContDiffOn ℝ j G (Icc 0 S)` for every `j` ⇒ `ContDiffOn ℝ ∞` via `contDiffOn_infty`/`contDiffOn_of_forall_nat`? check the exact Mathlib lemma for `∞ = ⊤` vs `ω`) transported to
   `w.velocity`'s slices by `hslice` (`IsSobolevDatum.congr_field`).
2. `pressure_recovery : ∀ t ∈ Ico 0 T, IsLerayComplement (fun x => f (t,x) − convectionDivergence w.velocity t x) (fun x => pressureGradient w.pressure t x)` — including `t = 0`:
   from 189/194: `pressureGradient w.pressure t = G(t,·)` (radial-gradient identity for symmetric-Jacobian smooth fields) and `G(t,·)` is the Leray complement of the residual's datum
   at every `t ∈ Icc 0 S` (194's per-time complement identity; the residual there is `νΔu + f − (u·∇)u` — check `IsLerayComplement`'s definition in `Contracts/V1/Data.lean`/D01 and
   whether the `νΔu` term must be removed: the complement of a divergence-free field's Laplacian is zero — prove that bridge, `Δ` preserves solenoidality).
3. `projected : ∀ t ∈ Ioo 0 T, ∀ x, temporalDerivative w.velocity t x − ν • spatialLaplacian w.velocity t x = (f (t,x) − convectionDivergence w.velocity t x) − pressureGradient w.pressure t x`
   — this is `ClassicalSolutionR.momentum` rearranged (`navierStokesResidual` unfolded); prove the rearrangement.
4. `pressure_potential : PressureGaugeEquivOn (Ico 0 T) (pressurePotential (fun z => pressureGradient w.pressure z.1 z.2)) w.pressure` — `w.pressure` **is** `pressurePotential G` and
   `pressureGradient w.pressure = G` on the slab, so this should be reflexive up to the definition of `PressureGaugeEquivOn` (differ by a function of time only); prove it.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/ManuscriptRegularity.lean` (namespace `NSFormalization.Section4.A01`).
2. Records `research/A01/ATTEMPTS_MANUSCRIPT_REGULARITY.md`, `A3_SPLIT.md` row 209, conformance `research/A01/axioms_manuscript_regularity.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.ManuscriptRegularity` (silent), `lake env lean` on the module (0 output), the axioms file, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/A01/REPORT_209.md`.
