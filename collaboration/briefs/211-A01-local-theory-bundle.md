# Lane 211-A01-local-theory-bundle — assemble the A01 local theory: carrier-bundled chosen solution, uniformly selected horizon, manuscript regularity, and the two horizon-uniformity variants (no contract file yet)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/211-A01-local-theory-bundle` (git branch `erenup/211-A01-local-theory-bundle`, based on branch `erenup/210-A01-horizon-uniform`
= `origin/erenup/integration` + lane 210's `Section4/A01/HorizonUniform.lean` (`exists_uniform_H7_sup_force_horizon`, `exists_uniform_H7_coefficient_horizon`, the budget monotonicity
lemmas); integration contains lane 208's `LocalSolution.lean` (`solution_of_base`, `smoothL2_of_initialClassR`, `localHorizon`, `localSolution`), lane 209's `ManuscriptRegularity.lean`
(`manuscriptLocalRegularity_of_pipeline` for any constructor output carrying `hslice`/`hpaths`), lane 207's `TameAssembly.lean` (`hb_of_base''`, `constructor_of_base`), and the
pipeline (`CylinderWiring`, `JointRepresentative`, `PressureRegularity`, `ConstructorAssembly`)). Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P7, **`research/A01/Spec.lean`**
(the target `LocalTheoryAPI` `:255-345` and `ManuscriptLocalRegularity` `:167-230`), `research/A01/REPORT_208.md`, `REPORT_209.md` (and its review note: carrier witnesses must be
preserved), `REPORT_210.md` §3 (the two obstacles and the two options), `NEXT_SESSION.md` (entry "spec 问题" 2026-09-16 0600Z: the lead's recommendation and the pending decision), and
the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing modules; new files only.
  **Do not touch `verification/Contracts`, `Bindings`, `Tests` or `contracts.json`** — the contract statement's final wording awaits the user/owner decision (rule 2, statement fidelity).
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.
- **Fidelity rule:** state the original H¹ field verbatim as a `def` and do not claim it; prove the H⁷/fixed-force variant.

## Goal — everything the V2 contract will need, in `formalization/`
1. **Carrier bundle:** `structure LocalCarrier (ν a f S)` bundling the chosen objects with their witnesses: `U`, the all-order pairs `hpairs` and paths `hpaths` (lane 192 shapes),
   `velocity`/`hslice`/`hc3` (190), `G`/`hG_int`/`hG` (189's `pressureSupply_of_pieces`), and `w : ClassicalSolutionR ν a f S` with `w.velocity = velocity` and the datum identification
   (208's `solution_of_base`). Provide `def localCarrier ν a f (hν) (ha) (hf) : LocalCarrier ν a f (localHorizon' ν a f)` where:
2. **Uniformly selected horizon:** define `localHorizon' ν a f` (total) so that it is **selected by lane 210's uniform theorem** rather than an arbitrary `Classical.choose`: for
   `MemForceR f` and `a ∈ initialClassR`, take `R := ‖a‖₇`-type norm (the order-7 cylinder datum norm of `ordinarySobolev 7 a.toLp …`) and `B :=` the time-sup of the order-6
   force path on `[0, 1]` (finite for `MemForceR` forces: `C01.forcePath` jets are continuous on the compact interval — prove it), and let `δ(ν, R, B)` be the budget of
   `exists_uniform_H7_sup_force_horizon` with `S := 1`; set `localHorizon' := δ(ν, R, B)` (or `min` with the base horizon if the constructor needs it) and rebuild the chosen solution on it
   via `constructor_of_base` (fixed `S` version, lane 207). Prove **antitonicity**: `R ≤ R' → B ≤ B' → δ(ν,R',B') ≤ δ(ν,R,B)` (from the budget lemmas; if the vendor's budget is not
   manifestly antitone, define `δ` as an infimum/explicit formula over the ball and prove the needed property).
3. **Regularity:** `manuscriptLocalRegularity_localCarrier : ManuscriptLocalRegularity ν a f (localHorizon' ν a f) (localCarrier …).w` by instantiating lane 209.
4. **Horizon uniformity, two variants:**
   - `theorem horizon_lower_bound_H7_fixedForce : ∀ ν, 0 < ν → ∀ f, MemForceR f → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∃ δ > 0, ∀ a, a ∈ initialClassR → sobolevENorm 7 a ≤ K → δ ≤ localHorizon' ν a f`
     (from 2 + antitonicity + the comparison between `sobolevENorm 7 a` and the cylinder order-7 norm — lanes 145/155's `‖A‖² ≤ 16^m·M`/sharp `4^m` datum comparisons, `OrderTwoCap`);
   - `def HorizonLowerBoundH1 : Prop :=` the contract field **verbatim** (`Spec.lean:338-345`), with a docstring: "manuscript wording (Tao H¹ theory); not provable from the tree; see
     REPORT_210 §3; the owner decides between implementing forced H¹ local theory and a V2 narrowing" — **do not prove or assume it**.
5. **The API shape:** `def localTheoryData : LocalTheoryDataShape` — a structure mirroring `LocalTheoryAPI`'s fields (`horizon`, `solution`, `regularity`) **plus** `horizon_lower_bound_H7_fixedForce`,
   inhabited from 1–4 (so that lane 212 can register V2 by copying fields), and a probe showing every field of `LocalTheoryAPI` except `horizon_lower_bound` is inhabited by it
   (copy the structure from `Spec.lean` into the probe; `Spec.lean` is research, not importable).

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/LocalTheoryBundle.lean` (namespace `NSFormalization.Section4.A01`).
2. Records `research/A01/ATTEMPTS_LOCAL_THEORY_BUNDLE.md`, `A3_SPLIT.md` row 211, conformance `research/A01/axioms_local_theory_bundle.lean`, probe `research/A01/probes/local_theory_api_shape.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.LocalTheoryBundle` (silent), `lake env lean` on the module (0 output), the axioms file, the probe, `make check`.

## Report
Commit on your branch; end with four parts. Also write it to `research/A01/REPORT_211.md`.
