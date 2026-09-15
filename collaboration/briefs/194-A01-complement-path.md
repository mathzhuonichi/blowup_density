# Lane 194-A01-complement-path — the Leray-complement datum paths of the residual: one physical path `w`, all-`j` all-`m` `C^j_t` data, complement identity at every time

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/194-A01-complement-path` (git branch `erenup/194-A01-complement-path`, based on
`origin/erenup/integration`). This lane is one half of the redesign of lane 189 (the other half is lane 195; lane 189 will assemble). Read
`CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P7/P9, `NEXT_SESSION.md` (entries "压力腿重设计" and "A01 管线现状"),
`Section4/A01/DatumPathSmooth.lean` (178: `reducedResidualPath`, `reducedResidualPath_contDiffOn`, `datumPath_contDiffOn_all_orders` under `hall`),
`Section4/A01/DatumPathDeriv.lean` (169: `cylinderResidualPath`, `ordinaryResidualPath`, `projectedResidualPath`, `projectedResidualPath_eq`,
`datumPath_hasDerivAt`, `exists_continuous_datumPath_general`), `Section4/A01/DatumPathContinuous.lean` (161: descent of cylinder paths to datum
paths at each order), `Section4/A01/L2Descent.lean` (153), `Section4/D01/{LerayDatum,LerayLowering,LeraySymbol}.lean` (Leray complement at datum
level: linear, order-preserving/lowering, continuous), `Section4/A01/JointRepresentative.lean` (190: `vectorRepresentative`, `vectorRepresentative_ae`,
`jointRepresentative`, `exists_joint_smooth_representative` — what it needs as input: datum paths + an `L²`-type carrier for the slice identity),
lane 189's partial helpers on branch `erenup/189-A01-pressure-regularity` (`git show erenup/189-A01-pressure-regularity:formalization/NSFormalization/Section4/A01/PressureRegularity.lean`:
`unprojectedResidualPath`, `unprojectedResidualPath_contDiffOn`, `lerayComplement_contDiffOn`, `carrierDatum_physicalSlice`,
`exists_smooth_lerayComplement_representative`; reuse by copying what you need with attribution, do not import the branch), and the top 40 lines of
`logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing
  modules; new files only. Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` on the zero pair.
- **Satisfiability rule:** named inputs must be restrictions of standard properties (one sentence each). Allowed inputs here: the cylinder pair at
  every order with common carrier `U` exactly in lane 192's combined-export shape (`git show erenup/192-A01-wiring-hsob:formalization/NSFormalization/Section4/A01/CylinderWiring.lean | sed -n 130,200p`;
  copy its conjunction as your hypothesis), `hf : D01.MemForceR f` with `F := C01.forcePath hf`, `hν`, `hS`. Nothing about pressure or time derivatives.

## Goal
For the residual `r(t) := νΔu(t) + f(t) − (u·∇)u(t)` of the cylinder solution, produce its Leray-complement path in physical form:
```lean
theorem exists_complement_paths … :
  ∃ w : ℝ → (Space → Space),
    (∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m:ℝ), ContDiffOn ℝ j G (Icc (0:ℝ) S) ∧ ∀ t : Icc (0:ℝ) S, IsSobolevDatum (m:ℝ) (w t.1) (G t.1)) ∧
    ∀ t : Icc (0:ℝ) S, ∃ A : RealVectorSobolev 0,
      IsSobolevDatum 0 (fun x => residualSlice t x) A ∧ IsSobolevDatum 0 (w t.1) (lerayComplement 0 A)
```
where `residualSlice t` is the physical residual slice expressed through the **velocity representative's** data (state it at datum level: the order-0
datum of `νΔu(t) + f(t) − (u·∇)u(t)` built from the velocity datum paths and the force datum, as 169/178 build `cylinderResidualPath`/`reducedResidualPath`;
name the exact object and prove it agrees with the physical residual of any smooth representative a.e. — that agreement is what lane 195 will use).
Route: (1) the residual datum path at every order `m` is `C^j` in `t` (178's `reducedResidualPath_contDiffOn`, descended to datum level as in 161/169;
lose orders honestly — the all-`j` all-`m` statement uses the all-order supply, exactly as `datumPath_contDiffOn_all_orders`); (2) the Leray complement is
a continuous linear map at each order, commuting with lowering (`D01/LerayLowering.lean`), so the complement paths are `C^j` and compatible across orders;
(3) `w t` := the canonical physical representative of the order-0 complement datum (`vectorRepresentative` from 190 at a fixed high order, or the `L²`
coercion — pick the one lane 190's `jointRepresentative` machinery consumes, and prove the a.e. identity). Also export the corollary for 190:
`exists_complement_joint_representative : ∃ G : SpaceTimeField, ContDiffOn ℝ ∞ G (Ico 0 S ×ˢ univ) ∧ ∀ t : Icc 0 S, (fun x => G (↑t,x)) =ᵐ w t.1`
(apply 190's generic construction to `w`'s paths; if 190's theorem insists on a solenoidal carrier `U`, apply its underlying
`vectorJointRepresentative_contDiffOn`/`jointRepresentative_slice` lemmas directly and say so).

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/ComplementPath.lean` (namespace `NSFormalization.Section4.A01`).
2. Records `research/A01/ATTEMPTS_COMPLEMENT_PATH.md`, `research/A01/A3_SPLIT.md` row "P4a complement path", conformance `research/A01/axioms_complement_path.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.ComplementPath` (silent), `lake env lean` on the module (0 output), the
axioms file, `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements and named inputs / files / gaps with error text / commands). Also write it
to `research/A01/REPORT_194.md`.
