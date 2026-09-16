# Lane 192-A01-wiring-hsob — wire 186'+187+178 together: from all-order a-priori bounds to the constructor's `hsob` (and the cylinder pair) with no other input

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/192-A01-wiring-hsob` (git branch `erenup/192-A01-wiring-hsob`, based on
`origin/erenup/integration`, which contains: `Section4/A01/CommonHorizon.lean` (186: `compatible_carriers_of_bounds`, `…Inv`,
`compatible_carriers_hall`, all with a `huniq : MildUniqueness` argument), `Section4/A01/MildUniqueness.lean` (188: `mildUniqueness` and the
primed unconditional corollaries `compatible_carriers_of_bounds'`, `compatible_carriers_of_boundsInv'`, `compatible_carriers_hall'`),
`Section4/A01/ForcePathSmooth.lean` (187: `forcePath_sobolevPath_contDiffOn`, `forcePath_of_memForceR_smooth` — supplies `hfs` for
`F := C01.forcePath hf`), `Section4/A01/DatumPathSmooth.lean` (178: `datumPath_contDiffOn_all_orders hν hS U hall : ∀ j m, ∃ G, ContDiffOn ℝ j G (Icc 0 S) ∧ ∀ t, IsSobolevDatum m (⇑(U t)) (G t.1)`),
`Section4/A01/Horizon.lean` (`HasAprioriBound`, `localTheory_on_prescribed_horizon`: the seven-clause cylinder pair at one order),
`Section4/A01/AprioriInvariance.lean` (173: `HasAprioriBoundInv`, `localTheory_on_prescribed_horizon_of_boundInv`)). The consumer is lane 180's
constructor (branch `erenup/180-A01-b2-assembly`, being re-cut to horizon `T := S`; `git show erenup/180-A01-b2-assembly:formalization/NSFormalization/Section4/A01/ConstructorAssembly.lean | sed -n 120,160p`
for the exact `hsob`/`hU`/`hdiv` binders — note it may change slightly in the fix2 commit; match the *shape*, and say if you had to adapt).
Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P7–P9, `research/A01/B1_LADDER.md`, `research/A01/A3_SPLIT.md` (rows A3-U, A3-M2),
and the top 40 lines of `logs/LESSONS.md` first.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to
  existing modules; new files only. Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity
  `example` (zero datum, zero force, any `R`).
- **Satisfiability rule:** the only analytic input allowed is the all-order a-priori bound family
  `hb : ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν a F hF (R q)` (or its `Inv` variant) with `F := C01.forcePath hf`, `hF := C01.forcePath_jetLp_continuous hf`;
  everything else must come from the tree.

## Goal
`theorem cylinderPair_of_bounds (hf : D01.MemForceR f) (hν : 0 < ν) (hS : 0 < S) (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
  (R : ℕ → ℝ) (hb : ∀ q hq, HasAprioriBound hq hν a (C01.forcePath hf) (C01.forcePath_jetLp_continuous hf) (R q)) :
  ∃ U : C(Icc 0 S, EulerMeanSolenoidal.L2), U ⟨0,…⟩ = a.toLp ∧
    (∀ q (hq : 6 ≤ q), ∃ u : C(Icc 0 S, SobolevSpace 1 (q+1)), (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧ (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧ (angle invariance) ∧ (Duhamel at order q)) ∧
    (∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m:ℝ), ContDiffOn ℝ j G (Icc 0 S) ∧ ∀ t : Icc 0 S, IsSobolevDatum (m:ℝ) (⇑(U t)) (G t.1))`
— i.e. one carrier `U` with (i) the cylinder pair at every order including divergence-freeness (from `localTheory_on_prescribed_horizon` at each
order + the identification of carriers by 186'/188), and (ii) 178's all-`j`, all-`m` datum paths (from `compatible_carriers_hall'` with 187's `hfs`).
Then the two exports the constructor consumes: `hsob_of_bounds` (the `j = 0` instance in lane 180's exact `hsob` shape — `ContDiffOn ℝ 0` or
`ContinuousOn`, whichever 180 uses; provide both if cheap) and `hU_hdiv_of_bounds` (the `hU`, `hdiv` binders at the order the constructor takes).
Also the `Inv` variants (`HasAprioriBoundInv`, via `localTheory_on_prescribed_horizon_of_boundInv` and `compatible_carriers_of_boundsInv'`).
Record in ATTEMPTS what is now the **only** remaining analytic input for the whole A01 pipeline besides `hc3` (lane 190) and `hpg` (lane 189):
the all-order bound family `hb` (A3-M2), and sketch (prose, no Lean) how it should follow from Grönwall (149/179) + uniqueness (188) + the
constructor once 189/190 close.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/CylinderWiring.lean` (namespace `NSFormalization.Section4.A01`).
2. Records `research/A01/ATTEMPTS_WIRING_HSOB.md`; update `research/A01/A3_SPLIT.md` (row A3-U: wired) and `B1_LADDER.md` (R3 all orders: wired
   given `hb`); conformance `research/A01/axioms_wiring_hsob.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.CylinderWiring` (silent), `lake env lean` on the module (0 output),
the axioms file, `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands). Also write it to
`research/A01/REPORT_192.md`.
