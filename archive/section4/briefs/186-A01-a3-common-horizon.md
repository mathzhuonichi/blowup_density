# Lane 186-A01-a3-common-horizon — A3 unit: one ordinary carrier `U` on `[0,S]` realized at every cylinder order (supply lane 178's `hall`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/186-A01-a3-common-horizon` (git branch
`erenup/186-A01-a3-common-horizon`, based on `origin/erenup/integration`). Read `CLAUDE.md`,
`collaboration/HANDOFF.md` §0 and §2 P7, `research/A01/A3_SPLIT.md`, `research/A01/B1_LADDER.md` §R3/R4,
`Section4/A01/Horizon.lean` (`HasAprioriBound`, `localTheory_on_prescribed_horizon`), `Section4/A01/AprioriInvariance.lean`
(`HasAprioriBoundInv`, `localTheory_on_prescribed_horizon_of_boundInv`), `Section4/A01/L2Descent.lean`, and the top 40
lines of `logs/LESSONS.md` first.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`,
  commented. No edits to existing modules; new files only.
- Before claiming a lemma is "not in the tree", `grep -rn` all of `Section4/{A01,A02,D01}`, `Source/`,
  `vendor/NavierStokesAndEuler/Euler/{QuadraticHeatLocal,CylinderSobolevSpace,MeanOrdinaryLift}*.lean`,
  `Source/OrdinaryCylinderDescent.lean`. Before citing a paper line, `sed -n` it. Every declaration must print exactly
  `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example` (`a := 0`, `F := 0`).

## Why this lane exists (the consumer)
Both the B1 ladder (lane 178, `datumPath_contDiffOn_all_orders`) and the B2 constructor (lane 180) stop at a
*finite* cylinder order: `localTheory_on_prescribed_horizon` gives, for each `q ≥ 6` with its own bound `R q`, a pair
`(u_q, U_q)` on the same `[0,S]`, but nothing identifies the ordinary carriers `U_q` across orders. The paper
(`appendix-a-local-theory.tex:66-76`) takes for granted that the higher-order bounds hold for **the same** solution
on **one** interval. Lane 178 isolated exactly what is needed as the hypothesis (copy verbatim; this is your target):

```lean
(hall : ∀ (q : ℕ) (hq : 6 ≤ q),
  ∃ (u₀ : SobolevSpace 1 (q + 1))
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))),
    ContDiffOn ℝ ∞ (extendPath S hS.le f) (Icc (0 : ℝ) S) ∧
    (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
    (∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
    ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl (coefficients 1 hq f) u₀ u t)
```
(`U : C(Icc 0 S, EulerMeanSolenoidal.L2)` fixed **before** `q`.) The first conjunct (time-smooth force path) is a
separate obligation; take it as the single named input
`hfs : ∀ q (hq : 6 ≤ q), ContDiffOn ℝ ∞ (extendPath S hS.le (sobolevPath F hF q)) (Icc (0:ℝ) S)` and do not work on it.

## Goal
`theorem compatible_carriers_of_bounds` : given `hν hS a ha F hF`, radii `R : ℕ → ℝ` with `∀ q (hq : 6 ≤ q),
HasAprioriBound hq hν a F hF (R q)` (and the `Inv` variant via lane 173), and `hfs`, produce
`∃ U : C(Icc 0 S, EulerMeanSolenoidal.L2), U 0 = a.toLp ∧ <hall with this U>` where at each order the witnesses are
the canonical ones: `u₀ := ordinarySobolev (q+1) a.toLp a.translation_contDiff`, `f := sobolevPath F hF q`, and `u`
the mild solution of `localTheory_on_prescribed_horizon` at order `q`. The mathematical content is **cross-order
uniqueness**: take `U := U_6`; for `q > 6` show `ordinaryLift (U_6 t) = value 1 (u_q t)`. Route to try first:
lowering `u_q` to order 7 (`restrictOperator 1 h` — lane 178's proof uses `value_restrictOperator`,
`restrictOperator_translation`; find the lemma that `quadraticDuhamel` commutes with `restrictOperator`, or prove it
from the definition in `vendor/.../Euler/QuadraticHeatLocal.lean:23`) gives a second mild solution at order 6 with
the same datum and force; then **uniqueness of the mild solution at a fixed order on `[0,S]`** (grep the vendor
and `Source/` for the fixed-point/contraction uniqueness of `quadraticDuhamel`; if only a small-ball contraction
exists, prove uniqueness on `[0,S]` by the standard continuity/first-divergence-time argument using the bilinear
bound that the contraction already uses). If a genuinely missing analytic fact remains, isolate it as **one** named
hypothesis with the exact statement (e.g. `MildUniqueness`) and prove everything else; do not hide it in `hall`.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/CommonHorizon.lean` (namespace
   `NSFormalization.Section4.A01`): the lowering/commutation lemma(s), the uniqueness lemma (or its named
   hypothesis), `compatible_carriers_of_bounds`, and `compatible_carriers_of_boundsInv`.
2. Records `research/A01/ATTEMPTS_A3_COMMON_HORIZON.md`; update `research/A01/A3_SPLIT.md` (new row "A3-U common
   horizon") and `B1_LADDER.md` §R3/R4 (what `hall` now reduces to); conformance `research/A01/axioms_a3_common_horizon.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.CommonHorizon` (silent), `lake env lean`
on the module (0 output), the axioms file, `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text /
commands). Also write it to `research/A01/REPORT_186.md`.
