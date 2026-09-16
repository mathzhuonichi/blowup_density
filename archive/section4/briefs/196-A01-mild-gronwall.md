# Lane 196-A01-mild-gronwall — prove `MildGronwall` (the finite-order mild energy inequality), the last analytic input of the A01 a-priori family

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/196-A01-mild-gronwall` (git branch `erenup/196-A01-mild-gronwall`, based on branch
`erenup/193-A01-a3-m2-bounds` = `origin/erenup/integration` + lane 193's `Section4/A01/AprioriFamily.lean` (`def MildGronwall`, `aprioriRadius`,
`hb_of_base`; lane 193 is being merged — if its `MildGronwall` statement changes, a fix run will tell you)). Read `CLAUDE.md`, `collaboration/HANDOFF.md`
§0 and §2 P7, `research/A01/REPORT_193.md` (exact `MildGronwall` statement and why the radius uses `256·‖restrictOperator … u s‖²`), the review
`research/A01/REVIEW_193-A01-a3-m2-bounds.md` §"route" (`sed -n 160,190p`), `research/A01/A3_SPLIT.md` row A3-M2, the vendor's regularized mild-energy
machinery (`grep -rn "mild_majorized_energy_subinterval\|EulerMildMajorantEnergy" vendor/NavierStokesAndEuler` — read that file and its prerequisites:
regularized words, majorant energy, the metric parameter), `Section4/A03/OuterTameProduct.lean:150-185` (`outerProductTame`),
`Section4/A04/HighEnergy.lean:120-185` (`inner_energy_Rhigh`, `outerSobolevNormAt_le`), `Section4/A01/OrderTwoCap.lean:200-250` (`kbnd_of_sup_bound`,
the `256` shape), `Section4/A01/GronwallInstance.lean` (the classical-level analogue, for the target shape only), and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing
  modules (including `AprioriFamily.lean`); new files only. Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity
  `example` on zero data.
- **Satisfiability rule:** if one genuinely missing analytic fact remains, isolate it as ONE named hypothesis with the exact statement and prove the
  rest; do not route through the all-order constructor (circular) and do not use `ClassicalSolutionR`-level energy lemmas on a mild path.

## Goal
`theorem mildGronwall (hq : 6 ≤ q) (hν) (a) (F) (hF) : MildGronwall hq hν a F hF (E q) (C q)` with explicit nonnegative constants `E q`, `C q`
(depending on `q`, `ν` only), token-for-token the `def` in `AprioriFamily.lean` — for every horizon `T ≤ S` and every order-`q` mild solution `u`
(fixed point of `quadraticDuhamel` with canonical datum/force), a continuous majorant `y` with `‖u t‖ ≤ y t`, `y 0 ≤ E·‖u₀‖`, and the integral
inequality `y t ≤ y 0 + ∫₀ᵗ (C·256·‖u|₆(s)‖²·y(s) + E·‖F‖_{q+1})`. Route (reviewer 193): the vendor's regularized mild-energy chain
(`mild_majorized_energy_subinterval` and its regularized-word prerequisites) specialized to the constant Euclidean metric and the finite word family
through order `q+1` gives a scalar energy that is a continuous majorant of the cylinder norm and satisfies a differential/integral inequality whose
nonlinear top-order term is the tame product; bound that term by `A03.outerProductTame` → `A04.outerSobolevNormAt_le` (transport to the real norm) →
`A04.inner_energy_Rhigh` (the algebraic energy inequality), with the low-order factor being the order-6 (lowered) norm — match the `256·‖restrictOperator … u s‖²`
shape exactly (if the natural constant differs, prove `MildGronwall` with your constants and add a one-line lemma showing 193's shape follows, or
report the exact mismatch). Handle the force term at order `q+1` as 193 states it.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/MildGronwall.lean` (namespace `NSFormalization.Section4.A01`): the specialization of the
   vendor energy chain, the tame top-order bound, `mildGronwall`, and the unconditional corollaries `hb_of_base' := hb_of_base … mildGronwall`
   (and `Inv`).
2. Records `research/A01/ATTEMPTS_MILD_GRONWALL.md` (negative examples included), update `research/A01/A3_SPLIT.md` row A3-M2, conformance
   `research/A01/axioms_mild_gronwall.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.MildGronwall` (silent), `lake env lean` on the module (0 output), the
axioms file, `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements and constants / files / gaps with error text / commands). Also write it to
`research/A01/REPORT_196.md`.
