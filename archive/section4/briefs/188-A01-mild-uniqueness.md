# Lane 188-A01-mild-uniqueness — prove `MildUniqueness` (order-6 mild uniqueness on the whole `[0,S]`), the last input of A3-U

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/188-A01-mild-uniqueness` (git branch `erenup/188-A01-mild-uniqueness`,
based on branch `erenup/186-A01-a3-common-horizon` = `origin/erenup/integration` + lane 186's
`Section4/A01/CommonHorizon.lean`; lane 186 is under review — if its `MildUniqueness` statement is revised, a fix run
will tell you). Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P7, `research/A01/REPORT_186.md`,
`research/A01/ATTEMPTS_A3_COMMON_HORIZON.md`, `Section4/A01/CommonHorizon.lean` (the `def MildUniqueness` and how
`compatible_carriers_of_bounds` consumes it), the vendor's `quadraticDuhamel` (`vendor/NavierStokesAndEuler/Euler/QuadraticHeatLocal.lean:23`)
and its contraction/uniqueness theorem `mild_solution_unique` (grep the vendor `Euler/` directory; it needs
`kernelMass T k * L < 1`), `kernelMass` and the bilinear/Lipschitz bound of the Duhamel map on a ball, and the top 40
lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`,
  commented. No edits to existing modules (including `CommonHorizon.lean`); new files only.
- Before claiming a lemma is "not in the tree", `grep -rn` the vendor `Euler/` directory, `Source/`, `Section4/{A01,A02,A04}`
  (A02/A04 have `restart`/shift results at the classical level: `Section4/A04/ForceShift.lean`, `A02/Restrict.lean`,
  `A02/Maximal.lean`). Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; include a
  non-vacuity `example` (zero datum, zero force: the zero path is the unique fixed point).

## Goal
`theorem mildUniqueness : MildUniqueness` — token-for-token the `def` in `CommonHorizon.lean` — so that
`compatible_carriers_of_bounds mildUniqueness …` is unconditional in that input. Mathematics: two fixed points
`u v : C(Icc 0 S, SobolevSpace 1 7)` of the same `quadraticDuhamel` map are equal. The vendor's `mild_solution_unique`
gives it when the whole-interval contraction condition `kernelMass S k * L < 1` holds; in general it fails on `[0,S]`
but holds on every window of length `δ` with `kernelMass δ k * L < 1`, where `L` is the Lipschitz constant of the
Duhamel map on a ball containing both paths (both are continuous on a compact interval, hence bounded — take
`M := max ‖u‖ ‖v‖`). Two standard routes; pick one, record the other in ATTEMPTS:
- **Windows by restart:** show `u = v` on `[0,δ]` (vendor lemma at horizon `δ`, restricting both paths), then that the
  restricted-and-shifted paths from `t₀ = δ` are fixed points of the Duhamel map with datum `u t₀` and shifted force
  (a restart/semigroup identity for `quadraticDuhamel`: grep for `shift`/`restart`/`translate`/`concat` lemmas in the
  vendor and in A02/A04), and iterate finitely many times (`Nat` induction on `⌈S/δ⌉`) or via
  `IsClosed`/`IsOpen`-connectedness of `{t | ∀ s ≤ t, u s = v s}`.
- **First divergence time (no restart identity):** let `t* := sSup {t ∈ Icc 0 S | ∀ s ≤ t, u s = v s}`; `u = v` on
  `[0,t*]` by continuity; on `[t*, t*+δ]` the Duhamel difference only involves `[t*, t]` (the integrand vanishes where
  `u = v`), so the vendor's contraction estimate restricted to that window gives `sup ‖u−v‖ ≤ kernelMass δ · L · sup ‖u−v‖`
  with factor `< 1`, hence `u = v` there, contradicting maximality unless `t* = S`.
Whatever the route, the constant `δ` must come from the tree's kernel-mass and Lipschitz lemmas (name them); if one
quantitative lemma is genuinely missing (e.g. the window-restricted contraction estimate), prove it as a separate
theorem in your module from the vendor's definitions.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/MildUniqueness.lean` (namespace `NSFormalization.Section4.A01`):
   the window lemma(s), `mildUniqueness : MildUniqueness`, and the unconditional corollaries
   `compatible_carriers_of_bounds' := compatible_carriers_of_bounds mildUniqueness` (and the `Inv` and `hall` variants).
2. Records `research/A01/ATTEMPTS_MILD_UNIQUENESS.md`; update `research/A01/A3_SPLIT.md` row A3-U (input discharged);
   conformance `research/A01/axioms_mild_uniqueness.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.MildUniqueness` (silent), `lake env lean`
on the module (0 output), the axioms file, `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with error text / commands).
Also write it to `research/A01/REPORT_188.md`.
