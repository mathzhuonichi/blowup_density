# Lane 195-A01-interior-momentum — the interior momentum identity for the joint representative: `∂ₜ u(t,x)` is the evaluated derivative datum, hence `residual − ∂ₜu = ` complement representative on `Ioo 0 S`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/195-A01-interior-momentum` (git branch `erenup/195-A01-interior-momentum`, based on
`origin/erenup/integration`). This lane is one half of the redesign of lane 189 (the other half, lane 194, builds the complement's datum paths;
lane 189 will assemble). Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P7/P9, `NEXT_SESSION.md` (entries "压力腿重设计" and "A01 管线现状"),
`Section4/A01/JointRepresentative.lean` (190: `boundedEvaluation_hasFDerivWithinAt`, `angularBoundedRepresentative_hasFDerivAt`, `angularEvaluation`,
`scalarJointRepresentative`, `vectorRepresentative`, `vectorRepresentative_ae`, `vectorRepresentative_eq_of_datums`, `jointRepresentative`,
`jointRepresentative_slice`, `jointRepresentative_contDiffOn`), `Section4/A01/DatumPathDeriv.lean` (169: `datumPath_hasDerivAt` — the velocity datum path
at order `m` is differentiable in `t` with derivative the projected residual datum `projectedResidualPath`, `projectedResidualPath_eq`),
`Section4/A01/DatumPathSmooth.lean` (178), `Section4/A01/ConstructorPressure.lean` (168: `momentumResidualOfVelocity`, `pressureGradientOfVelocity :=
residual − temporalDerivative`), `vendor/…/NavierStokes/ProblemStatement.lean:53-56` (`temporalDerivative` = ambient `fderiv` in `t`),
`vendor/…/NavierStokes/ResidualRegularity.lean:36-52` (`contDiffOn_temporalDerivative` on open sets), lane 189's review
(`git show erenup/189-A01-pressure-regularity:research/A01/REVIEW_189-A01-pressure-regularity.md | sed -n 95,185p`: why nothing may be claimed at `t = 0`),
and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. No edits to existing
  modules; new files only. Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`; non-vacuity `example` on the zero pair.
- **Satisfiability rule:** named inputs must be restrictions of standard properties; **nothing at `t = 0`**, all claims on `Ioo 0 S` only.

## Goal (two generic lemmas + one identity)
1. `jointRepresentative_temporalDerivative`: for `u := jointRepresentative U hpaths` (190) and an order `m` large enough for bounded evaluation, if the
   order-`m` datum path `G_m` has `HasDerivWithinAt G_m (D t) (Icc 0 S) t` at `t ∈ Ioo 0 S` (169's shape), then for every `x`,
   `temporalDerivative u t x = vectorRepresentative … (D t) x` (the ambient time derivative of the evaluated field is the evaluation of the derivative
   datum — bounded linear evaluation commutes with `fderiv`; use `boundedEvaluation_hasFDerivWithinAt`/`HasFDerivAt.comp` and pass from within-`Icc`
   to ambient at interior points via `HasDerivWithinAt.hasDerivAt` with `Icc ∈ 𝓝 t`).
2. `vectorRepresentative_sub` / linearity: the canonical representative of `A − lerayComplement 0 A` (or of any difference/scalar combination of data)
   equals the pointwise difference of representatives, for smooth data (`vectorRepresentative_eq_of_datums` + linearity of the datum relation; state at
   the order you need).
3. `interior_momentum_identity`: for the cylinder solution's joint representative `u` and any field `G` whose slices are a.e. the complement
   representative of the residual (lane 194's shape: `∀ t : Icc 0 S, (fun x => G (↑t,x)) =ᵐ w t.1` with `w t` the representative of `lerayComplement 0 A_t`,
   `A_t` the residual's order-0 datum, and `IsSobolevDatum 0 (residualSlice t) A_t`), with `G` and `u` slab-smooth (`ContDiffOn ℝ ∞ · (Ico 0 S ×ˢ univ)`):
   `∀ t ∈ Ioo (0:ℝ) S, ∀ x, G (t,x) = pressureGradientOfVelocity ν f u (t,x)`. Proof: on the interior, `pressureGradientOfVelocity = residual − ∂ₜu`;
   by (1) and 169 (`datumPath_hasDerivAt`, `projectedResidualPath_eq`: `∂ₜ` datum = `A_t − lerayComplement 0 A_t` at datum level, i.e. the *projected*
   residual), `∂ₜu(t,·)` is the representative of the projected residual; by (2) `residual − ∂ₜu` is the representative of the complement; both sides
   continuous in `x` and a.e. equal ⇒ equal everywhere (`Continuous.ae_eq_iff_eq`). State precisely which 169 lemma supplies the datum-level identity and
   at which order; if the physical residual slice vs the datum-built residual needs the a.e. agreement lemma from lane 194, take it as the named input
   `hres` in exactly lane 194's exported shape (copy from `collaboration/briefs/194-A01-complement-path.md` §Goal).

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/InteriorMomentum.lean` (namespace `NSFormalization.Section4.A01`).
2. Records `research/A01/ATTEMPTS_INTERIOR_MOMENTUM.md`, `research/A01/A3_SPLIT.md` row "P4b interior identity", conformance `research/A01/axioms_interior_momentum.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.InteriorMomentum` (silent), `lake env lean` on the module (0 output),
the axioms file, `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements and named inputs / files / gaps with error text / commands). Also write it
to `research/A01/REPORT_195.md`.
