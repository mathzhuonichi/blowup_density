# Lane 189-A01-pressure-regularity — the pressure gradient of a jointly smooth cylinder solution: slab-smooth, per-time L², symmetric Jacobian (supply `hpg`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/189-A01-pressure-regularity` (git branch `erenup/189-A01-pressure-regularity`,
based on `origin/erenup/integration`). Read `CLAUDE.md`, `collaboration/HANDOFF.md` §0 and §2 P7, `Section4/A01/ConstructorPressure.lean`
(`momentumResidualOfVelocity`, `pressureGradientOfVelocity := residual − ∂ₜu`, `pressureOfVelocity` = radial potential of it,
`pressure_gradient_memLp` and `pressure_smooth_of_velocity_smooth` with their premises), `Section4/A01/DatumPathDeriv.lean`
(lane 169: `residualDatum_is_timeDerivative`, `projectedResidualPath_eq` — the time derivative of the datum path *is* the projected
residual `P(νΔu + f − (u·∇)u)`), `Section4/D01/OrderZeroCurl.lean:400-504` and `D01/Longitudinal.lean` (curl-free ⇔ longitudinal
datum ⇔ Leray-complement fixed — forward direction only), `Section4/A01/PressureGauge.lean:126-157`
(`hasSymmetricJacobian_pressureGradient` from a smooth scalar pressure — circular for us, do not use), `Section4/A01/RadialPotential.lean`,
lane 180's `research/A01/REVIEW_180-A01-b2-assembly.md` §"`hpg` minimality and lane 189's obligation" (on branch
`erenup/180-A01-b2-assembly`: `git show erenup/180-A01-b2-assembly:research/A01/REVIEW_180-A01-b2-assembly.md | sed -n 129,175p`),
and the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented.
  No edits to existing modules; new files only.
- Before claiming a lemma is "not in the tree", `grep -rn` all of `Section4/{A01,A02,A03,A04,D01,C01}`, `Source/`, `Paper1/`.
  Before citing a paper line, `sed -n` it. Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`;
  include a non-vacuity `example` on the zero solution.

## Setting (honest slab, no clamp)
Fix `ν > 0`, the paper's global force `f` with `hf : D01.MemForceR f` (jointly smooth on `futureDomain`, all-order datum paths
`G_m` smooth in time — `D01/ForceClass.lean:158-164`), a horizon `S > 0`, and a velocity field `u : SpaceTimeField` with
- `hc3 : ContDiffOn ℝ ∞ u (Ico (0:ℝ) S ×ˢ univ)` (joint smoothness on the open slab),
- all-order data on the slab: `hsob : ∀ m, ∃ G : ℝ → RealVectorSobolev m, ContinuousOn G (Icc 0 S) ∧ ∀ t ∈ Ico 0 S, IsSobolevDatum m (fun x => u (t,x)) (G t)`
  (lane 178's shape at `j = 0`; use `Icc`/`Ico` as the tree's `IsSobolevDatum` prefers — state which),
- divergence-freeness `hdiv : ∀ t ∈ Ico 0 S, ∀ x, spatialDivergence (fun x => u (t,x)) x = 0`,
- the projected momentum identity at datum level: for each `t ∈ Ico 0 S`, the time derivative `∂ₜu(t,·)` equals the Leray projection
  of the residual `νΔu + f − (u·∇)u` (lane 169's `residualDatum_is_timeDerivative` / `projectedResidualPath_eq`; state it as a named
  input `hmom` in the exact form 169 exports, and check whether 169's statement is at datum level (a.e.) or pointwise — bridge with
  smoothness).
Do **not** assume a scalar pressure. `G := pressureGradientOfVelocity ν f u` is `residual − ∂ₜu`.

## Goal (the exact `hpg` of lane 180 after its re-cut to `T := S`)
1. `pressureGradient_contDiffOn : ContDiffOn ℝ ∞ G (Ico (0:ℝ) S ×ˢ univ)` — from `hc3` and `hf.1` (`temporalDerivative`, `Δ`, `(u·∇)u`
   of a slab-smooth field are slab-smooth; find the tree's `temporalDerivative`/`spatialDerivative` smoothness lemmas in
   `Section4/A04/TimeDerivative.lean`, `A03/SmoothJets.lean`, `D01/SmoothDatum.lean`).
2. `pressureGradient_memLp : ∀ t ∈ Ico 0 S, MemLp (fun x => G (t,x)) 2 volume` — via `hmom`: `G(t,·) = residual − P(residual) = (I − P)(residual)`
   is the Leray complement of an `L²` field (residual ∈ L² per time from `hsob` at order 2 + `f`'s order-0 datum + the tame product
   for `(u·∇)u`, `A03/VectorTameProduct.lean`, `A04/NonlinearDatum.lean`), and the Leray complement of an `L²` field is `L²`
   (`D01/LerayDatum.lean`, `LerayLowering.lean`).
3. `pressureGradient_hasSymmetricJacobian : ∀ t ∈ Ico 0 S, RadialPotential.HasSymmetricJacobian (fun x => G (t,x))` — the Leray
   complement is longitudinal (a gradient): the converse direction the tree lacks. Prove it at the level available: the Leray complement
   of a smooth field with data is curl-free pointwise (its Fourier datum is `ξ(ξ·ĝ)/|ξ|²`, `D01/LeraySymbol.lean`, `OrderZeroSymbol.lean`;
   or: it equals the spatial gradient of the radial potential and gradients of `C²` functions have symmetric Jacobians — `RadialPotential`
   already relates `G` and `pressureOfVelocity`; check `pressureGradient_pressureOfVelocity_lerayComplement` and whether symmetry can be read
   off the potential's `C²` regularity given (1)). If one identity (e.g. "Leray complement = ∇(radial potential of the complement)")
   is genuinely missing, prove it or isolate it as ONE named hypothesis with the exact statement.
4. Package: `theorem hpg_of_slab (…) : ContDiffOn ℝ ∞ G (Ico 0 S ×ˢ univ) ∧ ∀ t ∈ Ico 0 S, MemLp (fun x => G (t,x)) 2 volume ∧ RadialPotential.HasSymmetricJacobian (fun x => G (t,x))`
   in the exact conjunction shape lane 180 consumes.

## Deliverables
1. New module `formalization/NSFormalization/Section4/A01/PressureRegularity.lean` (namespace `NSFormalization.Section4.A01`).
2. Records `research/A01/ATTEMPTS_PRESSURE_REGULARITY.md` (negative examples included), `research/A01/A3_SPLIT.md` new row "P4 pressure
   regularity", conformance `research/A01/axioms_pressure_regularity.lean`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.PressureRegularity` (silent), `lake env lean` on the
module (0 output), the axioms file, `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements and the exact named inputs / files / gaps with error text /
commands). Also write it to `research/A01/REPORT_189.md`.
