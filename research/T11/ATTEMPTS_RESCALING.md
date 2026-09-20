# T11/U4 viscosity rescaling — attempts

## Successful route

- The initial datum is handled directly from the three conjuncts of
  `initialClassT`: `ContDiff.const_smul` preserves smoothness, congruence
  preserves unit spatial periods, and
  `NavierStokes.ResidualCalculus.spatialDivergence_const_smul` preserves
  solenoidality.
- If the original force has temporal support in a compact
  `K ⊆ Ioi 0`, the rescaled force uses
  `Kν := (fun t ↦ ν * t) '' K`.  This image is compact and remains in
  `Ioi 0` because `ν > 0`.  A support point of
  `unitViscosityForceT ν f` gives a support point of `f` at time `t / ν`;
  `closure_minimal` then proves the required `tsupport` inclusion.
- Each inverse identity is proved by `funext`, unfolding the two scaling
  maps, and simplifying with `ν ≠ 0`.
- The required declaration search covered
  `formalization/NSFormalization/Paper1/Periodic*.lean`, all of `Section3/`,
  `Section4/{A01,A02,A04,D01}`, and `vendor/HeliCorgi/Formal/`.  The closest
  reusable results were the rescaling smoothness/periodicity calculations in
  `Paper1/PeriodicUniqueness.lean`; no declaration already proved either exact
  U4 target.

## Paths tried and exact errors

1. Running the module directly before building its local dependency failed
   with the expected missing object file:

   ```text
   ../formalization/NSFormalization/Section3/T11/Rescaling.lean:1:0: error: object file '/data_8T/ping/blowup_density/.claude/worktrees/314-T11-U4-rescaling/formalization/.lake/build/lib/lean/NSFormalization/Section3/T11/LocalTheory.olean' of module NSFormalization.Section3.T11.LocalTheory does not exist
   ```

   Building `NSFormalization.Section3.T11.Rescaling` first generated the
   dependency object.

2. The first proof draft omitted the namespace containing divergence
   linearity and left the image-membership equality behind a reducible
   function expression.  Lean reported:

   ```text
   error: NSFormalization/Section3/T11/Rescaling.lean:36:8: Unknown identifier `spatialDivergence_const_smul`
   error: NSFormalization/Section3/T11/Rescaling.lean:54:2: unsolved goals
   ν : ℝ
   hν : 0 < ν
   f : SpaceTimeField
   hf_smooth : ContDiff ℝ ∞ f
   hf_periodic : IsPeriodicOn univ f
   K : Set ℝ
   hK_compact : IsCompact K
   hK_pos : K ⊆ Ioi 0
   hf_support : tsupport f ⊆ K ×ˢ univ
   Kν : Set ℝ := (fun t => ν * t) '' K
   z : ℝ × Space
   hz : z ∈ Function.support (unitViscosityForceT ν f)
   hf_ne : f (z.1 / ν, z.2) ≠ 0
   hs : (z.1 / ν, z.2) ∈ tsupport f
   ⊢ ((fun x => ν) * id) (z.1 / ν) = z.1
   ```

   Opening `NavierStokes.ResidualCalculus` fixed the first error.  A `change`
   to `ν * (z.1 / ν) = z.1`, followed by `field_simp [ne_of_gt hν]`,
   fixed the second.

## Residual named input

None.  Both exact fields are unconditional; no peeling hypothesis was
introduced.
