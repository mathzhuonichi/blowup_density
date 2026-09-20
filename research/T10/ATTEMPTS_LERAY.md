# Leray proof attempts (lane 287)

## Successful route

For each lattice frequency `k`, package its three complexified coordinates as
`frequencyVector k : EuclideanSpace ℂ (Fin 3)`.  The formula in
`periodicLeray` is the coordinate formula for the orthogonal projection onto
the orthogonal complement of `ℂ ∙ frequencyVector k` (and is the identity
at `k = 0`).  Mathlib's
`Submodule.norm_starProjection_apply_le`,
`Submodule.starProjection_apply_mem`, and
`Submodule.starProjection_eq_self_iff` then give contraction, solenoidal
range, and the fixed-point property.

The projected coordinates are placed back in `lp 2` using `memℓp_gen` and
summable domination by
`fun k ↦ ∑ i : Fin 3, ‖A.1 i k‖ ^ 2`.  The total contraction follows by
`PiLp.norm_sq_eq_of_L2`, `lp.norm_rpow_eq_tsum`, and
`Summable.tsum_finsetSum`.  Conjugate reflection is checked directly from the
coordinate symbol.

No residual hypothesis is needed.

## Failed probes and exact diagnostics

All experiments were in the now-removed temporary file
`research/T10/probes/leray_dev.lean`.

1. Running the first probe before building the canonical dependency failed
   with:

   ```text
   ../research/T10/probes/leray_dev.lean:1:0: error: object file '/data_8T/ping/blowup_density/.claude/worktrees/287-T10-leray/formalization/.lake/build/lib/lean/NSFormalization/Section3/T10/PeriodicData.olean' of module NSFormalization.Section3.T10.PeriodicData does not exist
   ```

   Building `NSFormalization.Section3.T10.PeriodicData` from `verification/`
   resolved this.

2. The guessed umbrella import
   `Mathlib.Analysis.InnerProductSpace.Projection` was not a built module:

   ```text
   ../research/T10/probes/leray_dev.lean:1:0: error: object file '/data_8T/ping/blowup_density/verification/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Analysis/InnerProductSpace/Projection.olean' of module Mathlib.Analysis.InnerProductSpace.Projection does not exist
   ```

   The correct import is
   `Mathlib.Analysis.InnerProductSpace.Projection.Basic`.

3. Guessed infinite-sum names were absent:

   ```text
   error(lean.unknownIdentifier): Unknown identifier `summable_finset_sum`
   error(lean.unknownIdentifier): Unknown constant `Summable.finset_sum`
   error(lean.unknownIdentifier): Unknown identifier `tsum_finsetSum`
   error(lean.unknownIdentifier): Unknown identifier `tsum_comm`
   ```

   Importing `Mathlib.Topology.Algebra.InfiniteSum.Constructions` exposed the
   actual APIs `summable_sum`, `Summable.tsum_finsetSum`, and
   `Summable.tsum_comm'`.

4. A first attempt to rewrite conjugate reflection with `simp_rw [A.2]`
   unfolded the nested `lp` subtype at the wrong transparency level:

   ```text
   error: `simp` made no progress

   Note: The target expression is not type-correct under the `implicit` transparency level, which may have triggered the failure.
   Full error:
     Application type mismatch: The argument
       fun x => x ∈ lp (fun x => ℂ) 2
     has type
       (PreLp fun x => ℂ) → Prop
     but is expected to have type
       (PeriodicFrequency → ℂ) → Prop
   ```

   Rewriting each finite-sum coordinate explicitly with `A.2 j k` avoids the
   coercion/transparency problem.

5. A first norm proof passed the real exponent from `Memℓp.summable` directly
   where a natural square was expected:

   ```text
   error: Type mismatch: After simplification, term
     Memℓp.summable ... (hbmem i)
   has type
     Summable fun i_1 => ‖(lerayVector i_1 (coefficientVector A i_1)).ofLp i‖ ^ (2 : ℝ)
   but is expected to have type
     Summable fun k => ‖(lerayVector k (coefficientVector A k)).ofLp i‖ ^ (2 : ℕ)
   ```

   Adding both `ENNReal.toReal_ofNat` and `Real.rpow_two` to the conversion
   gives the natural-square series used by the norm identities.

6. Reassociating the derivative multiplier with `simp_rw` did not leave the
   dot product in the syntactic form needed by the range lemma:

   ```text
   error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
     ∑ j, ↑(?k j) * (lerayVector ?k ?v).ofLp j
   in the target expression
     2 * ∑ i, ↑Real.pi * (Complex.I * (↑(k i) * (lerayVector k (coefficientVector A k)).ofLp i)) = 0
   ```

   An explicit `calc` factors the common scalar
   `2 * Real.pi * Complex.I` before invoking the frequency-dot-product lemma.

## Mandatory source search

Before selecting the local helper surface, declarations were searched in:

- `formalization/NSFormalization/Paper1/TorusCube.lean`
- `formalization/NSFormalization/Paper1/Periodic*.lean`
- `formalization/NSFormalization/Section4/D01/`
- `Mathlib/Analysis/Fourier/AddCircleMulti.lean`
- `Mathlib/Analysis/Fourier/AddCircle.lean`
- `Mathlib/MeasureTheory/Group/AddCircle.lean`
- `Mathlib/Analysis/Normed/Lp/lpSpace.lean`

The needed reusable APIs were the generic `lp`/`PiLp` norm identities and
orthogonal-projection lemmas; there was no pre-existing theorem proving this
canonical T10 Leray field.
