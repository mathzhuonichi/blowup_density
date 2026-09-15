# R44 (Prop. 4.4) — attempts and proof notes (lane 166)

Scope: split `04-whole-space.tex:145-174` and close only the scalar/constant
rows that do not assume an unregistered sibling theorem.  Lean output is
`Section4/R44/Pieces.lean`.

## Positive results

* The registry audit changed one conclusion of `COMPARISON.md`: lane 042's
  `forceSobolevENorm_ne_top` is now registered as
  `D01.datum_lemmas_v2` V2.  Its `m=0,s=-1/2,q=2` instance proves the R44 ball
  is not vacuous.  It does not provide the `B(t)^2` prefix-integral identity;
  that remains G3.

* The two truly identical rows were reused.  Importing `R43.Pieces` provides
  `enorm_npow_two_eq_rpow_two` and `criticalL3_gate_enorm`; there is no R44
  alias or copy.  The second theorem already has C01's exact target
  `ENNReal.ofReal C₁ * L3 ≤ ENNReal.ofReal (ν/4)`.

* `criticalSquaredNormBound_radius` is the R44 scalar closure.  R43's
  `critical_norm_bound` does not match eq:Rcritical2: R43 has a `b*y` right
  side and square-root division, whereas R44 has a linear inequality for
  `Y²` with source `B²`.  The proof therefore reuses
  `A04.gronwall_deriv` for the improvement and exactly the shared
  `Paper1.continuous_bootstrap` for first exit.  It obtains the stronger
  `Y ≤ theta*ν/2`, so a putative first crossing at `theta*ν` is impossible.

* `exists_rcritical2_constants` first invokes R43's universal shrinking
  theorem to choose `theta` below both the nonlinear threshold and C01's gate
  threshold.  It then takes
  `c = theta / (4*(C₃+1))` and `C=C₂+1`.  All three choices are made before
  `ν,S`, matching the quantifier order of the R44 API.

* `radius_forces_gronwall_small` verifies the displayed scaling rather than
  leaving it as prose.  The key normalization is
  `(ν^(3/2 : ℝ))² = ν³`; after multiplication by `ν⁻¹` the scale is `ν²`.
  The exponential product is
  `exp (C₂νS) * exp (-((C₂+1)νS))² ≤ 1` for `S≥0`.

## Negative attempts and pin-specific friction

* An early plan was to restate the power bridge and gate theorem under R44
  names.  This would add no content and violate the handoff's reuse rule, so
  it was discarded before editing.  The conformance file exercises the R43
  declarations directly.

* Applying `A04.gronwall_deriv` and immediately rewriting
  `intervalIntegral.integral_const_mul` failed because simplification had
  already extracted one constant but had not yet exposed the other integral:

  ```text
  Tactic `rewrite` failed: Did not find an occurrence of
    ∫ x in ?a..?b, r * f x
  ```

  The stable sequence is: simplify the zero initial value and constant
  coefficient integral; then rewrite the remaining source integral once; then
  normalize multiplication only.

* `linarith` did not prove nonpositivity of the combined exponential exponent
  while it still contained products `C₂*ν*S`.  The failure goal was

  ```text
  0 < C₂ * ν * S + 2 * -((C₂ + 1) * ν * S)
  ```

  Rewriting it by `ring` to
  `-(C₂*ν*S) - 2*(ν*S)` and using the two explicit nonnegativity facts is
  robust.

* Rewriting the `rpow` square failed while it was hidden inside the square of
  a three-factor product.  `simp only [mul_pow]` must expose
  `(ν^(3/2 : ℝ))²` before applying the `Real.rpow_mul` identity.

* The scalar theorem assumes one function `E' : ℝ → ℝ` with
  `IntervalIntegrable E' volume 0 T`, global `Continuous Y`, and continuity of
  `B²`.  These are honest inputs, not claimed consequences of `MemForceR` here.
  Pointwise derivative witnesses do not supply the first input; the PDE
  critical path (G2) should assemble it.  Instantiation must likewise provide
  global continuity of `Y` or extend the PDE norm path continuously from
  `Icc 0 T`.  The `H^{-1/2}` force slice (G3) should provide the last input or a
  slightly more general integrable version.  Weakening the scalar theorem
  before G3 fixes its final carrier shape would be premature.

* The `a=0` conversion from lifespan `>T` to exclusion from
  `breakdownSetRZero` is a two-line definitional reduction, but its exact
  statement imports frozen contract vocabulary.  It is recorded for the
  eventual binding rather than placed in the implementation module, respecting
  the repository's separation between `formalization/` and contract structures.

## Not attempted

* G1: construction of `J`, exact Bessel-weight identity, and negative-order
  duality.
* G2: differentiation/pairing and the nonlinear PDE estimate producing
  eq:Rcritical2.
* G3: a canonical real `H^{-1/2}` force-slice path and equality of its squared
  prefix integral with the R44 force norm.
* C01 V4, A05 V2, A04 V3, and maximal-endpoint gluing: their exact dependencies
  and owners are in `R44_SPLIT.md`; none is silently assumed by the Lean module.
