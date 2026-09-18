# T11/U3 Galilean classes — attempts

## Successful route

- Translation was implemented on `PeriodicSobolev` data by multiplying each
  coefficient by `UnitAddTorus.mFourier k (torusPoint y)`.  Haar right-translation
  invariance gives the physical Fourier-coefficient formula, and the monomial's
  norm-one identity gives exact datum-norm preservation.  Applying the resulting
  one-sided infimum inequality again at `-y` handles the empty-datum (`⊤`) case.
- Global smoothness of `forceMeanT` was obtained componentwise.  The scalar
  `cubeIntegral_contDiffOn_Ico` theorem was applied after translating an arbitrary
  time to the interior point `1 ∈ [0,2)`.  The two Galilean time primitives then
  follow from the fundamental theorem of calculus and
  `contDiff_infty_iff_deriv`.
- The compact time support of `galileanForceT` uses the original compact set:
  outside it every spatial value of `f`, and consequently `forceMeanT f`, is zero.
- The velocity-mean identity needed by `transformed_mean_zero` was proved privately
  rather than assumed.  Differentiation under `cubeIntegral`, the momentum
  equation, and periodic integration of the advection, Laplacian, and pressure
  gradient show `d/dt velocityMeanT = forceMeanT`; the interval FTC and the initial
  condition identify it with `galileanMeanT`.

## Paths tried and exact errors

1. The first conjugate-symmetry proof mixed `starRingEnd` and `star` notation.
   Lean reported:

   ```text
   unsolved goals
   ⊢ (starRingEnd ℂ) ((UnitAddTorus.mFourier k) (torusPoint y)) * star (...) =
       star ((UnitAddTorus.mFourier k) (torusPoint y)) * star (...)
   ```

   and, after reversing `star_mul`,

   ```text
   unsolved goals
   ⊢ star (Aik * phase) = star (phase * Aik)
   ```

   This was resolved with `map_mul (starRingEnd ℂ)` after rewriting by
   `UnitAddTorus.mFourier_neg`.

2. Rewriting the translated component coefficient directly failed because the
   PiLp coercion was visible in the target:

   ```text
   Tactic `rewrite` failed:
   Did not find periodicFourierCoeff (fun x => ?f (x + y)) k
   ```

   An explicitly typed `hcoeff` with
   `z := fun x ↦ ((z x i : ℝ) : ℂ)` fixed the elaboration boundary.

3. Rewriting `cubeIntegral_sum` initially unfolded `spatialPartial` on only one
   side.  Lean reported:

   ```text
   Tactic `rewrite` failed: Did not find an occurrence of the pattern
     cubeIntegral fun x => ∑ i, (fderiv ℝ ...)
   in the target expression
     (cubeIntegral fun x => ∑ i, spatialPartial i ... x) = 0
   ```

   The final proof uses a `calc` step with `cubeIntegral_sum`, whose conclusion
   is accepted definitionally without a syntactic rewrite.

4. The differentiation theorem returns a derivative written with `deriv`, while
   the momentum regularity lemmas use `temporalDerivative`.  A direct rewrite
   failed with:

   ```text
   Tactic `rewrite` failed: Did not find an occurrence of the pattern
     (cubeIntegral fun x => temporalDerivative w.velocity t x).ofLp k
   ```

   A `change` step exposes their definitional equality before commuting coordinate
   projection with the Bochner integral.

## Residual named input

None.  No peeling hypothesis was introduced.
