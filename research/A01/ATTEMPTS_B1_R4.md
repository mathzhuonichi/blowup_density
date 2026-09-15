# B1 rung R4 — attempts and proof route (lane 190)

## Successful route

The final field is fixed once, from the order-two path:

```lean
jointRepresentative U hpaths :=
  vectorJointRepresentative 2 (Classical.choose (hpaths 0 2))
```

For scalar data, `angularBoundedRepresentative` is differentiated in space on
the dense range of angular Schwartz data.  Uniform convergence of the
representatives and their gradient fields closes the derivative formula for
all Fourier data.  This gives `angularBoundedRepresentative_contDiff` and the
continuous-linear gradient `angularRepresentativeGradient`.

`scalarJointRepresentative_contDiffOn` then inducts on the finite joint order
on `Icc 0 S ×ˢ univ`.  At the successor step its derivative is the sum of:

- the time component, evaluation of `derivWithin G (Icc 0 S)`; and
- the spatial component, the finite coordinate sum of order-`s-1`
  directional-derivative data.

The closed-set bounded-evaluation lemma
`boundedEvaluation_hasFDerivWithinAt` makes this work at both endpoints, so no
global smooth extension of `G` is required.  The order inequality closes
exactly with `s = n+2`.

Vector reassembly is componentwise.  Every canonical representative is a.e.
equal to the physical `L²` slice by `A03.representative_ae`.  Two such
representatives are continuous, hence a.e. equality upgrades to pointwise
equality by `Continuous.ae_eq_iff_eq`.  Thus the order-`n+2` representative's
`C^n` regularity transfers to the one fixed order-two representative.  Taking
all finite `n` gives the stronger closed-slab theorem.

## Inputs and satisfiability

- `hS : 0 < S` is the ordinary restriction to a positive local existence
  horizon and is satisfied by every standard nonzero local solution.
- `U` is the standard ordinary `L²` solution path restricted to `[0,S]`; it is
  not an additional regularity assumption.
- `hpaths` is the restriction to `[0,S]` of the standard all-order
  `C^j_t H^m_x` regularity enjoyed by a smooth nonzero solution.
- In the composed theorem, `hν : 0 < ν` is the standard positive-viscosity
  condition and `hall` is the compatible all-order smooth cylinder
  realization of that same solution restricted to its common horizon.

The explicit `U := 0` example in `axioms_b1_r4.lean` checks that these
hypotheses and the packaged conclusion are inhabited.

## Rejected or corrected attempts

1. Proving operator-norm differentiability of the entire family
   `x ↦ angularEvaluation s hs x` asks for one more uniform spatial derivative
   than the argument needs.  The bounded-evaluation remainder estimate only
   needs a uniform operator bound and strong continuity on the derivative
   datum, and therefore preserves the sharp `n+2` order.

2. Choosing a smooth representative separately at each time via
   `exists_smoothL2Field_of_memHInfty` gives no canonical choice whose time
   regularity can be transported.  The bounded Fourier representative is
   continuous-linear in the datum and is therefore the correct uniform
   selection.

3. The first compatibility assembly passed an equality to
   `ContDiffOn.congr` in the wrong direction.  Lean spent its heartbeat budget
   trying to identify the dependent Sobolev types and reported:

   ```text
   error: (deterministic) timeout at `whnf`, maximum number of heartbeats
   (400000) has been reached
   ```

   `ContDiffOn.congr` requires `target = source`; reversing the pointwise
   equality removed the timeout, so no heartbeat override remains.

4. A direct change from `angularRepresentativeGradient` to its coordinate sum
   caused expensive definitional equality.  An explicit continuous sum plus
   continuous-linear-map extensionality is fast and exposes the exact spatial
   derivative formula.

## Source checks

The route was checked against `DatumToJets.lean`, `SmoothDatum.lean`,
`A03/SmoothJets.lean`, `A03/BoundedRepresentative.lean`, `SliceWiring.lean`,
the separated B01 modules, the relevant `Source/`, `Paper1/`, and vendor
`Euler/` evaluation and joint-smoothness modules.  The paper passage was read
directly at `appendix-a-local-theory.tex:66-80`: repeated time differentiation
of the projected equation supplies all `C^j_t H^k_x` orders, including the
initial one-sided derivatives used here as within derivatives.

The scalar/vector declarations and both packaged R4 theorems print exactly
`[propext, Classical.choice, Quot.sound]` in `axioms_b1_r4.lean`.
