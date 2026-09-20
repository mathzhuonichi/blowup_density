# T20 U5 (`constantTransportCommutesLambda`) — attempts log (lane 452)

The canonical field is proved verbatim in
`formalization/NSFormalization/Section3/T20/TransportLambda.lean`, with no
named input and no residual goal.  Its transitive axioms are exactly
`[propext, Classical.choice, Quot.sound]`.

## Route that closed

`IsPeriodicLambda v Lv` is a concrete coefficientwise graph, not an equality
of physical fields.  Consequently no Fourier-injectivity or datum-uniqueness
step is required: it is enough to establish the two conjuncts of the graph for
the transported fields.

1. For smooth periodicity, expand the fixed directional derivative as
   `(m·∇)z = ∑ j, m j • ∂_j z`.  Smoothness also follows directly from
   `ContDiff.fderiv_right` followed by `ContinuousLinearMap.clm_apply` at the
   constant vector `m`; periodicity of the finite sum uses
   `T12.isPeriodicSpatial_dirDeriv` term by term.
2. For each component `i` and lattice frequency `k`, apply
   `T20.periodicFourierCoeff_fderiv_dir` first to `Lv` and then to `v`.  The
   left coefficient becomes
   `(sum_j m_j (2π i k_j)) * FourierCoeff(Lv)`.  Rewrite the latter with the
   input `IsPeriodicLambda` graph.  The right coefficient becomes the same
   transport symbol times `FourierCoeff(v)`.  `ring` closes the commutation of
   the two complex scalar symbols.

The non-vacuity probe reproduces the actual nonzero witness
`meanZeroPartT (x ↦ cos(2π x₀) • e₀)`, obtains `Lv` from `lambda_exists`,
and applies U5 with `m = e₀` to produce the transported Lambda graph.

## Negative notes

- The lane brief suggested finishing through Fourier injectivity
  (`datum_unique` or coefficient injectivity).  That would be necessary for an
  equality-of-fields formulation, but the canonical target is already
  `IsPeriodicLambda ((m·∇)v) ((m·∇)Lv)`, whose second conjunct *is* the
  required coefficient identity.  Adding reconstruction would only introduce
  an unrelated uniqueness obligation.
- The first draft wrote the finite sum as the unknown identifier `sum` rather
  than Lean's `∑` notation.  The exact error was:

  ```text
  TransportLambda.lean:31:43: unexpected token ':'; expected ':=', 'where' or '|'
  TransportLambda.lean:31:38: Function expected at sum
  ```

  Replacing it by `∑ j : Fin 3, ...` fixed both that parse error and the
  downstream stuck `AddCommMonoid` metavariable.
- The probe initially omitted `open NSFormalization.Section3.T13`, so the
  already imported helper was not in scope.  The exact error was:

  ```text
  transport_lambda_closes.lean:74:2: error(lean.unknownIdentifier):
  Unknown identifier `integrable_torusLift_space`
  ```

  Opening `T13` resolved it; no new analytic lemma was needed.

No `sorry`, `admit`, `axiom`, `native_decide`, heartbeat override, placeholder,
or goal repackaging is used.
