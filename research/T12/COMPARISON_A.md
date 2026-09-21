# T12 draft A comparison

This is the independent draft-A comparison for node T12. It uses the physical
periodic-field / weighted-coefficient representation fixed by
`collaboration/SECTION3_PLAN.md` §1 and does not use finite-mode constants.

## Paper clause → Lean field

| Paper clause | Lean field in `MeanZeroSobolevCalculusAPI K` | Quantifier and representation notes |
|---|---|---|
| `appendix-a-local-theory.tex:9-11`, eq:Rproduct, `m ≥ 2` | `tameProduct` | `m`, `2 ≤ m`, the two scalar physical fields, then their `H^m` membership. `K.Cproduct m` is fixed first. No mean-zero assumption: the paper has none here. |
| `appendix-a-local-theory.tex:12`, `‖v‖∞ ≤ C‖v‖H²` | `boundedRepresentative` | Physical three-vector field; `L∞` is the essential-supremum `eLpNorm`. No mean-zero assumption. |
| `appendix-b-embeddings.tex:20-29`, `‖v‖₃ ≤ C‖v‖Ḣ¹ᐟ²` | `velocityCriticalL3` | Physical periodic `L²` representative, then `IsMeanZero`, then finiteness of the displayed homogeneous norm. The mean-zero condition is explicit and essential. |
| `appendix-b-embeddings.tex:26-31`, `‖∇v‖₃ + ‖Λv‖₃ ≤ C‖v‖Ḣ³ᐟ²` | `gradientLambdaCriticalL3` | Weak gradient and `Λ` are specified by the exact multipliers `2π i k_j` and `2π|k|`; no classical-derivative hypothesis is inserted. |
| `appendix-b-embeddings.tex:26-32`, `‖∇v‖₆ ≤ C‖Δv‖₂`; use at `03-torus.tex:471-477` | `gradientL6` | Mean-zero periodic form requested by T12. Gradient and Laplacian are Fourier-multiplier representatives. |
| `03-torus.tex:490-494`, `‖v‖H² ≤ C‖Δv‖₂` | `hTwo_le_laplacian` | Mean-zero physical periodic field with finite `L²` Laplacian representative. |
| `02-preliminaries.tex:52-54` and `appendix-b-embeddings.tex:85-90`, spectral gap | `spectralGap` | For every fixed `s ≥ 0`, mean zero and finite `Ḣ^s` imply `‖v‖H^s ≤ C_s‖v‖Ḣ^s`. This exposes the norm bridge needed by consumers, rather than only the pointwise weight inequality. |

The corresponding constants are the explicit real fields of
`MeanZeroSobolevCalculusConstants`: `Cproduct`, `Cinfty`, `CcriticalHalf`,
`CcriticalThreeHalves`, `Csix`, `CHtwo`, and `Cgap`. Their positivity clauses
are proof fields of the API and precede all inequality fields.

## Representation choices

1. **Physical layer.** `ScalarField` and `SpatialField` are functions on
   `EuclideanSpace ℝ (Fin 3)`. `IsUnitPeriodic` is a property, so this follows
   the Section 3 decision not to replace the physical carrier by
   `UnitAddTorus`. The quotient torus occurs only under spatial integration.

2. **Coefficient layer.** `PeriodicFrequency` is definitionally
   `Fin 3 → ℤ`. Each component datum is literally
   `lp (fun _ : PeriodicFrequency => ℂ) 2`; vector components are assembled by
   `PiLp 2`. The inhomogeneous datum stores
   `(1 + 4π²|k|²)^(s/2) v̂(k)`, and the homogeneous datum stores
   `|2πk|^s v̂(k)` with the zero entry set to zero.

3. **Mean zero.** `IsMeanZero v` is exactly `v̂_i(0) = 0` for every component.
   It appears on every homogeneous/critical clause and on the two
   Laplacian/spectral-gap comparisons, but not on eq:Rproduct or the
   inhomogeneous `H² → L∞` embedding.

4. **Total norms.** Sobolev quantities are `ℝ≥0∞` infima over matching weighted
   `lp` data. Missing data yield `⊤`; no `.toReal` can hide failure. Physical
   `L^p` quantities are `eLpNorm` over the unit-torus measure.

5. **Distributions and representatives.** Appendix B quantifies over periodic
   distributions with finite homogeneous norm. The draft spells the resulting
   physical `L²` representative plus its Fourier coefficients. For the positive
   orders used here, the spectral gap supplies `L²`; the critical inequalities
   then assert the stronger `L³`/derivative representatives. A future T10 datum
   carrier may make the distribution primary and derive this physical form.

6. **Weak multipliers.** `IsPeriodicGradient`, `IsPeriodicLambda`, and
   `IsPeriodicLaplacian` relate physical representatives by Fourier
   coefficients. This keeps the statement at the paper's distributional
   strength and avoids using totalized `fderiv` on nonsmooth fields.

7. **Product carrier.** eq:Rproduct is stated for real scalar fields, which is
   its literal multiplication form. The paper's componentwise vector/tensor
   consequence (`appendix-a-local-theory.tex:48-52`) is left as a lemma rather
   than duplicated as another target inequality field.

8. **Constants and `Prop`.** Lean forbids data-valued projections from a
   `Prop`-valued structure. Therefore the real constants live in
   `MeanZeroSobolevCalculusConstants`, and
   `MeanZeroSobolevCalculusAPI K : Prop` is parameterized by that explicit
   bundle. This preserves the requested `Prop` API and the required quantifier
   order. A theorem asserting the node would have type
   `∃ K, MeanZeroSobolevCalculusAPI K`.

9. **Scope.** The derived `H^k` algebra estimate, tensor tame estimate,
   product-difference estimate, and the general inhomogeneous `H¹ → L⁶`
   statement in Lemma A.1 are not separate T12-row targets and are not API
   fields. The three displayed homogeneous consequences are fields; the more
   general `a ∈ {1/2,1}` embedding pair is their proof source.

## Ambiguities for reconciliation

- T10 is not registered yet. Its final names and whether its primary carrier is
  a raw coefficient sequence, a weighted `lp` datum, or a physical-field/datum
  pair must replace the local copies verbatim through checked bridges.
- `torusLift`/`periodicTorusMeasure` are reused from the present local bridge.
  T10 must confirm that this is the paper's volume-one Haar normalization.
- The paper says “periodic distributions”; the planned physical layer says
  periodic fields on `R³`. Draft A uses an actual `L²` representative. If T10
  registers a distribution carrier, the critical fields should quantify the
  datum first and existentially produce the physical `L^p` representative.
- `‖v‖∞` is taken as essential supremum, matching the registered Section 4
  consumer. A pointwise continuous-representative bound may also be useful for
  classical solutions, but it would be a derived interface, not another paper
  clause.
- The paper reuses the letter `C` across derived estimates. Draft A uses
  separate constants, which is logically equivalent after taking their
  maximum and makes dependencies visible.
- The gradient-`L⁶` inequality does not intrinsically require the zero mode of
  `v`, since derivatives kill constants. T12's task card calls all listed
  critical bounds “mean-zero T³ bounds”, and its consumer applies it to the
  mean-zero field, so Draft A keeps the hypothesis.
- `spectralGap` is exposed for every `s ≥ 0`, following
  `02-preliminaries.tex:52-54` (“at each fixed order”). Appendix B itself only
  needs `s = 1/2, 1`, while the continuation step also needs order two.

## Needs a lemma

1. T10 bridges identifying its frequency, coefficient `lp`, physical
   periodicity, Fourier coefficient, Sobolev datum, homogeneous datum, and
   mean-zero definitions with the local copies in `DraftA.lean`.
2. Integrability and Fourier uniqueness on the volume-one torus: two `L¹`
   periodic representatives with all coefficients equal agree almost
   everywhere. This justifies the representative infima for `∇`, `Λ`, and `Δ`.
3. Parseval/Plancherel for vector-valued physical fields and the `PiLp 2`
   component norm, including the exact `2π` normalization.
4. The weight identities for coordinate derivatives, `Λ`, and `Δ`, plus
   existence of their physical representatives at the displayed exponents.
5. The spectral arithmetic
   `(1 + 4π²|k|²)^s ≤ (1 + (2π)⁻²)^s(4π²|k|²)^s` for `k ≠ 0`, followed by the
   weighted-`lp` norm comparison.
6. The order-two specialization identifying the homogeneous order-two datum
   norm with the physical `L²` norm of `Δv`; this yields `hTwo_le_laplacian`.
7. The torus Fourier convolution formula and weighted convolution estimate for
   eq:Rproduct, including closure of the physical product in `H^m`.
8. Weighted `ℓ² → ℓ¹` at order two and Fourier-series reconstruction to prove
   the essential-supremum bound without a finite-frequency cutoff.
9. Uniform compact-torus Sobolev embeddings at orders `1/2` and `1`, or an
   equivalent coefficient-side proof. Constants must be independent of
   frequency support; the finite-mode `PeriodicCriticalBridge` cannot discharge
   this item.
10. Componentwise assembly lemmas deriving scalar-times-vector, tensor, and
    gradient forms of eq:Rproduct from `tameProduct` when T11/T20 consumers need
    them.

## Section 4 counterparts on `R³`

| T12 role | Section 4 module / contract |
|---|---|
| eq:Rproduct | `verification/Contracts/V1/TameProduct.lean`, `TameProductAPI.tameProductScalar` (and its componentwise `tameProductVector`/tensor consequences) |
| `H² → L∞` | `verification/Contracts/V1/BoundedRepresentative.lean`, `BoundedRep.BoundedRepresentativeAPI.eLpNormTop_le` (plus `supNorm_le` for the continuous representative) |
| `Ḣ¹ᐟ² → L³` | `verification/Contracts/V2/GradientL6.lean`, `GradientL6V2API.velocityCriticalL3` |
| `‖∇v‖₆ ≤ C‖Δv‖₂` | `verification/Contracts/V1/GradientL6.lean`, `GradientL6API.gradientLSix`; its auxiliary Plancherel identity is `hessianLaplacianIdentity` |
| Datum-form homogeneous norm used by the critical clauses | `verification/Contracts/V1/HomogeneousNorm.lean`, `HomogeneousNorm.dotHomogeneousENorm` |
| `‖∇v‖₃ + ‖Λv‖₃ ≤ C‖v‖Ḣ³ᐟ²` | Part of the A05 paper/specification family but not a field of the focused registered V1/V2 contracts above |
| Mean-zero spectral gap and `‖v‖H² ≤ C‖Δv‖₂` | No whole-space counterpart: low frequency prevents these inequalities on `R³` |
