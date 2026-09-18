# T12 reconciled comparison

This file merges the independent lane-269 draft A and lane-270 draft B under
the binding decisions in `research/T12/RECONCILIATION.md`.  The accepted
statement is `research/T12/Spec.lean`; the two drafts and their original
comparisons/reports are retained verbatim for provenance.

## Paper clause → Lean field, provenance, and ruling

| Paper clause | Reconciled Lean field | Draft A | Draft B | Binding ruling |
|---|---|---|---|---|
| `appendix-a-local-theory.tex:8-11`, periodic scalar `eq:Rproduct` for every integer `m ≥ 2` | `tameProduct` | Same scalar inequality, named `tameProduct`; constant `K.Cproduct m`; separate membership hypotheses | Same scalar inequality and name; constant `K.product m`; same quantifier order | Keep the scalar display and A's constant name, but put `Cproduct` and `Cproduct_pos` first in the single Type-valued API.  Use the amended T10 data vocabulary.  No mean-zero hypothesis. |
| `appendix-a-local-theory.tex:8-12`, `H²(T³) ↪ L∞(T³)` | `boundedRepresentative` | Essential-supremum vector norm via `torusVectorENorm`; no mean zero | Essential-supremum vector norm via generic `periodicLpENorm`; no mean zero | Keep B's one generic `periodicLpENorm`, A's `Cinfty` name, and the literal absence of mean zero.  The pointwise representative bound remains a derived interface. |
| `appendix-b-embeddings.tex:20-22,26-29`, mean-zero `Ḣ¹ᐟ²(T³) ↪ L³(T³)` | `velocityCriticalL3` | Periodicity, `L²`, coefficient mean zero, and finite norm as separate hypotheses | Bundled `MemPeriodicHomogeneous (1 / 2) v` | Keep B's bundled shape, but replace coefficient mean zero with T10's physical `IsMeanZeroT` inside the bundle.  Use `CcriticalHalf`. |
| `appendix-b-embeddings.tex:8-9,97`, existence of the physical `Λv` representative used by the derivative display | `lambda_exists` | No existence field; `Λ` was totalized by an infimum over witnesses | No existence field; the next inequality accepted an `Lv`, so it could be vacuous if none existed | Add the honest existence obligation `SmoothPeriodicT v → ∃ Lv, IsPeriodicLambda v Lv`.  This is not a placeholder and closes B's vacuity gap. |
| `appendix-a-local-theory.tex:22-26` and `appendix-b-embeddings.tex:26-31`, `‖∇v‖₃ + ‖Λv‖₃ ≤ C‖v‖Ḣ³ᐟ²` | `gradientLambdaCriticalL3` | One displayed sum, but gradient and Lambda norms were infima over multiplier witnesses | One displayed sum over a chosen smooth `Lv`; classical gradient | Keep B's witness-as-argument and classical registered derivative spelling, guarded by the new `lambda_exists`; use A's `CcriticalThreeHalves` name. |
| `appendix-b-embeddings.tex:26-32`, used at `03-torus.tex:467-477`, `‖∇v‖₆ ≤ C‖Δv‖₂` | `gradientLSix` | Named `gradientL6`; multiplier-witness gradient/Laplacian; mean zero | Named `gradientLSix`; classical gradient/Laplacian; mean zero | Keep B's name and the token-identical `Contracts/V1/GradientL6.lean` definitions of `lift`, `gradientTensor`, and `laplacian`.  Retain paper-literal mean zero, though it is redundant.  Use `Csix`. |
| `03-torus.tex:490-500`, `‖v‖H² ≤ C‖Δv‖₂` | `hTwo_le_laplacian` | Multiplier-witness Laplacian; mean zero | Classical Laplacian; mean zero | Keep B's classical derivative layer and the essential physical mean-zero hypothesis; use `CHtwo`. |
| `02-preliminaries.tex:50-54` and `appendix-b-embeddings.tex:85-90`, spectral-gap direction `H^s ≤ C_s Ḣ^s` | `spectralGap` | Every `s ≥ 0`; separate periodicity/mean-zero/finiteness hypotheses; guarded `Cgap_pos` | Every `s ≥ 0`; bundled homogeneous membership; unguarded positivity | Keep B's bundled field shape, A's `Cgap` name, and A's exact positivity guard `∀ s, 0 ≤ s → 0 < Cgap s`. |
| `02-preliminaries.tex:50-54`, converse direction in the asserted norm equivalence | `homogeneous_le_sobolev` | Absent | Absent | Add the constant-one converse `Ḣ^s ≤ H^s` for `s ≥ 0` and `MemPeriodicHomogeneous s v`.  Without it the API states only half of the paper's equivalence. |

The resulting API has nine theorem clauses in exactly the table order.  Its
seven constants and seven positivity fields precede those clauses as data of
one `structure MeanZeroSobolevCalculusAPI where`; there is no separate constants
record and no proposition-valued API wrapper.

## Reconciled representation choices

| Topic | Draft A | Draft B | Ruling implemented in `Spec.lean` |
|---|---|---|---|
| T10 data layer | Local copies importing `NSFormalization.Paper1`; datum omitted periodicity and integrability | Local copies importing `NavierStokes.PeriodicIntegration`; datum used `UnitPeriods` and `MemLp 2` | Copy the selected post-amendment T10 declarations verbatim, including `Integrable (torusLift z) periodicTorusMeasure`; import no implementation module. |
| Scalar datum | `IsPeriodicScalarSobolevDatum` over raw scalar `lp` | Same role and local name | New `IsPeriodicScalarDatum` and `periodicScalarSobolevENorm`, spelled as the exact scalar mirrors of T10's vector pair, including periodicity and Haar integrability. |
| Mean zero | Vanishing component coefficients at `k = 0` | Same, plus a physical mean-zero part | T10's physical `IsMeanZeroT z : meanT z = 0` in every relevant hypothesis. |
| Torus `L^p` | Separate scalar and vector definitions | One generic `periodicLpENorm` | Keep B's generic definition, against normalized Haar measure. |
| `∇` and `Δ` | Fourier witness predicates and infima over witnesses | Classical derivatives, locally written with `fderiv` | Use `lift`, `gradientTensor`, and `laplacian` token-for-token from `Contracts/V1/GradientL6.lean`; three `example ... := rfl` checks pin the copies. |
| `Λ` | Witness predicate plus infimum norm | Chosen smooth physical witness | Keep B's chosen witness, respelled using T10 coefficients, and add `lambda_exists`. |
| Constants/API packaging | Constants record plus `API (K) : Prop` | Constants record plus `API (K) : Prop` | One Type-valued structure with constants first, matching the registered Section 4 API pattern. |
| Completed-density abbreviations | Not part of either T12 draft | Not part of either T12 draft | The lane brief explicitly requested both registered abbreviation checks; `Spec.lean` verifies by `rfl` that `CompletedDense` and `CompletedDenseHomogeneous` unfold to the corresponding `CompletedDenseVia` predicates.  They do not add API clauses. |

## Proof dependencies

Needs a lemma (union of both drafts, deduped): (1) T10 bridges for every copied declaration, plus `rfl` bridges once `T01.torus_data` is registered; (2) `L¹`-Fourier uniqueness on the unit-volume torus (two integrable periodic fields with equal coefficients agree a.e.) and the reconstruction/measurability bridges `physical ↔ torusLift ↔ eLpNorm`/`MemLp`; (3) vector Parseval: the `WithLp 2` datum norm equals `01-introduction.tex:103`'s sum of squared component norms (T10's `parseval_forward`/`parseval_backward` are the scalar input); (4) Fourier-multiplier identities for `∂_j`, `Λ`, `Δ` on smooth periodic fields, including zero-mode preservation, and existence of the `Λ` representative (`lambda_exists`); (5) the spectral-gap weight inequality `(1+4π²|k|²)^a ≤ (1+(2π)^{-2})^a (2π|k|)^{2a}` for `k ≠ 0` (`appendix-b-embeddings.tex:87-88`) summed in `lp`, uniformly in the field and its frequency support; (6) `‖Δv‖_{L²} = ‖v‖_{Ḣ²}` and the order-two Poincaré/spectral identity ⇒ `hTwo_le_laplacian`; (7) the Hessian–Laplacian Parseval identity (torus counterpart of `GradientL6API.hessianLaplacianIdentity`) plus mean-zero `H¹ ↪ L⁶` ⇒ `gradientLSix`; (8) torus Fourier convolution + weighted convolution/Young estimate + closure of `H^m(T³)` under products ⇒ `tameProduct`; (9) weighted `ℓ² → ℓ¹` at order two, i.e. `Σ_k (1+4π²|k|²)^{-2} < ∞` by dyadic shells (`appendix-a-local-theory.tex:44-47`), plus absolute Fourier convergence ⇒ `boundedRepresentative` without a frequency cutoff; (10) a **genuinely uniform** mean-zero `Ḣ^{1/2}(T³) ↪ L³(T³)` and its `a = 1` companion — `PeriodicFiniteCriticalInterface.lean`, `PeriodicCriticalBridge.lean`, `PeriodicCompactSobolevL6.lean` all retain a finite-mode or compact-periodization loss and cannot discharge it; (11) componentwise assembly: scalar↔vector component norm comparison and the `a = 1/2` embedding applied to each `∂_j v`, yielding the A03-style derived interfaces `tameProductVector` / `scalarSobolevENorm_component_le` / `sobolevENorm_le_sum_components` and the pointwise `supNorm_le` half of `H² ↪ L^∞` that T18 consumes.

## Open questions for the owner

1. The lane brief contains the R46 convention `q : ℝ≥0∞`, `(q = 1 ∨ q = 2)`,
   threshold `criticalOrder q.toReal`, and references to the R42 insertion
   records.  T12's binding reconciliation has no time exponent, density, or
   insertion-family clause; `research/T10/REPORT_277.md` also identifies this as
   an R46 template fragment.  The spec therefore adds no unrelated tenth field.
   The owner may wish to remove that fragment from future T12 task renderings.
2. No mathematical statement ambiguity remains after the reconciliation.  Once
   `T01.torus_data` is registered, replace the temporary T10 copy by the public
   contract import and add the reconciliation's listed `rfl` bridges there.

## Status — lane 341 (2026-09-18)

Lane 341 proved `boundedRepresentative` (`linftyConst`), `hTwo_le_laplacian` (`hTwoConst = 1 + 1/(4π²)`) and `lambda_exists` (`lambdaField`) in `Section3/T12/FourierEmbeddings.lean` (probe `fourier_embeddings_closes.lean`, report `REPORT_341.md`); still open in the T12 API (despite Section 4 analogues): `velocityCriticalL3`, `gradientLambdaCriticalL3`, `gradientLSix` (and `tameProduct`, lane 342).
