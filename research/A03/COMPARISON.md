# A03 — source-to-target comparison for `research/A03/Spec.lean`

Task `collaboration/tasks/A03.md`; graph node `A03`
(`formalization/blueprint/DEPENDENCY_GRAPH.md:214-223`). Target: Lemma A.1
(`lem:calculus`, `paper/sections/appendix-a-local-theory.tex:7-27`) on `R³`, in
the form Theorem 4.2 (`thm:Rinsert`, `paper/sections/04-whole-space.tex:31-46`),
A04 (`eq:Rhigh`, `appendix-a-local-theory.tex:132-137`) and `prop:local`
(`:117-125`) consume it.

All Lean paths are relative to the worktree root. Line numbers are of the
declaration keyword.

---

## 0. Every use of Lemma A.1 that Section 4 / Appendix A makes on `R³`

| # | site | clause | field it is applied to | constant |
|---|---|---|---|---|
| 1 | `04-whole-space.tex:53` | `eq:Rproduct` 2nd clause, `‖v‖_∞ ≤ C‖v‖_{H²}` | the smooth velocity slice `u_ε(t)`, real 3-vector, `H^∞` | universal `C` |
| 2 | `appendix-a-local-theory.tex:120-123` | same, applied to derivatives | the tensor `∇u₂`, 9 entries, from `u₂ ∈ C_tH³` | universal `C` |
| 3 | `appendix-a-local-theory.tex:130-137` (`eq:Rhigh`) | `eq:Rproduct` 1st clause through `eq:tame` | `u ⊗ u`, 3×3 tensor, `H^∞` | `C_m`, integer `m ≥ 3` |
| 4 | `paper/originals/local/paper_3_whole_space.tex:157,192` | product **difference** bound | `u⊗u − v⊗v` | `C_k`, integer `k ≥ 3` |
| 5 | `03-torus.tex:426`, `paper/originals/local/paper_1_theory.tex:955` | Lemma A.1 + Hölder | torus | out of scope (Section 3 deferred) |
| 6 | `appendix-a-local-theory.tex:20,22-26` | `H¹ ↪ L⁶`, `eq:embeddings` | — | **A05's**, `research/A05/Spec.lean` |

Constants: the manuscript writes `C_m`, `C_k`, `C`. The Fourier proof
(`appendix-a-local-theory.tex:33-47`) produces them from
`⟨ξ⟩^m ≤ C_m(⟨η⟩^m + ⟨ξ−η⟩^m)` and `∫⟨ξ⟩^{-4}dξ < ∞`, so they depend only on
the integer order and the fixed domain — never on the field, its support, or
its frequency support. In `Spec.lean` they are structure fields, which is that
quantifier order. This is the task's "with constants independent of support".

Note the mismatch between the task card's paraphrase and the manuscript: the
card says "products of an H^k field with an L^∞∩H^k field", the classical Moser
shape. `eq:Rproduct` does **not** use `L^∞` as the low norm — it uses `H²`, and
its own proof note (`:29-31`) says the `H²` low norm and the `H²↪L^∞` embedding
are two separate outputs of the same Cauchy–Schwarz. `Spec.lean` states the
manuscript's `H²` version; no `L^∞ ∩ H^k` estimate is anywhere in Section 4 or
Appendix A, and none is specified.

---

## 1. Field-by-field comparison

`Spec.lean` field | paper location | existing declaration (name, file:line, hypotheses, scalar vs vector, convention) or gap | mismatch
---|---|---|---
`C`, `C_pos` | `appendix-a-local-theory.tex:10-11` | Explicit numeric candidate exists: `NSFormalization.Paper3.sobolevTameConstant` (`formalization/NSFormalization/Paper3/CompleteTameProduct.lean:12`, `= 2^{m-1}·besselConstant`), with `sobolevTameConstant_nonneg` (`:15`); `NSFormalization.Source.BesselH2Fourier.besselConstant` (`Source/BesselH2Fourier.lean:39`, `= (∫(1+‖ξ‖²)^{-2})^{1/2}`, i.e. literally the manuscript's `∫⟨ξ⟩^{-4}dξ`). Angular transport multiplies it by `frequencyUnit^{2m+2} = (2π)^{2m+2}` (`Paper3/AngularTameProduct.lean:76`) | Only the *nonnegativity* is proved in tree, not positivity; `Spec.lean` asks `0 < C m`, which for `besselConstant` is a one-line `Real.rpow_pos` on a positive integral. Kept opaque so consumers never depend on the value.
`Calg`, `Calg_pos`, `Ctame`, `Ctame_pos` | `:16`, `:17-18` | No in-tree declaration; both are corollaries of `sobolevTameConstant` and order lowering (`Paper3/SobolevOrderLowering.lean:39`). Vendor analogue: `EulerOrdinarySobolev.h3ProductConstant` (`vendor/NavierStokesAndEuler/Euler/OrdinaryH3Products.lean:16`) | Separate fields because the manuscript derives them; nothing forces `Calg = C` or `Ctame = C`.
`Cinfty`, `Cinfty_pos` | `:12` | `Source.BesselH2Fourier.besselConstant` (`Source/BesselH2Fourier.lean:39`) is exactly this constant in the cycles convention; the angular one is `(2π)²·besselConstant` via `cyclesToAngular_symm_norm_le` (`Paper3/AngularTameProduct.lean:20`). Fourier-free alternative: `EulerSmoothSobolev.smoothEmbeddingConstant` (`vendor/NavierStokesAndEuler/Euler/EulerProof.lean:8227`) | Two independent constants for the same inequality exist in tree (Fourier and jet routes). Choosing one is unit U4 below.
`componentSobolevENorm` | `01-introduction.tex:103` "For vectors and tensors we sum the squared component norms" | `NSFormalization.Source.PhysicalIntegerSobolev.norm_vectorSobolevDatum_sq` (`Source/PhysicalIntegerSobolev.lean:45`) is exactly this identity — `‖vectorSobolevDatum n A‖² = ∑_i ‖integerSobolevDatum n (componentField i A)‖²` — proved by `PiLp.norm_sq_eq_of_L2`. `Data.RealVectorSobolev s = Product (Fin 3) (RealSobolevHilbert s)` (`Paper3/RealVectorPositiveDensity.lean:15`) with `Product = PiLp 2` (`Source/FiniteHilbertBochner.lean:11`) | Present as an identity of *data*; the clause needed is the identity of the two **infima over data of a physical field**, which needs datum uniqueness (D01 unit **L1**). Cycles vs angular: `norm_vectorSobolevDatum_sq` is stated for `sobolevRealization`; the angular counterpart is `cyclesToAngularRealVector` (`Paper3/AngularRealVectorBochner.lean:15`), whose norm comparison `cyclesToAngularRealVector_norm_le` (`:24`) is an inequality with `(2π)^{|s|}`, not an isometry, so the *identity* must go through the coordinatewise equivalence `cyclesToAngularReal`, not through that bound.
`memHInfty_memHm`, `memHInfty_component`, `memHInfty_partialDeriv` | `02-preliminaries.tex:12` eq:Rinitial; `:29-30` | `Contracts/V1/Data.lean:495` `MemHInfty` already gives `ContDiff` + an `H^m` datum at every `m`. Physical `L²` membership and the `SmoothL2Field` packaging are `EulerLpTranslation.SmoothL2Field` (`vendor/.../Euler/LpSmoothField.lean:31`) with `SmoothL2Field.memLp` (`:38`), and the datum construction `Source.PhysicalIntegerSobolev.vectorSobolevDatum` (`Source/PhysicalIntegerSobolev.lean:42`) with `vectorSobolevDatum_pairing` (`:52`) — the physical-field-to-datum bridge, hypothesis `A : SmoothL2Field Space`, real vector, **cycles** convention. `componentField` (`:32`) is the component extraction | **Booked as D01 unit L2** (`research/D01/RECONCILIATION.md:153`), which records the `⟸` direction (datum form ⟹ jet form / `SmoothL2Field`) as a **gap** at non-compact data: "only `Paper3.realCompactSobolevTimeSlice` (`RealPositiveDensity.lean:54`) currently produces data, and only for compact smooth input". A03 consumes L2; it does not re-prove it. `memHInfty_partialDeriv` additionally needs closure of the class under `∂_j`, which `SmoothL2Field.derivative` (`Euler/LpSmoothField.lean:49`) supplies on the jet side.
`gradientSobolevENorm_le` | `01-introduction.tex:94-95` with `∑_j\|ξ_j\|² = \|ξ\|²`; used at `appendix-a-local-theory.tex:122-123` and `:134` | `Paper3.sobolevDirectionalDerivative` (`Paper3/SobolevDirectionalDerivative.lean:54`, `SobolevHilbert s →L SobolevHilbert (s−1)`, symbol `2πi⟨ξ,a⟩⟨ξ⟩^{-1}` at `:10`), `sobolevDirectionalDerivative_norm_le` (`:67`), `sobolevRealization_directionalDerivative` (`:120`, realizes the genuine distributional `∂_a`); `Source.AngularGradientIdentity.angular_partial_norm_sq` (`Source/AngularGradientIdentity.lean:45`) and `vectorAngularSobolev_succ` (`:92`) | The derivative-on-data ↔ derivative-on-distribution bridge is complete and hypothesis-free, but the symbol carries a `2π` (cycles). `AngularGradientIdentity`'s statements require `HasCompactSupport`, which must be removed for a general `H^∞` field — the same adaptation `research/A05/COMPARISON.md` flags for `dotThreeHalvesLeGradientSobolev`. Both contracts must land the same quantity; they do (`(∑_j‖∂_jv‖²_{H^s})^{1/2}`).
`boundedRepresentative` | `appendix-a-local-theory.tex:12`, `:49-50` ("Absolute Fourier convergence also proves the `L^∞` estimate") | **The strongest match in the deliverable.** `Paper3.sobolevBoundedRepresentative2` (`Paper3/SobolevBoundedRepresentative.lean:20`, `SobolevHilbert 2 →L[ℝ] BoundedContinuousFunction Space ℂ`) with `sobolevBoundedRepresentative2_norm_le` (`:24`, `‖·‖ ≤ besselConstant·‖h‖`); the all-orders version `sobolevBoundedRepresentative` (`:34`) and `sobolevBoundedRepresentative_norm_le` (`:38`); `sobolevRealization_boundedRepresentative` (`:96`), which says the representative *is* the distribution, tested against every Schwartz `θ`; the angular transport `Paper3.angularBoundedRepresentative` (`Paper3/AngularTameProduct.lean:141`) with `angularRealization_boundedRepresentative` (`:146`). Schwartz-core input: `Source.BesselH2Fourier.schwartz_pointwise_bound` (`Source/BesselH2Fourier.lean:99`) and `schwartz_fourier_integral_bound` (`:78`) | Complete, on **complete scalar `ℂ` data**, valued in `BoundedContinuousFunction`, with an `ℝ`-valued sup norm. Four mismatches, all packaging: (i) scalar, not real `Fin 3`-vector; (ii) the input is a datum, not a physical `SpatialField`; (iii) the output is a `BoundedContinuousFunction`, and the statement that it agrees a.e. with the original physical field is exactly what `sobolevRealization_boundedRepresentative` gives *distributionally* and not yet a.e.; (iv) `ℝ` sup norm vs `ℝ≥0∞`.
`eLpNormTop_le` | `:12`; `research/section4/STATEMENTS.md:261-262` (`⟪D01:normLinfty⟫`) | Nothing in tree states `eLpNorm z ⊤ volume ≤ …`. Assembly from `boundedRepresentative` + `eLpNorm_le_of_ae_bound` (Mathlib) | Gap, but derivative of the previous row.
`supNorm_le_of_continuous` | `04-whole-space.tex:53` (the decisive sentence of Theorem 4.2) | Gap on the D01 carrier. Direct Fourier-free alternative already proved for the **jet** norm: `EulerSmoothSobolev.smooth_pointwise_le_H2` (`vendor/NavierStokesAndEuler/Euler/EulerProof.lean:8237`) — for any complete `F`, `ContDiff ℝ ∞ f` and `∀ j ≤ 2, MemLp (iteratedFDeriv ℝ j f) 2 volume` give `‖f x‖ ≤ smoothEmbeddingConstant · tensorSobolevNorm 2 f` at **every** `x`, with **no support hypothesis**; the real-vector wrapper is `EulerOrdinarySobolev.real_pointwise_H2` (`Euler/OrdinaryWordBounds.lean:67`) and the word-bound form `wordBound_pointwise` (`:76`) | Two viable routes. The Euler route delivers the everywhere-pointwise statement on the real vector field directly and is Fourier-free (no normalization risk), but its right-hand side is `tensorSobolevNorm 2 f = ∑_{j≤2}‖iteratedFDeriv ℝ j f‖₂` (`EulerProof.lean:8091`), the **jet** norm, so it needs the jet↔datum norm comparison (D01 unit **L2**) and pays a constant. The Fourier route lands the datum norm directly but must transport the `BoundedContinuousFunction` back to the physical field. `Spec.lean` is written so either route discharges it.
`gradientSupNorm_le` | `appendix-a-local-theory.tex:120-123` | Gap. Ingredients: the previous row applied to each `∂_jv`, plus the Frobenius reassembly. Assembly precedent for `Fin 3` sums: `Source.VectorForceNorms.eLpNorm_vector_le_sum` (`Source/VectorForceNorms.lean:47`); the codomain here is `WithLp 2 (Fin 3 → Space)`, the tensor of `Data.spatialGradient` (`Contracts/V1/Data.lean:453`) | Purely structural once the scalar clause is in hand. Note the Euler route gives this one for free at `E := Space →L[ℝ] Space` since `smooth_pointwise_le_H2` is generic in the codomain.
`tameProductScalar` | `appendix-a-local-theory.tex:9-11` eq:Rproduct, first clause | **The core reusable asset.** `Source.FourierTameProduct.schwartz_tame_product` (`Source/FourierTameProduct.lean:150`): for every `m : ℕ` and Schwartz `φ, ψ`, `‖weightedFourierLp m (φψ)‖ ≤ (2^{m-1}·besselConstant)(‖weightedFourierLp 2 ψ‖‖weightedFourierLp m φ‖ + ‖weightedFourierLp 2 φ‖‖weightedFourierLp m ψ‖)` — literally `eq:Rproduct`, no support hypothesis, constant order-only. Its proof runs through OpenAI's Young convolution: `NavierStokes.R3ConvolutionYoung.scalarConvolution` (`vendor/NavierStokesAndEuler/NavierStokes/R3ConvolutionYoung.lean:141`) and `Source.YoungConvolution.integrable_convolution_one_two` (`Source/YoungConvolution.lean:89`), with the weight split `besselWeight_split` (`Source/FourierTameProduct.lean:68`) = the manuscript's `⟨ξ⟩^m ≤ C_m(⟨η⟩^m + ⟨ξ−η⟩^m)` at `:33-35`. Extended off the Schwartz core to **all complete data** by `Paper3.sobolevProduct` (`Paper3/CompleteTameProduct.lean:101`) with `sobolevProduct_tame_bound` (`:128`), `sobolevProduct_opNorm_le` (`:120`) and `sobolevProduct_weightedFourierLp` (`:113`). Angular version: `Paper3.angularProduct` (`Paper3/AngularTameProduct.lean:61`), `angularProduct_tame_bound` (`:76`), `angularProduct_datum` (`:131`) | Scalar `ℂ`, datum-level. Three mismatches: (i) the low factor is `‖sobolevOrderLowering m 2 _ h‖`, which `sobolevRealization_orderLowering` (`Paper3/SobolevOrderLowering.lean:78`) / `angularRealization_orderLowering` (`Paper3/AngularTameProduct.lean:51`) identify as the `H²` norm of the **same physical field** — so this is already the right quantity, only spelled through the operator; (ii) `ℝ` vs `ℝ≥0∞`; (iii) **reality**: `angularProduct` acts on `FourierData = Lp ℂ 2 volume`, not on `RealSobolevHilbert s = realSubspace s` (`Source/RealSobolev.lean:118`); nothing in tree says the completed product of two conjugate-reflection-symmetric data is again symmetric. That is the one genuinely new (easy) lemma in this row.
`tameProductVector` | `:9-11` with `:50` "applies componentwise to vectors and tensors" | Gap as a statement; componentwise assembly of the previous row through `componentSobolevENorm`. Precedent for the assembly: `Paper3.cyclesToAngularRealVector` (`Paper3/AngularRealVectorBochner.lean:15`), `Source.PhysicalIntegerSobolev.vectorSobolevDatum` (`Source/PhysicalIntegerSobolev.lean:42`) | The dimensional factor from `∑_i` is absorbed into `C m`, which the manuscript permits.
`algebraProductScalar` | `:14-16` eq:algebra | Gap. Immediate from `tameProductScalar` plus `‖·‖_{H²} ≤ ‖·‖_{H^k}`, which is `Paper3.sobolevOrderLowering_norm_le` (`Paper3/SobolevOrderLowering.lean:39`) — and is D01 unit **L5** on the physical carrier (`research/D01/RECONCILIATION.md:156`) | No new analysis.
`outerProductTame` | `:17-18` eq:tame | Gap on this carrier. **Closest existing statement anywhere:** `EulerOrdinarySobolev.tame_outer_product` (`vendor/NavierStokesAndEuler/Euler/OrdinaryTameProduct.lean:83`) — `‖(wordField (coordinateProduct i (wordField A w) (wordField B v)) a).toLp‖ ≤ 2^n·h3ProductConstant·M·N` with hypotheses `WordBound 3 M A`, `WordBound m N A`, i.e. a genuine tame outer-product bound with the **low norm at order three**, real vector `SmoothL2Field Space`, no Fourier at all. Supporting: `coordinateProduct_tame` (`:63`), `gradient_outer_product` (`Euler/OrdinaryH3Products.lean:133`), `coordinateProduct` (`Euler/OrdinaryFieldAlgebra.lean:109`) | Three mismatches: the low norm is `H³` (via `WordBound 3`), not the manuscript's `H²`; the carrier is the word-jet `SmoothL2Field` scale, not the datum scale; and the norms are sup-over-words (`wordMaximum`, `Euler/OrdinaryWordInterpolation.lean:17`) rather than the Euclidean `PiLp 2` assembly. Useful as a cross-check on the shape, **not** as a discharge — `eq:Rhigh`'s `‖u‖_{H²}` factor is what makes the continuation criterion an `H²` criterion, so lowering it to `H³` would break Theorem 4.2's consumer A04.
`outerProductDifference` | `:51-52`; `paper/originals/local/paper_3_whole_space.tex:157,192` | Gap. Factorization `u⊗u − v⊗v = (u−v)⊗u + v⊗(u−v)` plus `algebraProductScalar`; no new analysis. Bilinearity of the completed product is available: `Paper3.sobolevProductLeftLinear` (`Paper3/CompleteTameProduct.lean:73`), `sobolevProduct` is a `→L[ℝ] … →L[ℝ]` | Purely algebraic given the algebra bound.
`advectionTame` | `01-introduction.tex:83` eq:NS, `02-preliminaries.tex:81` eq:projected; estimate by `:9-11` with `:50` | **Proved, but only at one order and non-tame, in HeliCorgi:** `MNS2.norm_r3SchwartzToHsCLM_two_convection_le_H3` (`vendor/HeliCorgi/Formal/R3SchwartzConvectionSobolevEstimate.lean:89`), `‖(u·∇)v‖_{H²} ≤ r3SchwartzConvectionFullH3Constant·‖u‖_{H³}‖v‖_{H³}` with an explicit constant (`:81`), packaged as `r3SchwartzConvectionSobolevEstimate_three` (`:114`) discharging the gate proposition `R3SchwartzConvectionSobolevEstimate` (`Formal/R3SchwartzSobolevCore.lean:94`), and extended off the Schwartz core by `r3ConvectionH3ToH2` (`Formal/R3SobolevConvectionExtension.lean:138`). Frequency inputs: `r3H2BesselWeight_le_additive_split` (`Formal/R3H2AdditiveConvolutionWeight.lean:11`), `Formal/R3H2WeightedConvolutionKernel.lean:19`. Upstream `advection` (`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:63`) is the pinned nonlinearity; `EulerOrdinarySobolev.advectionField` (`Euler/OrdinaryFieldAlgebra.lean:118`) is the two-field version | Four mismatches: only `m = 3 → 2` (HeliCorgi's own docstring calls the general-`m` version an open "gate"), both factors at the **high** order (not tame), Schwartz/cycles carrier, and **Lean 4.32.1** — HeliCorgi is a separate toolchain, blocked by task **U05** (`CLAUDE.md`, layout table). So this row is discharged from the local `tameProductVector` route, not from HeliCorgi; HeliCorgi is a cross-check.

### Summary of the gap surface

* **Present and directly reusable, modulo packaging.** The whole tame-product
  chain at every integer `m ≥ 2`, on complete scalar data, in both conventions,
  with support-independent constants:
  `Source/FourierTameProduct.lean:150` → `Paper3/CompleteTameProduct.lean:101,128`
  → `Paper3/AngularTameProduct.lean:61,76`. The bounded representative at every
  real order `≥ 2`: `Paper3/SobolevBoundedRepresentative.lean:20,24,34,38,96` →
  `Paper3/AngularTameProduct.lean:141,146`. The order lowering that supplies the
  `H²` low factor: `Paper3/SobolevOrderLowering.lean:26,39,78`. The Young
  convolution input is OpenAI's (`R3ConvolutionYoung.lean:141`), exactly as
  `formalization/blueprint/EXTERNAL_REUSE.md:35` claims.
* **Genuinely missing.** (a) every statement about a *physical real 3-vector or
  3×3 tensor field* rather than a scalar `ℂ` datum; (b) preservation of the
  reality subspace `realSubspace` under the completed product; (c) the specific
  bilinear forms `u ⊗ u` and `(u·∇)v` and the difference bound; (d) the
  everywhere-pointwise `L^∞` statement on the physical field (as opposed to the
  `BoundedContinuousFunction` representative); (e) `ℝ≥0∞` phrasing throughout.
* **Not needed.** No new Fourier, convolution, or Young theory. No Moser
  `L^∞ ∩ H^k` estimate. No maximal function. No torus.

---

## 2. What "complete physical multiplication" is, and what remains

The task card and `EXTERNAL_REUSE.md:35` say "Reuse complete physical
multiplication and exact low-order H2 factors". The declaration meant is:

* **The product itself** — `NSFormalization.Paper3.sobolevProduct`
  (`Paper3/CompleteTameProduct.lean:101`), a genuine
  `SobolevHilbert m →L[ℝ] SobolevHilbert m →L[ℝ] SobolevHilbert m`, obtained by
  two `extendOfNorm` extensions from the Schwartz core; **not** an assumed
  bilinear map.
* **"Complete"** — it is defined on all of `SobolevHilbert m`, not on a dense
  subspace, and `sobolevProduct_tame_bound` (`:128`) holds for *all* complete
  data with the exact low-order `H²` factors `‖sobolevOrderLowering m 2 _ ·‖`,
  with no approximation premise. That is what makes the low factor "exact"
  rather than a limit of Schwartz approximants.
* **"Physical"** — `Paper3.sobolevBoundedRepresentative_product`
  (`Paper3/SobolevPhysicalProduct.lean:17`) and its pointwise form `:34` prove
  that this abstract product *is* pointwise multiplication of the bounded
  continuous representatives; `sobolevRealization_product` (`:53`) proves the
  completed product realizes the ordinary physical product against every
  Schwartz test; `sobolevProduct_tame_and_physical` (`:64`) bundles the estimate
  and the identity. The angular counterparts are
  `angularBoundedRepresentative_product` (`Paper3/AngularTameProduct.lean:153`)
  and `angularRealization_product` (`:174`).

So the scalar theory is finished, in the manuscript's own convention, with the
manuscript's own constant shape. **What remains for A03 is exactly the four
things the task card names as the deliverable and nothing else:**

1. the real-vector and 3×3-tensor assembly (`componentSobolevENorm`,
   `columnsSobolevENorm`), including reality preservation;
2. the transfer from data to physical fields of type `Data.SpatialField`, so
   that Section 4's `MemHInfty` velocity slices are in scope;
3. the two named bilinear forms `u ⊗ u`, `(u·∇)v` and the difference bound;
4. the `L^∞` clause phrased on the physical field rather than on a
   `BoundedContinuousFunction`.

None of these is a new product theory. `Spec.lean` is written so that this is
visibly true: every product clause is a statement about the literal pointwise
product of physical fields, so the "physical multiplication" identification is
part of the statement rather than a separate obligation.

---

## 3. Convention risks

* **"A finite right-hand side asserts that the left-hand side has a datum" is a
  meta-argument, not a field.** `Spec.lean`'s conventions section notes that,
  because `Data.sobolevENorm` is `⊤` when no datum exists, a product bound with
  a finite right-hand side also forces the product into `H^m` — the "closed
  under multiplication" half of `eq:Rproduct`. That reading is sound but it is
  a remark *about* the clauses; **no field of `TameProductAPI` states it**, and
  it relies on one step the structure does not supply: the junk-`0`
  totalization of `Contracts/V1/Data.lean:148-155` must be excluded on the
  **left**-hand side, which needs the product to be genuinely `L²`. That in
  turn follows from the factors being in `H^m ⊆ L^∞ ∩ L²` for `m ≥ 2` (the
  second clause of `eq:Rproduct` applied to each factor, i.e. `eLpNormTop_le`),
  and from `MemHmScalar`/`MemHmVector` on the inputs. A consumer that needs
  `MemHmScalar m (fun x => a x * b x)` as a conclusion must run that argument;
  the alternative — adding the membership to the conclusion of each product
  field — was not taken, so that each field states exactly one inequality of
  `lem:calculus` and nothing more. Whichever implementation unit discharges
  **U7** should record the derived membership lemma next to the bound.
* **Cycles vs angular.** Every product and bounded-representative theorem is
  proved for `weightedFourierLp` / `sobolevRealization`, Mathlib's cycles
  convention (`𝓕 f(ξ) = ∫e^{-2πi x·ξ}f`). The manuscript fixes the unitary
  angular transform (`01-introduction.tex:91`), which `Contracts/V1/Data.lean`
  carries through `angularRealization`. The transport exists and is exact —
  `Paper3.cyclesToAngular` (`Paper3/AngularTameProduct.lean:11`) is a
  `≃L[ℂ]`, and `angularRealization_cyclesToAngular` (`:25`) says it preserves
  the realized distribution — but it is **not an isometry**: `cyclesToAngular_norm_le`
  (`:14`) and `cyclesToAngular_symm_norm_le` (`:20`) each cost `(2π)^{|s|}`.
  Every constant therefore picks up an explicit power of `2π`. Because all
  constants in `Spec.lean` are opaque structure fields, this is bookkeeping, not
  a correctness risk — but it means the in-tree numeric values
  (`sobolevTameConstant`, `besselConstant`) are *not* the contract's `C m` and
  `Cinfty`.
* **Reality.** `Data.RealVectorSobolev s` components live in `realSubspace s`
  (`Source/RealSobolev.lean:118`), the conjugate-reflection-symmetric subspace.
  `angularProduct` is defined on the ambient `Lp ℂ 2 volume`. Stability of
  `realSubspace` under `angularProduct` is not stated anywhere; it follows from
  `realSymmetry_involutive` (`Source/RealSobolev.lean:34`) and density, but it
  is a new lemma. Flagged as the one non-mechanical step of unit U7.
* **Junk totalization.** `Data.sobolevENorm` is an infimum and
  `Contracts/V1/Data.lean:148-155` records that it returns a junk `0` on a slice
  pairing integrably with no Schwartz test. `‖z‖_∞ ≤ C‖z‖_{H²}` would then be
  *false*, not vacuous. `MemHmVector` / `MemHmScalar` add exactly the `MemLp`
  hypothesis that excludes this, and `memHInfty_memHm` says Section 4's fields
  satisfy it. This is the reason those two predicates exist and are not
  decoration.
* **Order-`3` low norms in the vendor sources.** Both `Euler/OrdinaryTameProduct.lean:83`
  and HeliCorgi's convection estimate use an `H³` low norm. Substituting either
  for `eq:tame` would turn `eq:Rhigh`'s `‖u‖_{H²}` into `‖u‖_{H³}` and thereby
  change `eq:criterion`, the continuation criterion Theorem 4.2 and A04 depend
  on. They may be used as shape cross-checks only.

---

## 4. Bounded implementation split

Ten units, sized S (a few declarations, no new analysis), M (a real adaptation
of an existing proof), L (a new analytic argument). There is no L unit: the
analysis is already in tree.

| unit | content | size | depends on | source to reuse |
|---|---|---|---|---|
| **U1** | `IsScalarSobolevDatum` ↔ `Paper3.angularDatum`; `scalarSobolevENorm s a = ‖A‖ₑ` for the unique datum `A`; `scalarSobolevENorm s a = ⊤` iff none exists | S | D01 **L1** | `Paper3.angularRealization_injective` (`Paper3/AngularFourierDilation.lean:203`), `Paper3.existsUnique_sobolev_datum` (`Paper3/SobolevHilbertModel.lean:122`), `Paper3.angularDatum` (`Paper3/AngularFourierDilation.lean:225`) |
| **U2** | `memHInfty_memHm`, `memHInfty_component`, `memHInfty_partialDeriv`: a smooth `H^∞` field is in `L²`, has an integer datum at every order, and is closed under `∂_j` | M | D01 **L2** (gap noted there) | `Source.PhysicalIntegerSobolev.vectorSobolevDatum` (`Source/PhysicalIntegerSobolev.lean:42`), `vectorSobolevDatum_pairing` (`:52`), `componentField` (`:32`), `EulerLpTranslation.SmoothL2Field.derivative` (`vendor/.../Euler/LpSmoothField.lean:49`), transport by `Paper3.cyclesToAngularRealVector` (`Paper3/AngularRealVectorBochner.lean:15`) |
| **U3** | `componentSobolevENorm`: the vector quantity is the `PiLp 2` assembly of the three scalar quantities | S | U1 | `Source.PhysicalIntegerSobolev.norm_vectorSobolevDatum_sq` (`Source/PhysicalIntegerSobolev.lean:45`), `PiLp.norm_sq_eq_of_L2` |
| **U4** | `boundedRepresentative`, `eLpNormTop_le`, `supNorm_le_of_continuous`, and the value of `Cinfty` | M | U1, U2, U3 | Fourier route: `Paper3.angularBoundedRepresentative` (`Paper3/AngularTameProduct.lean:141`), `angularRealization_boundedRepresentative` (`:146`), `Paper3.sobolevBoundedRepresentative_norm_le` (`Paper3/SobolevBoundedRepresentative.lean:38`), `Source.BesselH2Fourier.besselConstant` (`Source/BesselH2Fourier.lean:39`). Jet route: `EulerSmoothSobolev.smooth_pointwise_le_H2` (`vendor/.../Euler/EulerProof.lean:8237`), `EulerOrdinarySobolev.real_pointwise_H2` (`Euler/OrdinaryWordBounds.lean:67`) |
| **U5** | `gradientSupNorm_le`: U4 componentwise on `∂_jv`, reassembled in the Frobenius norm of `Data.spatialGradient` | S | U4 | `Source.VectorForceNorms.eLpNorm_vector_le_sum` (`Source/VectorForceNorms.lean:47`); free from the jet route, which is generic in the codomain |
| **U6** | `gradientSobolevENorm_le`: `‖∇v‖_{H^s} ≤ ‖v‖_{H^{s+1}}`, constant one | M | U3 | `Paper3.sobolevDirectionalDerivative` (`Paper3/SobolevDirectionalDerivative.lean:54`), `sobolevDirectionalDerivative_norm_le` (`:67`), `sobolevRealization_directionalDerivative` (`:120`), `Source.AngularGradientIdentity.angular_partial_norm_sq` (`Source/AngularGradientIdentity.lean:45`) — remove `HasCompactSupport`, shared with A05 |
| **U7** | `tameProductScalar`: transport `angularProduct_tame_bound` to physical scalars; includes the new lemma "`realSubspace` is stable under `angularProduct`" | M | U1, U2 | `Paper3.angularProduct_tame_bound` (`Paper3/AngularTameProduct.lean:76`), `angularProduct_datum` (`:131`), `angularRealization_product` (`:174`), `angularRealization_orderLowering` (`:51`), `Source.RealSobolev.realSymmetry_involutive` (`Source/RealSobolev.lean:34`) |
| **U8** | `tameProductVector` and `algebraProductScalar` | S | U3, U7 | `Paper3.sobolevOrderLowering_norm_le` (`Paper3/SobolevOrderLowering.lean:39`) for `‖·‖_{H²} ≤ ‖·‖_{H^k}` (D01 **L5**) |
| **U9** | `outerProductTame` and `outerProductDifference`: columns `u_j·u`, Frobenius sum, factorization | M | U8 | shape cross-check `EulerOrdinarySobolev.tame_outer_product` (`Euler/OrdinaryTameProduct.lean:83`); bilinearity from `Paper3.sobolevProduct` (`Paper3/CompleteTameProduct.lean:101`) |
| **U10** | `advectionTame`: U8 applied to `u_j·∂_jv`, summed over `j` | M | U6, U8 | shape cross-check `MNS2.norm_r3SchwartzToHsCLM_two_convection_le_H3` (`vendor/HeliCorgi/Formal/R3SchwartzConvectionSobolevEstimate.lean:89`), blocked from direct use by U05 |

Order: U1 → U3 → {U2, U6} → U4 → U5, and U7 → U8 → {U9, U10}. U1/U3 and U7 can
start in parallel.

Four S, six M, no L. The constants are opaque structure fields, so no unit has
to compute a numeric value.

**Sizing risk on U2 (reviewer's note, `research/A03/REVIEW.md`).** U2's
prerequisite is D01 unit **L2**, and L2 is *itself* an open gap:
`research/D01/RECONCILIATION.md:153` records that the direction needed here
(datum form ⟹ jet form / `SmoothL2Field`, i.e. producing a datum from a
physical field) currently has only `Paper3.realCompactSobolevTimeSlice`
(`RealPositiveDensity.lean:54`) behind it, and that "only for compact smooth
input" — whereas `X_R` fields are not compactly supported. U2 is on the
critical path for **every** physical-field clause of the contract
(`memHInfty_memHm` feeds `boundedRepresentative`, `supNorm_le_of_continuous`,
`gradientSupNorm_le`, `advectionTame`, and — through `memHInfty_component` —
the whole product chain). **If L2 stalls, U2 is an L, and the "no L unit"
claim above fails.** Nothing else in the split depends on an open prerequisite;
the second-riskiest, U6, is M only at the optimistic end, since it must remove
`HasCompactSupport` from `Source/AngularGradientIdentity.lean:82,92,108`.

---

## 5. Notes for the reviewer

1. **Missing DAG edge.** `DEPENDENCY_GRAPH.md:46-50` has `A03 → A04` and
   `A03 → T01` but no `A03 → R42`. `research/section4/STATEMENTS.md:405-410`,
   `:1321` and `:1337-1340` argue for adding it, and `Spec.lean`'s
   `supNorm_le_of_continuous` is the field that edge carries. This comparison
   does not change the graph; it records that the edge is used.
2. **A05 overlap is deliberate and disjoint.** Lemma A.1 is a shared statement
   split across two tasks. A05 owns `eq:embeddings` and `H¹ ↪ L⁶`; A03 owns
   `eq:Rproduct`, `eq:algebra`, `eq:tame`. The one quantity both contracts
   mention is `(∑_j‖∂_jv‖²_{H^s})^{1/2}` — A05's `tensorSobolevENorm`, A03's
   `gradientSobolevENorm` — and they are the same formula. If both land, one of
   the two definitions should be deleted at contract-promotion time.
3. **`Spec.lean` states no torus clause.** `lem:calculus` is stated for "either
   domain" (`appendix-a-local-theory.tex:8`). Promoting this draft to
   `Contracts/V1` should keep the whole-space restriction explicit in the
   structure name or docstring so that a later torus lane does not silently
   reuse it.
4. **`advectionTame` is not consumed by `eq:Rhigh`.** The manuscript's own
   energy identity goes through `u ⊗ u` and the divergence form. `advectionTame`
   is included because `Data.ClassicalSolutionR.momentum`
   (`Contracts/V1/Data.lean:624`) states the equation with the upstream
   `advection`, so a consumer that never converts to divergence form still needs
   it. The conversion `∇·(u⊗u) = (u·∇)u` is A01's unit **E1**
   (`research/A01/COMPARISON.md:190`) and is deliberately absent here.
5. **Two hypothesis classes, on purpose** (revision after
   `research/A03/REVIEW.md` issue 1). Clauses involving only pointwise products
   — `tameProductScalar`, `tameProductVector`, `algebraProductScalar`,
   `outerProductTame`, `outerProductDifference`, and the three
   bounded-representative clauses — are stated at `MemHmScalar`/`MemHmVector`,
   so they hold on `H^k` exactly as `eq:algebra`/`eq:tame` do and can be applied
   to two arbitrary elements of the `C([0,τ];H³)` ball that the `prop:local`
   mild contraction runs on (`appendix-a-local-theory.tex:110-116`,
   `paper/originals/local/paper_3_whole_space.tex:186-192`). Clauses whose
   statement contains a **classical** derivative — `gradientSupNorm_le` and
   `advectionTame`, both built from `Data.spatialGradient` /
   `spatialDerivative` — keep `MemHInfty`, because `MemHmVector` does not make
   `fderiv` meaningful and the bound would otherwise be a statement about a
   field that totalizes to `0` off the differentiability set. Their consumers
   are classical smooth solutions in every case. `memHInfty_memHm` is the
   bridge, so every `H^∞` instance remains derivable.
6. **`gradientSobolevENorm_le` carries a non-vacuity hypothesis**
   (`REVIEW.md` issue 4). `sobolevENorm (s + 1) v ≠ ⊤` was added rather than
   restricting `s` to `ℕ`: `MemHInfty` supplies integer data only, so at the
   half-integer orders the clause advertises for Proposition 4.4 the right-hand
   side could be `⊤` and the clause true-but-empty. The hypothesis is implied
   by `memHInfty_memHm` at every integer order, so integer consumers pay
   nothing, and restricting to `ℕ` would have made both the `s = 1/2` use and
   the stated agreement with A05's `tensorSobolevENorm` unstatable here.
