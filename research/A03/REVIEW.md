# Review of `research/A03/Spec.lean` + `COMPARISON.md` (lane 017, task A03)

**VERDICT: ACCEPT-WITH-NOTES.**

The file typechecks clean, is hygienically empty of `sorry`/`axiom`/`admit`, and all 23
fields are fully spelled-out statements about explicitly named objects. Every clause I
checked against `lem:calculus` is faithful: the orders (`m ≥ 2`, `k ≥ 3`), the inhomogeneous
`H^s` datum norm of `Contracts/V1/Data.lean:189`, the `H²` low factor (not `L^∞`, not `H³`),
the Frobenius vector/tensor convention of `01-introduction.tex:103`, and constants as
structure fields (= quantified outside every field/support/frequency support). The two
deliberate restrictions — whole space only, embeddings deferred to A05 — match the task card
and Section 4's actual needs. The scope notes (no `∇·(u⊗u) = (u·∇)u`, no monotonicity, no
torus) are correct and correctly attributed. The reuse claims are accurate on 11 of the 12
rows I spot-checked. Notes below; none blocks promotion.

## Ranked issues

| # | sev | field / location | what differs | one-line fix |
|---|---|---|---|---|
| 1 | **Med** | `outerProductDifference` (also `outerProductTame`, `advectionTame`, `gradientSupNorm_le`) | Hypothesis is `MemHInfty`, but the docstring names the `prop:local` mild contraction as consumer, and that contraction runs on the ball of `C([0,τ];H³)` (`appendix-a-local-theory.tex:110-116`; `paper/originals/local/paper_3_whole_space.tex:186-192`), whose elements are `H³`, **not** `H^∞`. A01 books this as its unit **A1** (`research/A01/COMPARISON.md:197`). As stated the clause cannot be applied to two arbitrary elements of that ball — strictly weaker than `eq:algebra`/`eq:tame`, which hold on `H^k`. | State `outerProductDifference`/`outerProductTame` at `MemHmVector k u → MemHmVector k v`; keep `memHInfty_memHm` as the bridge for the smooth consumers. |
| 2 | **Med** | `supNorm_le_of_continuous` docstring vs `eLpNormTop_le` docstring | Both claim to be the clause the missing `A03 → R42` edge carries. `research/section4/STATEMENTS.md:261-262` and `:348-350` pin `⟪D01:normLinfty⟫ = ‖·‖_{L^∞(R³)}` (ess-sup) and state R42's blowup as `limsupLeft T (normLinfty ∘ uPert) = ⊤`, so the edge is carried by `eLpNormTop_le`. `supNorm_le_of_continuous` is strictly stronger and is correctly shaped (per-slice, every `x`, right constant, right norm) — it is *sufficient*, just not the *exact* D01 clause. Its justification ("a statement about the actual pointwise values … not merely almost everywhere") overstates. | One sentence: `eLpNormTop_le` is the `R42` input; `supNorm_le_of_continuous` is the pointwise convenience for consumers holding a continuous representative. |
| 3 | Low | Conventions §, "a bound with a finite right-hand side *asserts* that the left-hand side has a datum" | True only because the product is itself `L²` (`a,b ∈ H^m`, `m ≥ 2` ⟹ `L^∞ ∩ L²`), which defeats the junk-`0` on the **left**. That step is a meta-argument, not a field. | Add the observation to the docstring, or conclude `MemHmScalar m (fun x => a x * b x)` alongside the bound. |
| 4 | Low | `gradientSobolevENorm_le` | Stated at real `s ≥ 0`, but its only admissibility hypothesis (`MemHInfty`) supplies **integer**-order data. At the half-integer orders the docstring advertises (Prop. 4.4) the RHS can be `⊤`, so the clause is true-but-vacuous. Fails safe; not wrong. | Note it, or add `sobolevENorm (s+1) v ≠ ⊤` as a hypothesis so the clause has content at `s = 1/2`. |
| 5 | Low | `Spec.lean:413` | Cites `Paper3/CompleteTameProduct.lean:100` for `sobolevProduct`; the declaration keyword is at `:101` (COMPARISON.md has it right). | `100 → 101`. |
| 6 | Low | `COMPARISON.md` `advectionTame` row and unit **U10** | `vendor/HeliCorgi/Formal/R3SchwartzConvectionSobolevEstimate.lean:92` → the decl is at **`:89`**; `r3SchwartzConvectionSobolevEstimate_three` `:115` → **`:114`**. (Header says line numbers are of the declaration keyword.) | Fix both numbers. |
| 7 | Info | `componentSobolevENorm`, `tameProductVector`, `advectionTame`, `gradientSobolevENorm_le` | Not clauses of Lemma A.1; they are true corollaries / carrier conventions added as obligations. All four are correctly labelled as such and all four are true (`|ξ_j|⟨ξ⟩^s ≤ ⟨ξ⟩^{s+1}` gives constant one; the `Fin 3` factors are absorbed into `C m`, which the manuscript permits). | none |

### Answers to the specific questions

* **Admissibility predicates.** The argument is **right**. `Contracts/V1/Data.lean:148-155` says
  verbatim that a slice pairing integrably with no Schwartz test admits `A = 0`, so
  `sobolevENorm` is a junk `0`; `‖z‖_∞ ≤ C·0` is then **false**, not vacuous, so
  `MemHmVector`/`MemHmScalar` are load-bearing, not decoration. `MemLp z 2 volume` is exactly the
  condition Data.lean names as the escape ("Schwartz times `L²` is `L¹`") and costs nothing at
  `m ≥ 2` (`H^m ⊂ L²`). It is **not the logically weakest** fix — local integrability with
  tempered growth would do, and Data.lean deliberately declined to add local integrability — so
  "minimal" holds in spirit, not strictly. The second conjunct (`≠ ⊤`) is *not* needed to defeat
  the junk (the `⊤` case is already vacuous); it is a harmless non-vacuity restriction.
* **Pointwise-product formulation.** **Faithful.** `eq:Rproduct`'s `vw` is literal multiplication
  of functions; the Spec states every product clause on physical `Space → ℝ` / `SpatialField`
  with `fun x => a x * b x` and `fun x => a x • w x`, so no "the completed product is
  multiplication" clause is owed. The cost is honestly relocated into the proof: unit **U7** must
  transport through `angularRealization_product` (`Paper3/AngularTameProduct.lean:174`), and the
  COMPARISON books it there.
* **`supNorm_le_of_continuous` shape.** Correct shape and sufficient for the `04-whole-space.tex:53`
  step (per-slice everywhere bound, `Cinfty`, `sobolevENorm 2`); see issue 2 for the caveat that
  D01's `normLinfty` is the ess-sup and `eLpNormTop_le` is the literal match. Hypotheses are
  discharged at the use site by `memHInfty_memHm` + `velocity_smooth`.
* **A05 agreement.** `lift`, `partialDeriv`, `gradientTensor` are textually identical to
  `research/A05/Spec.lean:90,96,102`, and `gradientSobolevENorm s v` unfolds to A05's
  `tensorSobolevENorm s v` = `(∑_j ‖∂_jv‖²_{H^s})^{1/2}` (`A05/Spec.lean:138`). Claim holds.
  (Aside, not A03's defect: A05's docstrings cite `Data.lean:446/497` for `spatialGradient` /
  `IsSolenoidal`; the current tree has `:453/:504`, which A03 cites correctly.)
* **Gaps (confirmed by grep).** `grep -rn --include='*.lean' 'realSubspace\|realSymmetry' … | grep -iE 'product|mul_|_mul|prod'` returns nothing outside `RealSobolev.lean:133` — **no statement of
  `realSubspace` stability under the completed product**, as claimed. `grep … 'SpatialField' … | grep -iE 'tame|outer|product'` returns nothing — **no vector/tensor tame statement on
  `Data.SpatialField`**, as claimed. Every in-tree `*tame*`/`*outer_product*` theorem is either
  scalar-`ℂ`-datum (`Paper3`/`Source`) or vendor `SmoothL2Field` word-jet.
* **Unit split.** 4 S (U1, U3, U5, U8) + 6 M (U2, U4, U6, U7, U9, U10) — arithmetic correct, and
  "no L" is defensible: I confirmed the Fourier tame product, the Young convolution input and the
  bounded representative all exist complete and support-free in tree, so nothing left is new
  analysis. **Risk:** U2's prerequisite, D01 unit **L2**, is itself recorded as a gap
  (`research/D01/RECONCILIATION.md:153`, "only for compact smooth input"), and U2 is on the
  critical path for every physical-field clause — if L2 stalls, U2 is an L. U6 (removing
  `HasCompactSupport` from `AngularGradientIdentity.lean:82,92,108`) is M at the optimistic end.
* **DAG remark.** Consistent. `DEPENDENCY_GRAPH.md:46-50,82` has `D01/U04/A05 → A03 → A04, T01`
  and no `A03 → R42`. `STATEMENTS.md` v2 (`:314`, `:405-410`, `:1120-1122`, `:1321`, `:1337-1340`)
  argues for the edge, and `research/section4/REVIEW.md:38-49,181-185` marks item 2
  **CONFIRMED** and recommends adding it. A03 records the edge without changing the graph —
  correct division of labour.

## Reuse spot-check (12 rows)

| claimed | verdict |
|---|---|
| `Source/FourierTameProduct.lean:150` `schwartz_tame_product` | ✅ exact line; **no support hypothesis**; constant `2^(m-1)·besselConstant`, order-only; factor arrangement is `eq:Rproduct` verbatim |
| `Paper3/CompleteTameProduct.lean:101` `sobolevProduct`, `:128` `sobolevProduct_tame_bound` | ✅ both exact; `:120`, `:113` also correct |
| `Paper3/SobolevPhysicalProduct.lean:17,34,53,64` | ✅ all four exact |
| `Paper3/AngularTameProduct.lean:61,76,131,141,146,153,174` | ✅ all seven exact; `angularProduct` is on ambient `Lp ℂ 2 volume`, confirming the reality gap |
| `Paper3/SobolevBoundedRepresentative.lean:20,24,34,38,96` | ✅ all five exact |
| `Source/BesselH2Fourier.lean:39` `besselConstant` | ✅ exact; `= (∫ (1+‖ξ‖²)⁻²)^{1/2}` (`besselInverse` at `:19`), i.e. the manuscript's `∫⟨ξ⟩^{-4}dξ` |
| `vendor/…/Euler/EulerProof.lean:8237` `smooth_pointwise_le_H2` | ✅ exact; hypotheses `ContDiff ℝ ∞ f` + `∀ j ≤ 2, MemLp (iteratedFDeriv ℝ j f) 2`; **no support hypothesis**; every `x`; generic codomain `F` (so `gradientSupNorm_le` is free, as claimed); `smoothEmbeddingConstant` at `:8227`, `tensorSobolevNorm` at `:8091` |
| `Euler/OrdinaryWordBounds.lean:67` `real_pointwise_H2` | ✅ exact; RHS is the jet sum `∑_{j<3}‖A.jetLp j‖`, matching the "jet norm, needs D01 L2" caveat; `wordBound_pointwise` at `:76` ✅ |
| `Euler/OrdinaryTameProduct.lean:83` `tame_outer_product` | ✅ exact, and **the draft's warning is right**: hypotheses are `WordBound 3 M A` + `WordBound m N A`, so the low norm is `H³`. Substituting it would turn `eq:Rhigh`'s `‖u‖_{H²}` into `‖u‖_{H³}` and change `eq:criterion`. Cross-check only, as the draft says. |
| HeliCorgi `R3SchwartzConvectionSobolevEstimate.lean:92` | ❌ **wrong line — decl is at `:89`** (`:114`, not `:115`, for `…_three`). Content claim correct: `H³ × H³ → H²`, both factors at the high order, not tame. Constant `:81` ✅, gate `R3SchwartzSobolevCore.lean:94` ✅, `R3SobolevConvectionExtension.lean:138` ✅ |
| `vendor/…/NavierStokes/R3ConvolutionYoung.lean:141` `scalarConvolution` | ✅ exact |
| `Source/PhysicalIntegerSobolev.lean:32,42,45`, `RealVectorPositiveDensity.lean:15`, `SobolevOrderLowering.lean:26,39,78`, `RealSobolev.lean:118`, `VectorForceNorms.lean:47`, `SobolevDirectionalDerivative.lean:54,67,120`, `OrdinaryH3Products.lean:16` | ✅ all exact; `Product = PiLp 2` confirmed at `FiniteHilbertBochner.lean:11`, so `componentSobolevENorm`'s `PiLp 2` reading of `RealVectorSobolev` is right |

## Check log

```
. scripts/lean-env.sh ; LEAN_NUM_THREADS=6
cd verification && lake env lean ../research/A03/Spec.lean
  → no output, EXIT=0, 2.00s user / 2.93s wall
```
Pipeline sanity-check (a copy in `/tmp` with `#check`, `#print axioms`, and an injected
`example : False`): the `#check` printed the full elaborated type of
`TameProductAPI.supNorm_le_of_continuous`, `#print axioms` gave the three standard Mathlib
axioms, and the injected `False` errored — the file is genuinely elaborated, not skipped.

```
grep -nE '\b(sorry|axiom|admit|native_decide|unsafe)\b' research/A03/Spec.lean
  → line 11 only (prose "introduces no `axiom`, no `sorry`")
grep -nE '^\s*(theorem|lemma|example|instance|axiom|abbrev|opaque)\b' research/A03/Spec.lean
  → line 60 only (prose "lemma's *embedding* clauses")
```
14 `def`s + 1 `structure` (`TameProductAPI`), **23 fields**, zero theorem-like declarations,
zero `Prop` placeholders. `Contracts.V1.Data` is the only import.

Not verified: the mathematical truth of any field (a spec review, not a proof review); the
numeric value of any in-tree constant; anything in the HeliCorgi toolchain beyond line
locations (blocked by U05); the torus half of `lem:calculus` (out of scope by design).
