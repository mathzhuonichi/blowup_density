# A03 — attempts log for the *product* clauses of Lemma A.1

Lane `026-A03-tame-contract`, contract `A03.tame_products`
(`verification/Contracts/V1/TameProduct.lean`).  Companion of
`research/A03/ATTEMPTS.md`, which logs lane 023's *embedding* clause
(`A03.bounded_representative`).  Target: Lemma A.1 (`lem:calculus`,
`paper/sections/appendix-a-local-theory.tex:7-27`), `eq:Rproduct`'s first clause,
`eq:algebra`, `eq:tame`, the product difference bound of `:51-52`, and the
advection bound obtained from `:9-11` with `:50`.

All Lean paths are relative to the worktree root.

---

## 1. Exactly what is registered

`TameProductAPI`, all fields proved, acceptance test
`BlowupDensity.Tests.checkedTameProduct`, axioms
`propext, Classical.choice, Quot.sound`.

| field | paper | implementation |
|---|---|---|
| `C`, `C_pos` | `:10-11` | `A03.vectorTameConst` |
| `Calg`, `Calg_pos` | `:16` | `A03.algebraConst` |
| `Ctame`, `Ctame_pos` | `:17-18` | `A03.outerTameConst` |
| `Cdiff`, `Cdiff_pos` | `:51-52` | `A03.outerDiffConst` |
| `Cadv`, `Cadv_pos` | `:9-11` with `:50` | `A03.advectionConst` |
| `scalarSobolevENorm_component_le` | `01-introduction.tex:103` | `A03.scalarSobolevENorm_component_le` |
| `sobolevENorm_le_sum_components` | `01-introduction.tex:103` | `A03.sobolevENorm_le_sum_components` |
| `smoothJets_memHmVector` | `02-preliminaries.tex:12,29-30` | `A03.SmoothL2.memHmVector` |
| `smoothJets_memHmScalar` | same, componentwise | `A03.SmoothL2.memHmScalar` |
| `smoothJets_partialDeriv` | `:50` | `A03.SmoothL2.partialDeriv` |
| `tameProductScalar` (`m ≥ 2`) | **`eq:Rproduct`, first clause, `:9-11`** | `A03.tameProductScalar_vectorConst` |
| `tameProductVector` (`m ≥ 2`) | `:9-11` with `:50` | `A03.tameProductVector` |
| `algebraProductScalar` (`k ≥ 3`) | **`eq:algebra`, `:14-16`** | `A03.algebraProductScalar` |
| `outerProductTame` (`k ≥ 3`) | **`eq:tame`, `:17-18`** | `A03.outerProductTame` |
| `outerProductDifference` (`k ≥ 3`) | **`:51-52`** | `A03.outerProductDifference` |
| `smoothJets_advectionTame` (`m ≥ 2`) | `:9-11` with `:50` | `A03.advectionTame` |

**Not registered**, collected unproved in the sibling structure
`UnprovedTameProductObligations` in the same file (never instantiated, absent
from `verification/contracts.json`, mentioned by no test):

* `componentSobolevENorm`, the exact identity `‖z‖²_{H^s} = ∑_i‖z_i‖²_{H^s}`
  of `research/A03/Spec.lean:311`;
* `memHInfty_memHm`, the admissibility instance with the **datum** hypothesis
  `Data.MemHInfty` (`Spec.lean:324`);
* `memHInfty_advectionTame`, the advection clause with `Data.MemHInfty`
  (`Spec.lean:564`).

*What will close these.*  Lane 025 (`erenup/025-D01-datum-to-jets`) proves
`memHInfty_iff_smoothSquareIntegrableJets`, i.e. `Data.MemHInfty z ↔ SmoothJets z`,
the missing datum ⇒ jet direction of D01 unit L2.  Once it is merged it closes
**two of the three**: `memHInfty_memHm` follows from the registered
`smoothJets_memHmVector`, and `memHInfty_advectionTame` from the registered
`smoothJets_advectionTame`.  It does **not** close `componentSobolevENorm`, which
is a pure `ℝ≥0∞` identity through two datum infima with a `⊤` case split,
independent of D01 unit L2 and used by no registered clause.

Out of scope by design, and stated in the module docstring: every embedding
clause (`eq:Rproduct`'s `L^∞` half is lane 023's `A03.bounded_representative`;
`H¹ ↪ L⁶` and `eq:embeddings` are A05's `A05.gradient_l6`), the torus half of
`lem:calculus`, the order shift `‖∇v‖_{H^s} ≤ ‖v‖_{H^{s+1}}`, the uniqueness
coefficient `‖∇u₂‖_∞` of `:120-123`, and `∇·(u⊗u) = (u·∇)u` (A01 unit E1).
`Spec.lean`'s `memHInfty_component`, `memHInfty_partialDeriv`,
`gradientSobolevENorm_le`, `boundedRepresentative`, `eLpNormTop_le`,
`supNorm_le_of_continuous`, `gradientSupNorm_le` are therefore also absent —
the first two are `memHInfty_memHm`'s problem, the rest belong to other lanes.

---

## 2. What was reused and what is new

**Reused verbatim** (no change, no re-proof):

* `Source.FourierTameProduct.schwartz_tame_product`
  (`formalization/NSFormalization/Source/FourierTameProduct.lean:150`) —
  `eq:Rproduct` on the Schwartz core, in the cycles convention;
* `Paper3.sobolevProduct` (`Paper3/CompleteTameProduct.lean:101`),
  `sobolevProduct_weightedFourierLp` (`:113`), `sobolevProduct_tame_bound`
  (`:128`) — the completed bilinear product and `eq:Rproduct` on all complete
  data with the exact `H²` low factors;
* `Paper3.angularProduct` (`Paper3/AngularTameProduct.lean:61`),
  `angularProduct_apply` (`:70`), `angularProduct_tame_bound` (`:76`),
  `angularOrderLowering` (`:40`), `angularRealization_orderLowering` (`:51`),
  `angularBoundedRepresentative` (`:141`),
  `angularRealization_boundedRepresentative` (`:146`),
  `angularRealization_product` (`:174`) — the same in the manuscript's angular
  normalization, plus the physical identification of the completed product with
  pointwise multiplication of bounded continuous representatives;
* `Paper3.sobolevOrderLowering_norm_le` (`Paper3/SobolevOrderLowering.lean:39`),
  `cyclesToAngular_norm_le` / `cyclesToAngular_symm_norm_le`
  (`Paper3/AngularTameProduct.lean:14,20`),
  `cyclesToAngular_realSymmetry` (`Paper3/AngularRealSobolev.lean:54`),
  `angularRealization_injective` (`Paper3/AngularFourierDilation.lean:203`);
* `Source.RealSobolev.weightedFourierLp_conjugate` (`Source/RealSobolev.lean:72`),
  `mem_realSubspace_iff` (`:124`), `realSymmetry_involutive` (`:34`);
* `Section4.D01.realSymmetry_sobolevOrderLowering`
  (`Section4/D01/SmoothDatum.lean:208`),
  `sobolevENorm_ne_top_of_contDiff_memLp` (`:315`),
  `sobolevENorm_le_of_isSobolevDatum` (`:309`) — lane 020's jets ⇒ datum;
* `Section4.A03.SmoothL2` (`Section4/A03/SmoothJets.lean:60`) and
  `Section4.A05.SmoothL2.dir` / `.fderiv` / `.clm`, `A05.dirDeriv`
  (`Section4/A05/SmoothJets.lean:94,60,68,87`);
* Mathlib's `ae_eq_of_integral_contDiff_smul_eq`
  (`Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean:195`),
  `HasCompactSupport.toSchwartzMap`, `MemLp.integrable_mul`
  (`Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1085`).

**New in this lane** (four modules under
`formalization/NSFormalization/Section4/A03/`):

* `RealAngularProduct.lean`
  * `realSymmetry_sobolevProduct`, `realSymmetry_angularProduct`,
    `angularProduct_mem_realSubspace` — **stability of the reality subspace under
    the completed product**.  This is the single genuinely new mathematical
    lemma `research/A03/COMPARISON.md:164-169` predicted, and it is what makes the
    completed product usable on `Data.RealVectorSobolev`, whose components are
    conjugate-reflection symmetric (`02-preliminaries.tex:72`).
  * `cyclesToAngular_symm_realSymmetry`, `realSymmetry_angularOrderLowering`,
    `angularOrderLowering_mem_realSubspace` — the same for the operator that
    supplies the `H²` low factor.
  * `lowerDatum`, `mulDatum`, `norm_lowerDatum_le`, `norm_mulDatum_le`.
* `ScalarTameProduct.lean`
  * `IsScalarSobolevDatum.unique`, `scalarSobolevENorm_eq`,
    `exists_scalarSobolevDatum` — **D01 unit L1 on the scalar physical carrier**,
    plus the empty-infimum handling that turns `≠ ⊤` into existence of a datum.
  * `ae_eq_of_schwartz_pairing`, `representative_ae` — the bounded continuous
    representative of a datum *is* the physical field, almost everywhere.
  * `isScalarSobolevDatum_mul` / `_add` / `_sub`, `tameProductScalar`,
    `scalarSobolevENorm_two_le`, `algebraProductScalar`.
* `VectorTameProduct.lean` — `IsSobolevDatum.unique`, `sobolevENorm_eq`,
  `exists_sobolevDatum`, the two componentwise comparisons, `LocIntField` and
  `locIntField_smul`, subadditivity, `sobolevENorm_two_le`, `tameProductVector`,
  `algebraProductVector`, and the smooth-jet instances.
* `OuterTameProduct.lean` — `columnsSobolevENorm` and the two `ℓ²`↔`ℓ¹`
  comparisons, `outerProductTame`, `outerProductDifference`, `advectionOf_eq`
  and `advectionTame`.

---

## 3. Failed approaches, and what replaced them

1. **Reading the clauses off `Data.MemHInfty`.**  `Spec.lean` states every
   admissibility and advection clause with the datum hypothesis `MemHInfty`.
   Every proof route needs physical `L²` membership (for local integrability,
   §3.3 below), which is the **datum ⇒ jet** direction of D01 unit L2, recorded
   as open at `research/D01/RECONCILIATION.md:153` and again in the scope
   section of `Section4/D01/SmoothDatum.lean`.  No route around it was found:
   from an order-`0` datum one would have to invert `angularRealization` by
   Plancherel, which is not available in tree on the physical side.
   *Replacement*: state every clause on `MemHmVector`/`MemHmScalar`, which carry
   `MemLp _ 2` explicitly and are the spec's own predicates, and give the
   admissibility instances on the **jet** class `SmoothJets`, via lane 020's
   `SmoothDatum.lean`.  `SmoothJets z → Data.MemHInfty z` is proved upstream and
   the converse is not, so `smoothJets_memHmVector` is strictly weaker than
   `memHInfty_memHm`; the latter is therefore *not* registered but kept in
   `UnprovedTameProductObligations`, unweakened.  The same for the advection
   clause, registered as `smoothJets_advectionTame` under a distinct name.

2. **Projecting the product onto the reality subspace.**  `angularProduct` is
   defined on the ambient `Lp ℂ 2 volume`, so the first attempt took
   `Paper3.realProjectionTo` of the product — the projection is a contraction
   (`RealPositiveDensity.lean:31`), so the norm bound survives.  It is circular:
   the projected datum realizes the same tempered distribution only if the
   product was already symmetric, which is the lemma one is trying to avoid.
   *Replacement*: prove the symmetry directly.  On the Schwartz core the
   completed product is pointwise multiplication, conjugate reflection of a datum
   is pointwise conjugation of its Schwartz function
   (`weightedFourierLp_conjugate`), and conjugation is a ring homomorphism; the
   general case is density, exactly the pattern of
   `sobolevProduct_tame_bound`'s own proof.

3. **`MemLp _ 2` hypotheses in the datum-algebra lemmas.**  The first version of
   `isScalarSobolevDatum_add` / `_sub` and of the vector subadditivity required
   each summand to be in `L²`.  That is unusable for `outerProductDifference`
   and `advectionTame`: their summands are products of two `L²` factors
   (`(u_j−v_j)·u`, `u_j·∂_jv`), which are `L¹` but need not be `L²`.
   *Replacement*: the fundamental lemma needs only **local integrability**, so
   `representative_ae` and everything above it was restated with
   `LocallyIntegrable (fun x => ((a x : ℝ) : ℂ)) volume`, and `LocIntField` /
   `locIntField_smul` supply it for products through `MemLp.integrable_mul`
   (`L²·L² ⊆ L¹`).  This is the one design change that made the last two clauses
   go through.

4. **The exact componentwise identity.**  `Spec.lean:311` asks for
   `‖z‖²_{H^s} = ∑_i‖z_i‖²_{H^s}` in `ℝ≥0∞`.  Both sides are the same `PiLp 2`
   norm of the same datum, so it is true, but proving it needs
   `PiLp.norm_sq_eq_of_L2` pushed through **two** infima and a case split on the
   empty infimum (`⊤² = ⊤` on the left against a sum with one `⊤` summand on the
   right), and it is not needed: every estimate uses only the two inequalities
   `scalarSobolevENorm_component_le` and `sobolevENorm_le_sum_components`, which
   are proved and registered.  The identity was therefore not pursued and is
   recorded, unweakened, in `UnprovedTameProductObligations`.

5. **Mechanical dead ends** (recorded so the next lane does not repeat them):
   * `hA.component` / `hA.unique` dot notation does **not** resolve when the
     type head is a `def` living in another namespace
     (`Section4.D01.IsSobolevDatum` versus a helper declared in
     `Section4.A03`); Lean reports `Function.component`.  Apply the lemma by its
     full name instead.
   * `Finset.sum_eq_top` no longer exists in this Mathlib; the `⊤` case of
     `sobolevENorm_le_sum_components` is done with `Finset.single_le_sum`.
   * `mul_le_mul_right'` is not the ENNReal name; `mul_le_mul_left h c` is.
   * `zero_le` as a two-argument lambda fails in `ℝ≥0∞`; use `by simp`.
   * `open scoped ENNReal` alone makes `ContDiff ℝ ∞` elaborate `∞ : ℝ≥0∞`;
     `open scoped ContDiff ENNReal`, in that order, is what the other contracts
     use.
   * `SobolevHilbert s` is an `abbrev` for `Lp ℂ 2 volume`, so `rw` chains
     through `cyclesToAngular` can do large `isDefEq` checks.  **Exactly two
     theorems actually exceed the 200 000 default**, both with Lean's own
     `(deterministic) timeout at isDefEq` at the failing position and neither
     with a `simp` search or `nlinarith` there:
     * `RealAngularProduct.realSymmetry_angularProduct` — the
       `realSymmetry_sobolevProduct` rewrite; needs `> 250 000`, set to
       `400000`;
     * `ScalarTameProduct.tameProductScalar` — the
       `ENNReal.ofReal_add (by positivity) (by positivity)` step; needs
       `> 800 000`, set to `1200000`.

     During development six further sites were bumped defensively —
     `norm_mulDatum_le`, `tameProductVector`, `algebraProductVector`,
     `outerProductTame`, `outerProductDifference`, `advectionTame`.  The
     reviewer measured each (`research/A03/REVIEW_TAME.md` §3) and **all six
     compile at the default**, so they were removed after review: an unneeded
     bump suppresses the signal if such a proof later starts costing several
     times more.  The two that remain were lowered from `1000000`/`2000000` to
     roughly `1.5×` their measured requirement and each carries a one-line
     comment naming the `isDefEq` cost through `SobolevHilbert`.

---

## 4. Constants and the `(2π)` bookkeeping

`Source.frequencyUnit = 2 * Real.pi` (`Source/FourierConvention.lean:15`).

The manuscript fixes its Fourier normalization at `01-introduction.tex:91` to the
unitary **angular** transform; the in-tree product theory is proved in Mathlib's
**cycles** convention and transported by `Paper3.cyclesToAngular`, which is a
linear equivalence but **not** an isometry: `cyclesToAngular_norm_le` and
`cyclesToAngular_symm_norm_le` each cost `(2π)^{|s|}`.  Every constant therefore
carries an explicit power of `2π`, and the in-tree numeric values
(`besselConstant`, `sobolevTameConstant`) are **not** the contract's constants.

```
besselConstant            = (∫ (1+‖ξ‖²)^{-2} dξ)^{1/2}      Source/BesselH2Fourier.lean:39
                            (the manuscript's ∫⟨ξ⟩^{-4}dξ at :36; only
                             besselConstant_nonneg is proved in tree, :41)
sobolevTameConstant m     = 2^{m-1} · besselConstant         Paper3/CompleteTameProduct.lean:12
angularProduct_tame_bound   multiplies it by (2π)^{2m+2}     Paper3/AngularTameProduct.lean:76
                            ( = (2π)^m for each of the two symm transports
                              in, (2π)^m for the transport out, (2π)^2 for the
                              order-two low factor )

A03.scalarTameConst m     = (2π)^{2m+2} · sobolevTameConstant m + 1
A03.lowerConst s r        = (2π)^{|r|} · (2π)^{|s|} + 1
                            ( ‖angularOrderLowering s r h‖ ≤ (2π)^{|r|}·1·(2π)^{|s|}‖h‖,
                              the cycles order lowering being a contraction )
A03.vectorTameConst m     = 3 · scalarTameConst m                    (registered as C)
A03.algebraConst m        = 2 · scalarTameConst m · lowerConst m 2   (registered as Calg)
A03.vectorAlgebraConst m  = 2 · vectorTameConst m · (3 · lowerConst m 2)
A03.outerTameConst k      = 6 · vectorTameConst k                    (registered as Ctame)
A03.outerDiffConst k      = 3 · vectorAlgebraConst k                 (registered as Cdiff)
A03.advectionConst m      = 3 · vectorTameConst m                    (registered as Cadv)
```

Two kinds of pure bookkeeping appear above.

* **`+ 1`.**  Only `besselConstant_nonneg` is proved in tree, never positivity,
  and the contract asks for `0 < C m` so that the bounds are genuine estimates.
  Adding one to a nonnegative constant buys strict positivity and only weakens
  the inequality, whose right-hand side is a nonnegative product.  Same device as
  lane 019's `A05.gradientL6Const` and lane 023's `boundedRepresentativeConst`.
* **Factors of `3` and `2`.**  `3` is the `ℓ² ≤ ℓ¹` comparison over the three
  Euclidean components (or the three tensor columns, or the three summands of
  `(u·∇)v`); `2` is the two summands of `eq:Rproduct` collapsed into the
  symmetric `eq:algebra` form.  `appendix-a-local-theory.tex:10` allows both:
  `C_m` depends only on the integer order and the fixed domain `R³`, never on the
  field or its support.  No constant below depends on a field, a support, a
  frequency support, or a viscosity — they are structure fields, hence quantified
  outside everything.

---

## 5. Paper–Lean differences

1. **Order thresholds.**  The manuscript states `eq:algebra` and `eq:tame` for
   integers `k ≥ 3`.  The implementation proves `A03.algebraProductScalar` and
   `A03.outerProductTame` for every `k ≥ 2` — the derivation is `eq:Rproduct`
   plus `‖·‖_{H²} ≤ ‖·‖_{H^k}`, which needs only `k ≥ 2`.  The **contract is
   registered at the manuscript's `k ≥ 3`**, so the registered statement is the
   paper's; the stronger fact is in the implementation and in the field
   docstring.
2. **The difference bound is derived, not displayed.**  `:51-52` — and the same
   sentence at `paper/originals/local/paper_3_whole_space.tex:156` — claims only
   *qualitatively* that "factorizing `u⊗u−v⊗v` gives the corresponding difference
   estimate"; **no inequality of that shape is displayed anywhere under
   `paper/`**.  The registered
   `‖u⊗u−v⊗v‖_{H^k} ≤ C_k(‖u‖_{H^k}+‖v‖_{H^k})‖u−v‖_{H^k}` is the standard
   consequence of the factorization `u⊗u − v⊗v = (u−v)⊗u + v⊗(u−v)` together with
   `eq:algebra`, and that is exactly how `A03.outerProductDifference` proves it.
   Because the manuscript names no constant here, the contract carries a separate
   field `Cdiff` rather than reusing eq:algebra's `Calg`; both are quantified
   outside every field, so this is neither stronger nor weaker and it avoids an
   artificial `max`.  (An earlier draft of this file and of the contract cited
   `paper_3_whole_space.tex:192` as a quantified source; that line is the
   Plancherel/Young step of the a-priori `H^m` bound and says nothing about
   differences — corrected after `research/A03/REVIEW_TAME.md` finding 1.)
3. **The advection clause is not literally in Lemma A.1.**  The manuscript's own
   energy identity `eq:Rhigh` goes through `u ⊗ u` and the divergence form.
   `smoothJets_advectionTame` is `eq:Rproduct` applied componentwise to the
   summands `u_j·∂_jv` as `:50` licenses, and it is present because
   `02-preliminaries.tex:81` eq:projected and
   `Data.ClassicalSolutionR.momentum` (`Contracts/V1/Data.lean:624`) both state
   the equation with the upstream `advection`.  Its hypothesis class differs
   from `Spec.lean:564`'s: see §3.1.
4. **The low factor of `eq:tame` is at `H²`, not `H³`.**  The closest existing
   statement anywhere in the three code bases,
   `EulerOrdinarySobolev.tame_outer_product`
   (`vendor/NavierStokesAndEuler/Euler/OrdinaryTameProduct.lean:83`), and
   HeliCorgi's convection estimate both use an `H³` low norm.  Either would turn
   `eq:Rhigh`'s `‖u‖_{H²}` into `‖u‖_{H³}` and thereby change `eq:criterion`,
   the continuation criterion Theorem 4.2 and A04 depend on.  Neither was used;
   they were consulted as shape cross-checks only.  The registered `eq:tame`
   keeps the low factor at order two.
5. **Norm carrier.**  Unlike lane 023's jet-form contract, nothing here is
   measured in a jet norm: both sides of every clause are `Data.sobolevENorm` or
   its scalar/tensor companions, i.e. the manuscript's own datum norm in the
   manuscript's own normalization.  The only place a jet appears is the
   *hypothesis* class `SmoothJets` of the admissibility and advection clauses,
   and `Section4/D01/SmoothDatum.lean` converts it into data at every real order.
6. **"Closed under multiplication".**  `eq:Rproduct` also asserts that `H^m` is
   an algebra.  No field of `TameProductAPI` states it.  It follows from the
   registered bounds as a meta-argument — a finite right-hand side forces the
   left-hand side, which is `⊤` when the product has no datum, to be finite — but
   the left-hand side's own junk-`0` totalization
   (`Contracts/V1/Data.lean:148-155`) has to be excluded separately, and the
   implementation does exactly that internally by constructing the product datum
   (`A03.isScalarSobolevDatum_mul`).  A consumer that wants
   `MemHmScalar m (fun x => a x * b x)` as a conclusion should use that lemma,
   not the contract field.

---

## 6. Commands

```
bash scripts/lean-install.sh                                  # OK
lake build NSFormalization.Section4.A03.{RealAngularProduct,ScalarTameProduct,
             VectorTameProduct,OuterTameProduct}               # OK, no warnings
lake build Contracts.V1.TameProduct Bindings.TameProduct Tests.TameProduct   # OK
make check                                                     # OK
make test                                                      # 7 contracts, standard axioms only
make test-mutations                                            # implementation_refactor accepted;
                                                               # admitted_proof / extra_axiom /
                                                               # weakened_hypothesis rejected
python3 experiments/check_contracts.py --base-ref erenup/integration   # base_compatibility_checked: true
python3 experiments/build_changed_lean.py --dry-run …          # 7 modules, all built
```
