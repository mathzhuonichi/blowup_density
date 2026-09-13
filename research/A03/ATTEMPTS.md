# A03 — attempts and negative results for the bounded-representative clause

Lane 023, task A03, component **A03.bounded_representative**: the second half of
`eq:Rproduct`, `‖v‖_∞ ≤ C‖v‖_{H²}` on `R³`
(`paper/sections/appendix-a-local-theory.tex:12`, Lemma A.1 `lem:calculus`).
Registered version 1 is `verification/Contracts/V1/BoundedRepresentative.lean`;
the proofs are `formalization/NSFormalization/Section4/A03/{SmoothJets,BoundedRepresentative}.lean`.

This file records what was *not* done and why.  The tame product clauses of
`research/A03/Spec.lean` (`tameProductScalar`, `tameProductVector`,
`algebraProductScalar`, `outerProductTame`, `outerProductDifference`,
`advectionTame`, `gradientSobolevENorm_le`, `componentSobolevENorm`,
`memHInfty_*`) are untouched by this lane and stay unregistered.

## 1. Route taken, and the route rejected

The manuscript proves this clause by absolute Fourier convergence
(`appendix-a-local-theory.tex:44-50`): Cauchy–Schwarz gives
`‖v̂‖₁ ≤ C‖v‖_{H²}` because `∫_{R³}⟨ξ⟩^{-4}dξ < ∞`, and absolute convergence of
the inversion integral bounds `v` pointwise.

**Rejected: the in-tree Fourier route.**
`NSFormalization.Paper3.sobolevBoundedRepresentative`
(`formalization/NSFormalization/Paper3/SobolevBoundedRepresentative.lean:34`,
with the order-two case at `:20` and the norm bound at `:24`) is exactly that
argument, with the constant
`NSFormalization.Source.BesselH2Fourier.besselConstant`
(`formalization/NSFormalization/Source/BesselH2Fourier.lean:39`), which is the
manuscript's `(∫⟨ξ⟩^{-4})^{1/2}` since `besselInverse ξ = (1+‖ξ‖²)⁻¹` (`:19`);
see §2 for the exact relation to the vendor constant.  It was rejected for this
contract
because it is a statement about an **abstract `SobolevHilbert m` datum in the
cycles convention**, not about a physical field:

* it lands in `BoundedContinuousFunction Space ℂ` (complex scalar), so the real
  three-vector field of `Contracts.V1.Data.SpatialField` has to be assembled
  componentwise from it;
* `sobolevRealization_boundedRepresentative2` (`:84`) says only that the
  representative realizes the **same tempered distribution** as the datum.  To
  turn that into `‖z x‖ ≤ C‖z‖_{H²}` for a physical `z` one has to (i) produce a
  datum of `z`, and (ii) go from "equal Schwartz pairings" back to "equal
  a.e. as functions".  Step (i) for a non-compactly-supported field is D01 unit
  L2 (lane 020, in PR at the time of writing); step (ii) is a du-Bois-Reymond
  argument that is nowhere in tree;
* it carries the cycles normalization (`weightedFourierLp`), so a `(2π)`
  reconciliation against the manuscript's angular transform
  (`01-introduction.tex:91`) would have to be done or explicitly quarantined.

**Taken: the Fourier-free-in-statement jet route**, the same shape lane 019 uses
for Lemma B.1.  The pointwise estimate is the vendor's
`EulerSmoothSobolev.smooth_pointwise_le_H2`
(`vendor/NavierStokesAndEuler/Euler/EulerProof.lean:8238-8239`): an
**everywhere**-pointwise bound for any smooth function into a complex Hilbert
space, no compact support, with `tensorSobolevNorm 2` (a jet `L²` sum,
`:8090-8092`) on the right.  The real three-vector case comes from the vendor's
isometric complexification `EulerSobolev.complexify 3` (`:5600`) — three lines,
reproduced as `norm_le_tensorSobolevNorm`.

**Rejected: importing the vendor's own real wrapper.**
`EulerOrdinarySobolev.real_pointwise_H2`
(`vendor/NavierStokesAndEuler/Euler/OrdinaryWordBounds.lean:67`) is literally
those three lines, but phrased on the bundled `SmoothL2Field` structure.
Measured cost of importing it instead: `lake build Euler.OrdinaryWordBounds` =
**4551 jobs, 6 min 41 s** against `lake build Euler.EulerProof` = **3714 jobs,
49 s** on the same warm Mathlib cache — roughly 840 extra vendor modules
(`Euler.OrdinarySmoothWords`, `Euler.OrdinarySobolevL4`, `Euler.GevreyProductLp`
and their closures) permanently inside the acceptance test's closure, for a
three-line lemma.  Reproved instead.

## 2. The constant

`NSFormalization.Section4.A03.boundedRepresentativeConst :=
EulerSmoothSobolev.smoothEmbeddingConstant + 1`, where
(`EulerProof.lean:8227-8230`)

```
smoothEmbeddingConstant =
  embeddingConstant 3 2 * (unitBumpCoefficient 0 + (2π)^(-2) * 3 * unitBumpCoefficient 2)
```

* `embeddingConstant 3 2 = ‖reciprocalWeightLp 3 2‖ = ‖besselWeight 3 (-2)‖_{L²}`
  (`:5451-5457`), and `besselWeight 3 (-2) ξ = (1+‖ξ‖²)^{-1}` (`:5397-5398`),
  which is literally `NSFormalization.Source.BesselH2Fourier.besselInverse`
  (`formalization/NSFormalization/Source/BesselH2Fourier.lean:19`).  So
  `embeddingConstant 3 2` and `besselConstant` (`:39`) are the same real number,
  namely the manuscript's `(∫⟨ξ⟩^{-4})^{1/2}` of
  `appendix-a-local-theory.tex:47`.  **This equality holds by reading the two
  definitions; no Lean lemma states it, and none is needed** — nothing in the
  shipped contract mentions either constant by name.
* The two *routes* do **not** carry the same constant, and the earlier draft of
  this file was loose about that.  `sobolevBoundedRepresentative2_norm_le`
  (`SobolevBoundedRepresentative.lean:24-25`) carries `besselConstant` alone;
  the vendor route multiplies the same number by the **localization artifact**
  `unitBumpCoefficient 0 + (2π)^{-2}·3·unitBumpCoefficient 2`, which comes from
  the cutoff `localize` (`:8156`) that removes the compact-support hypothesis
  and has no counterpart in the manuscript.  Note also that the manuscript's
  `(∫⟨ξ⟩^{-4})^{1/2}` at `:47` is the constant of `‖v̂‖₁ ≤ C‖v‖_{H²}`, one
  Fourier-inversion factor short of the `C` in `‖v‖_∞ ≤ C‖v‖_{H²}`.  All of this
  is harmless: **only `Cinfty_pos` is exported**, and no clause of the contract
  fixes a numerical value.
* `unitBumpCoefficient n` (`:8152-8153`) is a Leibniz sum of Schwartz seminorms
  of the vendor's fixed unit bump, from the localization step
  (`localize`, `:8156`) that removes the compact-support hypothesis.  It is an
  artifact of the proof, not of the manuscript.

**`+1`.** The vendor proves `smoothEmbeddingConstant_nonneg` (`:8231`) but not
positivity, and positivity would mean unfolding `embeddingConstant` (a `Lp`
norm) and `unitBumpBound` (a Schwartz seminorm of an irreducible bump).  The
contract field `Cinfty_pos : 0 < Cinfty` is what makes the clause a nontrivial
bound, so the implementation adds one and uses monotonicity of
`C ↦ C·S` at `S ≥ 0`.  Same device, and same reason, as lane 019's
`NSFormalization.Section4.A05.gradientL6Const`.

## 3. Does `(2π)` enter?

**Not into any statement; yes into the value of the constant.**

* No statement of `Contracts/V1/BoundedRepresentative.lean` or of the two proof
  modules mentions a Fourier transform.  Both sides are physical-space
  quantities: an `ℝ≥0∞` pointwise norm / essential supremum on the left, and a
  sum of `L²` norms of `iteratedFDeriv` on the right.  So the manuscript's
  angular convention `(2π)^{-3/2}∫e^{-ix·ξ}` (`01-introduction.tex:91`) and
  Mathlib's cycles convention cannot disagree here — there is nothing for them
  to disagree about.
* Inside the vendor's proof they do enter: `pointwise_le_L2_second_derivatives`
  (`EulerProof.lean:8081-8084`) converts `‖⟨ξ⟩²f̂‖₂` into physical second
  derivatives and pays `(2π)^{-2}`, because the vendor's `sobolevNorm`
  (`:5472-5473`) is built on the cycles transform, where `∂_j ↔ 2πiξ_j`.  That
  factor survives into `smoothEmbeddingConstant`.  Since only positivity of
  `Cinfty` is exported, no convention leaks through the contract.

## 4. Clause (c), the datum form — **not provable in this lane, not registered**

The wanted clause was

```lean
∀ z : SpatialField, MemHInfty z → SmoothJetsUpTo 2 z →
  eLpNorm z ⊤ volume ≤ ENNReal.ofReal Cinfty * Data.sobolevENorm 2 z
```

with `Data.sobolevENorm` (`Contracts/V1/Data.lean:189`) on the right instead of
the jet norm.  It reduces, through the registered `eLpNormTop_le`, to

```
jetSobolevENorm 2 z ≤ C' * Data.sobolevENorm 2 z
```

i.e. to bounding `∑_{j≤2}‖D^jz‖₂` by the norm of **any** order-two angular datum
of `z` (`sobolevENorm` is an infimum over data, so the inequality must hold for
each datum).  That is precisely the **datum ⟹ jets** direction of D01 unit L2
(`Contracts/V1/Data.lean:487-491`), plus Plancherel in the angular
normalization.

Status of that direction, as of this lane:

* lane 020 (`erenup/020-D01-hm-datum`, in PR, not merged) proves the **jets ⟹
  datum** direction — `NSFormalization.Section4.D01.memHInfty_of_contDiff_memLp`
  and `sobolevENorm_ne_top_of_contDiff_memLp`, with the quantitative half
  `norm_angularDatum_le`, which bounds the *datum* norm by a jet expression.
  That is the inequality in the **wrong direction** for clause (c): composing it
  with `sobolevENorm = ⨅ ...` gives `sobolevENorm 2 z ≤ C·(jets)`, not the
  converse.
* `research/D01/REVIEW_L2.md` §4.1 and §4.4 (lane 020) state explicitly that the
  converse is absent, and `research/D01/ATTEMPTS_L2.md` §4.2 says the same.
* The same gap is what `research/A03/COMPARISON.md:210-221` and
  `research/A01/COMPARISON.md:197` rate **L** for A01 unit **A1**.

Consequence for consumers, recorded in the contract docstring: **a consumer that
holds `Data.MemHInfty z` (the datum form) cannot yet use this contract.**  It
needs D01's datum ⟹ jets direction to reach
`SmoothJetsUpTo 2 z`, and then, if it wants `Data.sobolevENorm` on the
right rather than the jet norm, the quantitative comparison as well.  Every
Section 4 consumer identified so far in fact holds a *smooth* field
(`Data.ClassicalSolutionR.velocity_smooth`, the packet fields of
`Contracts/V1/Packet.lean`), so the missing input is square integrability of the
jets, not smoothness.

Nothing weaker was registered in its place: no clause of the shipped contract
mentions `Data.sobolevENorm`, `Data.IsSobolevDatum` or `Data.MemHInfty`.

## 5. Smaller things that failed or were changed

* `ofReal_norm_eq_enorm` is deprecated at this Mathlib pin (`v4.34.0-rc2`);
  `ofReal_norm` is the current name.  The first draft tripped the deprecation
  warning, which would have been an error in `verification/Tests`
  (`warningAsError = true`) had it appeared there.
* The specification draft's `boundedRepresentative` field
  (`research/A03/Spec.lean`, "∃ w, Continuous w ∧ w =ᵐ z ∧ …") is **not**
  registered as a separate clause: on `SmoothJetsUpTo 2` the field is
  already continuous, so that clause is `supNorm_le` with `w := z`, and a
  separate field would carry no content.  A consumer that wants the
  representative form on a merely-`H²` field still needs the Fourier route of §1.
* The contract's definitions live in the nested namespace
  `BlowupDensity.Contracts.V1.BoundedRep`, not in
  `BlowupDensity.Contracts.V1`, because lane 019's
  `Contracts/V1/GradientL6.lean` puts an identically-spelled
  `SmoothSquareIntegrableJets` in the flat namespace; a future contract
  importing both would otherwise fail to compile.
* **Hypothesis strength (reviewer finding 2).**  The first draft stated both
  clauses on the all-order jet class and claimed it was "the weakest hypothesis
  the proof route uses".  That was false: `norm_le_tensorSobolevNorm`, and the
  vendor input behind it, take `ContDiff ℝ ∞ z ∧ ∀ j ≤ 2, MemLp …`.  The
  registered clauses now run on `SmoothJetsUpTo 2`
  (`NSFormalization.Section4.A03.SmoothL2UpTo 2`), which is the manuscript's
  `v ∈ H²` for a smooth field; the all-order class is kept only as the derived
  instance `smoothJetsUpTo_of_allOrders`, so an A05-style consumer is unaffected.
  No conclusion changed.  Remaining distance from the manuscript: it assumes no
  smoothness and concludes about a *representative*, whereas both clauses here
  need `ContDiff` — the price of `supNorm_le` being an everywhere statement.
* **Binding name collision (reviewer finding 1).**  `BlowupDensity.Bindings` is
  flat across adapters, and the first draft declared
  `Bindings.smoothSquareIntegrableJets_eq`, the same full name as lane 019's
  `Bindings/GradientL6.lean:36`.  Two modules declaring one full name cannot be
  imported together (`environment already contains …`); no module imports both
  today, so no gate caught it.  All three bridges are now prefixed
  `boundedRep_`.  Checked against 019: its remaining binding names
  (`partialDeriv_eq`, `gradientTensor_eq`, `laplacian_eq`, `gradientL6`) and its
  test name (`checkedGradientL6`) do not collide with anything here.
* `NSFormalization.Section4.A03.SmoothL2` is a **copy** of
  `NSFormalization.Section4.A05.SmoothL2` (lane 019,
  `formalization/NSFormalization/Section4/A05/SmoothJets.lean:44`), not an
  import: 019 was unmerged and a worktree may not import another worktree.  The
  two are syntactically identical; when 019 lands, the two copies can be merged
  into one module, or left alone — they are in different namespaces and do not
  clash.

## 6. Commands

```
bash scripts/lean-install.sh                                        # exit 0
cd verification && lake build Euler.EulerProof                      # 3714 jobs, 49 s
lake build Bindings.BoundedRepresentative Contracts.V1.BoundedRepresentative \
  NSFormalization.Section4.A03.{BoundedRepresentative,SmoothJets} \
  Tests.BoundedRepresentative                                       # exit 0, 8823 jobs
make check                                                          # exit 0, registered_contracts 4
make test                                                           # exit 0, 4 contracts axiom-clean
make test-mutations                                                 # exit 0, 4/4
python3 experiments/check_contracts.py --base-ref erenup/integration # exit 0, A03 closure 59
lake build Euler.OrdinaryWordBounds                                 # 4551 jobs, 6 min 41 s (measurement only, §1)
```

`#print axioms` on all **15** declarations of the contract closure that this
lane authored — `Tests.checkedBoundedRepresentative`;
`Bindings.{boundedRepresentative, boundedRep_smoothJetsUpTo_eq,
boundedRep_smoothSquareIntegrableJets_eq, boundedRep_jetSobolevENorm_eq}`;
`SmoothL2.{contDiff, jetMemLp, upTo}`, `SmoothL2UpTo.{contDiff, jetMemLp}`,
`boundedRepresentativeConst_pos`, `norm_le_tensorSobolevNorm`,
`ofReal_tensorSobolevNorm`, `enorm_le_jetENorm`, `eLpNormTop_le_jetENorm` —
all exactly `[propext, Classical.choice, Quot.sound]`.

## 7. Review round (`research/A03/REVIEW_CONTRACT.md`, ACCEPT-WITH-NOTES)

All six actionable findings applied in place; no conclusion weakened, no gate
regressed.  1 (Medium) binding-name collision with lane 019 — all three bridges
prefixed `boundedRep_`, and the full-name sets of the two lanes' bindings and
tests checked disjoint.  2 (Medium) hypothesis inflation — clauses restated at
`SmoothJetsUpTo 2`, all-order class kept as the derived field
`smoothJetsUpTo_of_allOrders`, false "weakest hypothesis" sentence removed
(§5).  3 right-hand-side provenance — the contract and the proof module now
carry the three-link chain from `01-introduction.tex:85-86`'s Fourier-side
definition, and the "physical-space quantities" claim is scoped to the Lean
statements.  4 constant relations — §2 above.  5 `contracts.json` scope now
states the whole-space restriction and the unasserted jet ↔ datum equivalence,
mirroring the A05 entry.  6 the uniqueness consumer's need for
derivative-closure is stated in the contract docstring and in
`Section4/A03/SmoothJets.lean`.  Finding 7 (the task card still says the
embedding clauses go to A05) is a card-text matter for the lead, not a lane
edit: `collaboration/tasks/*.md` is generated.
