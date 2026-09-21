# A05 — attempts, hypotheses and paper–Lean differences

Lane 019, task A05 (component): register **one** clause of Lemma B.1,
`‖∇v‖₆ ≤ C‖Δv‖₂` (`paper/sections/appendix-b-embeddings.tex:32`, third line of
`eq:critical-derived`; consumed at `paper/sections/04-whole-space.tex:110-112`
and reused at `:171`).  This is unit **U9** of `research/A05/COMPARISON.md:213`.
Everything else in the accepted specification draft `research/A05/Spec.lean`
(the `Ḣ^{1/2}`/`Ḣ^{3/2}` embeddings, `Λ`, `J`, the torus half) stays
unregistered.

Registered as `A05.gradient_l6`, version 1:
`verification/Contracts/V1/GradientL6.lean`, `Bindings/GradientL6.lean`,
`Tests/GradientL6.lean`; proofs in
`formalization/NSFormalization/Section4/A05/{SmoothJets,HessianLaplacian,GradientL6}.lean`.

## 1. What the clause needed, and what was tried

### 1.1 The Hessian–Laplacian identity: Plancherel (paper) vs integration by parts (Lean)

`04-whole-space.tex:112` justifies the clause by "the `Ḣ¹→L⁶` case of
Lemma~\ref{lem:critical-embeddings}, since **Plancherel gives**
`‖D²u‖₂ = ‖Δu‖₂`".

* **Rejected: the Plancherel route.**  In tree, "Fourier transform of an `H^∞`
  field" only exists through the *datum* predicates of
  `verification/Contracts/V1/Data.lean` (`IsSobolevDatum`,
  `IsHomogeneousDatum`) in the manuscript's angular normalization.  Turning
  `|ξ_iξ_j|² summed = |ξ|⁴` into `‖D²v‖₂ = ‖Δv‖₂` at that level needs the
  datum-level machinery of units U1–U3 (`COMPARISON.md:200-206`) — uniqueness of
  the slice distribution, the angular↔cycles weight identity, and the
  correspondence between coordinate derivatives and `iξ_j` multipliers
  (`Paper3/SobolevDirectionalDerivative.lean`,
  `Source/AngularGradientIdentity.lean`, whose gradient identity additionally
  assumes `HasCompactSupport`).  That is the whole Fourier half of A05 and is
  out of this lane's budget.
* **Adopted: integration by parts, Fourier-free.**  Mathlib's
  `MeasureTheory.integral_bilinear_fderiv_right_eq_neg_left_of_integrable`
  (`Mathlib/Analysis/Calculus/LineDeriv/IntegrationByParts.lean:195`) has **no
  boundary term and no decay hypothesis**: it asks only that `B f g`, `B f' g`
  and `B f g'` be integrable.  With `B = innerSL ℝ` and square-integrable jets,
  Cauchy–Schwarz supplies all three.  Two integrations by parts plus one use of
  Clairaut give, for each pair `(i,j)`,
  `∫⟪∂_i∂_j v, ∂_i∂_j v⟫ = ∫⟪∂_i∂_i v, ∂_j∂_j v⟫`
  (`HessianLaplacian.lean`, `integral_inner_hessian`), whose double sum is
  exactly `‖D²v‖₂² = ‖Δv‖₂²` (`sum_integral_hessian`).  Each summand is
  nonnegative, so each entry obeys `‖∂_i∂_j v‖₂ ≤ ‖Δv‖₂` (`eLpNorm_hessian_le`).
* **Rejected: cutoff + Fatou** (the device the vendor uses in
  `NavierStokes/R3/SmoothSobolevL6.lean:72` to remove compact support).  It would
  have avoided assuming order-3 jets in `L²` — the identity for `χ_R v` needs no
  hypothesis at all, and Fatou gives the `≤` direction — at the price of a
  Leibniz expansion of `Δ(χ_R v)` and of `D²(χ_R v)` with two error terms.  Once
  the Mathlib lemma above turned out to need only integrability, this was
  strictly more work for a marginally weaker hypothesis.  Recorded here because
  it is the route to take if a consumer ever needs the clause for a field that
  is only `H²`.

### 1.2 Which `H¹ → L⁶` inequality

`NavierStokesR3.RieszTestOperators.smooth_eLpNorm_six_le`
(`vendor/NavierStokesAndEuler/NavierStokes/R3/SmoothSobolevL6.lean:72`) was used
verbatim: `ContDiff ℝ 1 f` and `MemLp f 2 volume` give
`eLpNorm f 6 ≤ C · eLpNorm (fderiv ℝ f) 2` in `ℝ≥0∞`, for an arbitrary real
inner-product codomain, with **no support assumption** and no Fourier transform.
`COMPARISON.md:55` had already identified it as the strongest match; nothing had
to be adapted.

* **Rejected: applying it once to the assembled tensor**
  `∇v : Space → WithLp 2 (Fin 3 → Space)`.  That form is admissible (the
  codomain is an inner-product space), but its right-hand side is
  `eLpNorm (fderiv ℝ (∇v)) 2`, and relating `fderiv ℝ (∇v)` to the nine
  `∂_i∂_j v` requires pushing `fderiv` through the `WithLp.toLp` assembly, i.e.
  a continuous linear map `(Space →L[ℝ] Space) →L[ℝ] WithLp 2 (Fin 3 → Space)`
  that Mathlib does not provide ready-made (`PiLp.continuousLinearEquiv` plus
  `ContinuousLinearMap.pi` would have to be composed by hand).
* **Adopted: applying it to each column** `∂_j v : Space → Space` and assembling
  afterwards with the pointwise `l² ≤ l¹` bound
  `‖WithLp.toLp 2 g‖ ≤ ∑_j ‖g j‖` (`SmoothJets.lean`, `norm_toLp_le_sum`).  No
  new continuous linear map is needed; the cost is a factor `3`.

### 1.3 Operator norm versus Frobenius norm

`fderiv ℝ (∂_j v) x` carries the **operator** norm, while the Hessian identity is
about the **Frobenius** norm.  The sharp comparison is Hilbert–Schmidt
(`‖T‖ ≤ (∑_i ‖T e_i‖²)^{1/2}`, Cauchy–Schwarz over the orthonormal basis); the
crude one, `‖T‖ ≤ ∑_i ‖T e_i‖`, is three lines from
`ContinuousLinearMap.opNorm_le_bound` and `PiLp.norm_apply_le`
(`SmoothJets.lean`, `opNorm_le_sum`).  The crude one was taken: it costs another
factor `3`, and `appendix-b-embeddings.tex:109-110` leaves the constant free.

## 2. Hypotheses actually needed

The contract's field class is

```
SmoothSquareIntegrableJets v ↔ ContDiff ℝ ∞ v ∧ ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n v) 2 volume
```

the **jet form** of the manuscript's smooth `H^∞` class, field-for-field the
vendor's `EulerLpTranslation.SmoothL2Field`
(`vendor/NavierStokesAndEuler/Euler/LpSmoothField.lean:31-34`).  Only jets of
order **1, 2 and 3** are used:

| where | order used |
|---|---|
| `smooth_eLpNorm_six_le` on `∂_j v` | 1 (`MemLp (∂_j v) 2`) |
| `hfg'`, `hf'g` of the second integration by parts | 2 |
| `hf'g` of the first integration by parts (`⟪∂_i∂_i∂_j v, ∂_j v⟫`) | 3 |

Order 3 is a genuine hypothesis of this route that the manuscript's Plancherel
route would not need.  It is free on `H^∞` fields, which is the only class
Section 4 applies the clause to (`appendix-b-embeddings.tex:34-37`,
`research/section4/STATEMENTS.md:467`).  `ContDiff ℝ ∞` is likewise stronger
than the `ContDiff ℝ 3` the proof consumes; it was kept because
`SmoothL2.fderiv` (order bookkeeping for `ContDiff.fderiv_right`) is trivial at
`∞` and fiddly at a finite order.

## 3. The remaining gap: datum form versus jet form of `H^∞`

`Contracts.V1.Data.MemHInfty` (`verification/Contracts/V1/Data.lean:495`) is the
**datum** form — smooth, with an angular Sobolev datum at every integer order —
and `Data.lean:487-491` books the equivalence with the jet form as a separate
lemma (unit L2).  `research/A05/REVIEW.md:140-143` flagged exactly this as
missing from U9's ingredient list, and it is still missing: **nothing in this
lane proves `MemHInfty v → SmoothSquareIntegrableJets v`**, and no field of
`GradientL6API` asserts it.  A consumer holding `MemHInfty v` (which is what
`Data.initialClassR` and `ClassicalSolutionR` supply) therefore still needs unit
L2 before it can use `gradientLSix`.  This is the honest reason the contract is
stated on the jet class rather than on `MemHInfty`: stating it on `MemHInfty`
would have required either unit L2 or an unproved field, both excluded.

Registering the clause on the jet class was preferred over the fallback the task
allowed (`A05.gradient_l6_hessian`, bounding by `‖D²v‖₂` instead of `‖Δv‖₂`):
the Hessian–Laplacian identity did **not** resist, so the registered clause is
the paper's, with the paper's right-hand side `‖Δv‖₂`.

## 4. Paper–Lean differences

1. **Proof route.**  The paper derives the clause from its own `Ḣ¹→L⁶`
   embedding plus Plancherel; the Lean proof uses the vendor's support-free
   `H¹→L⁶` inequality plus integration by parts.  Same statement, different
   ingredients.  `COMPARISON.md:308-316` had already recorded and accepted this,
   noting that `embeddingPair` at `a = 1` therefore stays unconsumed.
2. **No `(2π)` factor anywhere, and none possible.**  Every quantity in the
   contract (`‖∇v‖₆`, `‖Δv‖₂`, and the Bochner integrals of the Hessian
   identity) is a physical-space quantity, and no statement or proof step in the
   registered closure mentions a Fourier transform.  This confirms
   `COMPARISON.md:126-128` ("the `gradientLSix` clause has no normalization
   content at all") *constructively*: the manuscript's angular convention and
   Mathlib's cycles convention agree at order `0`, so even the paper's own route
   would be factor-free here, and the route actually taken never raises the
   question.
3. **The constant.**  The paper writes an unspecified `C`
   (`appendix-b-embeddings.tex:109-110`: depends only on exponents, domain and
   norm conventions).  The binding supplies

   ```
   gradientL6Const = 9 * (eLpNormLESNormFDerivOfEqInnerConst volume 2 : ℝ) + 1
   ```

   `9 = 3 · 3` is the price of the two `l² ≤ l¹` steps (§1.2, §1.3) and is not
   sharp.  The `+ 1` is **only** a positivity workaround: Mathlib builds
   `eLpNormLESNormFDerivOfEqInnerConst` out of `irreducible_def`s
   (`Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean:359,433,453`) and
   exposes no positivity lemma, so `0 < C` is not available without unfolding
   them; `0 < 9C + 1` follows from `C ≥ 0` alone.  Nothing downstream may depend
   on the value: `Csix` is a structure field.
4. **Class of fields.**  The paper states the derived estimates for the
   homogeneous completion of `{v : v̂ ∈ C_c^∞(R³∖{0})}` and adds that they apply
   to all smooth `H^∞` fields; the contract states the clause for the smooth
   `H^∞` fields only (jet form).  The completion is not built anywhere in tree
   and no Section 4 statement quantifies over a completion element
   (`COMPARISON.md` §6.2).
5. **An extra clause, not a weaker one.**  `hessianLaplacianIdentity` records
   `∑_{i,j} ∫‖∂_i∂_j v‖² = ∫‖Δv‖²`, which is the ingredient
   `04-whole-space.tex:112` names by hand.  It is proved, not assumed, and it is
   an equality, not the inequality the estimate needs.

## 5. Lean-level snags worth not rediscovering

* `MemLp.const_mul` is scalar-valued only; for a normed-space codomain use
  `MemLp.const_smul` (`Mathlib/MeasureTheory/Function/LpSeminorm/SMul.lean:47`).
* `ContinuousLinearMap.norm_iteratedFDeriv_comp_left` lives in
  `Mathlib.Analysis.Calculus.ContDiff.Bounds`, not in `ContDiff.Basic`;
  `AEStronglyMeasurable.inner` lives in
  `Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner`.  Both are easy to
  miss because the vendor files that use them import them transitively.
* `innerSL ℝ : E →L⋆[ℝ] E →L[ℝ] ℝ` unifies with the `B : F →L[ℝ] G →L[ℝ] W`
  that the bilinear integration-by-parts lemma wants, so the general bilinear
  form needs no hand-built replacement.
* With both `ContDiff` and `ENNReal` scoped notations open, a bare `∞` is
  ambiguous; write `(∞ : ℕ∞ω)`, and get `(n : ℕ∞ω) ≤ ∞` by `exact_mod_cast le_top`.
* `Data.spatialGradient (lift v) 0` is **definitionally**
  `fun x => WithLp.toLp 2 (fun j => fderiv ℝ v x (coordinateVector j))`, and
  `spatialLaplacian (lift v) 0` is definitionally `∑ i, ∂_i∂_i v`; both bridges
  in `Bindings/GradientL6.lean` are `rfl`, as is
  `SmoothSquareIntegrableJets = SmoothL2` and `partialDeriv = dirDeriv`.

## 6. Commands run (all inside the lane worktree)

```
bash scripts/lean-install.sh                                  # exit 0
. scripts/lean-env.sh; export LEAN_NUM_THREADS=6
cd verification && lake build Contracts.V1.GradientL6 \
    Bindings.GradientL6 Tests.GradientL6 \
    NSFormalization.Section4.A05.{SmoothJets,HessianLaplacian,GradientL6}   # exit 0
make check                                                    # exit 0
make test                                                     # exit 0; three contracts,
                                                              #   each "standard logical axioms only"
make test-mutations                                           # exit 0; 1 accepted, 3 rejected
python3 experiments/tasks.py render
```

`python3 experiments/check_contracts.py --base-ref erenup/integration` **fails in
this worktree** with `Removed stable specification:
verification/Contracts/V1/Correction.lean`.  The cause is not this change: the
worktree branches from `09fcb90`, and `erenup/integration` advanced to `f1603c9`
(lanes 011, 015–018 merged) while this lane was running, so the base now carries
the `I02.correction` contract that the worktree has never seen.  Two runs pin
this down:

* against the merge base `09fcb90` — passes, `registered: 3`,
  `base_compatibility_checked: true`;
* against `erenup/integration` on a scratch export of `f1603c9` with this lane's
  files overlaid (`git archive` into `/tmp`, no repository write) — passes,
  `registered_contracts: 4`, `base_compatibility_checked: true`, closures
  `R41.threshold_arithmetic, I01.packet, I02.correction, A05.gradient_l6`; and
  `check_work_queue.py` there reports 30 consistent work items.

So the lane is compatible with the current integration tip; it needs a rebase
(and the usual `verification/contracts.json` / `collaboration/work_items.json`
conflict resolution plus `tasks.py render`) before merge.  No git write command
was run by this lane.

`experiments/build_changed_lean.py --dry-run` compares `base..HEAD`, and this
lane has no commit, so it reports `none`.  Its `targets()` applied to the
working-tree paths gives exactly

```
Bindings.GradientL6, Contracts.V1.GradientL6,
NSFormalization.Section4.A05.GradientL6, NSFormalization.Section4.A05.HessianLaplacian,
NSFormalization.Section4.A05.SmoothJets, Tests.GradientL6
```

and `lake build` on that list succeeds.
