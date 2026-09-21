# D01 · P2 sub-lemma SL4α — attempts and design notes

Lane 074.  Deliverable: `div ∂ₜu = 0` for a classical whole-space solution, and (if
reachable) the Fourier-side transversality of any datum of `∂ₜu(t,·)`.

New module: `formalization/NSFormalization/Section4/D01/DivergenceTime.lean`
(namespace `NSFormalization.Section4.D01.DivergenceTime`).

## What was proved (fully, no `sorry`/`axiom`)

`spatialDivergence_temporalDerivative_eq_zero (u : ClassicalSolutionR ν a f T)
  (ht : t ∈ Ioo 0 T) (x) : spatialDivergence (fun p => temporalDerivative u.velocity p.1 p.2) t x = 0`.

`#print axioms` → `[propext, Classical.choice, Quot.sound]` for it and the three helpers.

## The exact statement chosen

The manuscript's `∂ₜu(t,·)` is `temporalDerivative u.velocity t ·`.  `spatialDivergence`
takes a `VelocityField = SpaceTime → Space = (ℝ × Space) → Space` (a *pair* argument), so the
informal `fun s x => temporalDerivative u s x` must be written on the pair:
`fun p : SpaceTime => temporalDerivative u.velocity p.1 p.2`.  Writing `fun s x => …` and
ascribing `VelocityField` does NOT type-check — `Space = EuclideanSpace ℝ (Fin 3)` is itself
a Pi type, so a curried two-argument lambda binds `x : Fin 3`, not `x : Space`.

## Field names actually read (SolutionClass.lean)

* `velocity_smooth : ContDiffOn ℝ ∞ velocity (Ico 0 T ×ˢ univ)`.
* `divergence : ∀ t ∈ Ico (0:ℝ) T, ∀ x, spatialDivergence velocity t x = 0`.
  **Note:** the field is over `Ico 0 T` (closed at 0), not `Ioo 0 T` as the task brief
  said — strictly stronger, and it is exactly what makes `Ico 0 T ∈ 𝓝 t` usable at interior `t`.

Operator defs (`vendor/NavierStokes/R3/ProblemStatement.lean`, via
`NavierStokes.ProblemStatement`):
* `temporalDerivative u t x = fderiv ℝ (fun s => u (s,x)) t 1`  (⇒ `= deriv (fun s => u (s,x)) t`
  definitionally, since `deriv f a := fderiv ℝ f a 1`).
* `spatialDerivative u t x = fderiv ℝ (fun y => u (t,y)) x`.
* `spatialDivergence u t x = ∑ i, (spatialDerivative u t x (coordinateVector i)) i`,
  `coordinateVector i = EuclideanSpace.single i 1`.

## Proof method (what worked)

Let `Φ s := fderiv ℝ (fun y => u.velocity (s,y)) x`.  Then
`div u (s,x) = ∑ᵢ (Φ s (eᵢ)) i` and, by the definitional `temporalDerivative = deriv`,
`div (∂ₜu)(t,x) = ∑ᵢ (M (eᵢ)) i` with `M = fderiv ℝ (fun y => deriv (fun r => u.velocity (r,y)) t) x`.

1. **Mixed-derivative commutation** `spatial_fderiv_hasDerivAt`: `HasDerivAt Φ M t`.
2. Compose with evaluation-at-`eᵢ` (`HasDerivAt.clm_apply` with a constant) and the coordinate
   CLM (`PiLp.proj 2 _ i`, via `HasFDerivAt.comp_hasDerivAt`) to get, per `i`,
   `HasDerivAt (fun s => (Φ s eᵢ) i) ((M eᵢ) i) t`; sum over `Fin 3` with `HasDerivAt.sum` ⇒
   `HasDerivAt (fun s => div u(s,x)) (div (∂ₜu)(t,x)) t`.
3. `div u(·,x)` is identically `0` on `Ico 0 T ∈ 𝓝 t` (`Ico_mem_nhds_iff.mpr ht` + field
   `divergence`), so `HasDerivAt (fun s => div u(s,x)) 0 t`.
4. `HasDerivAt.unique` ⇒ `div (∂ₜu)(t,x) = 0`.

Every `∑ᵢ …`/`div …`/`temporalDerivative … = deriv …` identification is definitional, so the
final line is `exact hsum.unique hzero` with no rewriting.

### The symmetry-of-second-derivatives lemma

`spatial_fderiv_hasDerivAt` is Clairaut.  Its core is `ContDiffAt.isSymmSndFDerivAt`
(`Mathlib/Analysis/Calculus/FDeriv/Symmetric.lean:530`),
`IsSymmSndFDerivAt 𝕜 f x := ∀ v w, fderiv 𝕜 (fderiv 𝕜 f) x v w = fderiv 𝕜 (fderiv 𝕜 f) x w v`
(def `:91`), applied at the two directions `(0, v)` and `(1, 0)` of `ℝ × Space`, i.e.
`∂ᵧ∂ₜ = ∂ₜ∂ᵧ`.  Regularity comes from `ContDiffOn.contDiffAt` on the open slab
`Ioo 0 T ×ˢ univ` (`isOpen_Ioo.prod isOpen_univ`, `mem_nhds_iff`), downgraded `ℝ ∞ → ℝ 2`
by `ContDiffAt.of_le (by simp)`.  Supporting Mathlib lemmas:
`ContDiffAt.fderiv_right`, `hasFDerivAt_const/​id`, `HasFDerivAt.prodMk/comp/comp_hasDerivAt/
clm_comp/clm_apply/congr_of_eventuallyEq/fderiv`, `hasDerivAt_const/​id`,
`ContinuousLinearMap.inr/ext/comp_zero`.

### Reuse vs reproduction

The three helpers `fderiv_spatial_slice`, `deriv_time_slice`, `spatial_fderiv_hasDerivAt` are a
**literal (byte-for-byte) copy** of `Euler.ComparatorBridge.{fderiv_spatial_slice,
deriv_time_slice, spatial_fderiv_hasDerivAt}`
(`vendor/NavierStokesAndEuler/Euler/CurlTimeDerivative.lean:14,25,33`), which is exactly this
commutation and compiles at this toolchain — **this local copy is the re-sync point if the vendor
pin changes.**  Kept local rather than imported because importing `Euler.*` would pull in ~6
modules / ~21.9k lines (incl. `Euler.EulerProof`, via `Euler.MeanBoundaryOperator`); the task also
restricts reuse to the canonical modules.  So the module imports only the canonical A02 restatement
+ Mathlib, and reaches the operators through A02 from `NavierStokes.ProblemStatement`.  Local
analogue `A05.SmoothJets.dirDeriv_comm` handles only coordinate–coordinate commutation, not
time–space, so it does not apply.

## What did not work / was rejected

* **Curried field `fun s x => …`** — ill-typed against `VelocityField` (see above).  Fixed by the
  pair form.
* **The planned name/sketch `div_temporalDerivative_eq_zero` in `research/D01/P2_SPLIT.md:151`**
  — its sketch statement `(∑ i, spatialDerivative (fun y => temporalDerivative u.velocity t y) i x i)`
  is ill-typed (`spatialDerivative` takes a `VelocityField`, i.e. a pair-argument field, and a time
  `ℝ`, not a `Fin 3`/`Space` in those slots).  The delivered name/form
  `spatialDivergence_temporalDerivative_eq_zero` with the pair field
  `fun p : SpaceTime => temporalDerivative u.velocity p.1 p.2` is the correct one.  (P2_SPLIT.md is
  not edited by this lane — the lead updates it.)
* **`set g := u.velocity`** — rejected: `set` makes `g` an opaque fvar, breaking the final
  definitional `spatialDivergence … = ∑ᵢ (M eᵢ) i` reduction (`rfl`/`exact` would fail).  Kept
  `u.velocity` explicit throughout instead.
* **Downgrade `ℝ ∞ → ℝ 2` by `le_top`** — `∞` is `↑(⊤ : ℕ∞)`, not `⊤ : ℕ∞ω`, so `le_top`
  is wrong; `by simp` (and `by norm_num` for finite `1+1 ≤ 2`) discharges the `≤` goals, matching
  the vendor idiom.

## Transverse statement (`temporalDerivative_datum_transverse`) — NOT proved, precise gap

The Fourier-side transversality "any order-`m` (`m ≥ 2`) datum `A` of `∂ₜu(t,·)` satisfies
`⟪ξ, Â(ξ)⟫ = 0` for a.e. `ξ`" reduces to:
  (i)   SL4α, proved here (`div ∂ₜu = 0`);
  (ii)  D2 `A04.TimeDerivative.timeDeriv_isSobolevDatum` (**available** on this branch): the
        datum of `∂ₜu(t,·)` is `deriv G t`;
  (iii) the `∂ⱼ`-datum lemma **`isSobolevDatum_partialDeriv`** (SL6) of lane 066 (PR #73), now on
        `origin/erenup/integration` at `formalization/NSFormalization/Section4/D01/DerivativeDatum.lean:245`,
        signature `{Z : SmoothL2Field Space} (j) (m : ℕ) {A : RealVectorSobolev ((m:ℝ)+1)} …`,
        which turns `div z = 0` into the a.e. symbol identity `∑ⱼ (iξⱼ) Âⱼ = 0`, i.e. `⟪ξ, Â⟫ = 0`;
        that identity is what `LeraySymbol.complementSymbol_eq_zero_of_inner_eq_zero` (**available**)
        then annihilates.

**Gap (updated after review).**  Lane 066's `isSobolevDatum_partialDeriv` is now merged (not a
missing dependency).  This *this* worktree does not contain 066's file, so the transverse theorem
was not written here; but the remaining work beyond composing (ii) D2, (iii) that lemma, and
`complementSymbol_eq_zero_of_inner_eq_zero` is only:
  (a) a `SmoothL2Field` wrapper for the slice `∂ₜu(t,·)` — `isSobolevDatum_partialDeriv` is stated
      for `Z : SmoothL2Field Space` acting on `Z.field`, so `∂ₜu(t,·)` must be presented in that
      class (its jets are `H^∞`, available from SL4α's regularity + D2), and
  (b) the `m+1 → m` order bookkeeping — the lemma consumes an order-`(m+1)` datum
      `A : RealVectorSobolev ((m:ℝ)+1)` and yields order `m`, so the transverse statement at order
      `m ≥ 2` reads the datum of `∂ₜu(t,·)` at order `m+1` (`deriv G t` from D2 at `m+1`).
No `sorry` was introduced; the theorem is deferrable to a lane that has 066's file present, where
it is `(ii) datum via D2 → (iii) `isSobolevDatum_partialDeriv` applied to `div ∂ₜu = 0` (SL4α) →
complementSymbol kill`, modulo (a)+(b).

## Commands run

* `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.D01.DivergenceTime`
  → `Built … (3.9s)`, `Build completed successfully`, no warnings from the module.
* `cd verification && lake env lean ../research/D01/axioms_sl4a.lean`
  → all four decls `depends on axioms: [propext, Classical.choice, Quot.sound]`.
