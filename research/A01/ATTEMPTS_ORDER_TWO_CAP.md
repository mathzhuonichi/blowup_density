# ATTEMPTS — lane 147 (A01 · row A3-L1·k), the order-2 norm cap `Kbnd`

Module: `formalization/NSFormalization/Section4/A01/OrderTwoCap.lean` (namespace
`NSFormalization.Section4.A01`).  New file only; no existing module edited.

## What is proved (9 theorems, constants explicit)

1. `norm_word_le` : `‖word 1 u hn w‖ ≤ ‖u‖` — every derivative word of a cylinder Sobolev array is
   bounded by the array norm (the `SobolevSpace` norm is the sup norm on the finite word-indexed
   product; one line, `norm_le_pi_norm`).
2. `eLpNorm_descend_le` : `(eLpNorm (⇑Zw) 2 volume).toReal ^ 2 ≤ ‖u‖ ^ 2` when
   `ordinaryLift Zw = word 1 u hn w` (`Lp.norm_def` + `ordinaryLift.norm_map`, the isometry).
3. **`hasWeakDerivsL2Bound_of_word`** (deliverable 1, word level) — the quantitative twin of lane
   140's `hasWeakDerivsL2_of_word`, re-running the descent induction with the tracked bound
   `M := ‖u‖²`, **constant 1**.  Conclusion `HasWeakDerivsL2Bound (⇑Zw) (‖u‖^2) m`.
4. **`hasWeakDerivsL2Bound_of_cylinder`** (deliverable 1, cylinder level) — from the order-`(q+1)`
   angle-invariant cylinder value `u` and its ordinary lift `U` (`ordinaryLift U = value 1 u`):
   `HasWeakDerivsL2Bound (⇑U) (‖u‖^2) m` for every `m + 3 ≤ q + 1`.  Constant 1.
5. **`sobolevENorm_two_toReal_le`** (deliverable 2, single slice) — for `4 ≤ q`:
   `(sobolevENorm ((2:ℕ):ℝ) (⇑U)).toReal ≤ 16 * ‖u‖`.  Route: deliverable 1 at `m=2` gives
   `HasWeakDerivsL2Bound (⇑U) (‖u‖^2) 2`; `D01.exists_isSobolevDatum_norm_le` a datum `A`;
   `A04.Forcing.sobolevENorm_eq hA : sobolevENorm 2 (⇑U) = ‖A‖ₑ`;
   `D01.norm_isSobolevDatum_le_two : ‖A‖^2 ≤ 256 * ‖u‖^2`; then `‖A‖ ≤ 16‖u‖` by nlinarith
   (`sq_nonneg (‖A‖ - 16‖u‖)`), and `(‖A‖ₑ).toReal = ‖A‖`.
5b. **`sobolevENorm_two_ne_top`** (deliverable 2, non-vacuity, **F2**) — under the same
   hypotheses `sobolevENorm ((2:ℕ):ℝ) (⇑U) ≠ ⊤`.  So the `.toReal` bound of (5) is a genuine
   real inequality, not the `⊤ ↦ 0` vacuity the A3-L1·k row warned about.  4 lines: the datum
   `A` has finite enorm and `sobolevENorm_eq hA` equates it to `sobolevENorm 2 (⇑U)`.
6. **`sobolevNormAt_two_le_of_cylinder`** (deliverable 2, time-indexed) — for a `SpaceTimeField v`
   with `hslice : ∀ t : Icc 0 T, (fun x => v (↑t, x)) =ᵐ[volume] ⇑(U t)` (F1, a.e.; the `Lp`
   representative is defined only up to a.e., the B1 hand-off shape):
   `∀ t, sobolevNormAt (2:ℝ) v ↑t ≤ 16 * ‖u t‖`.  Builds the slice datum from the
   `⇑(U t)` datum via `IsSobolevDatum.congr_field` (a.e., F1), then closes as (5) (the `(2:ℝ)` /
   `((2:ℕ):ℝ)` numerals are `rfl`-defeq, verified).
7. **`sobolevNormAt_two_sq_le_of_sup`** (deliverable 3, unconditional pointwise) — from the
   `ContinuousMap` sup-bound `‖u‖ ≤ R`: `∀ t : Icc 0 T, sobolevNormAt (2:ℝ) v ↑t ^ 2 ≤ 256 * R^2`.
   Uses `ContinuousMap.norm_coe_le_norm u t : ‖u t‖ ≤ ‖u‖`, `sobolevNormAt_nonneg`,
   `pow_le_pow_left₀`.  **No integrability needed** — this is the brief's fallback, delivered.
8. **`kbnd_of_sup_bound`** (deliverable 3, the cap) — with `hR : ‖u‖ ≤ R`,
   `hcont : ContinuousOn (fun s => sobolevNormAt (2:ℝ) v s) (Ico 0 T)` (the exact shape
   `A04.continuousOn_sobolevNormAt_velocity w 2` produces), `0 < T₀`, `T₀ ≤ T`:
   `∀ t ∈ Ico 0 T₀, (∫ s in 0..t, sobolevNormAt (2:ℝ) v s ^ 2) ≤ 256 * R^2 * T₀`.
   I.e. **`Kbnd := 256·R²·T₀`**.  Integrand `≤ 256R²` pointwise (7), interval-integrable via
   `hcont.pow 2 |>.mono |>.intervalIntegrable`, `intervalIntegral.integral_mono_on`, then
   `∫ const = t·256R² ≤ T₀·256R²`.

`#print axioms` = `[propext, Classical.choice, Quot.sound]` for all 8
(`research/A01/axioms_order_two_cap.lean`), which also contains a concrete non-vacuity witness:
the zero cylinder value `0 : SobolevSpace 1 (q+1)` satisfies every hypothesis of deliverable 1
(`sobolevTranslation … 0 = 0` by `simp`; `ordinaryLift 0 = value 1 0` by `simp [value]`), so the
constructor fires and yields `HasWeakDerivsL2Bound 0 0 2`.

## How `Kbnd` plugs into `GronwallInstance` (verified)

`research/A01/probes/otc_plugin.lean` (compiles, standard 3 axioms) feeds
`kbnd_of_sup_bound … w.velocity … (continuousOn_sobolevNormAt_velocity w 2) …` directly into
`GronwallInstance.highOrder_bddAbove_of_kbnd` as its `hkbnd` argument, with `v := w.velocity`,
`Kbnd := 256·R²·T₀`, yielding the explicit high-order bound
`sobolevNormAt m w.velocity t ≤ (sobolevNormAt m w.velocity 0 + ‖f‖_{L¹H^m}) · exp(Cgron m ν · 256R²T₀)`.
So for an actual `ClassicalSolutionR w`, the **integrability hypothesis `hcont` is free from the
tree** (`continuousOn_sobolevNormAt_velocity`); the only remaining input is the slice identity
`hslice` (the carrier bridge, below).  This sharpens the 142-review note "for `T₀ < T` a `Kbnd`
always exists": the cap is now a *named* `256·R²·T₀`, not merely an unquantified compact-interval
bound.  It is still a function of the a-priori radius `R` (and the Grönwall output grows like
`exp(Cgron·256R²T₀)`), so it closes the *conditional* implication `‖u‖ ≤ R ⇒ explicit R-dependent
bound`, **not** `HasAprioriBound` itself (whose `R` must be fixed before `T ≤ S` and before `u`).

## What remains for `HasAprioriBound` (four rows + the restart spine, exact statements)

`kbnd_of_sup_bound` closes the arithmetic of A3-L1·k.  Building `HasAprioriBound` (Horizon.lean)
still needs the restart/continuation rows already in the table (**A2b-a′ / A3-Tm / H1**) to pin one
`R` before the window, plus these four glue rows (a.e. slices per F1) (`A3_SPLIT.md:263`):

1. **Carrier bridge (mild ⇒ classical velocity), a.k.a. the `hslice` discharge.**  Need a
   `SpaceTimeField v` and a `ClassicalSolutionR ν a f T` whose `.velocity` is `v`, with `v`'s
   time-`t` slice equal to `⇑(U t)`, i.e. produce
   `hslice : ∀ t : Icc 0 T, (fun x => v (↑t, x)) =ᵐ[volume] ⇑(U t)` (a.e., F1)
   from `exists_local_shape_of_aprioriBound`'s cylinder pair `(u, U)`.  This is rows B1/B2
   (`SpatialField`/`SpaceTimeField` ⟶ `SmoothL2Field` in, cylinder `(u,U)` ⟶ `ClassicalSolutionR`
   out).  Without it deliverables 2–3 are stated for an arbitrary `v` carrying `hslice` as a
   hypothesis (route-robust, exactly like `GronwallInstance` carries `hkbnd`).
2. **Converse norm comparison (cylinder sup-norm ≤ R³ energy).**  `HasAprioriBound` quantifies the
   sup-norm `‖u‖_{SobolevSpace 1 (q+1)} ≤ R` over *mild* cylinder solutions; eq:Rhigh / the
   Grönwall bound live on the *energy* norm `sobolevNormAt`.  Exact obligation: a `t`-free reverse
   bound `‖u t‖_{SobolevSpace 1 (q+1)} ≤ C · sobolevNormAt (q+1) (⇑(U t))` (or the mild⇒energy
   identity of norms) so that a Grönwall energy cap feeds back into the cylinder sup-bound.  This
   lane provides only the *forward* direction `sobolevNormAt 2 (⇑(U t)) ≤ 16 ‖u t‖`.
3. **`Ico → Icc` widening.**  `kbnd_of_sup_bound` and `highOrder_bddAbove_of_kbnd` bound the norm on
   the half-open `Ico 0 T₀`; the a-priori sup-norm `‖u‖` is over the closed `Icc 0 T`.  Exact
   obligation: extend the `Ico 0 T₀` bound to `Icc 0 T₀` and take `T₀ = T`, i.e.
   `BddAbove (… '' Ico 0 T₀) ⇒ ∀ t : Icc 0 T₀, … ≤ R`.  **Splits:** for `T₀ < T` it is cheap (S) —
   `T₀ ∈ Ico 0 T`, so `continuousOn_sobolevNormAt_velocity` is available *at* `T₀` and a limit closes
   it; for `T₀ = T` it is the hard endpoint the 142 note calls A3-L1·k's "real content" (needs the
   energy identity). **This lane's cheapest next row is (iii) for `T₀ < T`.**
4. **Angle invariance `hinv` of the quantified `u` (unit A2b).**  `HasAprioriBound`
   (`Horizon.lean:106`) constrains its `u` only by the Duhamel equation, but both `exists_local` and
   this lane need `∀ θ t, sobolevTranslation 1 (q+1) (0,θ) (u t) = u t`.  Once that is in hand `U` is
   free (`Continuation.forced_ordinary_descent`, the last lines of `exists_local` factored out).
   This is unit A2b's `hinv`, tracked elsewhere in `A3_SPLIT.md`; it is absent from the naive
   three-row list.  (Row (i) also silently needs the `ClassicalSolutionR` horizon `T` to be the
   *same* `T` as the cylinder path's `Icc 0 T`, a matching obligation `exists_local` does not force.)

Together these turn "the Grönwall bound gives an *upper* bound on norms given a horizon" into
`HasAprioriBound` (an *a-priori* uniform bound before the window); note H1 (`horizon_lower_bound`)
is a separate, orthogonal obligation (a lower bound on the horizon, untouched here).

## Failed / rejected approaches

* **Post-composing lane 140's `hasWeakDerivsL2_of_cylinder` with the bound** — rejected: that
  theorem returns only the qualitative `HasWeakDerivsL2`, which discards the per-node `L²` sizes;
  the bound has to ride *inside* the same descent induction.  So the induction is re-run here
  (deliverable 1) without editing `EulerPairing.lean`, reusing its `exists_descend`,
  `word_hasDerivAt`, `weakDeriv_pairing_of_lift_hasDerivAt`.
* **`rw [hbridge]` with the goal at `sobolevENorm (2:ℝ)`** — the D01 lemmas produce
  `sobolevENorm ((2:ℕ):ℝ)`; `rw` is syntactic and would not match the `(2:ℝ)` goal despite defeq.
  Resolved by stating the single-slice lemma at `((2:ℕ):ℝ)` and bridging to `(2:ℝ)` with `show` +
  `exact` (the two numerals are `rfl`-defeq, checked in `research/A01/probes/rev147_checks.lean`
  example (1)).
* **Deriving `hcont` (integrability) for a general `v` from the tree** — not possible: the tree's
  `continuousOn_sobolevNormAt_velocity` needs a `ClassicalSolutionR`, which is exactly the carrier
  bridge (row 1 above).  Hence `hcont` is taken as an explicit hypothesis; the plug-in probe shows
  it is discharged for free once `v = w.velocity`.
* **Concrete non-vacuity on a *nonzero* cylinder solution** — not cheap (needs a real angle-
  invariant cylinder field + ordinary lift); the zero instance is used instead (still a genuine
  conclusion, `HasWeakDerivsL2Bound 0 0 2`).

## Commands

```
cd verification
lake build NSFormalization.Section4.A01.OrderTwoCap        # Built … (9952 jobs), EXIT 0
lake env lean ../formalization/…/OrderTwoCap.lean          # 0 bytes, EXIT 0 (silent)
lake env lean ../research/A01/axioms_order_two_cap.lean    # 9 decls, all 3-axiom; EXIT 0
lake env lean ../research/A01/probes/otc_plugin.lean       # plug-in into highOrder_bddAbove_of_kbnd; EXIT 0
make check                                                 # EXIT 0 (policy + work queue)
```
