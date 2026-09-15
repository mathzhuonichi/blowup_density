# ATTEMPTS — lane 149 (A01 · residual a-priori rows (iii) widening + (ii) converse)

Module: `formalization/NSFormalization/Section4/A01/AprioriRows.lean` (namespace
`NSFormalization.Section4.A01`).  New file only; no existing module edited.  Imports
`OrderTwoCap` (lane 147), `GronwallInstance` (lane 142), `D01.DatumToJets`.

Residual-row audit source: `research/A01/REVIEW_ORDER_TWO_CAP.md` §"Residual-row audit" (rows
(i)–(iv)); `research/A01/A3_SPLIT.md:263`.

## What is proved (7 theorems, constants explicit)

### Deliverable (iii) — `Ico → Icc` endpoint widening, `T₀ < T` case

1. **`kbnd_of_sup_bound_Icc`** — the exact lane-147 cap `kbnd_of_sup_bound`, restated on the
   **closed** window with `T₀ < T` (replacing `0 < T₀`, `T₀ ≤ T`):
   `∀ t ∈ Icc 0 T₀, (∫ s in 0..t, sobolevNormAt 2 v s ^ 2) ≤ 256·R²·T₀`.  Same explicit constant
   `256·R²·T₀`.  Direct re-derivation reusing the lane-147 **unconditional** pointwise bound
   `sobolevNormAt_two_sq_le_of_sup` (exported): for `t ≤ T₀ < T` the endpoint stays inside
   `Ico 0 T`, so `uIcc 0 t ⊆ Ico 0 T`, `hcont` gives interval-integrability, and
   `intervalIntegral.integral_mono_on` + `∫ const = t·256R² ≤ T₀·256R²` closes it (`ht.2 : t ≤ T₀`
   is used directly, where lane 147's `Ico` proof used `ht.2.le`).

2. **`highOrder_bddAbove_of_kbnd_Icc`** — `GronwallInstance.highOrder_bddAbove_of_kbnd`'s explicit
   one-order bound widened to `Icc 0 T₀`, **same** constant
   `(sobolevNormAt m w.velocity 0 + ‖f‖_{L¹_tH^m})·exp(A04.Cgron m ν·Kbnd)`.  **(review note N1
   applied)** the cap `hkbnd` is asked on an *intermediate* horizon `Ico 0 T₁` with `T₀ < T₁ ≤ T`:
   instantiate `highOrder_bddAbove_of_kbnd` at horizon `T₁` (`0 < T₁` from `0 ≤ T₀ < T₁`), giving the
   bound on `Ico 0 T₁`, then restrict along `Icc 0 T₀ ⊆ Ico 0 T₁`.  This is strictly more general
   than the earlier full-horizon (`T₁ := T`) form and lets a caller keep `Kbnd = 256·R²·T₁` from
   `kbnd_of_sup_bound` at horizon `T₁`, so the exponential constant does **not** degrade to
   `exp(Cgron·256R²T)`.  (Earlier draft only asked `hkbnd` on `Ico 0 T`, forcing `Kbnd = 256·R²·T`;
   the two halves of (iii) then did not chain — the cap produced `Icc 0 T₀`, the Grönwall row consumed
   `Ico 0 T`.  N1 fixes exactly this, verified by `rev149_generalized_horizon.lean`.)

3. **`highOrder_bddAbove_all_orders_of_kbnd_Icc`** — the all-orders `BddAbove` conclusion widened
   to `Icc 0 T₀`, constant-free, same N1 intermediate-horizon `Ico 0 T₁`:
   `∀ m ≥ 3, BddAbove ((sobolevNormAt m w.velocity) '' Icc 0 T₀)`, by `BddAbove.mono` along
   `Icc 0 T₀ ⊆ Ico 0 T₁`.

3'. **`kbnd_of_sup_bound_Icc_endpoint`** (added, review note N3 / row iii-a′) — the **cap** at the
   closed endpoint `T₀ = T`: `∀ t ∈ Icc 0 T, (∫ s in 0..t, sobolevNormAt 2 v s ^ 2) ≤ 256·R²·T`,
   same constant.  The lane's `T₀ < T` was needed only to get interval-integrability from `hcont`
   (continuity on `Ico 0 T`); the pointwise bound is already unconditional on the closed `Icc 0 T`,
   so at the endpoint integrability follows from a.e.-continuity on `Ioo 0 t` (`Ioo_ae_eq_Ioc`) plus
   the pointwise bound (`Integrable.mono'`).  So on row (iii) only the **Grönwall output** at `t = T`
   (`highContinuationIntegral` needs `t < T`) remains the hard eq:criterion endpoint.

**On the `T₀ = T` endpoint of row (iii) (review note N3, three-way split).**  (a) the *cap* at
`T₀ = T` is now done (`kbnd_of_sup_bound_Icc_endpoint`, S); (b) the **Grönwall output** at `t = T`
is the genuine hard eq:criterion endpoint (L) — the continuity/continuation window closes only up to
the boundary and the closed endpoint needs the energy identity at `T`; (c) the endpoint the a-priori
sup-bound *actually* needs (`‖u‖ ≤ R` on the closed `Icc 0 T`) is **free at the cylinder level** — `u`
is a `ContinuousMap`, so a bound on `{t : ↑t < T}` extends to the endpoint by continuity (reviewer
probe `rev149_cylinder_endpoint.lean`), and is not an energy-side obligation at all.

### Deliverable (ii) — converse norm comparison (cylinder ≤ energy)

4. **`sobolevSpace_norm_le_of_forall_word`** (backbone, fully proved) — the `SobolevSpace 1 q` norm
   is the sup over derivative words: `(0 ≤ C) → (∀ n (hn : n ≤ q) w, ‖word 1 u hn w‖ ≤ C) → ‖u‖ ≤ C`.
   The cylinder Sobolev space is a closed submodule of `SobolevWord q → LiftL2 1`
   (`vendor/…/Euler/CylinderSobolevSpace.lean:44,49`) with the inherited **sup (Pi) norm** (`:52`),
   and `word 1 u hn w = u.val ⟨⟨n,_⟩,w⟩` (`:66`), so this is `pi_norm_le_iff_of_nonneg` after
   destructuring the word index `⟨⟨n, hlt⟩, w⟩` (`n < q+1 ⇒ n ≤ q`).  This is the genuine structural
   content on the cylinder side (converse of lane 147's `norm_word_le : ‖word‖ ≤ ‖u‖`).

5. **`eLpNorm_iteratedFDeriv_le_sobolevENorm_toReal`** (the reverse embedding, fully proved) — for a
   smooth `H^{q+1}` field `z` (`ContDiff ℝ ∞ z`, `sobolevENorm (q+1) z ≠ ⊤`) and `n ≤ q+1`:
   `(eLpNorm (iteratedFDeriv ℝ n z) 2 volume).toReal ≤ jetSobolevConst (q+1) · (sobolevENorm (q+1) z).toReal`.
   Explicit `n`-uniform constant **`jetSobolevConst (q+1)`** (`DatumToJets.lean:316`, one `(2π)^{q+1}`
   Bessel-weight factor).  Route: `eLpNorm (iteratedFDeriv ℝ n z)` is one summand of
   `jetSobolevENorm (q+1) z` (`Finset.single_le_sum`, `n ∈ range(q+2)`), and
   `DatumToJets.jetSobolevENorm_le_sobolevENorm` bounds the whole jet sum by
   `jetSobolevConst (q+1)·sobolevENorm (q+1) z`.  **This is the direction the brief flags as "the
   reverse `eLpNorm(∂^α) ≤ ‖A_k‖` bound"; it IS in the tree — for smooth fields via `iteratedFDeriv`.**
   The `H^{q+1}` finiteness `hfin` is load-bearing: without it `sobolevENorm (q+1) z = ⊤` makes the
   real bound false (`⊤.toReal = 0` on the right while the left jet norm can be positive).

6. **`sobolevSpace_norm_le_sobolevENorm`** (converse, single slice) — for a smooth `H^{q+1}` field
   `z` and the cylinder value `u : SobolevSpace 1 (q+1)`:
   `‖u‖ ≤ jetSobolevConst (q+1) · (sobolevENorm (q+1) z).toReal`, constant `jetSobolevConst (q+1)`
   (`t`-free).  Proof = backbone (4) ∘ reverse embedding (5), threaded per word through the single
   named hypothesis `hword_jet` (below).

7. **`sobolevSpace_norm_le_sobolevNormAt`** (converse, time-indexed) — for a `C(Icc 0 T, …)`
   cylinder path `u` and a `SpaceTimeField v` whose every slice is a smooth `H^{q+1}` field:
   `∀ t : Icc 0 T, ‖u t‖ ≤ jetSobolevConst (q+1) · sobolevNormAt (q+1) v ↑t`
   (using `sobolevNormAt s v t = (sobolevENorm s (v(t,·))).toReal` by `rfl`).  Same constant.  This
   is the shape a Grönwall energy cap feeds back into the cylinder sup-bound for `HasAprioriBound`.

7'. **`sobolevENorm_congr_ae` / `sobolevSpace_norm_le_sobolevENorm_ordinary`** (added, review note N5)
   — `sobolevENorm_congr_ae : z =ᵐ[volume] z' → sobolevENorm s z = sobolevENorm s z'` (the datum norm
   reads the field only through the `IsSobolevDatum` Bochner pairings, `IsSobolevDatum.congr_field`),
   and the corollary restates the converse on the ordinary `L²` observation `⇑U` verbatim as the
   audit's row (ii) shape: `‖u‖ ≤ jetSobolevConst (q+1) · (sobolevENorm (q+1) (⇑U)).toReal`, for a
   smooth slice `z =ᵐ ⇑U`.  Same constant, same `hword_jet` gap; only the *proof* routes through the
   smooth slice (the a.e. representative `⇑U` is not smooth, so `DatumToJets`'s reverse bound cannot
   be applied to it directly).

## The one isolated gap of deliverable (ii): `hword_jet` (the carrier bridge, row (i)/B1-B2)

Theorems 6/7 carry a **single** named hypothesis:

```
hword_jet : ∀ n (hn : n ≤ q+1) (w : Fin n → Fin 4),
  ‖word 1 u hn w‖ ≤ (eLpNorm (iteratedFDeriv ℝ n z) 2 volume).toReal
```

i.e. each cylinder derivative word's `L²` norm is bounded by the smooth slice `z = v(t,·)`'s
order-`|w|` Fréchet-jet `L²` norm.  **Why it is a genuine tree gap, not laziness:**

* The descent that produces the words, `EulerPairing.exists_descend`, lives at the **lift** level:
  `word_hasDerivAt` is a strong *translation-orbit* derivative on `LiftL2 1`
  (`CylinderSobolevSpace.lean:70`), and the identification of the ordinary-space descent field
  `⇑Zw` with the **classical spatial derivative** of the physical velocity slice is not in the tree.
  This is precisely the carrier bridge (row (i) / B1-B2), the same content the A3_SPLIT residual
  note names.
* `SmoothDatum.lean:388-390` records the datum-to-datum **order shift** (unit U1b(ii)) as
  **untouched** ("`norm_smoothAngularDatum_le` is a one-sided bound … not a comparison of two datum
  norms").  The descent-to-classical-jet identity is the same missing analytic content.
* Phrasing the gap directly on `‖word 1 u hn w‖` (rather than on a descended `Zw`) is deliberate:
  `exists_descend`'s regularity budget is `n + 3 ≤ q + 1`, i.e. only words up to order `q − 2`
  descend (the **3-order jet loss** of the C³ representative), so the top-order words
  `n ∈ {q−1, q, q+1}` cannot even be produced by the descent.  Stating `hword_jet` on the word makes
  the hypothesis cover **all** orders `n ≤ q+1` uniformly, so the top words are not a second gap
  hiding inside the first.

**Everything except `hword_jet` is proved** (the backbone Pi-sup structure and the full reverse
embedding through `DatumToJets`, with the explicit constant `jetSobolevConst (q+1)`).

## What (i) and (iv) still need after this lane (exact statements)

* **(i) carrier bridge / `hslice` discharge — open, L.**  Produce `v : A02.SpaceTimeField` and
  `w : ClassicalSolutionR ν a f T` with `w.velocity = v`, and
  `hslice : ∀ t : Icc 0 T, (fun x => v (↑t,x)) =ᵐ[volume] ⇑(U t)` (a.e., F1) from the cylinder pair
  `(u, U)` of `Horizon.exists_local_shape_of_aprioriBound`.  **This lane sharpens (i):** it now also
  owes `hword_jet`.  The **four-part carrier-bridge lemma** that discharges `hword_jet` (reviewer §2,
  exact statements):

  - **(a) descent-to-classical-jet identity** (spatial words within the descent's reach,
    `n + 3 ≤ q + 1`): for `w : Fin n → Fin 3` and `Zw` with `ordinaryLift Zw = word 1 u _ (fun i => (w i).succ)`,
    `(⇑Zw) =ᵐ[volume] fun x => iteratedFDeriv ℝ n z x (fun i => coordinateVector (w i))`, given a
    smooth `z` with `⇑U =ᵐ z` (**open** — the descent's `word_hasDerivAt` is a *lift/translation-orbit*
    derivative, not the ordinary-space Fréchet jet);
  - **(b) jet-component bound** (elementary, `ContinuousMultilinearMap.le_opNorm` at unit vectors):
    `eLpNorm (fun x => iteratedFDeriv ℝ n z x (fun i => coordinateVector (w i))) 2 ≤ eLpNorm (iteratedFDeriv ℝ n z) 2`;
  - **(c) angular words vanish** (`hu`, **proved** by the reviewer, `rev149_angular_words.lean`):
    `word 1 u _ (Fin.cons 0 w) = 0` for angle-invariant `u` — direction `0` of `Fin 4` is the circle
    direction (`standardDirection 0 = (0,1)`, spatial ones are `i.succ`), and the orbit of an
    angle-invariant field is constant, so its `0`-derivative word is `0`;
  - **(d) L²-level descent of the invariant lift** (removes the 3-order loss, covers `n ∈ {q−1,q,q+1}`):
    `∀ g : LiftL2 1, (∀ θ, translation 1 (0,θ) g = g) → ∃ G : EulerMeanSolenoidal.L2, ordinaryLift G = g`
    by Fubini/disintegration on `ℝ³ × S¹`, **no** jet/regularity hypothesis (`exists_ordinary_value`
    spends 3 orders only on a *continuous* representative to slice at `θ = 0`, which an L²-level
    disintegration does not need).

  (a)+(b)+(c) give `hword_jet` for spatial words up to order `q − 2`; (d) removes the 3-order loss.
  Once (i) is in hand, the classical velocity slice's smoothness (`DatumToJets.contDiff_slice` from
  `ClassicalSolutionR.velocity_smooth`) and its order-`(q+1)` datum path
  (`ClassicalSolutionR.sobolev`) discharge `hz` and `hfin` of theorems 6/7 for free, closing (ii).
  Also requires matching the `ClassicalSolutionR` horizon `T` to the cylinder path's `Icc 0 T`.

* **(iv) angle invariance `hinv` of the quantified `u` — open (unit A2b), now also owed by (ii)
  (review note N2, correction).**  `HasAprioriBound` (`Horizon.lean:106`) constrains its `u` only by
  the Duhamel equation, but both `exists_local`/lane-147 and — as the review found — the *discharge*
  of (ii)'s `hword_jet` need `∀ θ t, sobolevTranslation 1 (q+1) (0,θ) (u t) = u t`.  **Correction to
  the earlier draft's "the converse is invariance-free":** true only of the *proved* part (the
  backbone Pi-sup and the reverse embedding); the *gap* `hword_jet` ranges over all `w : Fin n → Fin 4`,
  including **angular words** (direction `0`), which no property of the spatial slice controls and
  which vanish only under angle invariance (§(i)(c), proved in `rev149_angular_words.lean`).  So (iv)
  is required by (ii) as well, not only by the forward route.  Once in hand, `U` is free
  (`Continuation.forced_ordinary_descent`).

* **(v) datum / forcing bridge — open, M–L (review note, previously unlisted).**  `HasAprioriBound`
  is stated for `a : SmoothL2Field Space` and `F : Icc 0 S → SmoothL2Field Space`, but the energy
  route (this lane's (iii), and `GronwallInstance`) speaks `a ∈ initialClassR`, `f : SpaceTimeField`
  with `MemForceR f`, `MemL1Hm f`, plus `HasSmoothSobolevPath T w.velocity` and `hcont`.  **No A01
  module connects `F` to `f`:** `grep MemForceR formalization/…/A01` hits only `ForceCap`,
  `GronwallInstance`, `AprioriRows`; every `Continuation*`/`Horizon` theorem speaks
  `F`/`sobolevPath`/`coefficients`.  Exact obligation: from `(a, F)` produce `(a', f)` (a matching
  `initialClassR`/`MemForceR`/`MemL1Hm` forcing) and a `ClassicalSolutionR ν a' f T` whose velocity
  is the cylinder path's carrier.

Note: the **Grönwall output at `t = T`** of (iii) (row iii-b, the hard eq:criterion endpoint) and
the restart spine (A2b-a′ / A3-Tm / H1) that pins one `R` before the window are also still required
for `HasAprioriBound`; unchanged by this lane.  (The *cap* at `t = T` is now provided,
`kbnd_of_sup_bound_Icc_endpoint`; the *cylinder-level* endpoint `‖u‖ ≤ R` on the closed `Icc 0 T` is
free, `u` being a `ContinuousMap`, `rev149_cylinder_endpoint.lean`.)

## Failed / rejected approaches

* **Stating the converse against `⇑U`'s order-`(q+1)` datum directly (as the brief's route
  suggested).**  Rejected: `⇑U`'s datum via `EulerPairing.exists_isSobolevDatum_m_of_cylinder`
  exists only up to order `q − 2` (`m + 3 ≤ q + 1`), so `sobolevENorm (q+1) (⇑U)` is not
  constructible from the descent and may be `⊤`; and even at reachable orders the reverse bound
  `eLpNorm(⇑Zw) ≤ ‖A_k‖` on the **a.e. representative** `⇑U` is not in the tree (`DatumToJets`
  needs `ContDiff ℝ ∞`).  Resolved by routing through the smooth velocity **slice** `z = v(t,·)`
  (`ContDiff` + `H^{q+1}` datum available for a `ClassicalSolutionR`) and isolating the single
  descent-to-slice bridge `hword_jet`.
* **The `.toReal` reverse bound without the `H^{q+1}` finiteness `hfin`.**  False: with
  `sobolevENorm (q+1) z = ⊤` the RHS `jetSobolevConst·⊤.toReal = 0` while the LHS jet norm can be
  positive.  `hfin` (equivalently, an order-`(q+1)` datum of the slice) is mandatory; the ENNReal
  bound `eLpNorm ≤ ofReal c · sobolevENorm` is true but its `.toReal` is not, at `⊤`.
* **Widening the `highOrder_bddAbove_of_kbnd` conclusion by an intermediate horizon
  `T₀ < T₁ ≤ T`.**  Rejected: `kbnd_of_sup_bound` at horizon `T₁` gives `Kbnd = 256·R²·T₁ > 256·R²·T₀`,
  degrading the exponential constant to `exp(Cgron·256R²T₁)`.  Using the **same** `Kbnd` (full-horizon
  cap on `Ico 0 T`) and restricting `Icc 0 T₀ ⊆ Ico 0 T` preserves the constant.
* **`zero_le _` for the ENNReal nonneg side of `Finset.single_le_sum`** — elaboration error
  ("Function expected at `zero_le`"); `bot_le` works (`⊥ = 0` in `ℝ≥0∞`).

## Non-vacuity (`research/A01/axioms_apriori_rows.lean`)

* `nonvacuous_backbone (q) : ‖(0 : SobolevSpace 1 q)‖ ≤ 0` — the backbone fires on the zero cylinder
  field (every word is `0`), giving a genuine conclusion (`‖0‖ = 0`), not a vacuous one.
* `nonvacuous_reverse (q n) (hn : n ≤ q+1)` — the reverse embedding fires on the zero smooth field
  (`ContDiff ℝ ∞`, `H^{q+1}` via `sobolevENorm_ne_top_of_contDiff_memLp` + `iteratedFDeriv_fun_zero`),
  a genuine `0 ≤ jetSobolevConst (q+1)·0` (the finite, non-`⊤` case).

## Commands and results

All from `/data_8T/ping/blowup_density/.claude/worktrees/149-A01-a3-widen-converse`, after
`. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, lake run from `verification/`.

| command | result |
|---|---|
| `lake build NSFormalization.Section4.A01.AprioriRows` | `Built … (9981 jobs)`, EXIT 0; the only warnings are from replayed upstream/vendor modules (none from `AprioriRows`) |
| `lake env lean ../formalization/…/AprioriRows.lean` | EXIT 0, silent (0 bytes) |
| `lake env lean ../research/A01/axioms_apriori_rows.lean` | EXIT 0; all **15** declarations `depends on axioms: [propext, Classical.choice, Quot.sound]`; no `sorryAx`/`native`/extra axiom. (10 module decls incl. N1-generalized widenings, `kbnd_of_sup_bound_Icc_endpoint`, `sobolevENorm_congr_ae`, `sobolevSpace_norm_le_sobolevENorm_ordinary`; 5 non-vacuity incl. the two assembled converse theorems 6/7 and the ordinary corollary — N4) |
| `make check` | EXIT 0 (`test_contract_policy` 13 tests OK; `check_work_queue` 30 items consistent; no contract touched) |
| `grep -nE 'sorry\|admit\|native_decide\|maxHeartbeats\|\baxiom\b'` on `AprioriRows.lean` | no hits (no `set_option maxHeartbeats` used) |
