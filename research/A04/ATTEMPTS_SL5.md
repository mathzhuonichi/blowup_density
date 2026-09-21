# A04 unit G1, sub-lemma SL5 — attempts (lane 095)

Split-and-start lane for SL5 (`research/A04/G1_SPLIT.md:157-165`, rated **L**).  Goal:
split SL5 into sub-lemmas (`SL5_SPLIT.md`) and prove the **S** steps; do **not** attempt the
whole L unit.

## What was proved (all in `formalization/NSFormalization/Section4/A04/NonlinearPairing.lean`)

* **5e** `sum_inner_le_sqrt_mul_sqrt`, `abs_sum_inner_le_sqrt_mul_sqrt` — discrete
  Cauchy–Schwarz for a finite sum of inner products on any real inner product space,
  `∑ⱼ ⟪aⱼ,bⱼ⟫ ≤ √(∑‖aⱼ‖²)·√(∑‖bⱼ‖²)` (signed and `|·|` forms), generic in the finset index.
* **5d.amb** `sum_real_inner_angularDirectionalDerivative` — summed real skew-adjointness of
  `angularDirectionalDerivative s a` on the ambient `Lp ℂ 2 volume` carrier.
* **5d.sub** `sum_real_inner_angularDirectionalDerivativeReal` — the datum-carrier subtype lift
  of 082's `real_inner_angularDirectionalDerivativeReal` to `RealVectorSobolev s`.
* **5i** `inner_loweringMid_transfer`, `inner_lowering_transfer_complex`,
  `real_inner_lowering_transfer` — the two-vector, two-source-order lowering transfer
  `⟪Λ_{s→r} v, Λ_{s'→t} w⟫ = ⟪Λ_{s→r'} v, Λ_{s'→t'} w⟫` for `r + t = r' + t'`, in the mid /
  complex / real layers (added in the review-response revision below).

Axioms: all seven are exactly `[propext, Classical.choice, Quot.sound]`
(`research/A04/axioms_sl5.lean`).  No `sorry`, no `axiom`, no `native_decide`, no `maxHeartbeats`.

## Design decisions and why

1. **5e is generic in `[InnerProductSpace ℝ E]`, not `RealVectorSobolev m`.**  The final
   Cauchy–Schwarz step of SL5 runs over the three tensor columns `j : Fin 3`, pairing
   `D_j (datum G)` with `datum Wⱼ`; stating it for any real inner product space compiles today,
   sidesteps the datum carrier, and is reused verbatim at the concrete carrier.  Route:
   termwise `real_inner_le_norm` (resp. `abs_real_inner_le_norm` after `Finset.abs_sum_le_sum_abs`),
   then the real discrete Cauchy–Schwarz `Real.sum_mul_le_sqrt_mul_sqrt`
   (`Mathlib/Analysis/Real/Sqrt.lean:500`) — the same lemma C01 uses for `advection_norm_le`.

2. **5d is given in two forms.**  The subtype form (`…Real`) is the literal vector lift of 082
   (both arguments at a common order `s`).  But the SL5 integration by parts pairs `G = datum_m(u)`
   with `datum(∂ⱼWⱼ)` built from `datum_{m+1}(Wⱼ)` — different subtype orders on the shared
   `FourierData` — so the ambient form (`sum_real_inner_angularDirectionalDerivative`, over
   `Fin 3 → FourierData`) is the one the assembly (5h) actually consumes.  Both are one
   `Finset.sum_congr` + `Finset.sum_neg_distrib` over the corresponding 082 lemma.

3. **The `-∑ = ∑ -` step is `Finset.sum_neg_distrib`** (used elsewhere in tree:
   `Source/OrdinaryViscousStability.lean:42`, `Paper1/ConservativeForce.lean:66`), applied
   backwards so the goal becomes a termwise `Finset.sum_congr`.

## Approaches tried and outcome

* **`Finset.sum_neg` for `-∑ = ∑ -`** — wrong lemma family (`Finset.sum_neg` in tree is about
  `SignType`/sign sums with side hypotheses).  The additive-group distributor is
  `Finset.sum_neg_distrib`.  Confirmed by grep of both mathlib and the local tree.

* **Stating 5d only on the subtype at a common order** — rejected as insufficient.  Would force
  an artificial order match between `G` (order `m`) and the column data (order `m+1`) that the
  actual IBP does not have; kept the ambient-carrier version as the primary consumer form.

* **Doc-comment `/--` on `open` in the axioms file** — parse error (`/--` must attach to a
  declaration).  Switched to a plain `/- … -/` block comment.

## 5a — recorded, not attempted (M, per the split brief)

The brief says to attempt 5a only if its derivative bookkeeping is **S**, else record the exact
obstacle and stop.  It is **M** (no blocker), so it is recorded here and left to the L unit.

Target (div-free `u`, `z := u(t,·)`, at a point `x`):
`advection u t x = ∑ⱼ partialDeriv j (outerColumn z z j) x`.

Verified facts:
* `advection u t x = fderiv ℝ z x (z x)` and `partialDeriv j v x = fderiv ℝ v x (coordinateVector j)`
  (both defeq to `spatialDerivative`; C01 uses the first as `rfl`).
* `outerColumn z z j = fun y => (z y j) • z y`.

Route (the M-sized work):
1. Product rule `HasFDerivAt.smul` on `Wⱼ = (fun y => z y j) • z` gives
   `fderiv ℝ Wⱼ x = (z x j) • fderiv ℝ z x + (fderiv ℝ (fun y => z y j) x).smulRight (z x)`;
   evaluate at `e_j`, using the chain rule `fderiv (projⱼ ∘ z) x = projⱼ ∘ fderiv z x`
   (`projⱼ = PiLp.proj 2 _ j` a CLM), to get
   `partialDeriv j Wⱼ x = (z x j) • (fderiv z x e_j) + ((fderiv z x e_j) j) • z x`.
2. Sum over `j`.  First term: `∑ⱼ (z x j) • fderiv z x e_j = fderiv z x (z x) = advection`, the
   basis expansion `hmap`/`hbasis` of `C01/Trilinear.lean:92-98`.  Second term:
   `(∑ⱼ (fderiv z x e_j) j) • z x = (spatialDivergence u t x) • z x` (definition
   `spatialDivergence`), which vanishes when `div u = 0`.

Obstacle to S: two CLM manipulations (`.smulRight` evaluation and the `projⱼ` chain rule) plus a
`Fin.sum_univ_three`-style rearrangement — real fderiv product-rule bookkeeping, more than a
one-liner.  No datum carrier, no upstream gap; a follow-up lane can close it.

## Commands
* `lake build NSFormalization.Section4.A04.RealPairing NSFormalization.Section4.A03.OuterTameProduct
  NSFormalization.Section4.A04.LaplacianDatum` — OK (9893 jobs).
* `lake build NSFormalization.Section4.A04.NonlinearPairing` — OK (9894 jobs, 3.9s).
* `lake env lean ../formalization/.../A04/NonlinearPairing.lean` — clean (silent, exit 0).
* `lake env lean ../research/A04/axioms_sl5.lean` — all four
  (`sum_inner_le_sqrt_mul_sqrt`, `abs_sum_inner_le_sqrt_mul_sqrt`,
  `sum_real_inner_angularDirectionalDerivative`, `sum_real_inner_angularDirectionalDerivativeReal`)
  `[propext, Classical.choice, Quot.sound]`.
* `make check` — see final report.

## Review response (095, ACCEPT-WITH-NOTES — `research/A04/REVIEW_SL5.md`)

The four lemmas were accepted as faithful, unconditional and non-vacuous.  Doc + one-lemma
follow-ups applied:

### F4 — branch note (088 absent).  The correct reason SL5 could not reuse SL3's machinery is not
that "SL3 is open" but that **lane 088's `Section4/A04/LaplacianAssembly.lean` is absent from this
worktree**: PR #94 merged it to `erenup/integration` *after* this lane branched.  It closed SL3 and
supplies `derivDatumStep`, `isSobolevDatum_castOrder`/`castOrder`/`cast_mid_order`/`cast_top_order`,
`coe_derivDatumStep`, `norm_sq_derivDatumStep`, `isSobolevDatum_lowerVectorL` + `coe_lowerVectorL`,
`directionalDerivative_orderLowering_comm`, `angularMid_comm`, `isSobolevDatum_laplacian` — all
reused by SL5's 5c/5h.  Read it with
`git show origin/erenup/integration:formalization/NSFormalization/Section4/A04/LaplacianAssembly.lean`;
it is **not** imported here.  `SL5_SPLIT.md` now carries this note and the corrected table.

### Size re-ratings (F1–F3) recorded in `SL5_SPLIT.md`.
* **5f is S, not "gated on SL3".**  As stated (`√(∑‖D_j A'‖²) = gradientSobolevNormAt`, with
  `A' = datum_{m+1}(u)`) it is exactly `gradientSobolevENorm_toReal_sq_eq_datum_sum`
  (`LaplacianDatum.lean:130`, already on this branch) + `Real.sqrt_sq ENNReal.toReal_nonneg`.  The
  order shift the old note attributed to 5f is a property of the **assembly (5h)**, and PR #94
  supplies the transports (`isSobolevDatum_lowerVectorL`, `directionalDerivative_orderLowering_comm`).
* **5b is S** (`A03.tameProductVector (m+1)` ⇒ enorm `≠ ⊤`, then `A03.exists_sobolevDatum`;
  `VectorTameProduct.lean:77,256`); the `SmoothL2Field` wrapping is a 5c requirement.
* **5c is S–M** (one-step copy of 088's `isSobolevDatum_laplacian`).

### F5 — citation drift fixed in `SL5_SPLIT.md`: `outerColumn` :68 (was :63), `gradientSobolevENorm`
:87 (was :76), `realSobolev_inner_eq_ambient` :77, `real_inner_angularDirectionalDerivative` :84
(was :85).  Re-verified all by grep against the current branch.

### 5i — the two-vector lowering transfer (the substantive follow-up, proved).

The reviewer identified 5i as SL5's only genuinely new analytic content and rated it **S**.  Proved
in three layers mirroring 082 (`RealPairing.lean:168/199/218`):

* `inner_loweringMid_transfer` — generalizes `inner_loweringMid_pairing`.  Route confirmed: the two
  `ring` steps of the single-vector proof never used `v = w`.  After
  `L2.inner_def` + `integral_congr_ae` + the four `angularOrderLoweringMid_coeFn` filters and
  `RCLike.inner_apply`/`lowering_mid_symbol_eq`, the pointwise goal is
  `(b_{r-s}·conj(v ξ))·(b_{t-s'}·w ξ) = (b_{r'-s}·conj(v ξ))·(b_{t'-s'}·w ξ)`.  The shared factor is
  `conj(v ξ)·w ξ` (not `v ξ·conj(v ξ)`), and the symbol identity
  `b_{r-s}·b_{t-s'} = b_{r'-s}·b_{t'-s'}` follows from `sobolevBesselWeight_mul` with exponents equal
  under `r + t = r' + t'`.  Closed with `linear_combination (conj (v ξ) * w ξ) * hsym` — robust to
  the multiplication ordering, unlike the original's two `show … from by ring` rewrites.
* `inner_lowering_transfer_complex` — transport across `U = angularFrequencyDilation`
  (`angularOrderLowering_eq_dilation_mid` on all four slots + `inner_map_map` twice), passing
  `U⁻¹ v`, `U⁻¹ w`; verbatim structure of `inner_lowering_pairing_complex`.
* `real_inner_lowering_transfer` — real part via `real_inner_eq_re_complex` on **both** sides
  (two inner products, unlike the single `real_inner_lowering_pairing` whose RHS is a norm).

Approaches considered and rejected:
* **Matching the original's `show A = B from by ring` term forms** — brittle here because the two
  vectors break the symmetric `v ξ * conj (v ξ)` grouping.  `linear_combination` over ℂ (a comm
  ring, `conj (v ξ)` an atom) handles all reassociation and is order-agnostic.
* No `maxHeartbeats` bump needed; there is **no dependent-order index** (unlike the midpoint
  `(r+t)/2` of the single-vector pairing), so none of 082's `rw`-motive caveats apply.

Commands (in addition to those above):
* `lake build NSFormalization.Section4.A04.NonlinearPairing` — OK (9894 jobs, 3.3s).
* `lake env lean ../formalization/.../A04/NonlinearPairing.lean` — silent, exit 0.
* `lake env lean ../research/A04/axioms_sl5.lean` — all **seven** declarations
  `[propext, Classical.choice, Quot.sound]`.
