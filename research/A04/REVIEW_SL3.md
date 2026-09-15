# Review — lane 066, task A04, sub-lemma SL3 (partial)

Reviewer: opus (lane-review, light & strict).  Commit under review: `e779166`
(`[066-A04] SL3 partial: angular directional-derivative multiplier …`).
Worktree: `.claude/worktrees/066-A04-sl3-laplacian`.  Read/build only.

## Verdict

**ACCEPT-WITH-NOTES.**

The Lean is sound: both new modules build and elaborate with zero warnings, are
`sorry`-free, depend only on the three standard logical axioms, and `make check`
passes.  The mathematics is right — including the `2π` question, which I checked
independently and which comes out exactly as the module docstring claims.  The
lane is honestly labelled "partial": it delivers precisely the two prerequisites
`G1_SPLIT.md` §SL3 named, and leaves the pairing identity.

The notes are (a) one avoidable `maxHeartbeats` bump whose recorded cause
mis-locates the cost, (b) one redundant hypothesis, (c) **two substantive
inaccuracies in the gap analysis, both of which make the remaining work *smaller*
than the record claims**, and (d) documentation hygiene.  No finding requires a
change to any proved statement.

---

## 1. Build, axioms, hygiene — all green

| check | result |
|---|---|
| `lake build …D01.DerivativeDatum …A04.LaplacianDatum` | `Build completed successfully (9891 jobs)` |
| fresh `lake env lean` on `DerivativeDatum.lean` | **empty output** — zero warnings, zero errors |
| fresh `lake env lean` on `LaplacianDatum.lean` | **empty output** — zero warnings, zero errors |
| `lake env lean ../research/A04/axioms_sl3.lean` | exit 0; **11** declarations, each `[propext, Classical.choice, Quot.sound]` |
| `make check` | **exit 0** (plan, contracts, contract policy, work queue: "30 work items … consistent") |
| `grep -nE 'sorry\|admit\|native_decide\|axiom\|maxHeartbeats\|set_option'` | see below |

Grep hits, complete list:

* `LaplacianDatum.lean:32` — the words "no `sorry`" inside a docstring heading.
* `LaplacianDatum.lean:106` — `set_option maxHeartbeats 400000 in`.  **The only
  `set_option` in either module.**  Finding 1.
* `research/A04/axioms_sl3.lean:5,7,8` — the word "axioms" in the docstring; lines
  16-29 are the `#print axioms` commands themselves.
* `DerivativeDatum.lean` — **no hits at all**.

No `sorry`, no `admit`, no `native_decide`, no `axiom` declaration anywhere.

---

## 2. Findings

### Finding 1 — [Medium] `LaplacianDatum.lean:106`: the heartbeat bump is avoidable, and the recorded cause mis-locates the cost

The record (`ATTEMPTS_SL3.md:57-59`, and the brief) attributes the bump to "the
datum-term defeq — the operator's codomain type `RealSobolevHilbert ((m:ℝ)+1-1)`
unifies with `RealSobolevHilbert (m:ℝ)`, which is expensive".  I bisected and
localized this in a scratch copy (`/tmp/sl3rev/`, outside the worktree).

**Measured floor.**  FAIL at `200100`, OK at `201000`.  The declaration overshoots
the default 200000 budget by **less than 0.5 %**.  `400000` is therefore ~2× the
need — generous but harmless.

**The statement is not the expensive part.**  Replacing the proof by `sorry` and
removing the `set_option` compiles at the default budget (only the `sorry`
warning).  So the type ascription `… : RealVectorSobolev (m : ℝ))` in the
statement elaborates comfortably inside the default.

**Localization of the cost.**  With the `set_option` removed and the default
budget:

* proof truncated before the last `rw` block → **OK**
* `rw [sobolevENorm_eq (isSobolevDatum_partialDeriv j m hA)]` then `sorry` → **OK**
* `rw [sobolevENorm_eq …, ← ofReal_norm]` then `sorry` → **OK**
* adding `ENNReal.toReal_ofReal (norm_nonneg _)` → **timeout**

The entire overshoot sits in the final `ENNReal.toReal_ofReal (norm_nonneg _)`
rewrite, where `norm_nonneg _` leaves the type and its `Norm`/`NormedAddCommGroup`
instance as metavariables that must be reconciled against the datum term's
instance tower.  That tower is indeed the phantom-order carrier — `realSubspace`
(`Source/RealSobolev.lean:118`) ignores its `_s` argument, so the unifier fails
first-order on `(m:ℝ)+1-1 =?= (m:ℝ)` and has to delta-unfold — so the recorded
cause is right in **kind**, but wrong in implying it bites at the statement, and
wrong in implying it is unavoidable.

**The brief's suggested fixes do NOT work.**  Both still time out at the default:

* a typed `have hdat : IsSobolevDatum (m:ℝ) … ((… ) : RealVectorSobolev (m:ℝ)) := isSobolevDatum_partialDeriv j m hA` before the `rw` → **timeout**
* dropping the type ascription from the statement entirely → **timeout**

**The fix that does work.**  Mathlib has the one-shot lemma
`toReal_enorm : ‖x‖ₑ.toReal = ‖x‖` (`Mathlib/Analysis/Normed/Group/Basic.lean:392`,
the `to_additive` of `toReal_enorm'`).  Replacing the two rewrites by it:

```lean
  rw [sobolevENorm_eq (isSobolevDatum_partialDeriv j m hA), toReal_enorm]
```

compiles **at the default budget**, no `set_option`, no warnings.  So does
`rw [sobolevENorm_eq (isSobolevDatum_partialDeriv j m hA)]; simp`.

**Fix:** delete `set_option maxHeartbeats 400000 in` at `:106` and use
`toReal_enorm`.  (Best combined with Finding 2 — see the combined patch there.)

### Finding 2 — [Medium] `LaplacianDatum.lean:119`: `hfin` is a redundant hypothesis

`gradientSobolevENorm_toReal_sq_eq_datum_sum` takes
`hfin : ∀ j, sobolevENorm (m:ℝ) (partialDeriv j Z.field) ≠ ⊤`, but `hA` already
implies it: `sobolevENorm_eq (isSobolevDatum_partialDeriv j m hA)` rewrites that
enorm to `‖…‖ₑ`, which is never `⊤`.  Every downstream SL3 consumer would
otherwise have to discharge a side condition that is free.

Verified: the following compiles at the **default** heartbeat budget, `sorry`-free,
`[propext, Classical.choice, Quot.sound]` only — it fixes Findings 1 and 2 together:

```lean
theorem gradientSobolevENorm_toReal_sq_eq_datum_sum {Z : SmoothL2Field Space} (m : ℕ)
    {A : RealVectorSobolev ((m : ℝ) + 1)} (hA : IsSobolevDatum ((m : ℝ) + 1) Z.field A) :
    (gradientSobolevENorm (m : ℝ) Z.field).toReal ^ 2 =
      ∑ j : Fin 3, ‖((WithLp.toLp 2 fun i =>
          angularDirectionalDerivativeReal ((m : ℝ) + 1) (coordinateVector j) (A i)) :
          RealVectorSobolev (m : ℝ))‖ ^ 2 := by
  have hfin : ∀ j : Fin 3, sobolevENorm (m : ℝ) (partialDeriv j Z.field) ≠ ⊤ := by
    intro j
    rw [sobolevENorm_eq (isSobolevDatum_partialDeriv j m hA)]
    exact enorm_ne_top
  rw [gradientSobolevENorm_toReal_sq_eq_sum hfin]
  apply Finset.sum_congr rfl
  intro j _
  rw [sobolevENorm_eq (isSobolevDatum_partialDeriv j m hA), toReal_enorm]
```

(`gradientSobolevENorm_toReal_sq_eq_sum` at `:84` should keep its `hfin` — there it
is genuinely needed, since no datum is assumed.)

### Finding 3 — [Medium] `ATTEMPTS_SL3.md:111-113`: "genuinely different maps at different orders" is false

The record warns that "the angular `cyclesToAngular` transport depends on the
order, so `angularDirectionalDerivative` at orders `m+2→m+1` and `m+1→m` are
genuinely different maps (unlike the cycles operator, whose symbol is
order-independent)", and calls the resulting order bookkeeping "intricate".

This is wrong.  Unfolding the definition,
`angularDirectionalDerivative s a = U ∘ (W_{s-1} ∘ σ_a ∘ W_{-s}) ∘ U⁻¹`
where `U = angularFrequencyDilation`, `W_t = angularWeightEquiv`-multiplication by
`angularWeightSymbol t`, and `σ_a = sobolevDirectionalSymbol a`-multiplication.
The middle symbol is
`angularWeightSymbol (s-1) ξ · sobolevDirectionalSymbol a ξ · angularWeightSymbol (-s) ξ`,
and the two weight factors collapse to `W(-1)(2πξ)·W(1)(ξ)` — **independent of `s`**.
`U` does not depend on `s` either.  So all `angularDirectionalDerivative s a` are
the *same* operator.

Machine-checked in a scratch file (`sorry`-free, standard axioms only):

```lean
theorem mid_symbol_order_independent (s t : ℝ) (a ξ : Space) :
    angularWeightSymbol (s - 1) ξ * sobolevDirectionalSymbol a ξ * angularWeightSymbol (-s) ξ =
      angularWeightSymbol (t - 1) ξ * sobolevDirectionalSymbol a ξ * angularWeightSymbol (-t) ξ
```

**Consequence:** the "intricate" order bookkeeping of gap item 3 largely dissolves;
once the coefficient function is in hand (gap item 1, cheap — see Finding 4), the
order-independence is a corollary.  **This makes the remaining work smaller, not
larger.**  The gap record should be corrected so the next lane does not budget for
a problem that isn't there.

### Finding 4 — [Medium] `ATTEMPTS_SL3.md:88-100` / `LaplacianDatum.lean:38-44`: the proposed route is harder than necessary — the dilation's a.e. coefficient function is not needed

The record calls the crux "the a.e. coefficient function of
`angularDirectionalDerivative` … a multi-step a.e. chase through the
dilation/weight coefficient functions", obtained by "composing the a.e. coefficient
functions of `cyclesToAngular` (= `angularFrequencyDilation ∘ angularWeightEquiv`,
a frequency dilation and a real weight multiplication)".

The dilation part is unnecessary, and it is the only expensive part.  I confirmed
there is **no** a.e. coefficient lemma for `angularFrequencyDilation` anywhere in
the tree (only `angularWeightMap_coeFn` / `angularWeightEquiv_coeFn` exist), and
getting one would mean a change-of-variables argument through
`extendOfIsometry` — genuinely awkward.  But `angularFrequencyDilation` is a
`LinearIsometryEquiv` (`AngularFourierDilation.lean:80`, `≃ₗᵢ[ℂ]`), i.e. **unitary**,
so `LinearIsometryEquiv.inner_map_map` transports adjointness across it in one
step.  Do the adjointness work on the *middle* operator only, where all three
factors are multiplication operators that **already have `_coeFn` lemmas**:

* `angularWeightMap_coeFn (s-1)` (`AngularSobolevCoordinates.lean:62`)
* `sobolevDirectionalDerivative_coeFn s a` (`SobolevDirectionalDerivative.lean:59`)
* `angularWeightMap_coeFn (-s)` — note `(angularWeightEquiv s).symm = angularWeightMap (-s)` by definition (`AngularSobolevCoordinates.lean:97`)

### Finding 5 — [Low] `ATTEMPTS_SL3.md:89-90`: `conj_sobolevDirectionalSymbol_neg` is not the fact skew-adjointness needs

The record says the symbol is "purely imaginary (`conj σ = -σ`, already isolated as
`conj_sobolevDirectionalSymbol_neg`)".  It is not isolated.
`conj_sobolevDirectionalSymbol_neg` (`DerivativeDatum.lean:82`) states
`conj (σ(-ξ)) = σ(ξ)` — the *odd-and-imaginary* combination, which is exactly right
for reality preservation but is a strictly weaker statement than pure imaginarity
at a point.  From `conj σ(-ξ) = σ(ξ)` alone you cannot get `conj σ(ξ) = -σ(ξ)`.

The missing fact is trivial (I proved it, `sorry`-free, standard axioms, in three
lines with the same simp set), so the *cost* is negligible — but the record claims
something it does not have, and the next lane should not be told the step is done.

### Finding 6 — [Low] `ATTEMPTS_SL3.md` has no snags section; the two snags the brief named are real but unrecorded

The project workflow asks for positive *and* negative examples.  `ATTEMPTS_SL3.md`
records only successes — no "what failed" section, no mention of `map_ofReal` or of
`norm_num`.  Both snags are genuine; I verified them:

* **`map_ofReal` unknown.**  `#check @map_ofReal` →
  `error(lean.unknownIdentifier): Unknown identifier 'map_ofReal'`.  The lane
  correctly used `Complex.conj_ofReal` + `map_ofNat` instead
  (`DerivativeDatum.lean:85-86`).
* **`norm_num` collapses `^(2:ℝ)` to `^(2:ℕ)`.**
  `example (x : ℝ) : x ^ (2:ℝ) = x ^ (2:ℕ) := by norm_num` **succeeds**.  This is
  exactly why `LaplacianDatum.lean:90` has the defensive
  `← Real.rpow_natCast (…) 2` before the bare `norm_num` at `:93`.  (The same
  hazard is handled upstream with `norm_num only [… , Real.rpow_two]` in
  `AngularFourierDilation.lean:70`.)

Both are worth writing down — they are the kind of thing the next lane re-discovers.

### Finding 7 — [Low] every Lean line citation in `ATTEMPTS_SL3.md` is off by +10 to +16

Cited → actual:

`angularDirectionalDerivative` :63→**61** · `angularRealization_directionalDerivative`
:73→**68** · `conj_sobolevDirectionalSymbol_neg` :85→**82** ·
`realSymmetry_sobolevDirectionalDerivative` :93→**90** ·
`cyclesToAngular_symm_realSymmetry` :106→**103** ·
`realSymmetry_angularDirectionalDerivative` :113→**111** ·
`angularDirectionalDerivative_mem_realSubspace` :126→**123** ·
`angularDirectionalDerivativeReal` :143→**133** · `…Real_coe` :153→**140** ·
`isSobolevDatum_partialDeriv` :190→**172**;
`gradientSobolevNormAt` :88→**75** · `…_toReal_sq_eq_sum` :100→**84** ·
`…NormAt_sq_eq_sum` :116→**100** · `…_datum_sum` :127→**117**.

### Finding 8 — [Low] `research/A04/axioms_sl3.lean` audits 11 of the 15 new declarations

Not audited directly: `conj_sobolevDirectionalSymbol_neg`,
`realSymmetry_sobolevDirectionalDerivative`, `cyclesToAngular_symm_realSymmetry`,
`angularDirectionalDerivativeReal_coe`.  All four are transitive dependencies of
audited declarations, so coverage is complete **in substance** — but adding the
four lines makes the audit self-evidently complete.  (The brief expected 12
commands; the file has 11.)

### Finding 9 — [Low] the proposed gap route silently diverges from `G1_SPLIT.md`'s own SL3 recommendation

`G1_SPLIT.md` §SL3 recommends the "pin-the-representative" technique
(`A03.representative_ae` + `angularRealization_boundedRepresentative`) for the
pairing identity, "reducing it to a pointwise integration by parts of continuous
representatives".  `ATTEMPTS_SL3.md` proposes a different (symbol/adjointness)
route without mentioning the split's.  I think the symbol route is the **better**
one — the datum-carrier inner product *is* the angular `L²` inner product of
Fourier data, so "integration by parts" there is literally "the symbol is
imaginary" — but the divergence should be recorded so `G1_SPLIT.md` can be updated.

---

## 3. What I checked and found **correct** (no action)

* **The `2π` question — the docstring's symbol claim is exactly right.**  The
  cycles symbol is `sobolevDirectionalSymbol a ξ = 2πi⟨ξ,a⟩(1+‖ξ‖²)^{-1/2}`
  (Mathlib's `e^{-2πi⟨x,ξ⟩}` convention).  Conjugating by
  `cyclesToAngular = angularFrequencyDilation ∘ angularWeightEquiv`: the weight
  factors contribute `⟨2πη⟩^{-1}⟨η⟩`, turning the middle symbol into
  `2πi⟨η,a⟩(1+‖2πη‖²)^{-1/2}`; the dilation then evaluates at `η = ξ/2π`
  (`schwartzAngularDilation φ ξ = c^{-3/2}•φ(c⁻¹ξ)`, amplitudes cancel), giving
  `2πi·(2π)⁻¹⟨ξ,a⟩(1+‖ξ‖²)^{-1/2} = i⟨ξ,a⟩(1+‖ξ‖²)^{-1/2}`.
  Since `frequencyUnit = 2 * Real.pi` (`Source/FourierConvention.lean:15`), the
  cycles `2π` is **exactly** cancelled by the `(2π)^{-1}` the dilation
  contributes.  **So the docstring's `iξⱼ (1+‖ξ‖²)^{-1/2}` is literally correct,
  and no stray `(2π)^{±1}` is hiding anywhere.**
* **`angularRealization_directionalDerivative` (`:68`) is constant-free and the
  chain into the physical derivative is honest.**  It is stated as
  `angularRealization (s-1) (D h) = ∂_{a} (angularRealization s h)` with no
  constant, proved by transport from `sobolevRealization_directionalDerivative`.
  Downstream, `physicalDistribution_directionalField`
  (`Source/PhysicalSobolevDistribution.lean:29`) is a genuine integration by parts
  (`integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable`), and
  `partialDeriv j v x = spatialDerivative (lift v) 0 x (coordinateVector j)`
  (`A03/OuterTameProduct.lean:59`) is the plain `∂ⱼ`.  No constant anywhere.
* **`isSobolevDatum_partialDeriv` (`:172`) says what the brief expects** — for a
  `SmoothL2Field Space` `Z` and an order-`(m+1)` datum `A` of `Z.field`, the
  componentwise `angularDirectionalDerivativeReal (m+1) eⱼ` of `A` is an order-`m`
  datum of `A03.partialDeriv j Z.field`.  The `calc` chain is five honest steps.
* **Reality preservation.**  `conj_sobolevDirectionalSymbol_neg` is correct:
  `σ` is odd × imaginary, so `conj σ(-ξ) = σ(ξ)`.  The transport
  (`realSymmetry_sobolevDirectionalDerivative` → `cyclesToAngular_symm_realSymmetry`
  → `realSymmetry_angularDirectionalDerivative` → `…_mem_realSubspace`) follows the
  existing `realSymmetry_sobolevOrderLowering` template faithfully.
* **"`cyclesToAngular` rescales the inner product non-uniformly" is CORRECT.**
  `cyclesToAngular s = (angularWeightEquiv s).trans angularFrequencyDilation`
  (`AngularTameProduct.lean:11`).  The dilation is a `≃ₗᵢ` (unitary), but
  `angularWeightEquiv s` is multiplication by
  `angularWeightSymbol s ξ = (1+4π²‖ξ‖²)^{s/2}(1+‖ξ‖²)^{-s/2}`
  (`AngularSobolevCoordinates.lean:12`), genuinely `ξ`-dependent for `s ≠ 0`.  So
  `cyclesToAngular` is not a scalar multiple of an isometry and adjointness does
  not transport by conjugation in general.  The lane is also right that the
  imaginary-symbol argument supplies it anyway — I verified that below.
* **`gradientSobolevNormAt` faithfully restates `Spec.lean:190`.**  Both
  `A03.gradientSobolevENorm` (`OuterTameProduct.lean:87`) and
  `Contracts.V1.TameProduct.gradientSobolevENorm` (`TameProduct.lean:192`) are
  `columnsSobolevENorm s (fun j => partialDeriv j v)`, with `columnsSobolevENorm`
  and `partialDeriv` textually identical in the two files.  The docstring's
  "definitionally equal" claim holds.
* **`inner_energy_assembly` really does weaken `hlap` to `≤`** with `0 ≤ ν`
  (`HighEnergy.lean:101-110`), over a general real inner-product space `E`; and
  `RealVectorSobolev s = PiLp 2 (fun _ : Fin 3 => RealSobolevHilbert s)` does carry
  a real inner product (`#check fun (s:ℝ) (x y : RealVectorSobolev s) => ⟪x,y⟫_ℝ`
  elaborates to `ℝ`).  So the SL3 target type-checks as an instance.
* **Scope honesty.**  `G1_SPLIT.md` §SL3 names exactly two prerequisites — "the
  datum of `∂ᵢu` at order `m` and the **datum-side** order shift", and "a
  formalization def of `gradientSobolevNormAt` … as N1-style bookkeeping over
  `A03.gradientSobolevENorm`".  Both are delivered.  Labelling the lane "partial"
  is accurate, and the module docstrings state the gap precisely rather than
  hiding it.

---

## 4. Gap-route assessment — the honest remaining work, and its size

**Is the proposed route the honest remaining work?**  Yes in outline, but it is
described as harder than it is, and two of its three items are mis-stated
(Findings 3–5).  Corrected, the route is:

Write `angularDirectionalDerivative s a = U ∘ M_s ∘ U⁻¹` with `U =
angularFrequencyDilation` (unitary) and `M_s = W_{s-1} ∘ σ_a ∘ W_{-s}` a product of
three **multiplication** operators.  Then:

| step | what | size | evidence |
|---|---|---|---|
| 1 | a.e. coefficient of `M_s`: chain `angularWeightMap_coeFn (s-1)`, `sobolevDirectionalDerivative_coeFn s a`, `angularWeightMap_coeFn (-s)` with three `filter_upwards` | **S** | all three lemmas already exist |
| 2 | the middle symbol is purely imaginary, at every order | **XS** | machine-checked by me, one `simp only … ; ring` |
| 3 | skew-adjointness of `M_s` on `L²`: `MeasureTheory.L2.inner_def` + `integral_congr_ae` + step 2 | **S–M** | the only genuinely new analytic step |
| 4 | transport to `angularDirectionalDerivative` | **XS** | `LinearIsometryEquiv.inner_map_map` on the unitary `U` — **no dilation coeFn needed** |
| 5 | self-adjointness of `angularOrderLowering` — same template, middle symbol is real | **XS** given 3 | machine-checked by me |
| 6 | real-subspace + `PiLp 2` bookkeeping (`re` of the complex pairing, componentwise sum) | **S–M** | carrier inner product verified to exist |
| 7 | Laplacian datum `datum_m(Δu) = ∑ⱼ D_j(D_j(datum_{m+2} u))`: `isSobolevDatum_partialDeriv` twice + `D01.isSobolevDatum_add` | **M** | **no order bookkeeping**, by Finding 3 |

I machine-checked steps 2 and 5 and the order-independence of step 7's operator in
a scratch file — all three `sorry`-free with `[propext, Classical.choice,
Quot.sound]`:

```lean
theorem mid_symbol_imaginary (s : ℝ) (a ξ : Space) :
    conj (angularWeightSymbol (s-1) ξ * sobolevDirectionalSymbol a ξ * angularWeightSymbol (-s) ξ)
      = -(angularWeightSymbol (s-1) ξ * sobolevDirectionalSymbol a ξ * angularWeightSymbol (-s) ξ)
theorem lowering_symbol_real (s r : ℝ) (ξ : Space) :
    conj (angularWeightSymbol r ξ * sobolevBesselWeight (r-s) ξ * angularWeightSymbol (-s) ξ)
      = angularWeightSymbol r ξ * sobolevBesselWeight (r-s) ξ * angularWeightSymbol (-s) ξ
theorem cycles_symbol_imaginary (a ξ : Space) :
    conj (sobolevDirectionalSymbol a ξ) = -(sobolevDirectionalSymbol a ξ)
```

**Overall size: S–M — smaller than the lane's own estimate.**  The record calls the
a.e. chase "the crux"; with the unitary shortcut of Finding 4 it is three
`filter_upwards` over lemmas that already exist.  The real work is steps 3, 6 and
7, i.e. roughly one prover lane.  Nothing is blocked on unowned upstream, as the
record correctly says.

**One asset the gap analysis does not mention:**
`Source/OrdinaryViscousStability.lean:32` already proves the order-0 identity in
exactly the target shape —
`laplacian_pairing (W : SmoothL2Field Space) : ⟪W.toLp, (laplacianField W).toLp⟫_ℝ = -∑ i, ‖(W.directionalField (axis i)).toLp‖ ^ 2`
— on the jet carrier, from a physical integration by parts (`field_directional_inner`).
It cannot be transported to order `m` (the datum-carrier norm is the `H^m` norm,
not the `L²` norm), but it is a ready-made template and a sanity target for step 7,
and `laplacian_pairing_nonpos` is the exact `≤` shape `hlap` wants.

---

## 5. Commands run, with results

All from `WT/verification` after `bash scripts/lean-install.sh`,
`. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`, one lake at a time.
Scratch experiments were written to `/tmp/sl3rev/`, never into the worktree.

```
$ bash scripts/lean-install.sh
… == OK

$ lake build NSFormalization.Section4.D01.DerivativeDatum \
             NSFormalization.Section4.A04.LaplacianDatum
Build completed successfully (9891 jobs).
  # all warnings in the log come from pre-existing modules
  # (RealPositiveDensity, PhysicalBesselSobolev, PacketForceExtension,
  #  ViscosityPacket, RealVectorPositiveDensity, BoundedViscosityUniqueness);
  # none from either new file.

$ lake env lean ../formalization/NSFormalization/Section4/D01/DerivativeDatum.lean
  (empty — zero warnings, zero errors)
$ lake env lean ../formalization/NSFormalization/Section4/A04/LaplacianDatum.lean
  (empty — zero warnings, zero errors)

$ lake env lean ../research/A04/axioms_sl3.lean ; echo $?
'NSFormalization.Paper3.angularDirectionalDerivative'                 [propext, Classical.choice, Quot.sound]
'NSFormalization.Paper3.angularRealization_directionalDerivative'     [propext, Classical.choice, Quot.sound]
'NSFormalization.Paper3.realSymmetry_angularDirectionalDerivative'    [propext, Classical.choice, Quot.sound]
'NSFormalization.Paper3.angularDirectionalDerivative_mem_realSubspace'[propext, Classical.choice, Quot.sound]
'NSFormalization.Paper3.angularDirectionalDerivativeReal'             [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.D01.angularRealization_of_isSobolevDatum'   [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.D01.isSobolevDatum_partialDeriv'            [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.gradientSobolevNormAt'                  [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.gradientSobolevENorm_toReal_sq_eq_sum'  [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.gradientSobolevNormAt_sq_eq_sum'        [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.gradientSobolevENorm_toReal_sq_eq_datum_sum' [propext, Classical.choice, Quot.sound]
0
  # 11 commands, not the 12 the brief expected — Finding 8.

$ make check ; echo $?
… python3 experiments/check_formalization_plan.py --check   → ok
… python3 experiments/check_contracts.py                    → ok
… python3 experiments/test_contract_policy.py               → Ran 13 tests … OK
… python3 experiments/check_work_queue.py                   → 30 work items: ownership,
                                                              contract registration and
                                                              task cards consistent.
0

# --- heartbeat bisection (scratch copies of LaplacianDatum.lean) ---
maxHeartbeats 200000 → FAIL  "(deterministic) timeout at `whnf`, maximum number of heartbeats (200000)"
maxHeartbeats 200100 → FAIL
maxHeartbeats 201000 → OK
maxHeartbeats 202000 / 205000 / 208000 / 212000 / 216000 / 220000 / 260000 / 300000 / 340000 / 380000 → OK
  ⇒ floor is 200 100 < N ≤ 201 000; the recorded 400000 is ~2× the need.

# --- localization at the DEFAULT budget, set_option removed ---
statement only (proof = sorry)                              → OK (only the sorry warning)
proof truncated before the last rw block                    → OK
… + rw [sobolevENorm_eq (isSobolevDatum_partialDeriv j m hA)] → OK
… + rw [← ofReal_norm]                                      → OK
… + rw [ENNReal.toReal_ofReal (norm_nonneg _)]              → TIMEOUT   ⇐ the whole cost

# --- fix candidates at the DEFAULT budget, set_option removed ---
typed `have hdat : … : RealVectorSobolev (m:ℝ)` before the rw → TIMEOUT  (brief's suggestion: does NOT work)
statement with the type ascription dropped                   → TIMEOUT  (does NOT work)
rw [sobolevENorm_eq …, toReal_enorm]                         → OK, clean
rw [sobolevENorm_eq …]; simp                                 → OK, clean
hfin derived internally + toReal_enorm (Findings 1+2)        → OK, clean, [propext, Classical.choice, Quot.sound]

# --- snag spot-checks ---
#check @map_ofReal
  → error(lean.unknownIdentifier): Unknown identifier `map_ofReal`      (snag confirmed)
example (x : ℝ) : x ^ (2:ℝ) = x ^ (2:ℕ) := by norm_num
  → succeeds                                                            (snag confirmed)

# --- gap-route verification (scratch) ---
mid_symbol_imaginary          → proved, [propext, Classical.choice, Quot.sound]
lowering_symbol_real          → proved, [propext, Classical.choice, Quot.sound]
cycles_symbol_imaginary       → proved, [propext, Classical.choice, Quot.sound]
mid_symbol_order_independent  → proved, [propext, Classical.choice, Quot.sound]
#check fun (s:ℝ) (x y : RealVectorSobolev s) => ⟪x,y⟫_ℝ  → elaborates, result type ℝ
#check @LinearIsometryEquiv.inner_map_map                → exists, exactly the shape step 4 needs
```

---

## 6. Recommendation

Merge.  Ask the lane (or fold into the next SL3 lane) to:

1. apply the combined patch in Finding 2 — it removes the `maxHeartbeats 400000`
   and the redundant `hfin` in one edit;
2. correct `ATTEMPTS_SL3.md` items 1 and 3 per Findings 3–5, since as written they
   will make the next lane over-budget the work and attempt the wrong (harder)
   route;
3. add the four missing `#print axioms` lines (Finding 8), a snags section
   (Finding 6), and fix the line citations (Finding 7).

None of these blocks the merge: the proved content is correct as it stands.
