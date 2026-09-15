# D01, homogeneous half — the first inhabitant of the homogeneous realization

Lane 024, task **D01**.  Deliverable:
`formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean` (**59**
declarations in 700 lines — 37 `theorem`, 3 `@[simp] theorem`, 15 `def`,
4 `abbrev` — no `sorry`/`axiom`/`native_decide`, every declaration
`#print axioms`-clean: `[propext, Classical.choice, Quot.sound]`).

Before this module every homogeneous name of `verification/Contracts/V1/Data.lean`
had zero users (`research/I03/COMPARISON.md:223,284`), so `Data.lean:338`
`homogeneousENorm` and `Data.lean:390` `forceHomogeneousENorm` were empty infima
(`⊤`) and every statement about them was vacuous.

---

## 1. Route chosen, and why

**Schwartz-first, not `L² → 𝓢'`-multiplier-first.**

`Paper3/HomogeneousRealization.lean:7` states outright that a full `L² → 𝓢'`
homogeneous multiplier is deliberately not built, and `Source/FractionalRealization.lean:44`
only has the `0 < a < 3/2` cycles-convention one landing in `L^{p_a}` (Appendix B's
completion, A05's object).  Building the multiplier is the hard direction
(`G ↦` inverse transform of `|ξ|^{-s}G`, an unbounded/singular symbol).

The *forward* direction is what the two blocked lanes actually need, and it is easy:
`Data.lean:324` `IsHomogeneousDatum s G u` asks for a datum `G ∈ L²` with
`⟨angularFourierDistribution u, φ⟩ = ∫ φ(ξ)·|ξ|^{-s}G(ξ)dξ`.  For a physical field
`z` whose complex components are Schwartz, take

```
G_i(ξ) = |ξ|^s ẑ_i(ξ)        (angular convention, Data.lean's `angularFourier`)
u_i    = (z_i : 𝓢(Space,ℂ) : 𝓢'(Space,ℂ))
```

and the realization identity is `Paper3.angularFourierDistribution_schwartz_apply`
(`Paper3/AngularFourierDilation.lean:218`) plus `|ξ|^{-s}·|ξ|^{s} = 1` a.e.
(`{0}` is Lebesgue-null in `R³`).  Nothing else is needed:

* **`G_i ∈ L²`** is `∫ |ξ|^{2s}|ẑ_i|² < ∞`, i.e. `Paper3.schwartz_homogeneous_negative_integrable`
  (`Paper3/CompactFourier.lean:17`) for `-3/2 < s ≤ 0`, and, for `s ≥ 0`,
  `|ξ|^{2s} ≤ (1+|ξ|²)^s` fed into `Paper3.schwartz_bessel_integrable`
  (`Paper3/CompactFourier.lean:37`).  Both are stated for an *arbitrary* Schwartz
  function, so they apply directly to the **angular** transform packaged as a
  Schwartz map (`schwartzAngularFourier`, using the `rfl` bridge
  `Paper3.schwartzAngularDilation_fourier_apply`, `AngularFourierDilation.lean:208`).
  **No Fourier-convention transport is involved.**
* **Reality** (`02-preliminaries.tex:72`) is `conj(ẑ(-ξ)) = ẑ(ξ)`, from
  `Source.RealSobolev.fourier_conjugate` (`Source/RealSobolev.lean:61`) and
  `‖-ξ‖ = ‖ξ‖`; this is the same shape as lane 020's `SmoothDatum.lean`
  §3 but two orders of magnitude shorter, because the weight `|ξ|^s` is real and
  even and needs no `sobolevOrderLowering` chain.
* **`IsSliceDistribution`** (`Data.lean:298`) is `SchwartzMap.coe_apply`.

**Routes rejected.**

| route | why rejected |
|---|---|
| Build `L² → 𝓢'` homogeneous realization first (mirror `Source/FractionalRealization.lean:44`) | Wrong convention and wrong sign range (`0 < a < 3/2`, cycles).  Both blocked lanes need only the *forward* map, and the forward map does not need it. |
| Reuse `Paper3.cyclesToAngularRealVector` to transport a cycles homogeneous datum | There is no cycles homogeneous datum in the tree to transport (`research/B02/COMPARISON.md:167`: the carrier transports, the weight `|ξ|^{-s}` does not). |
| Reuse lane 020's `SmoothDatum.lean` (`H^∞`, no compact support) | Its whole route is the *inhomogeneous* Bessel weight, iterated `1−(2π)^{-2}Δ` and `sobolevOrderLowering`.  Nothing in it survives the change of weight. Only the *reality* pattern was reused, and it was reimplemented (5 lines) rather than imported — no cross-worktree import. |
| Prove uniqueness from the `2s < 3` Cauchy-Schwarz estimate of the `Data.lean:324` docstring | Would have restricted uniqueness to `-3/2 < s < 3/2`.  The `Integrable` clause of `IsHomogeneousDatum` *itself* gives local integrability (see §3), so uniqueness holds at **every** real `s`. |

---

## 2. Exact statements proved, with hypotheses

All in `namespace NSFormalization.Section4.D01.Homogeneous`; `s : ℝ`,
`Space = EuclideanSpace ℝ (Fin 3)`.  Line numbers are in
`formalization/NSFormalization/Section4/D01/HomogeneousWitness.lean`.

### Goal 1 — spatial witness  ✅ **done, and stronger than asked**

* `:109 integrable_homogeneous_schwartz (hs : -3/2 < s) (ψ : 𝓢(Space,ℂ))` :
  `Integrable (fun ξ => ‖ξ‖^(2*s) * ‖ψ ξ‖^2)`.  Every `s > -3/2`, no upper bound.
* `:153 memLp_homogeneousProfile (hs : -3/2 < s) (φ : 𝓢(Space,ℂ))` :
  `MemLp (fun ξ => (‖ξ‖^s : ℝ) * angularFourier φ ξ) 2 volume`; `:162 homogeneousDatum`
  is its `MemLp.toLp`.
* `:201 realSymmetry_homogeneousDatum (hs) (φ) (hφ : ∀ x, conj (φ x) = φ x)` :
  the datum is fixed by `Source.RealSobolev.realSymmetry`, hence
  `:214 mem_realSubspace_homogeneousDatum` lands in `realSubspace s`.
* `:277 isHomogeneousDatum_homogeneousDatum (hs : -3/2 < s) (φ)` :
  `IsHomogeneousDatum s (homogeneousDatum hs φ) (φ : 𝓢'(Space,ℂ))` — the
  **existence half of eq:homogeneous-realization** (`02-preliminaries.tex:58-69`).
* `:389 isHomogeneousSliceDatum_schwartz (hs : -3/2 < s) (z : SpatialField)
  (ψ : Fin 3 → 𝓢(Space,ℂ)) (hz : ∀ i x, ψ i x = ((z x i : ℝ):ℂ)) (hre)` :
  `IsHomogeneousSliceDatum s z (homogeneousVectorDatum hs ψ hre)` — **the first
  inhabitant of `Data.lean:367`.**
* `:418 enorm_homogeneousVectorDatum` (same hypotheses) :
  `‖homogeneousVectorDatum hs ψ hre‖ₑ = homogeneousFourierENorm s z`
  (`Data.lean:410`, the literal Fourier integral).
* `:473 exists_isHomogeneousSliceDatum` and `:486 enorm_of_isHomogeneousSliceDatum`:
  the two clauses of `research/B02/Spec.lean:454` `lebesgueHomogeneousDatum`
  (existence + "*every* datum has norm `homogeneousFourierENorm s k`"), with a
  Schwartz-components hypothesis in place of `MemLp k 1 ∧ MemLp k 2`.
* `:519 isHomogeneousSliceDatum_compact (hs : -3/2 < s) (hzs : ContDiff ℝ ∞ z)
  (hzc : HasCompactSupport z)` : both clauses for a real `C_c^∞(R³;R³)` field.
  This is the statement B02 unit 6 and I03 U7c consume.
* `:456 homogeneousENorm_schwartz` : `homogeneousENorm s (φ : 𝓢') = ‖homogeneousDatum hs φ‖ₑ`
  — the `Data.lean:338` infimum is *attained and equal*, not merely `≤`;
  `:463 homogeneousENorm_schwartz_ne_top` : it is `≠ ⊤`.

**Range of `s`.**  The task asked for `-3/2 < s < 3/2`.  Only `-3/2 < s` is used.
The upper bound in the `Data.lean:324` docstring guards the *sufficient*
Cauchy-Schwarz temperedness bound for a general `L²` datum; a Schwartz profile's
datum is `|ξ|^s φ̂` with `φ̂` Schwartz, whose pairing with any Schwartz test is
integrable at every order (`:268 integrable_schwartz_mul_angularFourier`).
So the theorems are stated with the weaker hypothesis.

### Uniqueness — RECONCILIATION unit **L7**  ✅ **done, at every real `s`**

* `:294 locallyIntegrable_of_schwartz_mul` : if `ψ·h` is integrable for every
  Schwartz `ψ` then `h` is locally integrable.  Proof: given a compact `K`, pick a
  `ContDiffBump 0` with `rIn = max R 1` where `K ⊆ closedBall 0 R`, push it through
  `NavierStokesR3.CompactSchwartz.ofCompactSupport`, and use
  `IntegrableOn.congr_fun` with `ψ ≡ 1` on `K`.
* `:325 homogeneousDatum_unique {s G G' u} (hG hG')` : `G = G'`.
  Via `NavierStokesR3.WeakFourierUniqueness.ae_eq_zero_of_integral_schwartz_test_mul_eq_zero`
  (`vendor/.../R3/WeakFourierUniqueness.lean:40`) applied to
  `h(ξ) = |ξ|^{-s}(G−G')(ξ)`; local integrability of `h` comes from the
  `Integrable` clause of `Data.lean:324` itself via the previous lemma, **not**
  from `2s < 3`, which is why no range hypothesis appears.
* `:437 isSliceDistribution_unique`, `:445 isHomogeneousSliceDatum_unique` : the
  vector versions.  `isHomogeneousSliceDatum_unique` is what upgrades B02's
  "every datum has the same norm" clause from a norm statement to genuine
  uniqueness — B02 deliberately asked only for the norm to avoid needing this;
  it is now available if wanted.

### Goal 2 — difference / linearity  ✅ **done, with one side condition**

* `:534 isHomogeneousDatum_sub` : `IsHomogeneousDatum s (G−G') (u−v)`.
  **Unconditional** — the two `Integrable` clauses in the hypotheses are exactly
  what lets `integral_sub` fire.
* `:551 isHomogeneousVectorDatum_sub` : componentwise, unconditional.
* `:566 isSliceDistribution_sub` : `IsSliceDistribution (z−w) (U−V)`, **with**
  `∀ i ψ, Integrable (fun x => ψ x * (z x i : ℂ))` and the same for `w`.
* `:585 isHomogeneousSliceDatum_sub` : `research/B02/Spec.lean:470`
  `homogeneousDatumSub`, carrying those two integrability hypotheses.
* `:597 integrable_schwartz_mul_component` discharges them for any field with
  Schwartz components (hence for `C_c^∞` and for the fields of B02's diagonal
  argument).

> **B02 must widen `homogeneousDatumSub`.**  As currently written
> (`Spec.lean:470`) the field has *no* hypothesis on `z`, `w`.  That statement is
> false in general: `Data.lean:298` totalizes `∫ ψ·z_i` to `0` when the integrand
> is not integrable, so if `ψz_i` and `ψw_i` are both non-integrable while
> `ψ(z−w)_i` is integrable, then `U ψ = V ψ = 0` while `∫ψ(z−w)_i ≠ 0`, and no
> datum of `z−w` can be `Z−W`.  The fix is either the integrability side
> condition above, or restricting the field to `L¹∩L²` fields (for which it is
> automatic, since Schwartz·L¹-or-L² is `L¹`).  Nothing downstream is affected:
> every field B02 applies it to is Schwartz.
>
> **Reviewer's preferred fix (`research/D01/REVIEW_HOMOGENEOUS.md` ruling (c)),
> adopted here as the recommendation to B02:** add `MemLp z 1 volume` and
> `MemLp w 1 volume` as hypotheses rather than the `∀ i ψ, Integrable (ψ · z_i)`
> side condition.  Both are correct fixes — `∀ i ψ, Integrable (ψ · z_i)` is
> literally what `isSliceDistribution_sub` needs to fire `integral_sub`, and
> `:597 integrable_schwartz_mul_component` discharges it for Schwartz-component
> fields — but `MemLp _ 1` is better *for the spec*: it is the hypothesis class
> the sibling field `lebesgueHomogeneousDatum` (`Spec.lean:454`) already uses, it
> is free at B02's call site, it implies the integrability condition (bounded ×
> `L¹` is `L¹`, so Schwartz × `L¹` is `L¹`), and it keeps the structure's
> hypothesis class uniform.  The reviewer also exhibits a concrete
> counter-witness to the hypothesis-free form (a Bernstein set `A`,
> `z := 1_A·e₁ + g`, `w := 1_A·e₁` with `g` real `C_c^∞` and `g_1 ≢ 0`), which
> settles that this is a real defect in the spec and not a formalisation
> artefact.
>
> The theorem in this module keeps the `Integrable` side condition, because that
> is the weakest hypothesis its proof uses; a `MemLp _ 1` wrapper is one
> application of `integrable_schwartz_mul_component`'s argument and belongs in
> whichever lane edits `Spec.lean`.

### Goal 3 — path lift  ⚠️ **all but strong measurability**

`Data.lean:99,104,118,205,375,390` are restated at `:614,:617,:620,:624,:629`.

* `:646 compactHomogeneousPath (hs : -3/2 < s) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)`
  and `:658 isHomogeneousPath_compact` : `IsHomogeneousPath s f (compactHomogeneousPath …)`.
  **`Data.lean:375` is inhabited.**  (Spatial slices: `:637 compact_spatial_slice'`,
  the `Space`-valued copy of `Paper3.compact_spatial_slice`,
  `Paper3/CompactFourierTime.lean:20`, which is stated only for `ℂ`-valued fields.)
* `:667 bochnerDatumENorm_eq_eLpNorm_slice (hs) (hf) (hc) (G) (hG : IsHomogeneousPath s f G)` :
  for **every** admissible path `G` and every `q`,
  `bochnerDatumENorm q s G = eLpNorm (fun t => homogeneousFourierENorm s (f(t,·))) q forceTimeMeasure`.
  This is U7c's "`L^q_t` form": the Bochner norm of the datum path *is* the
  `L^q(0,∞)` norm of the slice quantity, and the infimum in `Data.lean:390` is
  over a set on which the objective is constant.
* `:683 eLpNorm_slice_le_forceHomogeneousENorm` :
  `eLpNorm (fun t => homogeneousFourierENorm s (f(t,·))) q forceTimeMeasure
   ≤ forceHomogeneousENorm q s f`, unconditionally (empty infimum is `⊤`).
* `:692 forceHomogeneousENorm_eq_of_aestronglyMeasurable` : *given*
  `AEStronglyMeasurable (compactHomogeneousPath hs hf hc) forceTimeMeasure`, the
  two are **equal**.

**The gap is exactly that one hypothesis**; see §4.

### Goal 4 — scaling identity  ❌ **not attempted**

Nothing is proved.  See §4 for the worked-out route and the two lemmas it needs.

---

## 3. Failed attempts and dead ends (chronological)

1. `Real.rpow` normalisation.  `‖ξ‖^(2*s) = (‖ξ‖^s)^2` does not fall to
   `rw [mul_comm, Real.rpow_mul]; norm_num`; the working spelling is
   `rw [← Real.rpow_natCast ‖ξ‖ 2, ← Real.rpow_mul (norm_nonneg ξ)]; norm_num`.
   Same trap in `norm_homogeneousProfile_sq`.
2. `RealSobolev.fourier_conjugate` is not resolvable as written when
   `NSFormalization.Source.RealSobolev` is `open`ed; the full path
   `NSFormalization.Source.RealSobolev.fourier_conjugate` is required.
3. `locallyIntegrable_iff` takes no explicit `LocallyCompactSpace` argument in
   this Mathlib; `(locallyIntegrable_iff (by infer_instance))` fails.
4. `Integrable.congr` goals produced by `Pi.sub` need `Pi.sub_apply` in the
   `simp only` set before `ring` — but only in one of the two places, and the
   unused-simp-arg linter rejects it in the other.
5. `ENNReal` power juggling.  `‖x‖ₑ ^ (2:ℝ)` (rpow) versus `^ 2` (ℕ pow) print
   identically.  `ENNReal.ofReal_rpow_of_nonneg` will not fire; the working chain
   is `← ofReal_norm`, `ENNReal.rpow_two`, `← ENNReal.ofReal_pow (norm_nonneg _)`.
6. `iInf_le _ ⟨…⟩` on the `Data.lean:338` subtype infimum hit a
   `(deterministic) timeout at isDefEq` (200000 heartbeats).  Unfolding the
   definition first (`rw [homogeneousENorm]`) and using `iInf_le_of_le … le_rfl`
   elaborates instantly.
7. `ext i` on a `RealVectorSobolev s = PiLp 2 (fun _ : Fin 3 => RealSobolevHilbert s)`
   equality over-applies: it goes through `funext`, `Subtype.ext` **and** `Lp.ext`
   and leaves an a.e. goal.  `WithLp.ofLp_injective 2 (funext …)` stops at the
   right level.
8. `MeasureTheory.IntegrableOn.congr_fun`'s `EqOn` goal does not accept
   `rw [hone x hx]` directly (the LHS is a beta-redex); `show ψ x * h x = h x`
   first.
9. `Paper3.compact_spatial_slice` is `ℂ`-valued only; the `Space`-valued copy had
   to be written out (proof copied verbatim, attributed in the docstring).

---

## 3b. Post-review revisions (`research/D01/REVIEW_HOMOGENEOUS.md`, ACCEPT-WITH-NOTES)

Applied in this worktree after the review:

* **Issue 3 (header overclaim).**  The module header said the module "builds the
  witness" for both `Data.lean:338` and `Data.lean:390`.  True only for `:338`.
  For `:390` `forceHomogeneousENorm` the infimum's subtype also demands
  `AEStronglyMeasurable G forceTimeMeasure`, which is *not* supplied, so
  `forceHomogeneousENorm` is still not known `< ⊤`; only `Data.lean:375`
  `IsHomogeneousPath` is inhabited.  The header now says exactly that and points
  at §4(a)1.  §15's own docstrings were already correct.
* **Issue 4 (reuse).**  `integrable_schwartz_mul_angularFourier` (was 12 lines of
  hand-rolled `Integrable.mono'` + `calc`) and `integrable_schwartz_mul_component`
  (was 20 lines) are now `Integrable.mul_bdd`
  (`Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:1072`) at 4 and 6
  lines.  Both compiled first try.  The reviewer's third suggestion — generalise
  `Paper3.compact_spatial_slice` in its codomain upstream so that
  `compact_spatial_slice'` can be deleted — is **not** applied: it edits
  `Paper3/CompactFourierTime.lean`, outside this lane's file scope.
* **Issue 5 (counts).**  "56 declarations" → 59, with the cause of the
  miscount recorded in §6; the `--dry-run` note in §6 updated now that the file
  is committed.  All `:NNN` citations into the module in §2 and §4 were
  recomputed after the edits above.
* **Ruling (c).**  The reviewer's preferred fix for B02's `homogeneousDatumSub`
  (`MemLp z 1`, `MemLp w 1` rather than the `Integrable` side condition), and the
  Bernstein-set counter-witness that settles the defect, are recorded in the box
  in §2.

Not applied, and why:

* **Issue 1 (branch 22 commits behind `erenup/integration`).**  This lane runs no
  git write commands; rebasing is the merge step's.  The reviewer checked that
  all six imported modules are byte-identical on integration and that the added
  file collides with nothing, so the build carries over; both builds should be
  re-run after the rebase.
* **Issue 2 (`verification/Bindings` `rfl` bridge for the 13 restated
  `Data.lean` declarations).**  `verification/` is out of this lane's scope.  The
  13 `rfl`s were verified by hand today (§6) but nothing in CI guards them; this
  is the first item of the follow-up lane.
* **Issue 6 (nits).**  `ae_ne_zero` is generic but sits in the D01 namespace, and
  `locallyIntegrable_of_schwartz_mul`'s inline bump duplicates
  `Paper1.exists_spatial_cutoff` (`Paper1/LocalCutoff.lean:11`).  Left as is;
  importing `Paper1` here is not worth it.  Recorded so the next lane does not
  rebuild either a third time.

---

## 4. The remaining gaps, stated plainly

### (a) For **I03 U7c** (`HomogeneousScalingAPI`, `Contracts/V1/Scaling.lean:509-538`)

`packetNegativeHomogeneous` and `correctionNegativeHomogeneous` are **upper**
bounds on `Data.forceHomogeneousENorm q s (scaledForce …)`.  This module gives a
matching **lower** bound and the equality-modulo-measurability, so two things are
still owed:

1. **Strong measurability of the datum path.**
   `AEStronglyMeasurable (compactHomogeneousPath hs hf hc) forceTimeMeasure`.
   Without it `forceHomogeneousENorm` can still be `⊤` and no upper bound is
   provable.  This is the single blocking item.

   *Route (worked out, not formalised).*  Prove `Continuous (compactHomogeneousPath …)`
   and finish with `Continuous.aestronglyMeasurable`.  By
   `isHomogeneousSliceDatum_sub` + `enorm_of_isHomogeneousSliceDatum`,
   `‖G t − G t₀‖ₑ = homogeneousFourierENorm s (f(t,·) − f(t₀,·))` — both lemmas
   are in this module, and the components of the difference are Schwartz.  Then,
   for `-3/2 < s ≤ 0`, apply `Paper3.homogeneous_energy_le_bound_add_L2`
   (`Paper3/HomogeneousTime.lean:14`) **directly to `φ := angularFourier k`**
   with `k = f(t,·)−f(t₀,·)`; that lemma is generic in `φ` and involves no
   Fourier convention, so its `Metric.ball 0 1` is already the *angular* unit
   ball.  Two inputs remain:
   * `‖angularFourier g ξ‖ ≤ (2π)^{-3/2} ∫‖g‖` — the `(2π)^{-3/2}` amplitude of
     `Source/FourierConvention.lean:23` on top of
     `SchwartzMap.norm_fourier_apply_le_toLp_one` (used at `Paper3/HomogeneousTime.lean:56`);
   * angular Plancherel `∫‖angularFourier g‖² = ∫‖g‖²` — `angularSobolevSq_eq_frequency_weight`
     at `s = 0` (`Source/FourierConvention.lean:50`) plus
     `SchwartzMap.integral_norm_sq_fourier`.
   Then `‖f(t,·)−f(t₀,·)‖_{L¹}, ‖·‖_{L²} → 0` from uniform continuity of a
   compactly supported smooth `f` on the fixed compact `Prod.snd '' tsupport f`.
   For `s > 0` the high-frequency half instead needs
   `|ξ|^{2s} ≤ (1+|ξ|²)^s` and an `H^m` bound, i.e. Schwartz seminorm continuity
   in `t`.  Estimated 150-250 lines.

   The cheap-looking alternative — separability of `Lp ℂ 2 volume` plus
   Pettis — was not pursued: it still needs `t ↦ ⟪G t, e⟫` measurable for a
   countable family, which is no easier than continuity.

2. **The scaling identity itself** (goal 4, untouched).
   *Route.*  Spatial first: for `k > 0`, `x₀`, amplitude `a`,
   `w(x) = a·z(k(x−x₀))` gives `ŵ(ξ) = a k^{-3} e^{-i x₀·ξ} ẑ(k^{-1}ξ)` — from
   `Source.fourier_dilation` (`Source/FourierScaling.lean:25`) and
   `Source.fourier_translate` (`Source/FourierTranslation.lean:9`), pushed through
   the `angularFourier` definition (the translation factor has modulus 1 and drops
   out).  Then
   `∫|ξ|^{2s}|ŵ|² = a² k^{2s−3} ∫|η|^{2s}|ẑ|²`, i.e.
   `homogeneousFourierENorm s w = |a| k^{s−3/2} homogeneousFourierENorm s z`.
   The real-integral change of variables already exists as
   `Paper3.homogeneous_energy_dilate` (`Paper3/SobolevWeights.lean:87`); what is
   missing is its `∫⁻`/`ℝ≥0∞` form (via `ofReal_integral_eq_lintegral_ofReal`, or a
   direct `lintegral` change of variables).  With `k = ε^{-1}`, `a = ε^{-3}` this
   gives `ε^{-3/2−s}` per slice; the time dilation by `ε²` contributes `ε^{2/q}`,
   and the product is `ε^{2/q−3/2−s} = ε^{β(q,s)}`, matching
   `04-whole-space.tex:57` and `ThresholdAPI.exponent`.  The time half is exactly
   `Source.force_eLpNorm_negative_epsilon` (`Source/TimeNormScaling.lean:135`)
   with `homogeneousFourierNorm` replaced by its angular counterpart — and by the
   note in §5 that replacement is a clean `(2π)^s` factor.

### (b) For **B02 unit 6** (`research/B02/Spec.lean`)

* `lebesgueHomogeneousDatum` (`:454`) — **discharged for Schwartz / `C_c^∞`
  fields** by `isHomogeneousSliceDatum_compact` and
  `exists_isHomogeneousSliceDatum` + `enorm_of_isHomogeneousSliceDatum`.
  **Not discharged for the full `MemLp k 1 ∧ MemLp k 2` class.**  That matters:
  the field the spec applies it to at `04-whole-space.tex:249` is `(1−χ_R)h_n`,
  which is Schwartz but not compactly supported — so the *Schwartz* version, which
  this module provides, is enough for that use, but the literal `L¹∩L²` field is
  not proved.  Widening from Schwartz to `L¹∩L²` costs: `ẑ` is then only
  bounded-continuous (`L¹`) and in `L²` (Plancherel), which is enough for
  `G ∈ L²` when `s ≤ 0`; the realization identity needs
  `angularFourierDistribution` of an `L¹∩L²` field (the `Lp.toTemperedDistribution`
  coercion rather than the Schwartz one) — a genuine extra step, roughly the
  density argument of `fourier_conjugation` in lane 020's `SmoothDatum.lean:114`.
* `homogeneousDatumSub` (`:470`) — proved, **but the spec's hypothesis-free form
  is false**; see the box in §2.
* `lowHighSplit` (`:421`) — **not proved here** (it is B02's own field).  One
  finding: `research/B02/COMPARISON.md:108` row (b) argues the cycles→angular
  step is "a restatement, not a transport" because the manuscript's unit ball is
  the cycles ball of radius `1/(2π)`.  That is right, and the conclusion should be
  that no transport is needed at all: `Paper3.homogeneous_energy_le_bound_add_L2`
  is generic in its profile `φ`, so applying it with `φ := angularFourier k`
  produces the manuscript's display, with the manuscript's radius-1 ball, directly.
  Only the two inputs listed in §4(a)1 are then required.
* `spatialApproxHomogeneous`, `approxCompactHomogeneous`, `annularSchwartz`,
  `cutoffLebesgue` — untouched; they are B02's.

### (c) For **R46**

`R46` consumes `CompletedDenseHomogeneous` (`Data.lean:752`), i.e.
`CompletedDenseVia q s (IsHomogeneousPath s)`.  This module makes
`IsHomogeneousPath` inhabited and pins the Bochner norm of every path, which
removes the vacuity, but `CompletedDenseHomogeneous` additionally needs
(i) the `AEStronglyMeasurable` witness of §4(a)1 so that the approximants are
genuine `L^q(0,∞;Ḣ^s)` elements, and (ii) all of B02's stages 1-6.  **R46 is
unblocked at the level of "the objects exist", not closed.**

---

## 5. The cycles-vs-angular radius issue

It was **not** hit, and the reason is worth recording because
`research/B02/COMPARISON.md:108` flags it as a real cost.

`Source/FourierConvention.lean:23` fixes
`angularFourier f ξ = (2π)^{-3/2} • 𝓕 f ((2π)^{-1} • ξ)`, so the angular variable
`ξ` and Mathlib's cycles variable `η` are related by `ξ = 2πη`.  Consequently:

* **The homogeneous norms differ by exactly `(2π)^{s}`:**
  `∫|ξ|^{2s}|angularFourier f (ξ)|²dξ = (2π)^{2s}∫|η|^{2s}|𝓕f(η)|²dη`
  (the `(2π)^{-3}` amplitude cancels the `(2π)^{3}` Jacobian; only the weight
  survives).  This is `RECONCILIATION.md` unit L8's factor.  *Not formalised here*
  — nothing in this module needed it, because every finiteness lemma reused
  (`schwartz_homogeneous_negative_integrable`, `schwartz_bessel_integrable`,
  `homogeneous_energy_le_bound_add_L2`) is stated for an arbitrary profile
  function and was applied to the angular transform directly.
* **The low/high split radius is where the conventions genuinely disagree:**
  the manuscript splits at angular `|ξ| = 1`, i.e. cycles `|η| = 1/(2π)`, so
  `homogeneousFourierNorm_le_physical` (`Paper3/HomogeneousTime.lean:47`), whose
  ball is the *cycles* unit ball, is not the manuscript's constant even after the
  `(2π)^s` factor.  The escape is the one in §4(b): re-apply the generic
  `homogeneous_energy_le_bound_add_L2` in the angular variable instead of
  transporting its compact-input corollary.

---

## 6. Verification

* `lake build NSFormalization.Section4.D01.HomogeneousWitness` from `verification/`:
  **success**, no warnings from this file.
* `#print axioms` on all **59** declarations: every one
  `[propext, Classical.choice, Quot.sound]`.  (Scratch file, deleted.)
  An earlier run of this check said "56": the declaration-harvesting grep used
  `^(theorem|def|abbrev)` and silently skipped the three `@[simp] theorem`
  lines.  Reviewer issue 5; the three omitted declarations
  (`schwartzAngularFourier_apply`, `homogeneousVectorDatum_coe`,
  `compactSchwartzComponents_apply`) are clean too.
* **Definitional agreement with the contract**, checked in a deleted scratch file
  that imports both `Contracts.V1.Data` and this module and closes each of
  `SpatialField`, `SpaceTimeField`, `VectorDistribution`, `IsSliceDistribution`,
  `IsHomogeneousDatum`, `homogeneousENorm`, `IsHomogeneousVectorDatum`,
  `IsHomogeneousSliceDatum`, `homogeneousFourierENorm`, `forceTimeMeasure`,
  `bochnerDatumENorm`, `IsHomogeneousPath`, `forceHomogeneousENorm` by `rfl`, and
  additionally restates `isHomogeneousSliceDatum_compact`,
  `isHomogeneousPath_compact` and `eLpNorm_slice_le_forceHomogeneousENorm` in
  pure `BlowupDensity.Contracts.V1.Data` vocabulary.  All accepted.
  A `verification/Bindings` bridge carrying these `rfl`s is owed; `verification/`
  is out of scope for this lane.
* `make check`: pass.
* `python3 experiments/build_changed_lean.py --base-ref erenup/integration --dry-run`
  reports `NSFormalization.Section4.D01.HomogeneousWitness`, which builds.
  (An earlier run of this gate reported `none`, correctly: the script diffs
  `base-ref..HEAD` and the file was then still untracked, so `targets()` had to
  be applied to the working-tree path by hand.  Reviewer issue 5; stale, now
  superseded.)
