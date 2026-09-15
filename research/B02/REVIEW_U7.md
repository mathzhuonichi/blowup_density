# Review — lane 059, B02 unit 7 (`low_high_split`)

Reviewer: independent opus reviewer, read/build only, no code changes.
Worktree: `.claude/worktrees/059-B02-unit-7`, commit `11c585b`
("[059-B02] Unit 7: low/high frequency split …"), working tree clean.
Files under review: `formalization/NSFormalization/Section4/B02/LowHigh.lean` (331 lines),
`research/B02/axioms_u7.lean`, `research/B02/ATTEMPTS_U7.md`.

## Verdict: **ACCEPT-WITH-NOTES**

The spec field is discharged with the exact constant of the manuscript display, the
build and axiom checks are clean, and the new angular Plancherel bridge is a correct,
faithful, minimal-hypothesis assembly of Mathlib's abstract `L²` isometry. All four
notes below are documentation / placement issues; none is a mathematical defect and
none blocks merge.

---

## 1. Commands and results

All run with `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`, lake invoked only
from `WT/verification`, one at a time.

| # | Command | Result |
|---|---------|--------|
| 1 | `bash scripts/lean-install.sh` | `== OK` |
| 2 | `cd verification && lake build NSFormalization.Section4.B02.LowHigh` | `Build completed successfully (8780 jobs).` `EXIT=0` |
| 3 | `cd verification && lake env lean ../formalization/NSFormalization/Section4/B02/LowHigh.lean` | **no output at all** (`EXIT=0`, 4.9 s wall) — zero warnings, zero infos from the file |
| 4 | `cd verification && lake env lean ../research/B02/axioms_u7.lean` | `'NSFormalization.Section4.B02.lowHighSplit' depends on axioms: [propext, Classical.choice, Quot.sound]` `EXIT=0` — the spec-typed `example` elaborates with no error |
| 5 | `grep -nE "sorry\|admit\|native_decide\|axiom\|maxHeartbeats\|set_option" formalization/NSFormalization/Section4/B02/LowHigh.lean` | **no matches** (`rc=1`) |
| 6 | same grep on `research/B02/axioms_u7.lean` | two hits, both legitimate: `:16` inside the `/- … -/` header comment, `:45` the required `#print axioms` command. No `axiom` declaration, no `set_option`, no `maxHeartbeats`. |
| 7 | `make check` | `EXIT=0` — `check_formalization_plan.py --check`, `check_contracts.py`, `test_contract_policy.py` (13 tests, OK), `check_work_queue.py` (`30 work items: … consistent`) |
| 8 | probe file: `example : SpatialField = (Space → Space) := rfl` and `example (s k) : homogeneousFourierENorm s k = (∑ i, ∫⁻ ξ, ENNReal.ofReal (‖ξ‖^(2*s) * ‖angularFourier (fun x => ((k x i:ℝ):ℂ)) ξ‖^2))^((2:ℝ)⁻¹) := rfl` | both `rfl` accepted — the theorem's LHS **is** definitionally `Data.homogeneousFourierENorm s k ^ (2:ℝ)` |
| 9 | `#print axioms angular_plancherel`, `#print axioms coeFn_l2Fourier_ae` | `[propext, Classical.choice, Quot.sound]` for both |

## 2. Spec conformance

* `research/B02/axioms_u7.lean:29-33` restates `lowHighConstant` and `SplitRange`.
  Diffed token-for-token against `research/B02/Spec.lean:231-232` and `:237`:
  **identical**.
* `axioms_u7.lean:37-41` is the type of `Spec.lean:421-425` `HomogeneousApproxAPI.lowHighSplit`
  character-for-character (binders, `MemLp k 1 volume → MemLp k 2 volume`,
  `homogeneousFourierENorm s k ^ (2 : ℝ) ≤ ENNReal.ofReal (lowHighConstant s) *
  eLpNorm k 1 volume ^ (2 : ℝ) + eLpNorm k 2 volume ^ (2 : ℝ)`), with
  `homogeneousFourierENorm`/`eLpNorm` the frozen `Contracts.V1.Data` ones (imported, not
  mirrored). It is closed by `fun s hs k hk1 hk2 => lowHighSplit s hs.1 hs.2 k hk1 hk2`.
* LHS definitional check: command 8 above. `SpatialField = Space → Space`
  (`Contracts/V1/Data.lean:99`); the theorem's `k : Space → Space` is the same type.
* **Constant vs the paper.** `paper/sections/04-whole-space.tex:242-248` (label
  `eq:Rnegative-cutoff` at `:247`) reads
  `‖k‖²_{Ḣ^{-1}} = ∫_{|ξ|<1}|ξ|^{-2}|k̂|² + ∫_{|ξ|≥1}|ξ|^{-2}|k̂|² ≤ C‖k‖₁²∫_{|ξ|<1}|ξ|^{-2}dξ + ‖k‖₂² ≤ C'‖k‖₁² + ‖k‖₂²`.
  The manuscript's transform is `01-introduction.tex:91`
  `ẑ(ξ) = (2π)^{-3/2}∫ e^{-ix·ξ}z(x)dx`, so `|k̂|_∞ ≤ (2π)^{-3/2}‖k‖₁` and the unnamed
  `C` is its **square**, `(2π)^{-3}`. That is exactly `Spec.lean:231`'s
  `(2*π)^(-(3:ℝ)) * ∫_{ball 0 1} ‖ξ‖^(2s)` and exactly what the Lean RHS carries. The
  square is realised in the proof at `LowHigh.lean:291-293` (`hpow :
  ((2π)^{-3/2})^2 = (2π)^{-3}`) feeding unit 4's vector bound
  `fourierSupBound` (`LowFrequency.lean:125`), whose constant is `(2π)^{-3/2}`.
  **Answer to the brief's question: yes — the paper's `(2π)^{-3}` is the square of unit 4's
  `(2π)^{-3/2}`, and the Lean proof derives it that way rather than postulating it.**
* High-frequency coefficient is literally `+ eLpNorm k 2 volume ^ (2:ℝ)`, i.e. **1**, as in
  the display. It is obtained from `|ξ|^{2s} ≤ 1` on `‖ξ‖ ≥ 1` (`s ≤ 0`,
  `Real.rpow_le_one_of_one_le_of_nonpos`, `LowHigh.lean:306`) plus Plancherel with
  constant 1 — no stray `(2π)` factor anywhere.
* **The ball-radius trap of `COMPARISON.md:108(b)` is avoided.** The whole computation is
  carried out in the *angular* frequency variable (`N ξ = ∑_i ‖angularFourier (g i) ξ‖²`,
  split at `Metric.ball (0:Space) 1` in that same variable), so the manuscript's radius-1
  split is the Lean radius-1 split. The lane did **not** transport `HT:14`'s cycles-radius-1
  statement; it re-ran the majorant argument, as the plan required.
* `SplitRange` is used with both halves: `-3/2 < s` only for `lowFrequencyIntegrable`
  (finiteness of the low weight), `s ≤ 0` only for the high half. No unused hypothesis, no
  extra hypothesis beyond the spec.

## 3. The Plancherel bridge — assessment

**What `angular_plancherel` proves** (signature printed by `#check`):

```
angular_plancherel : ∀ (g : Space → ℂ), Integrable g volume → MemLp g 2 volume →
  ∫⁻ (ξ : Space), ‖angularFourier g ξ‖ₑ ^ 2 = ∫⁻ (x : Space), ‖g x‖ₑ ^ 2
```

i.e. for scalar `g ∈ L¹(ℝ³) ∩ L²(ℝ³)`, `∫ |ĝ|² = ∫ |g|²` in the manuscript's angular
convention, **with constant exactly `1`** — not `(2π)^{3}`, not `(2π)^{-3}`. This is the
correct statement: the manuscript's transform is unitary on `ℝ³`.

The `1` is not asserted, it is computed, and I checked the cancellation by hand:
`angularFourier g ξ = (2π)^{-3/2} • 𝓕g((2π)⁻¹ • ξ)` (`Source/FourierConvention.lean:23-24`).
Squaring the amplitude gives `(2π)^{-3}`; the substitution `η = ξ/(2π)` contributes the
Jacobian `(2π)^{3}` (`lintegral_comp_const_smul` → `Measure.map_addHaar_smul` at
`finrank ℝ Space = 3`). `LowHigh.lean:173-176` `hprod` discharges
`((2π)^{-3/2})^2 · |((2π)⁻¹)^3|⁻¹ = 1` by `rpow` arithmetic. Correct.

**Hypotheses are minimal and are *not* a Schwartz/compact-support restriction.**
`Integrable g` is needed for the pointwise Bochner transform `𝓕 g` to exist at all (and
for its continuity, hence local integrability); `MemLp g 2` is needed to form the `Lp`
element the abstract isometry acts on. Measurability is *not* assumed separately — it is
derived (`VectorFourier.fourierIntegral_continuous`, `MemLp.aestronglyMeasurable`). So
`L¹ ∩ L²` is exactly the natural domain of this formulation, and it is exactly the class
`Spec.lean:399-406` insists on (load-bearing, because `04-whole-space.tex:249` applies the
split to `(1−χ_R)h_n`, Schwartz but not compactly supported).

**Faithfulness to Mathlib.** I read each cited Mathlib statement and confirmed the chain:

1. `fourier_mul_formula` (`:56`) instantiates
   `VectorFourier.integral_fourierIntegral_smul_eq_flip`
   (`Mathlib/Analysis/Fourier/FourierTransform.lean:242`), whose conclusion is
   `∫ 𝓕f • g = ∫ f • 𝓕_{L.flip} g`. The lane proves `(innerₗ Space).flip = innerₗ Space`
   from `real_inner_comm` and rewrites. `innerₗ V` is *exactly* the bilinear form behind
   the `𝓕` notation on an inner-product space
   (`FourierTransform.lean:430`: `fourier f := VectorFourier.fourierIntegral 𝐞 volume (innerₗ V) f`).
   Correct, and the pairing is bilinear — **no conjugation is silently dropped**.
2. `l2_fourier_pairing` (`:72`) uses `Lp.fourier_toTemperedDistribution_eq`
   (`Fourier/LpSpace.lean:117`), `TemperedDistribution.fourier_apply`
   (`Distribution/TemperedDistribution.lean:482`, `𝓕 f g = f (𝓕 g)`, `rfl`),
   `Lp.toTemperedDistribution_apply` (`:169`, `= ∫ x, g x • f x`, again bilinear) and
   `SchwartzMap.fourier_coe` (`SchwartzSpace/Fourier.lean:98`, `𝓕 f = 𝓕 (⇑f)`, `rfl`).
   All used in their stated direction.
3. `coeFn_l2Fourier_ae` (`:86`) applies
   `ae_eq_of_integral_contDiff_smul_eq` (`AEEqOfIntegralContDiff.lean:196`) — the genuine
   faithfulness statement: two locally integrable functions with equal `∫ φ • ·` against
   **every** real `C^∞_c` test function agree a.e. Both local-integrability side conditions
   are discharged honestly (`Lp.memLp … |>.locallyIntegrable`, and continuity of the
   Fourier integral of an `L¹` function). Real test functions are complexified through
   `NavierStokesR3.CompactSchwartz.ofCompactSupport`
   (`vendor/…/R3/CompactSchwartz.lean:37`, a real `def`, `coe … = f` by `rfl`), and the
   `ℝ`-smul/`ℂ`-smul mismatch is bridged by `Complex.real_smul`. No gap.
4. `eLpNorm_fourierIntegral_eq` (`:121`) transports `Lp.norm_fourier_eq`
   (`Fourier/LpSpace.lean:89`, `‖𝓕 f‖ = ‖f‖`, i.e. `(Lp.fourierTransformₗᵢ E F).norm_map`,
   a genuine linear **isometry** equivalence, constant 1) to `eLpNorm` via `Lp.norm_def`
   and `ENNReal.toReal_eq_toReal_iff'` with both sides finite (`Lp.eLpNorm_lt_top`). The
   `toReal` step is guarded by the two finiteness proofs, so nothing is lost.
   `Lp.fourierTransformₗᵢ` is the extension of the Schwartz (cycles) Fourier transform, so
   this is honest cycles Plancherel.
5. `angular_lintegral_eq_cycles` (`:153`) is the dilation step described above.

**Independent audit of the "nothing beyond Schwartz existed" claim — CONFIRMED.**
I grepped the whole tree myself:

* `grep -rniE "plancherel" formalization vendor --include='*.lean'` → the only
  `L¹ ∩ L²`-level angular statement is the one this lane adds. Everything else is either
  prose in a docstring, or Schwartz/`Lp`-abstract.
* `grep -rnE "norm_fourier|integral_norm_sq_fourier" formalization vendor` → 25 hits, all
  either `SchwartzMap.integral_norm_sq_fourier` (Schwartz-only: `Paper1/PeriodicNonpositiveForce.lean:27`,
  `Paper1/PeriodicEndpointInstantiation.lean:77`, `Paper1/PeriodicScalarForceEndpoints.lean:34`,
  `Paper1/PeriodicForceEndpointScaling.lean:58`, `Paper3/HomogeneousTime.lean:62,76,98`,
  `Paper3/PositiveFourierTime.lean:44`, `Paper3/SpatiallyCompactTime.lean:61`,
  `Paper3/CompactPhysicalTime.lean:58`, `Paper3/AllOrderFourierTime.lean:52`) or
  `Lp.norm_fourier_eq` applied to an already-`Lp` element (`Paper1/SchwartzCriticalEmbedding.lean:65,193`,
  `Source/PhysicalSobolevDistribution.lean:50`, `Source/PhysicalBesselSobolev.lean:159`,
  `Source/FractionalRealization.lean:35`, several `vendor/HeliCorgi` files).
* `formalization/NSFormalization/Paper1/PeriodicScalarForceEndpoints.lean:30`
  `angularSobolevSq_zero_eq_physical` — confirmed by reading it: hypothesis is
  `(φ : SchwartzMap Space ℂ)`, proof is `SchwartzMap.integral_norm_sq_fourier`. **Schwartz-only**,
  as the lane says.
* Mathlib side: `grep -rnE "coeFn_fourier|fourierIntegral.*=ᵐ" Mathlib/Analysis/Fourier/`
  returns only the `AddCircle` analogue. There is **no** Mathlib lemma identifying the
  representative of `Lp.fourierTransformₗᵢ f` with the pointwise `VectorFourier.fourierIntegral`
  on `L¹ ∩ L²`. `vendor/HeliCorgi/Formal/R3DecoderFrequencyBridge.lean:191`
  `r3DecodedFrequency_ae_coeFn_fourier` looks superficially similar but is pure bookkeeping
  for a constructed `toLp` element (`MemLp.coeFn_toLp` after `fourier_fourierInv_eq`), not a
  pointwise-integral bridge.

So the lane's headline finding is accurate: `coeFn_l2Fourier_ae` / `angular_plancherel`
are genuinely new to this tree, and they are the asset that unit 6
(`homogeneous_datum_of_lebesgue`) and I03 U7c need. This corrects
`research/B02/COMPARISON.md:248` (row 7), whose sketch said widening the hypothesis class
"costs nothing … `HT:14` never uses compactness, only `‖φ‖_∞ ≤ C` and `Integrable ‖φ‖²`" —
`Integrable ‖angularFourier k‖²` *is* the Plancherel statement at `L¹ ∩ L²`, so the sketch
was circular. It also corrects row 6 (`:247`), which plans to get its norm clause from
`MSF:306 integral_norm_sq_fourier` — Schwartz-only, and therefore unusable there as written.

## 4. Honesty spot-checks of `research/B02/ATTEMPTS_U7.md`

**Snag (a) — `innerSL ℝ` vs `innerₗ Space`, `isDefEq` timeout. CONFIRMED.**
`/tmp/rev059/snag_a3.lean`, `set_option maxHeartbeats 200000`:
```lean
VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
  (L := (innerSL ℝ (E := Space) : Space →ₗ[ℝ] Space →ₗ[ℝ] ℝ)) (by fun_prop) hg1
```
→ `error: Type mismatch: innerSL ℝ has type Space →L⋆[ℝ] Space →L[ℝ] ℝ but is expected to
have type Space →ₗ[ℝ] Space →ₗ[ℝ] ℝ` **and**
`error: (deterministic) timeout at 'isDefEq', maximum number of heartbeats (200000) has
been reached` (8.5 s). The lane's diagnosis — the `𝓕` notation's bilinear form is
`innerₗ V` (`FourierTransform.lean:430`), not `innerSL` — is exactly right. The recorded
fix `/tmp/rev059/snag_a_ok.lean` (`L := innerₗ Space`, `continuous_inner`) compiles in 2.7 s.
(For completeness: the explicitly coerced `(innerSL ℝ).toLinearMap₁₂` *does* work, both for
the continuity goal and for the `integral_fourierIntegral_smul_eq_flip` instantiation — so
the obstruction is specifically passing `innerSL` un-coerced, which is what the note claims.)

**Snag (b) — `‖ξ‖^{2s}` at `0`. CONFIRMED for continuity, overstated for measurability.**
* `/tmp/rev059/snag_b4.lean`: `example (s : ℝ) : Continuous (fun ξ : Space => ‖ξ‖ ^ (2*s)) := by fun_prop`
  → `error: 'fun_prop' was unable to prove 'Continuous fun ξ => ‖ξ‖ ^ (2 * s)' … Failed to
  prove necessary assumption '0 ≤ 2 * s' when applying theorem 'Real.continuous_rpow_const'`.
* `/tmp/rev059/snag_b2.lean`: `continuous_norm.rpow_const (fun x => Or.inr …)` →
  `error: unsolved goals … ⊢ 0 ≤ s`.
  Both match the note, and the underlying claim (the function is genuinely discontinuous at
  `0` for `s < 0`, so no tactic can close it) is correct.
* However `/tmp/rev059/snag_b.lean`:
  `example (s : ℝ) : Measurable (fun ξ : Space => ‖ξ‖ ^ (2*s)) := by fun_prop` **succeeds**.
  The goal the proof actually needs (`hw_meas`, `LowHigh.lean:232-233`) is the *measurability*
  one, so `by fun_prop` would replace `(by measurability : …).comp measurable_norm`. See
  finding 3.

Nothing in `ATTEMPTS_U7.md` overstates what was achieved; the `#print axioms` and build
lines quoted there (`8780 jobs`, the three-axiom list) reproduce exactly.

## 5. Findings

**Finding 1 — INFO (placement of a shared asset).**
Declarations: `fourier_mul_formula`, `l2_fourier_pairing`, `coeFn_l2Fourier_ae`,
`eLpNorm_fourierIntegral_eq`, `sq_eLpNorm_two`, `finrank_space_eq_three`,
`lintegral_comp_const_smul`, `angular_lintegral_eq_cycles`, `angular_plancherel`
(`formalization/NSFormalization/Section4/B02/LowHigh.lean:56-190`).
What is suboptimal: none of these is about the low/high split; they are convention-level
infrastructure that `COMPARISON.md:247` (unit 6) and `research/I03/COMPARISON.md` U7c both
need. Leaving them in a `Section4/B02` unit module means those consumers must
`import NSFormalization.Section4.B02.LowHigh`, an inverted dependency (a realization lemma
importing a Section-4 estimate).
Fix (follow-up lane, not this one): promote lines 54-190 verbatim to a new
`formalization/NSFormalization/Paper3/AngularPlancherel.lean` (or `Source/`, next to
`FourierConvention.lean`), and have `LowHigh.lean` import it. Nothing in the proofs would
change. The lane already recommends this itself (`ATTEMPTS_U7.md:49-53`), so this is a
note, not a defect.

**Finding 2 — LOW (stale line references in the record).**
File: `research/B02/ATTEMPTS_U7.md:36,45,47`.
What is wrong: `l2_fourier_pairing` is cited at `:71` (actual `:72`),
`angular_lintegral_eq_cycles` at `:171` (actual `:153`), `lintegral_comp_const_smul` at
`:161` (actual `:145`). The last two are off by ~16-18 lines, presumably written before a
final edit to the module header.
Fix: correct the three numbers to `:72`, `:153`, `:145`.

**Finding 3 — LOW (a recorded snag is slightly overstated).**
File: `research/B02/ATTEMPTS_U7.md:82-84`; declaration `hw_meas`,
`LowHigh.lean:232-233`.
What is wrong: the bullet reads "`Continuous.rpow_const` / `fun_prop` for `‖ξ‖^{2s}` …
`fun_prop`/`Continuous.rpow_const` fail. `measurability` proves `Measurable (fun r:ℝ => r^{2s})`,
composed with `measurable_norm`." The first half is true only of the *continuity* goal
(verified above); on the *measurability* goal that the proof actually uses, `fun_prop`
closes it outright (verified above). As written the note could lead a later lane to avoid
`fun_prop` for measurability goals of this shape.
Fix: reword to "`Continuous` is false at `0` for `s<0`, so `Continuous.rpow_const` and
`fun_prop` both fail on the continuity goal; the measurability goal is what is needed and
`fun_prop` (or `measurability ∘ measurable_norm`) discharges it", and optionally simplify
`LowHigh.lean:232-233` to `by fun_prop`.

**Finding 4 — INFO (upstream planning docs not updated).**
File: `research/B02/COMPARISON.md:247` (row 6) and `:248` (row 7).
What is stale: row 7's "Widening `HR:17`'s compact-support hypothesis to `L¹ ∩ L²` costs
nothing: `HT:14` never uses compactness, only `‖φ‖_∞ ≤ C` and `Integrable ‖φ‖²`" is refuted
by this lane — `Integrable ‖angularFourier k‖²` at `L¹ ∩ L²` *is* the Plancherel statement,
so the reuse is circular and the bridge had to be built. Row 6 likewise plans to obtain its
norm clause from `MSF:306 SchwartzMap.integral_norm_sq_fourier`, which is Schwartz-only and
will not apply to its `L¹ ∩ L²` input; row 6 should now be pointed at `angular_plancherel`.
(Related, cosmetic: `ATTEMPTS_U7.md:12` attributes the "a Plancherel exists" assumption to
"COMPARISON row 7"; row 7 does not mention Plancherel at all — row 6 does, and the quoted
grep suggestion is from the lane task card.)
Fix: update the two COMPARISON rows when this lane merges, so the unit-6 lane does not plan
against the stale sketch. Not a change to any Lean file.

## 6. What I verified is *not* wrong

* No `sorry`/`admit`/`native_decide`/`axiom`/`set_option`/`maxHeartbeats` anywhere in the
  module; the axiom set is the three standard ones for `lowHighSplit`, `angular_plancherel`
  and `coeFn_l2Fourier_ae` alike.
* The statement is not vacuous: under `MemLp k 1` and `-3/2 < s` (which gives
  `lowFrequencyIntegrable`) the right-hand side is finite, so the inequality has content.
* Unit 4's **vector** `fourierSupBound` is used, not a componentwise bound — so no spurious
  factor `3` sneaks into the constant (`hsup`, `LowHigh.lean:265-270`); `hN`/`hC0` match
  `fourierSupBound`'s statement by `rfl`.
* The `Fin 3` bookkeeping closes with `EuclideanSpace.norm_sq_eq` (`:323`), i.e. the
  component sum really is `‖k x‖²` for the `PiLp 2` norm — no norm-equivalence fudge.
* `lintegral_const_mul'` is used with the `≠ ∞` side condition (`ENNReal.ofReal_ne_top`),
  `setLIntegral_le_lintegral` only enlarges, and `lintegral_add_compl` is applied to a
  `MeasurableSet` — the `ℝ≥0∞` manipulation is sound throughout.
