# A3-L1·f — the forcing integral cap `Bbnd` (lane 137)

Module: `formalization/NSFormalization/Section4/A01/ForceCap.lean`
(namespace `NSFormalization.Section4.A01`, same as `Propagation.lean`).
Audit: `research/A01/axioms_a3_force.lean` (all 9 decls = `[propext, Classical.choice, Quot.sound]`).

## What the row asked and what shape actually fits Grönwall

Row A3-L1·f is stated in the manuscript-literal form `∫₀ᵗ‖f‖_{H^m} ≤ ‖f‖_{L¹_tH^m}`.  But the
slot it feeds is the `Bbnd` bundle of `gronwall_bddAbove_Ico`
(`Propagation.lean`), which for `b := fun s => sobolevNormAt m f s` wants **three** facts on
`Ico 0 T₀`: `ContinuousOn b`, `∀ t, 0 ≤ b t`, and one real `Bbnd` with
`∀ t ∈ Ico 0 T₀, ∫ s in 0..t, b s ≤ Bbnd`.  So the deliverable is a `Bbnd` witness plus the two
side facts, not just the inequality.  Two caps are provided:

* `forceCap` (route-robust): `Bbnd := ∫ s in 0..T₀, sobolevNormAt m f s`, valid because the
  integrand is continuous on the closed `[0,T₀]` (hence integrable) and nonnegative; monotone in
  `t` by `intervalIntegral.integral_mono_interval` with `[0,t] ⊆ [0,T₀]`.  This is the cap the
  bare `C^∞([0,∞);H^m)` regularity always supplies, and is the one plugged into
  `gronwall_bddAbove_Ico` in the module's `example`.
* `intervalIntegral_le_forceSobolevENormL1` (manuscript-literal): the row's own inequality,
  conditional on `forceSobolevENormL1 m f ≠ ⊤`; its `_of_memForceR` corollary discharges that
  hypothesis via `A04.memL1Hm_of_memForceR` (the `L¹_t H^m` clause of the *formalized* `F_R`,
  eq:Rclasses `02-preliminaries.tex:17`, is part of `MemForceR`).  `forceCap_L1` packages it as
  the Grönwall bundle with `Bbnd := (forceSobolevENormL1 m f).toReal`, uniform over all `t`.

**Key fact discovered:** the brief warns `forceSobolevENormL1` may be `⊤` for the paper's
`F_R = C([0,∞);H^∞)`.  But eq:Rclasses (`02-preliminaries.tex:17`, review Finding 1) is *not*
merely `C^∞([0,∞);H^∞)`: it also requires `‖f‖_{L¹_tH^m}+‖f‖_{L²_tH^m}<∞` at every order, and
`MemForceR` (D01/ForceClass, verbatim of the frozen `Data.lean:544`) carries exactly those two
clauses (`MemLp G 1/2 forceTimeMeasure`).  So the L¹ norm is **finite for free** —
`memL1Hm_of_memForceR` proves it — and the L¹ cap is a theorem, not a dead end.

**Correction (review Finding 2): `hfin` is NOT load-bearing in
`intervalIntegral_le_forceSobolevENormL1` as stated.**  Because it also takes `hf : MemForceR f`,
and `hf ⟹ hfin` (`memL1Hm_of_memForceR`), `hfin` is a *provably redundant* argument (reviewer
proved both `hfin_redundant` and the `hfin`-deleted `no_hfin_needed`).  The earlier "`hfin` is
genuinely load-bearing / the inequality is false without it" claim was **inaccurate for this
lemma** — it is true only of a *different* statement, the one that drops `hf` as well.  Two
sub-points:
* the `⊤ ↦ 0` trap on the **right** is real in the abstract but needs a force with slice data
  that is not `L¹` in time (a nonzero *time-independent* `g`: `∫₀^∞‖g‖_{H^m}=∞`, so
  `forceSobolevENormL1=⊤`, RHS `=0`, LHS `>0`).  Such a `g` is **not** in `F_R`, which is exactly
  why `hfin` cannot be violated for `f ∈ F_R`;
* the dual trap on the **left**: a field with *no* datum path has `sobolevENorm=⊤`, so
  `sobolevNormAt=⊤.toReal=0` and both sides collapse to `0` (vacuously true) — the counterexample
  must therefore have slice data.
`intervalIntegral_le_forceSobolevENormL1` is kept in its conditional form (an honest, visible
argument, and useful if `MemForceR` is ever weakened); `_of_memForceR` is the clean
finiteness-free form.  The docstring, this record and the `A3_SPLIT.md` row are reworded to say
"`hfin` is *derivable* from `hf` here", not "essential".

`0 ≤ y_m 0` needs **no bridge** (F7): `sobolevNormAt s u t = (sobolevENorm s _).toReal`, so
`sobolevNormAt_nonneg := ENNReal.toReal_nonneg` — one line (grep confirmed no prior
`sobolevNormAt_nonneg` in `formalization/verification/research`).

## Inputs reused (all `#check`ed against a compiled env, no re-proof)

* `A04.continuousOn_sobolevNormAt_force hf m T : ContinuousOn (sobolevNormAt m f) (Ico 0 T)` —
  holds on `Ico 0 T` for **every** `T`, so continuity on the closed `Icc 0 T₀` is obtained at
  horizon `T₀+1` (`Icc 0 T₀ ⊆ Ico 0 (T₀+1)`).  (Its interval is `Ico 0 T`, not `Icc`; this is
  why the `T₀+1` trick is needed for `ContinuousOn.intervalIntegrable`.)
* `A04.sobolevNormAt_eq (hpath s hs) : sobolevNormAt m f s = ‖G s‖` (slice-datum uniqueness).
* `A04.sobolevENorm_force_ne_top`, `A04.forceSobolevENorm(L1)`, `A04.bochnerDatumENorm`,
  `A04.memL1Hm_of_memForceR`.
* `D01.MemForceR`, `D01.IsSobolevPath`, `D01.forceTimeMeasure` (= `volume.restrict (Ioi 0)`,
  by `rfl`).
* Mathlib: `intervalIntegral.integral_mono_interval`, `integral_of_le`, `integral_nonneg`,
  `ofReal_integral_eq_lintegral_ofReal`, `eLpNorm_one_eq_lintegral_enorm`,
  `setLIntegral_congr_fun`, `lintegral_mono'`, `Measure.restrict_mono`, `Ioc_subset_Ioi_self`,
  `ofReal_norm`, `ENNReal.toReal_mono`, `ENNReal.{toReal_ofReal,ofReal_toReal,toReal_nonneg}`.

## L¹-cap proof shape (Step 1 = pass to ℝ≥0∞)

`ENNReal.ofReal (∫ s in 0..t, sobolevNormAt m f s) ≤ forceSobolevENorm 1 m f`, via `le_iInf`
over datum paths `G`; for each `G`:
`ofReal (∫ s in Ioc 0 t, sobolevNormAt m f s)`
`= ∫⁻ s in Ioc 0 t, ofReal (sobolevNormAt m f s)`  (`ofReal_integral_eq_lintegral_ofReal`, needs
integrability + nonneg)
`= ∫⁻ s in Ioc 0 t, ‖G s‖ₑ`  (`setLIntegral_congr_fun`; pointwise `sobolevNormAt_eq` then
`ofReal_norm`)
`≤ ∫⁻ s in Ioi 0, ‖G s‖ₑ`  (`lintegral_mono'` + `Measure.restrict_mono Ioc_subset_Ioi_self`)
`= eLpNorm G 1 forceTimeMeasure`  (`eLpNorm_one_eq_lintegral_enorm`; `forceTimeMeasure` defeq
`volume.restrict (Ioi 0)`).
Step 2: `.toReal` monotone, RHS finite by `hfin`.

## Failed / corrected attempts (exact errors)

1. **`rw [sobolevNormAt_eq ...]` in the `setLIntegral_congr_fun` pointwise goal, before
   β-reduction.**  The congruence goal is `(fun s => ENNReal.ofReal (sobolevNormAt m f s)) s =
   (fun s => ‖G s‖ₑ) s`, an *un-β-reduced* lambda application, so `rw` reports
   `error: Tactic 'rewrite' failed: Did not find an occurrence of the pattern sobolevNormAt (↑m) f s`.
   **Fix:** open the pointwise goal with `show ENNReal.ofReal (sobolevNormAt (m : ℝ) f s) = ‖G s‖ₑ`
   (defeq + β), then `rw [sobolevNormAt_eq (hpath s (le_of_lt hs.1)), ofReal_norm]`.
   **Attribution correction (review Finding 6):** the `set g := …` I used while prototyping is a
   **red herring** — the reviewer reproduced the *identical* error with the `set` line deleted.
   The sole cause is `setLIntegral_congr_fun`'s un-β-reduced pointwise goal; the `show …` fix
   stands.

2. **`exact hasCompactSupport_zero` for `HasCompactSupport (0 : VelocityField)`** (non-vacuity
   witness):
   `error: unknownIdentifier 'hasCompactSupport_zero'` — no such lemma in this Mathlib pin.
   **Fix:** `simp only [HasCompactSupport, tsupport, Function.support_zero, closure_empty]` then
   `exact isCompact_empty`; the `tsupport ⊆ positiveTimeDomain` clause is `by simp [tsupport]`
   (`tsupport 0 = ∅ ⊆ _`).

3. **`Filter.eventually_of_forall`** for the a.e.-nonneg argument of `integral_mono_interval`:
   used `ae_of_all _ (fun x => sobolevNormAt_nonneg ..)` instead (robust across the deprecation
   of `eventually_of_forall`).

## Optional variant and MAINT notes (review Findings 3, 4, 5)

* **Finding 4 — `hT₀ : 0 < T₀` is removable** (optional, statement unchanged).  `hT₀` only
  orients `Set.uIcc_of_le` in the integrability step; for `T₀ ≤ 0` the set `Ico 0 T₀` is empty
  and the bundle holds with `Bbnd := 0`.  A hypothesis-free `forceCap'` compiles in ~5 extra
  lines (`rcases le_or_gt T₀ 0`; empty case discharges `∀ t ∈ ∅` by `absurd`, else `forceCap`).
  Reviewer confirmed it (`/tmp/rev137/nohT0.lean`, standard-3).  **Not added** to the module to
  keep the export surface minimal and the existing statement unchanged; fold in if the module is
  touched again.
* **Finding 5 — placement (MAINT split candidate).**  `sobolevNormAt_nonneg`,
  `intervalIntegral_le_forceSobolevENormL1(_of_memForceR)` name no A01 object and belong beside
  their inputs in `A04/Forcing.lean` / `A04/Continuity.lean`; only `forceCap`, `forceCap_L1` and
  the `example` are A01-flavoured (shaped by `gronwall_bddAbove_Ico`).  Left in A01 for now
  because the *bundle* is the deliverable.
* **`sobolevNormAt_nonneg` should be the single name** (MAINT).  The same fact is written inline
  at `A04/HighContinuation.lean:207`, in lane 138's `A04/HighContinuationIntegral.lean:104`, with
  a `gradientSobolevNormAt` twin at `A04/EnergyIdentityHigh.lean:115`.  It belongs in
  `A04/Forcing.lean` next to the `def` (plus `gradientSobolevNormAt_nonneg`), with those call
  sites rewritten.
* **Finding 6 — CI coverage.**  Like `A01/Propagation.lean`, `ForceCap.lean` is imported by no
  `Contracts/`/`Bindings/` module, so `make test`'s closure never compiles it; only
  `experiments/build_changed_lean.py` (and the lead's explicit `Section4` sweep) covers it.
  Unchanged from lane 122 F1.

## Non-vacuity — now with a nonzero witness (review Finding 3)

Two `F_R` members exhibit non-vacuity:

* **Zero force** (degenerate; both sides of the L¹ cap `= 0`): `memForceR_zero : MemForceR 0`
  built via `memForceR_of_memForceCompact` (zero is globally smooth with empty, hence compact,
  support).  `nonvac_forceCap`, `nonvac_L1cap`, `nonvac_forceCap_L1` apply the three consumers.
* **Nonzero bump force** (review Finding 3, preserved verbatim in
  `research/A01/probes/memForceR_bump_witness.lean`): `Fbump (t,x) = (tb t · xb x) • e₀` with a
  time `ContDiffBump` supported in `[1,3] ⊂ (0,∞)` and a space bump, `memForceR_Fbump` via
  `memForceR_of_memForceCompact`, `Fbump_ne_zero` at `(2,0)`; `nonvac_forceCap_nonzero`,
  `nonvac_L1_nonzero` instantiate the two caps.  This is the **first nonzero closed `MemForceR`
  term in the project** — grep of `memForceR_` had shown only conditional constructors
  (`memForceR_add`, `memForceR_of_memForceCompact`, `memForceR_add_compact`, `memForceR_congr`,
  `memForceR_of_force_formula`, `memForceR_of_compact_difference`, `R42.memForceR_insertedForce`),
  all needing a base, and no `memForceR_zero` in `formalization/`.  **Promotion candidate for
  D01** as `memForceR_bump`; every future non-vacuity audit of an `F_R` consumer wants a nonzero
  witness.  Pin gotcha (LESSON): `ContDiffBump.contDiff`'s `n : ℕ∞`, so `(n := ∞)` mismatches —
  write `(n := (⊤ : ℕ∞))`.

All 13 declarations in `research/A01/axioms_a3_force.lean` (5 exports + 4 zero-force + 4
nonzero-force) audit to exactly `[propext, Classical.choice, Quot.sound]`.
