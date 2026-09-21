# Review — lane 051, B02 unit 1 (`annular_truncation`)

Reviewer: independent opus reviewer. Worktree `.claude/worktrees/051-B02-unit-1`, commit `793c07b`.
Scope: the two spec fields `annularRestriction` and `annularSmoothing`
(`research/B02/Spec.lean:302-318`), module
`formalization/NSFormalization/Section4/B02/Annular.lean` (405 lines, namespace
`NSFormalization.Section4.B02`).

## Verdict: **ACCEPT-WITH-NOTES**

The two theorems are the spec fields verbatim, they are proved from standard axioms
only, the mathematics is correct, and the honesty record checks out. One real
finding (a dead 8x heartbeat bump) and four informational notes.

---

## 1. Commands and results

All from `WT/verification` after `. ../scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`.

| # | Command | Result |
|---|---------|--------|
| 1 | `bash scripts/lean-install.sh` (from WT) | `== OK`; `lake test` green, all contract tests report "standard logical axioms only" |
| 2 | `lake build NSFormalization.Section4.B02.Annular` | **exit 0**, `Build completed successfully (8809 jobs)` |
| 3 | `grep -n 'Annular' <build log>` | **no matches** — zero warnings/info emitted by `Annular.lean` (the 12 warnings in the log are pre-existing, from `Source/RealSobolev.lean`, `Paper3/RealPositiveDensity.lean`, `Paper3/RealVectorPositiveDensity.lean`, `Paper3/SobolevDirectionalDerivative.lean`) |
| 4 | `lake env lean ../formalization/NSFormalization/Section4/B02/Annular.lean` (fresh elaboration, not a replay) | **exit 0**, **0 bytes of output**, 5.5 s wall |
| 5 | `lake env lean ../research/B02/axioms_u1.lean` | **exit 0**; both `example`s type-check; `annularRestriction depends on axioms: [propext, Classical.choice, Quot.sound]`, `annularSmoothing depends on axioms: [propext, Classical.choice, Quot.sound]` — exactly the permitted three |
| 6 | `grep -n 'sorry\|admit\|native_decide\|axiom\|maxHeartbeats\|set_option' Annular.lean` | one hit outside comments: **`Annular.lean:58: set_option maxHeartbeats 1600000`** (see Finding 1). The other hit, line 44, is inside the module docstring. `axioms_u1.lean` hits are only the two `#print axioms` lines and a path in a comment. **No `sorry`, no `admit`, no `native_decide`, no `axiom` declaration anywhere.** |
| 7 | `make check` (from WT) | **exit 0** — `check_formalization_plan.py --check`, `check_contracts.py`, `test_contract_policy.py` (13 tests, OK), `check_work_queue.py` ("30 work items: ownership, contract registration and task cards consistent") |
| 8 | Heartbeat-necessity probe: `sed '/^set_option maxHeartbeats 1600000$/d' Annular.lean > /tmp/AnnularNoHB.lean; lake env lean /tmp/AnnularNoHB.lean` | **exit 0, 0 bytes of output, 5.8 s** — the bump is not needed (see Finding 1) |

---

## 2. Spec conformance — PASS

### 2.1 The §0 restatements are byte-identical to the spec

Extracted each `def` body from the three files and diffed:

```
for d in frequencyAnnulus closedFrequencyAnnulus IsAnnularDatum \
         IsAnnularRestriction IsAnnularSupported; do
  diff <(awk "/^def $d /,/^$/" research/B02/Spec.lean | sed '/^$/d') \
       <(awk "/^def $d /,/^$/" formalization/.../Annular.lean | sed '/^$/d')
  diff <(...) <(awk "/^def $d /,/^$/" research/B02/axioms_u1.lean | sed '/^$/d')
done
```

All ten diffs empty: **Spec.lean ≡ Annular.lean §0 ≡ axioms_u1.lean SpecMirror**, token
for token, for all five predicates. Only the namespace differs, as the header claims.

### 2.2 The theorem statements are the spec field types, with no extra hypotheses

`diff -w` of each spec field's type against the corresponding `example` type in
`axioms_u1.lean`: **empty for both** (the raw diff shows indentation only, since the
spec fields are indented as structure fields).

* `annularRestriction : ∀ (s : ℝ) (A : RealVectorSobolev s) (η : ℝ≥0∞), 0 < η → ∃ (δ R : ℝ) (Z : RealVectorSobolev s), 0 < δ ∧ δ < R ∧ IsAnnularRestriction δ R A Z ∧ ‖Z - A‖ₑ < η` — matched.
* `annularSmoothing : ∀ (s : ℝ) (δ R : ℝ), 0 < δ → δ < R → ∀ (Z : RealVectorSobolev s), IsAnnularSupported δ R Z → ∀ η : ℝ≥0∞, 0 < η → ∃ (δ' R' : ℝ) (W : RealVectorSobolev s), 0 < δ' ∧ δ' < δ ∧ R < R' ∧ IsAnnularDatum δ' R' W ∧ ‖W - Z‖ₑ < η` — matched.

Both `example`s are discharged by the bare theorem name (`:= NSFormalization.Section4.B02.annularRestriction`), so the theorems *are* the spec fields definitionally. No hypothesis was added, weakened or reordered; no `s`-restriction was introduced (both are `∀ s : ℝ`).

### 2.3 The `annularSmoothing` output annulus — the specific question raised in the brief

**The spec does not fix `δ'` and `R'`; it existentially quantifies them** (`Spec.lean:317`:
`∃ (δ' R' : ℝ) (W : RealVectorSobolev s), 0 < δ' ∧ δ' < δ ∧ R < R' ∧ …`), with the
docstring at `Spec.lean:310-313` asking only for "an `IsAnnularDatum δ' R'` with
`0 < δ' < δ` and `R < R'`, so that the enlarged annulus still avoids the origin".

The lane instantiates `δ' := δ/2`, `R' := 2*R` (`Annular.lean:334`,
`refine ⟨δ / 2, 2 * R, W, by positivity, by linarith, by linarith, ?_, ?_⟩`). The three
side conditions discharge because `0 < δ` and `0 < R` (`hR : 0 < R := hδ.trans hδR`):

* `0 < δ/2` ✓, `δ/2 < δ` ✓ (needs `0 < δ`, which is a hypothesis), `R < 2*R` ✓ (needs `0 < R`, derived).

**This is a legitimate instance of the spec's `∃ δ' R'`, not a mismatch.** It is also the
*tightest* choice the cutoff supports: `annularCutoff δ R = cutoff R · (1 − cutoff (δ/2))`
is exactly `1` on `[δ, R]` and supported in `(δ/2, 2R)`, matching the vendor bump's
`cutoff_eq_one (0<R) (‖x‖ ≤ R)` / `cutoff_eq_zero (0<R) (2R ≤ ‖x‖)`
(`vendor/NavierStokesAndEuler/NavierStokes/R3/ComparisonCutoffs.lean:76,87`). I checked
both cutoff lemma signatures against the uses in `annularCutoff_eq_one`
(`Annular.lean:288`) and `annularCutoff_support` (`Annular.lean:296`) — the arithmetic
(`2·(δ/2) = δ ≤ ‖ξ‖`) is right. **No finding.**

Note the support proof correctly targets the *closed* annulus: `closure_minimal` reduces
`tsupport (g i) ⊆ closedFrequencyAnnulus (δ/2) (2R)` to `support (g i) ⊆ …`, which yields
strict inequalities that are then relaxed with `le_of_lt`. Using the closed annulus is
what makes taking the closure sound, and it is what `IsAnnularDatum` asks for.

---

## 3. Mathematics — PASS

### 3.1 The datum norm is **unweighted** L² — the brief's weight concern does not arise

Traced the carrier:

* `RealVectorSobolev s := Product (Fin 3) (RealSobolevHilbert s)` (`Paper3/RealVectorPositiveDensity.lean:15`)
* `Product ι H := PiLp 2 (fun _ : ι => H)` (`Source/FiniteHilbertBochner.lean:11`)
* `RealSobolevHilbert s := realSubspace s` (`Source/RealSobolev.lean:122`)
* `realSubspace (_s : ℝ) : ClosedSubmodule ℝ FourierData` (`Source/RealSobolev.lean:119`) — **the `s` is a discarded underscore**
* `FourierData := Lp ℂ 2 (volume : Measure Space)` (`Source/RealSobolev.lean:19`) — **plain, unweighted L²(ℝ³;ℂ)**
* cross-check: `SobolevHilbert (_s : ℝ) := Lp ℂ 2 (volume : Measure Space)` (`Paper3/SobolevHilbertModel.lean:21`), also weight-free.

So `‖·‖ₑ` on `RealVectorSobolev s` is the ℓ²-over-`Fin 3` combination of **unweighted**
L²(ℝ³;ℂ) norms. The Sobolev weight `(1+‖ξ‖²)^(s/2)` enters this model only inside
`weightedFourierLp s`, the *map* that sends a Schwartz function to its datum; the datum
itself is the already-weighted Fourier representative, living in plain L². The module
docstring's claim (`Annular.lean:21-23`, "the datum norm `‖·‖ₑ` read below is literally
the `L²(ℝ³;ℂ³)` norm of that Fourier-side representative") is **accurate**, and matches
the spec's own justification at `Spec.lean:293-300` ("`homogeneousENorm` *is* the `L²`
norm of the datum … Every real `s` is covered: the step is a property of `L²`, not of the
weight").

**Consequence for the brief's question:** there is no weight left inside the norm, so the
dominated-convergence argument does not need to carry one. The `∫⁻`-DCT in
`tendsto_eLpNorm_annulus_compl` (`Annular.lean:138`) dominating by `‖f ξ‖ₑ^2` with
`∫⁻ ‖f‖ₑ^2 ≠ ⊤` (from `Lp.memLp`) is complete as written. **No finding.** See Note 2 for
the modelling caveat this implies.

### 3.2 `annularRestriction` — correct

Sequence `S n = frequencyAnnulus ((n:ℝ)+2)⁻¹ ((n:ℝ)+2)`, so `δ ↓ 0` and `R ↑ ∞`.
For each `ξ ≠ 0` (a.e., since `{0}` is null in ℝ³ — `measure_singleton`), the tail
indicator `(S n)ᶜ.indicator (‖f ·‖ₑ^2) ξ` is eventually `0`, because `((n:ℝ)+2)⁻¹ < ‖ξ‖`
eventually and `‖ξ‖ < (n:ℝ)+2` eventually. Dominated by `‖f ξ‖ₑ^2`, integrable.
`tendsto_lintegral_of_dominated_convergence'` gives `∫⁻_{(S n)ᶜ} ‖f‖ₑ^2 → 0`, lifted to
`eLpNorm → 0` by `Filter.Tendsto.ennrpow_const (1/2)` plus
`ENNReal.zero_rpow_of_pos`. Correct.

The truncation error is then identified exactly: `annularTruncLp δ R (A i) − A i` is a.e.
`−((annulus)ᶜ.indicator (A i))`, so `‖Z i − A i‖ = (eLpNorm of the tail).toReal`. Correct
— this is an identity, not an inequality, so nothing is lost.

**Reality is preserved.** `annularTruncLp_mem` (`Annular.lean:197`) is the lemma the brief
asked me to find. It proves `annularTruncLp δ R A ∈ realSubspace s` via
`mem_realSubspace_iff` (`Source/RealSobolev.lean:123`, `h ∈ realSubspace s ↔ realSymmetry h = h`),
using `realSymmetry_ae` (`RealSobolev.lean:27`, `realSymmetry h =ᵐ fun ξ => conj (h (−ξ))`)
and `neg_mem_frequencyAnnulus` (`Annular.lean:97`, the annulus is `ξ ↦ −ξ` invariant since
`‖−ξ‖ = ‖ξ‖`). The indicator is real (a `Set.indicator`, so the two cases are
`conj (A(−ξ)) = A(ξ)` and `conj 0 = 0`). Both cases are handled. Correct.

**δ genuinely depends on η** (the brief's "datum supported near 0" sanity check). The
binder order in the spec is `∀ η, 0 < η → ∃ δ R Z`, i.e. `δ` after `η`. In the proof
(`Annular.lean:225-240`) the chain is `η → ε` (`exists_real_le_enorm`) `→ n` (`hev.exists`,
where `hev` is the eventual-smallness statement built from `ε/4`) `→ δ₀ = ((n:ℝ)+2)⁻¹`.
So `δ₀` is chosen after and as a function of `η`. Confirmed, no cheat.

Trivial-case sanity: with `A = 0` the statement is satisfiable but not vacuously — the
spec still demands `IsAnnularRestriction δ R A Z`, which pins `Z` to the indicator of `A`,
so nothing degenerate is being exploited.

### 3.3 `annularSmoothing` — correct

`MemLp.exist_eLpNorm_sub_le` (Mathlib `Analysis.Normed.Lp.SmoothApprox`) gives smooth
compactly supported `g₀ i` with `eLpNorm (Z i − g₀ i) 2 ≤ ofReal (ε/4)`. The cutoff
multiplication `v i = χ · g₀ i` does not increase the error, by a **pointwise** bound
proved a.e. (`Annular.lean:381-400`):

* where `Z i ξ = 0`: `‖χ ξ • g₀ i ξ − 0‖ = ‖χ ξ‖·‖g₀ i ξ‖ ≤ ‖g₀ i ξ‖ = ‖Z i ξ − g₀ i ξ‖`, using `0 ≤ χ ≤ 1`;
* where `Z i ξ ≠ 0`: the contrapositive of `hZ i : ∀ᵐ ξ, ξ ∉ frequencyAnnulus δ R → Z i ξ = 0` puts `ξ` in the open annulus, hence `δ ≤ ‖ξ‖ ≤ R`, hence `χ ξ = 1`, and the bound is the equality `‖g₀ − Z‖ = ‖Z − g₀‖`.

This is where `IsAnnularSupported` is consumed, and it is consumed correctly. Then
`eLpNorm_mono_ae` transports the pointwise bound.

**Reality is restored, and for free.** `W i := realProjectionTo s ((hvmem i).toLp)`
(`Paper3/RealPositiveDensity.lean:21`, `realProjection.codRestrict …`). The estimate
survives because `realProjectionTo_inclusion` gives `realProjectionTo s (Z i) = Z i` (so
`W i − Z i = realProjectionTo (v.toLp − Z i)` after `← map_sub`) and
`realProjectionTo_norm_le` gives operator norm `≤ 1`. Correct — this is the right order of
operations; projecting first and estimating after would not have worked.

The smooth representative demanded by `IsAnnularDatum` is
`g i ξ = (1/2)·(v i ξ + conj (v i (−ξ)))`, which is exactly the coeFn of `realProjection`
(`realProjection_apply` + `realSymmetry_ae`, assembled a.e. at `Annular.lean:357-371`).
Smoothness: `(hvsmooth i).add (conjCLE.contDiff.comp ((hvsmooth i).comp contDiff_neg))`,
scaled. Support: both the `ξ` branch and the `−ξ` branch land in the annulus, the latter
via `norm_neg`. All three `IsAnnularDatum` conjuncts are discharged. Correct.

### 3.4 The componentwise-to-datum step is sound

`enorm_sub_lt_of_forall_le` (`Annular.lean:103`): from `‖(X−Y) i‖ ≤ ε/4` for each of the
three components it derives `‖X−Y‖ₑ < ofReal ε`, by `PiLp.norm_eq_of_L2` and
`√(Σ aᵢ²) ≤ Σ aᵢ` (for `aᵢ ≥ 0`), giving `‖X−Y‖ ≤ 3·(ε/4) = 0.75ε < ε`. The slack is real,
not a rounding fudge. Correct. `exists_real_le_enorm` handles `η = ⊤` by returning `ε = 1`
— correct, since `ofReal 1 ≤ ⊤`.

---

## 4. Honesty of `ATTEMPTS_U1.md` — PASS (both spot-checks reproduce)

Checked the two snags named in the brief, by elaborating probe files against the same
environment.

**Snag 3** — "`AddSubgroupClass.coe_sub` does **not** apply to `↥(realSubspace s)` (no
`AddSubgroupClass (ClosedSubmodule …)` instance)".

```lean
example (s : ℝ) : True := by
  have : AddSubgroupClass (ClosedSubmodule ℝ FourierData) FourierData := by infer_instance
  trivial
```
→ `error(lean.synthInstanceFailed): failed to synthesize instance of type class
AddSubgroupClass (ClosedSubmodule ℝ ↥FourierData) ↥FourierData`. **Reproduced exactly as recorded.**

**Snag 5** — "`Set.not_mem_compl_iff` does not exist".

```lean
#check @Set.not_mem_compl_iff
```
→ `error(lean.unknownIdentifier): Unknown constant `Set.not_mem_compl_iff``. **Reproduced
exactly as recorded.** The replacement the log claims (`not_not.mpr`) is indeed what the
proof uses, at `Annular.lean:177` (`Set.indicator_of_notMem (not_not.mpr hmemS)`).

Both records are truthful and specific. The remaining seven entries are consistent with
what the proof actually does (e.g. entry 7's `lintegral_indicator` bridge is visibly
present at `Annular.lean:181-184`; entry 9's `lt_of_lt_of_le · hεη` pattern appears at both
theorem endings). I found nothing in the log that overstates the work.

---

## 5. Findings

### Finding 1 — `set_option maxHeartbeats 1600000` is dead weight (severity: **minor**)

* **Declaration/location**: `formalization/NSFormalization/Section4/B02/Annular.lean:58` (file-scope, so it covers every declaration in the module).
* **What is wrong**: an 8x bump over Lean's default `200000`. It is **not needed**: I deleted the line and re-elaborated the whole file, which succeeded in **5.8 s with zero output** (command 8 above) — essentially the same 5.5 s the file takes with the bump. A permanent 8x ceiling on a file that uses a small fraction of the default budget hides future regressions: a later Mathlib bump could make one of these proofs 8x slower and CI would stay green.
* **Fix**: delete line 58. If some single declaration is later found to need headroom, scope the bump to it with `set_option maxHeartbeats … in` immediately above that declaration rather than to the whole file.

---

## 6. Notes (no action required for this unit)

**Note 1 — the module is in no default build target.** `formalization/lakefile.toml`'s
`NSFormalization` lean_lib declares neither `globs` nor `roots`, so its root is
`NSFormalization.lean`, which does not import `Section4.B02.Annular`. `lake build
NSFormalization`, `lake test` and `make check` therefore never compile this file; only the
explicit module target does. This is **not this lane's doing** — I checked all eight
sibling `Section4` directories (`A02 A03 A05 D01 I01 I02 I03 R42`) and `grep -c 'Section4'`
over `NSFormalization.lean` and both lakefiles returns **0** for every one of them. Flagging
it because it means none of the Section 4 work is currently regression-protected by CI.

**Note 2 — "every real `s` is covered" is true but carries no `s`-dependent content.**
Because `realSubspace (_s : ℝ)` and `SobolevHilbert (_s : ℝ)` both discard `s`,
`RealVectorSobolev s` is literally the same type with the same norm for every `s`. The
two theorems are therefore honest, fully general statements about L²(ℝ³;ℂ³) — which is
exactly what `Spec.lean:293-300` says they should be. The bridge from this L² statement to
the physical `Ḣ^s` truncation is the isometric identification asserted elsewhere in the
model (`02-preliminaries.tex:63`), not something this unit proves or needs to prove. I
raise it only so it is not later mistaken for a proof that the weighted tail is small.

**Note 3 — the pre-existing warnings.** The 12 warnings in the build log all come from
files this lane did not touch (`Source/RealSobolev.lean:90`, `Paper3/RealPositiveDensity.lean:57,66,78,90`,
`Paper3/RealVectorPositiveDensity.lean:29`, `Paper3/SobolevDirectionalDerivative.lean:103`)
— unused simp args, `<;>` style, an unused binder name, one deprecation. Out of scope here,
but they will trip `warningAsError` if any of these modules is ever pulled into the
`Tests` library.

**Note 4 — `Spec.lean` is not on the module path.** `research/B02/Spec.lean` imports
`Contracts.V1.Data`, which depends on `NSFormalization`, so `Annular.lean` cannot import
the spec and the §0 restatement is unavoidable. The lane handled this the right way: the
restatements are byte-identical (verified in §2.1) and `axioms_u1.lean` closes the loop by
exhibiting the spec-shaped `example`s. The residual risk is that a future edit to
`Spec.lean` silently desynchronises the copies; a text-level guard in `make check` would
close it, but that is a repo-level improvement, not a lane obligation.

---

## 7. Summary

* Builds clean, exit 0, no warnings from the file, fresh elaboration produces no output.
* `#print axioms` = `[propext, Classical.choice, Quot.sound]` for both theorems.
* No `sorry`/`admit`/`native_decide`/`axiom`. One `set_option` — Finding 1.
* `make check` exit 0.
* Both theorems are the spec fields verbatim; all five §0 predicates byte-identical to `Spec.lean`; no extra hypotheses; `δ' = δ/2, R' = 2R` is a valid instance of the spec's `∃ δ' R'`.
* Mathematics correct: the datum norm is unweighted L², so the DCT argument is complete; reality preservation is proved (`annularTruncLp_mem`, `realProjectionTo`); `δ` genuinely depends on `η`.
* `ATTEMPTS_U1.md` reproduces on both spot-checks.

**ACCEPT-WITH-NOTES** — merge after deleting `Annular.lean:58`, or accept as-is and track
Finding 1 as cleanup.
