# Lane 391 — T22 U-A2: the Fourier transform of a smooth compact cutoff is weighted-`L¹` (Opus 4.8)

Branch `erenup/391-T22-UA2-cutoff-kernel`. No `sorry`/`admit`/`axiom`/`native_decide`,
no named input, no `maxHeartbeats` bump; every declaration prints exactly
`[propext, Classical.choice, Quot.sound]`.

## 1. What was proved (`Section3/T22/CutoffKernel.lean`, namespace `NSFormalization.Section3.T22`)

- `integrable_weighted_schwartz (s : ℝ) (ψ : SchwartzMap Space ℂ) :`
  `Integrable (fun ζ : Space => (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖ψ ζ‖)`
  — the master analytic lemma: every Schwartz function is weighted-`L¹` for every
  real polynomial order.

- `cutoffSchwartz {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) : SchwartzMap Space ℂ`
  (+ `@[simp] cutoffSchwartz_apply … : cutoffSchwartz hχ hc x = (χ x : ℂ)`) — the
  smooth compact cutoff, complexified, packaged as a Schwartz function.

- **`integrable_weighted_fourier_cutoff {χ : Space → ℝ} (hχ : ContDiff ℝ ∞ χ)`**
  **`(hc : HasCompactSupport χ) (s : ℝ) :`**
  **`Integrable (fun ζ : Space => (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖angularFourier (fun x => (χ x : ℂ)) ζ‖)`**
  — the U-A2 target in the datum-layer angular-Fourier spelling
  (`NSFormalization.Source.angularFourier`, the convention `angularRealization` /
  `IsCutoffDatum` pair against).

- `integrable_weighted_fourier_cutoff_mathlib {χ : Space → ℝ} (hχ …) (hc …) (s : ℝ) :`
  `Integrable (fun ζ : Space => (1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖𝓕 (fun x => (χ x : ℂ)) ζ‖)`
  — the same in Mathlib's cycles convention (`FourierTransform.𝓕`).

- `lintegral_weighted_fourier_cutoff_ne_top {χ : Space → ℝ} (hχ …) (hc …) (s : ℝ) :`
  `(∫⁻ ζ : Space, ENNReal.ofReal ((1 + ‖ζ‖ ^ 2) ^ (|s| / 2) * ‖angularFourier (fun x => (χ x : ℂ)) ζ‖)) ≠ ⊤`
  — the `ENNReal`/`lintegral` finiteness form for U-A3's `‖·‖ₑ` bookkeeping.

Proof shape: `SchwartzMap.one_add_le_sup_seminorm_apply` (at `n = 0`, with
`norm_iteratedFDeriv_zero`) gives `(1+‖ζ‖)^N · ‖ψ ζ‖ ≤ C_N`; with
`(1+‖ζ‖²)^(|s|/2) ≤ (1+‖ζ‖)^|s|` and a natural `N > |s| + 3` the integrand is
dominated by `C_N · (1+‖ζ‖)^{-(N-|s|)}`, integrable by
`MeasureTheory.integrable_one_add_norm` (`finrank ℝ Space = 3 < N - |s|`). The two
convention wrappers apply the master lemma to `𝓕 (cutoffSchwartz …)` and to
`Paper3.schwartzAngularDilation (𝓕 (cutoffSchwartz …))` respectively; both
coercion identities are `rfl` (`SchwartzMap.fourier_coe`,
`Paper3.schwartzAngularDilation_fourier_apply`).

## 2. What exists in Lean now

New file `formalization/NSFormalization/Section3/T22/CutoffKernel.lean` (6 public
declarations above), building on:
- `NavierStokesR3.CompactSchwartz.ofCompactSupport` (vendor) — smooth compact ⇒ `SchwartzMap`;
- `NSFormalization.Paper3.schwartzAngularDilation` / `schwartzAngularDilation_fourier_apply`
  (`Paper3/AngularFourierDilation.lean`) — `SchwartzMap`-level angular transform;
- `NSFormalization.Source.angularFourier` — the manuscript's angular convention (datum layer);
- Mathlib `SchwartzMap.one_add_le_sup_seminorm_apply`, `integrable_one_add_norm`.

Supporting research files: probe `research/T22/probes/cutoff_kernel_closes.lean`
(a concrete `ContDiffBump` cutoff, `s = 1/2` and `s = -2`, both convention
spellings + the `ENNReal` form), axiom audit `research/T22/axioms_ua2.lean`,
notes `research/T22/ATTEMPTS_UA2.md`, U-A2 status appended in
`research/T22/T22_SPLIT.md`, one line in `logs/LESSONS.md`.

## 3. Gap

None for U-A2 as scoped. Two deliberate points recorded for the U-A3 consumer:
- The target cannot be stated for `𝓕χ` with `χ : Space → ℝ` directly — Mathlib's
  `𝓕` requires a `NormedSpace ℂ` codomain, and `ℝ` is not one. The kernel is the
  transform of the complex coercion `fun x => (χ x : ℂ)`, which is exactly what
  `IsCutoffDatum`'s `SchwartzMap.smulLeftCLM ℂ (fun x => (χ x : ℂ))` multiplies by,
  so U-A3 consumes it without conversion.
- The scalar/vector `χ • z` convolution-kernel form is left to U-A3 (not trivial
  here, and not needed to state the kernel mass).

## 4. Commands and results (from the worktree, after `. scripts/lean-env.sh`)

- `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T22.CutoffKernel`
  → `Built NSFormalization.Section3.T22.CutoffKernel (2.7s)`, `Build completed successfully (8812 jobs)`,
  0 errors (only pre-existing Paper3 deprecation/linter warnings, none in the new file).
- `lake env lean ../research/T22/probes/cutoff_kernel_closes.lean` → exit 0 (all six `example`s close).
- `lake env lean ../research/T22/axioms_ua2.lean` → every declaration
  `[propext, Classical.choice, Quot.sound]`.
- `make check` → contract policy tests `Ran 13 tests … OK`; work-queue check
  `45 work items: … consistent`.
- Forbidden-token scan (`sorry|admit|native_decide|axiom|set_option`) over the
  module, probe and audit files → no forbidden Lean declarations; the word axiom occurs only in the audit docstring.
