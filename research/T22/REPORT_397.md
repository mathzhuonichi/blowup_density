# REPORT_397 — T22 U-A3 `cutoffMultiplier` analytic core (Opus; transcribed by lead from the agent message, report-file guard)

Committed as `44bd6441`. All gates green, no forbidden tokens, axioms clean. Here is the four-part report.

---

## Lane 397 — T22 U-A3 (`cutoffMultiplier` analytic core): report

**Commit `44bd644172bde8023698f436aadf9e09f6c884b4`** on branch `erenup/397-T22-UA3-cutoff-multiplier`.

### 1. What was proved (theorems, exact statements, the constant)

New module `/data_8T/ping/blowup_density/.claude/worktrees/397-T22-UA3-cutoff-multiplier/formalization/NSFormalization/Section3/T22/CutoffMultiplier.lean` (namespace `NSFormalization.Section3.T22`). The **analytic engine** of U-A3 — the `Peetre × kernel-mass × Young` route — is complete and self-contained.

- `def besselW (t ξ) := (1 + ‖ξ‖^2)^(t/2)`; `besselW_nonneg`; `besselW_peetre (s ξ y) : besselW s ξ ≤ peetreConst s * besselW s (ξ - y) * besselW |s| y` (Peetre, lane 386).
- **`eLpNorm_besselWeight_scalarConvolution_le`** (the engine):
  ```
  (s : ℝ) (K g : Space → ℂ)
  (hK : Integrable (fun ζ => besselW |s| ζ * ‖K ζ‖))
  (hg : MemLp (fun η => (besselW s η : ℝ) • g η) 2 volume) :
  eLpNorm (fun ξ => (besselW s ξ : ℝ) • scalarConvolution K g ξ) 2 volume ≤
    ENNReal.ofReal (peetreConst s * ∫ ζ, besselW |s| ζ * ‖K ζ‖)
      * eLpNorm (fun η => (besselW s η : ℝ) • g η) 2 volume
  ```
  Proof: pointwise a.e. `‖besselW s ξ • (K∗g) ξ‖ ≤ peetreConst s · (K̃ ∗ g̃) ξ` (Peetre inside the convolution integral, `K̃ = besselW |s|·‖K‖`, `g̃ = ‖besselW s • g‖`), via `norm_integral_le_integral_norm` + `integral_mono_of_nonneg`; then `eLpNorm_mono_ae_real`, `eLpNorm_const_smul`, and Young `L¹∗L²→L²` (`Source.YoungConvolution.memLp_convolution_one_two`) lifted to `ℝ≥0∞`; kernel mass `eLpNorm K̃ 1 = ofReal (∫ K̃)`.
- `def cutoffMultiplierConst (s χ) := peetreConst s * ∫ ζ, besselW |s| ζ * ‖angularFourier (fun x => (χ x : ℂ)) ζ‖`; `cutoffMultiplierConst_nonneg`.
- **`eLpNorm_cutoff_multiplier_le`** — the engine specialized to `K = angularFourier χ_ℂ` for smooth compact `χ` (lane 391 kernel mass), constant `cutoffMultiplierConst s χ`.

**The constant** is exactly `C = peetreConst s · ∫ (1+‖ζ‖²)^{|s|/2}‖angularFourier χ_ℂ ζ‖` (386 Peetre constant × 391 kernel mass), the `T22_SPLIT` U-A3 constant. Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`.

### 2. What exists in Lean now

The full `L²`-operator content of the cutoff `H^s` multiplier bound, for **every real `s`**, as a reusable engine plus its cutoff specialization: given any input transform `g` with `besselW s • g ∈ L²`, the Bessel-weighted convolution against `angularFourier χ_ℂ` is `L²`-bounded by `cutoffMultiplierConst s χ`. This is the estimate the `cutoffMultiplier` field consumes once its datum `A` is identified with `g` in the angular normalization.

### 3. The gap (verbatim field NOT closed — residual is datum-model plumbing, not analysis)

`BoundedDomainNormAPI.cutoffMultiplier` is **not** delivered. It quantifies over every tempered `A : RealVectorSobolev s` and states `IsCutoffDatum` through `angularRealization` (a weighted-angular-Fourier `L²` model). On top of the engine it needs (exact statements in `research/T22/ATTEMPTS_UA3.md`), none of which is new analysis nor has an in-tree proof:

- **R1 (long pole)** — general-`A` datum ↔ weighted-convolution identity: for `b i = besselW s • scalarConvolution (angularFourier χ_ℂ) (besselW (-s) • (A i))`, prove `∀ i ψ, angularRealization s (b i) ψ = angularRealization s (A i) (smulLeftCLM ℂ (χ·) ψ)`. This is the angular Fourier **product→convolution** identity at the `L²`/tempered level. Mathlib has only the Schwartz-level **forward** direction `Real.fourier_mul_convolution_eq` (`𝓕(f∗g)=𝓕f·𝓕g`); the product→convolution direction, its `Lp` lift by density, and the `frequencyUnit`/angular-dilation bookkeeping are all absent.
- **R2** — `realSubspace` preservation `realSymmetry (b i) = b i` (real-even `angularFourier χ_ℂ`), so `B : RealVectorSobolev s`.
- **R3** — datum-norm ↔ `eLpNorm` identification and the `PiLp 2` Pythagorean vector assembly `‖B‖ₑ² = ∑ i ‖B i‖ₑ²`.
- **R4** — `0 < C` for all `χ` (incl. `χ=0`): take `C := cutoffMultiplierConst s χ + 1`.

The smooth-datum fallback is **not** a shortcut: its norm conjunct still needs R1 (product→convolution), so it too cannot close without a sorry — hence not delivered as a stub. Rejected route: Mathlib has **no** spatial-multiplier-preserves-`MemSobolev` theorem (only Fourier multipliers and scalar smul); `LocalizationBoundary`+T13 covers only `s∈(0,1)`, a cross-check not a substitute.

### 4. Commands run and results

From the worktree, `. scripts/lean-env.sh`, `lake` from `verification/` with `LEAN_NUM_THREADS=6`:
- `lake build NSFormalization.Section3.T22.CutoffMultiplier` → `✔ Built … (0 errors)`.
- `lake env lean …/CutoffMultiplier.lean` → no errors.
- `lake env lean …/research/T22/probes/cutoff_multiplier_closes.lean` → no errors (ContDiffBump cutoff + genuinely nonzero finite-`L²` input, engine + specialization applied at `s=1/2` and `s=-2`, plus `cutoffMultiplierConst_nonneg`).
- `lake env lean …/research/T22/axioms_ua3.lean` → all four key declarations `[propext, Classical.choice, Quot.sound]`.
- `make check` → exit 0.

Files (absolute):
- `/data_8T/ping/blowup_density/.claude/worktrees/397-T22-UA3-cutoff-multiplier/formalization/NSFormalization/Section3/T22/CutoffMultiplier.lean`
- `/data_8T/ping/blowup_density/.claude/worktrees/397-T22-UA3-cutoff-multiplier/research/T22/probes/cutoff_multiplier_closes.lean`
- `/data_8T/ping/blowup_density/.claude/worktrees/397-T22-UA3-cutoff-multiplier/research/T22/axioms_ua3.lean`
- `/data_8T/ping/blowup_density/.claude/worktrees/397-T22-UA3-cutoff-multiplier/research/T22/ATTEMPTS_UA3.md` (residual R1–R4)
- `/data_8T/ping/blowup_density/.claude/worktrees/397-T22-UA3-cutoff-multiplier/research/T22/T22_SPLIT.md` (U-A3 status: PARTIAL)
- `/data_8T/ping/blowup_density/.claude/worktrees/397-T22-UA3-cutoff-multiplier/logs/LESSONS.md` (one line)

Note: `REPORT_397.md` was blocked by the report-file guard (as the brief anticipated), so this full report is in the message instead.
