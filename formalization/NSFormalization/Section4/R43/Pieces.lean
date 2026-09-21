import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import NSFormalization.Paper1.ScalarEnergy

/-!
# R43 (Proposition 4.3) — the cheapest fully-closed proof-route pieces

`paper/sections/04-whole-space.tex:82-133` (`prop:Rcritical1`).  Split table:
`research/R43/R43_SPLIT.md`; reconciled contract: `research/R43/Spec.lean`
(`BlowupDensity.R43.Draft.RCritical1API`); gap table: `research/R43/COMPARISON.md` §4.

This module collects the R43 proof-route rows that close **without** any
unregistered upstream input, kept Fourier-free and contract-free so it depends
only on `Mathlib` and the domain-agnostic scalar bootstrap already in the tree
(`NSFormalization.Paper1.ScalarEnergy`).  It contains no `sorry`, no `axiom`, no
`native_decide`, and no placeholder `Prop`.

Rows delivered here:

* **G6** (`COMPARISON.md` §4, the `A04 ↔ C01` power-spelling pin): the `ℝ≥0∞`
  identity `x ^ (2:ℕ) = x ^ (2:ℝ)` that bridges A04's `squaredHTwoIntegral`
  (npow, `research/A04/Spec.lean:202`) to C01's `h2TimeIntegral` (rpow,
  `research/C01/Spec.lean:576,599`).  Instantiating `x := sobolevENorm 2 z`
  recovers the exact bridge; the binding does that after C01/A04 register.
* **G8** (`COMPARISON.md` §4, the `A05 ↔ C01` constant threading, "nothing owed"):
  the two `ν`-free shrinkings of the radius `c`.  `exists_critical_radius`
  chooses one `c` below both `1/(4C₀)` (`:104`) and the C01-gate threshold; the
  two `criticalL3_gate_*` lemmas discharge C01's absorption gate
  `ENNReal.ofReal C₁ * ‖u‖₃ ≤ ENNReal.ofReal (ν/4)`
  (`research/C01/Spec.lean:532,576`) from A05's `‖u‖₃ ≤ C(1/2)·y`
  (`research/A05/Spec.lean:366`) and `y ≤ cν`.
* **S2** (`04-whole-space.tex:100-104`), the `a = 0` clause: `criticalNormBound_radius`
  packages the tree's `NSFormalization.Paper1.critical_norm_bound` (the regularized
  square-root division + first-crossing continuity bootstrap) with the `ν/(2C₀)`
  gate arithmetic, so that the eq:Rcritical1 energy inequality propagates
  `y(t) ≤ cν` throughout the lifespan.  **Reuse, not a reproof**: the scalar
  bootstrap is domain-agnostic and already proved in `Paper1/ScalarEnergy.lean`.

What is deliberately **not** here, because it needs an unregistered sibling
clause or an R43-owned analytic input (see `R43_SPLIT.md`): S1/G7 (eq:Rcritical1
itself, R43-owned, size L); S3's `‖u‖₃ ≤ C(1/2)·y` (A05 `velocityCriticalL3`,
draft-only); S4 (C01 `h2TimeIntegral`, draft-only); S5 (A04
`lifespanInfiniteOfLocallyFinite`, draft-only); S6/G2 (the time-integrated force
monotonicity).  This file proves only the arithmetic and reuse rows.
-/

noncomputable section

namespace NSFormalization.Section4.R43

open Set
open scoped ENNReal

/-! ## G6 — the `ℕ`-pow vs rpow spelling pin -/

/-- **G6** (`research/R43/COMPARISON.md` §4): in `ℝ≥0∞`, the natural-number square
equals the real-power square.  This is the one identity that bridges A04's
`squaredHTwoIntegral` (`sobolevENorm 2 _ ^ (2:ℕ)`, `research/A04/Spec.lean:202`)
to C01's `h2TimeIntegral`/`sobolevTwoFourier` (`sobolevENorm 2 _ ^ (2:ℝ)`,
`research/C01/Spec.lean:576,599`).  Stated for a general `x : ℝ≥0∞`; the binding
instantiates `x := sobolevENorm 2 (slice w.velocity t)` to get the exact
per-slice bridge without any `.toReal`. -/
theorem enorm_npow_two_eq_rpow_two (x : ℝ≥0∞) : x ^ (2 : ℕ) = x ^ (2 : ℝ) := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]

/-! ## G8 — the two `ν`-free radius shrinkings and the absorption-gate discharge -/

/-- **G8** (`research/R43/COMPARISON.md` §4; `04-whole-space.tex:104,112`): a single
universal radius `c > 0` below **both** shrinkings of the proof —
`c < 1/(4C₀)` (the continuity-bootstrap gate, `:104`, with `C₀` R43's own) and
`C₁·C(1/2)·c ≤ 1/4` (which, after `y ≤ cν` and `‖u‖₃ ≤ C(1/2)·y`, discharges
C01's absorption gate `C₁‖u‖₃ ≤ ν/4`, `:112`).  Both thresholds are `ν`-free, so
one `c` serves every `ν`, exactly as the contract's single field `c` requires.
`C₀`, `C₁` and `Cemb = C(1/2)` are the strictly positive constants of R43, C01
(`research/C01/Spec.lean:260`) and A05 (`research/A05/Spec.lean:201`). -/
theorem exists_critical_radius {C₀ C₁ Cemb : ℝ}
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hCemb : 0 < Cemb) :
    ∃ c : ℝ, 0 < c ∧ c < 1 / (4 * C₀) ∧ C₁ * Cemb * c ≤ 1 / 4 := by
  have hpos : 0 < C₁ * Cemb := by positivity
  refine ⟨min (1 / (8 * C₀)) (1 / (4 * (C₁ * Cemb))), ?_, ?_, ?_⟩
  · exact lt_min (by positivity) (by positivity)
  · calc min (1 / (8 * C₀)) (1 / (4 * (C₁ * Cemb))) ≤ 1 / (8 * C₀) := min_le_left _ _
      _ < 1 / (4 * C₀) := by
          apply div_lt_div_of_pos_left one_pos (by positivity) (by linarith)
  · have hle : min (1 / (8 * C₀)) (1 / (4 * (C₁ * Cemb))) ≤ 1 / (4 * (C₁ * Cemb)) :=
      min_le_right _ _
    have key : C₁ * Cemb * (1 / (4 * (C₁ * Cemb))) = 1 / 4 := by
      have : C₁ * Cemb ≠ 0 := ne_of_gt hpos
      field_simp
    calc C₁ * Cemb * min (1 / (8 * C₀)) (1 / (4 * (C₁ * Cemb)))
        ≤ C₁ * Cemb * (1 / (4 * (C₁ * Cemb))) := mul_le_mul_of_nonneg_left hle hpos.le
      _ = 1 / 4 := key

/-- **G8**, real form of the absorption-gate discharge (`04-whole-space.tex:112`):
from A05's `‖u‖₃ ≤ Cemb·y` (`L3 ≤ Cemb·y`), the bootstrap bound `y ≤ c·ν`, and
the `ν`-free second shrinking `C₁·Cemb·c ≤ 1/4`, the gate `C₁·‖u‖₃ ≤ ν/4`.  No
sign hypothesis on `y` or `L3` is needed: the chain is monotone in the given
inequalities. -/
theorem criticalL3_gate_real {C₁ Cemb c ν y L3 : ℝ}
    (hC₁ : 0 ≤ C₁) (hCemb : 0 ≤ Cemb) (hν : 0 < ν)
    (hyc : y ≤ c * ν) (hL3le : L3 ≤ Cemb * y) (hgate : C₁ * Cemb * c ≤ 1 / 4) :
    C₁ * L3 ≤ ν / 4 := by
  nlinarith [mul_le_mul_of_nonneg_left hL3le hC₁,
             mul_le_mul_of_nonneg_left hyc (mul_nonneg hC₁ hCemb),
             mul_le_mul_of_nonneg_right hgate hν.le]

/-- **G8**, `ℝ≥0∞` form of the absorption-gate discharge, in the exact shape of
C01's hypothesis `ENNReal.ofReal C₁ * criticalL3 (slice w.velocity t) ≤
ENNReal.ofReal (ν/4)` (`research/C01/Spec.lean:532,576`).  Here `L3 : ℝ≥0∞` is
`criticalL3 (u t)` and `ENNReal.ofReal (Cemb * y)` is the right-hand side of
A05's `velocityCriticalL3` after `dotHomogeneousENorm (1/2) (u t) ≤ y` and
finiteness.  Everything stays in `ℝ≥0∞` with no `.toReal`. -/
theorem criticalL3_gate_enorm {C₁ Cemb c ν y : ℝ} {L3 : ℝ≥0∞}
    (hC₁ : 0 ≤ C₁) (hCemb : 0 ≤ Cemb) (hν : 0 < ν)
    (hyc : y ≤ c * ν) (hL3le : L3 ≤ ENNReal.ofReal (Cemb * y))
    (hgate : C₁ * Cemb * c ≤ 1 / 4) :
    ENNReal.ofReal C₁ * L3 ≤ ENNReal.ofReal (ν / 4) := by
  have hreal : C₁ * (Cemb * y) ≤ ν / 4 := by
    nlinarith [mul_le_mul_of_nonneg_left hyc (mul_nonneg hC₁ hCemb),
               mul_le_mul_of_nonneg_right hgate hν.le]
  calc ENNReal.ofReal C₁ * L3
      ≤ ENNReal.ofReal C₁ * ENNReal.ofReal (Cemb * y) := mul_le_mul' le_rfl hL3le
    _ = ENNReal.ofReal (C₁ * (Cemb * y)) := (ENNReal.ofReal_mul hC₁).symm
    _ ≤ ENNReal.ofReal (ν / 4) := ENNReal.ofReal_le_ofReal hreal

/-! ## S2 — the critical-norm continuity bootstrap at `a = 0`, by reuse -/

/-- **S2** (`04-whole-space.tex:100-104`), the `a = 0` clause the contract's
`inhomogeneousAtZero` consumes.  Given the eq:Rcritical1 scalar energy inequality
`½(y²)' + (ν − C₀y)z² ≤ by` (hypothesis `henergy`), a continuous nonnegative
`y` with `y(0) = 0`, and a forcing primitive `N` with `N(0) = 0` bounded by the
small total forcing `c·ν`, the critical norm obeys `y(t) ≤ c·ν` throughout
`[0,T]`.

This is a **reuse** of the domain-agnostic scalar bootstrap
`NSFormalization.Paper1.critical_norm_bound` (`Paper1/ScalarEnergy.lean:123`,
which is itself the regularized square-root division `sqrt_energy_le_primitive`
plus the first-crossing `continuous_bootstrap`).  The R43-specific content added
here is only the `ν`-free arithmetic that turns the single radius `c < 1/(2C₀)`
into the paper's gate `C₀·K ≤ ν/2` at `K = ν/(2C₀)` and the strict smallness
`ρ = c·ν < K`.  The general-`a` case (`y(0) ≠ 0`) is not closed here: it needs
`NSFormalization.Section4.C01.sqrt_energy_le_primitive'`
(`Section4/C01/EnergyBounds.lean:179`, the `E(0)/N(0)`-arbitrary generalization)
fed the same energy inequality, and is recorded as an open row in
`research/R43/R43_SPLIT.md`. -/
theorem criticalNormBound_radius {T ν C₀ c : ℝ} {y E' z b N : ℝ → ℝ}
    (hC₀ : 0 < C₀) (hν : 0 < ν) (hc0 : 0 ≤ c) (hclt : c < 1 / (2 * C₀))
    (hy : Continuous y) (hy0 : y 0 = 0)
    (hynonneg : ∀ t ∈ Icc 0 T, 0 ≤ y t)
    (hN : ContinuousOn N (Icc 0 T)) (hN0 : N 0 = 0)
    (hNbound : ∀ t ∈ Icc 0 T, N t ≤ c * ν)
    (hb : ∀ t ∈ Ioo 0 T, 0 ≤ b t)
    (hdE : ∀ t ∈ Ioo 0 T, HasDerivAt (fun x => (y x) ^ 2) (E' t) t)
    (hdN : ∀ t ∈ Ioo 0 T, HasDerivAt N (b t) t)
    (henergy : ∀ t ∈ Ioo 0 T, E' t / 2 + (ν - C₀ * y t) * (z t) ^ 2 ≤ b t * y t) :
    ∀ t ∈ Icc 0 T, y t ≤ c * ν := by
  have hC₀' : C₀ ≠ 0 := ne_of_gt hC₀
  have hKeq : C₀ * (ν / (2 * C₀)) = ν / 2 := by field_simp
  have hK : C₀ * (ν / (2 * C₀)) ≤ ν / 2 := le_of_eq hKeq
  have hρK : c * ν < ν / (2 * C₀) := by
    have := mul_lt_mul_of_pos_right hclt hν
    rwa [one_div, inv_mul_eq_div] at this
  exact NSFormalization.Paper1.critical_norm_bound hν.le hC₀.le (mul_nonneg hc0 hν.le) hρK hK
    hy hy0 hynonneg hN hN0 hNbound hb hdE hdN henergy

end NSFormalization.Section4.R43
