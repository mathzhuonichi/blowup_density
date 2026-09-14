import NSFormalization.Section4.R43.Pieces

/-!
Reviewer 159 negative probes **B** — these all COMPILE, and each one *proves*
that a mutated / weakened form of a `Section4/R43/Pieces.lean` statement is
false (or, for `weaker_radius`, that a proposed "mutation" is in fact a
weakening and therefore not a valid negative check).
-/

open Set
open scoped ENNReal

namespace Rev159

/-- **B1.**  The G6 mutation `x ^ (2:ℕ) = x ^ (3:ℝ)` is not merely unprovable by
the original script: it is false, at `x = 2`. -/
theorem g6_rpow_three_false : (2 : ℝ≥0∞) ^ (2 : ℕ) ≠ (2 : ℝ≥0∞) ^ (3 : ℝ) := by
  rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
  norm_num

/-- **B2.**  The `ν`-freeness of the second shrinking is load-bearing: a radius
`c` chosen before `ν` can never satisfy a threshold that still carries `ν`
(`C₁·Cemb·c·ν ≤ 1/4` for every `ν > 0`).  So `exists_critical_radius`'s
`C₁ * Cemb * c ≤ 1/4` — from which `C₁·Cemb·c·ν ≤ ν/4` follows for each `ν` —
is the only spelling that can hold with one universal `c`. -/
theorem no_nu_carrying_radius {C₀ C₁ Cemb : ℝ}
    (hC₁ : 0 < C₁) (hCemb : 0 < Cemb) :
    ¬ ∃ c : ℝ, 0 < c ∧ c < 1 / (4 * C₀) ∧ ∀ ν : ℝ, 0 < ν → C₁ * Cemb * c * ν ≤ 1 / 4 := by
  rintro ⟨c, hc, -, h⟩
  have hp : 0 < C₁ * Cemb * c := by positivity
  have hν := h (1 / (C₁ * Cemb * c)) (by positivity)
  rw [mul_one_div, div_self (ne_of_gt hp)] at hν
  linarith

/-- **B3.**  The "mutation" `c < 1/(2C₀)` with `C₁·Cemb·c ≤ 1/2` is a strict
WEAKENING of `exists_critical_radius`, hence still provable (from the original).
Recorded so that it is not mistaken for a valid negative check. -/
theorem weaker_radius {C₀ C₁ Cemb : ℝ}
    (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hCemb : 0 < Cemb) :
    ∃ c : ℝ, 0 < c ∧ c < 1 / (2 * C₀) ∧ C₁ * Cemb * c ≤ 1 / 2 := by
  obtain ⟨c, hc, h1, h2⟩ :=
    NSFormalization.Section4.R43.exists_critical_radius hC₀ hC₁ hCemb
  refine ⟨c, hc, lt_of_lt_of_le h1 ?_, by linarith⟩
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- **B4.**  `criticalL3_gate_real`'s `hν : 0 < ν` is load-bearing: the same
statement without it is false (`C₁ = Cemb = 1`, `c = 0`, `ν = -1`,
`y = L3 = 0`). -/
theorem gate_needs_nu_pos :
    ¬ ∀ (C₁ Cemb c ν y L3 : ℝ), 0 ≤ C₁ → 0 ≤ Cemb →
        y ≤ c * ν → L3 ≤ Cemb * y → C₁ * Cemb * c ≤ 1 / 4 → C₁ * L3 ≤ ν / 4 := by
  intro h
  have := h 1 1 0 (-1) 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  norm_num at this

/-- **B5.**  `criticalNormBound_radius`'s `hy0 : y 0 = 0` is load-bearing, i.e.
the lemma really is the paper's `a = 0` clause and NOT the general clause.  With
`hy0` deleted the statement is false: `T = ν = C₀ = 1`, `c = 1/4`, `y ≡ 1/2`,
`E' = z = b = N ≡ 0` satisfies every remaining hypothesis (eq:Rcritical1 reads
`0 ≤ 0`) yet `y 0 = 1/2 > 1/4 = c·ν`.  The paper's general clause concludes
`y(t) ≤ y(0) + ∫₀ᵗ b` (`04-whole-space.tex:102`), not `y(t) ≤ cν`. -/
theorem bootstrap_needs_zero_datum :
    ¬ ∀ (T ν C₀ c : ℝ) (y E' z b N : ℝ → ℝ), 0 < C₀ → 0 < ν → 0 ≤ c →
        c < 1 / (2 * C₀) → Continuous y → (∀ t ∈ Icc 0 T, 0 ≤ y t) →
        ContinuousOn N (Icc 0 T) → N 0 = 0 → (∀ t ∈ Icc 0 T, N t ≤ c * ν) →
        (∀ t ∈ Ioo 0 T, 0 ≤ b t) →
        (∀ t ∈ Ioo 0 T, HasDerivAt (fun x => (y x) ^ 2) (E' t) t) →
        (∀ t ∈ Ioo 0 T, HasDerivAt N (b t) t) →
        (∀ t ∈ Ioo 0 T, E' t / 2 + (ν - C₀ * y t) * (z t) ^ 2 ≤ b t * y t) →
        ∀ t ∈ Icc 0 T, y t ≤ c * ν := by
  intro h
  have hbad := h 1 1 1 (1 / 4) (fun _ => 1 / 2) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ => 0)
    one_pos one_pos (by norm_num) (by norm_num) continuous_const
    (fun _ _ => by norm_num) continuousOn_const rfl (fun _ _ => by norm_num)
    (fun _ _ => le_rfl)
    (fun _ _ => hasDerivAt_const _ _)
    (fun _ _ => hasDerivAt_const _ 0)
    (fun _ _ => by norm_num)
    0 ⟨le_rfl, by norm_num⟩
  norm_num at hbad

end Rev159
