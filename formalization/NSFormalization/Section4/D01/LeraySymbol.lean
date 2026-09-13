import Formal.R3LerayFrequencySymbol
import NSFormalization.Section4.A02.SolutionClass

/-!
# The Leray complement fiber symbol `(I−P)(ξ) = ξξᵀ/|ξ|²` (D01 unit P2, piece (d), S-level)

`research/D01/P2_SPLIT.md`, sub-lemma **(d)**.  This module proves the *algebraic*
facts of the frequency-fiber multiplier that carries the Leray complement `(I−P)`
of eq:Rpressure `∇p = (I−P)(f − ∇·(u⊗u))` (`research/D01/ATTEMPTS_L9C.md`, gap (iv)).

At a fixed real frequency `ξ : Space = EuclideanSpace ℝ (Fin 3)`, the whole-space
angular Leray decomposition splits `Space` into the solenoidal (transverse) plane
`(ℝ ∙ ξ)ᗮ` and the longitudinal (gradient) line `ℝ ∙ ξ`.  HeliCorgi already carries
the solenoidal fiber projection `P(ξ) := MNS2.r3LeraySymbol ξ = ((ℝ ∙ ξ)ᗮ).starProjection`
(`vendor/HeliCorgi/Formal/R3LerayFrequencySymbol.lean`, real, angular convention, on
`EuclideanSpace ℝ (Fin 3)`), with idempotence, norm ≤ 1 and the explicit formula
`P(ξ)v = v − (⟨ξ,v⟩/‖ξ‖²)ξ` all proved.  This module adds its orthogonal complement

  `complementSymbol ξ := (ℝ ∙ ξ).starProjection`,  `complementSymbol ξ v = (⟨ξ,v⟩/‖ξ‖²)ξ`,

which is the `(I−P)` multiplier `ξξᵀ/|ξ|²`, and records the four properties the
`H^m` boundedness step (piece (d) proper) consumes: it is a **projection**
(idempotent), of **operator norm ≤ 1**, **real** (a `→L[ℝ]` map, i.e. real matrix
entries), and **even** in `ξ`.  Real + even is exactly what makes the multiplier
preserve the Hermitian symmetry `Â(−ξ) = conj Â(ξ)` characterizing the Fourier
transforms of *real* fields — so `(I−P)` maps real `L²` fields to real `L²` fields,
the reality bridge sub-lemma (a) needs.

At `ξ = 0` there is no longitudinal direction: `ℝ ∙ 0 = ⊥` and `Submodule.starProjection_bot`
makes `complementSymbol 0 = 0` (the whole zero mode is assigned to the solenoidal part,
matching upstream's `MNS2.r3LeraySymbol_zero = id`).  `{0}` is Lebesgue-null in `Space`, so an
`L²`/`Lᵖ` Fourier multiplier does not see the choice; both conventions define the same operator.

This module is symbol-level algebra only.  Turning `complementSymbol` into a bounded
operator on `RealVectorSobolev m` (piece (d) proper — the worked template is HeliCorgi's
operator-valued `L²` multiplier `R3LerayPointwiseL2.lean` / `ContinuousLinearMap.holderL`,
see `P2_SPLIT.md` SL3), and the distributional↔classical identification (piece (e)), are
the M pieces of `P2_SPLIT.md`; nothing here touches `RealVectorSobolev`, the Fourier
transform, or `pressureGradient`.

No `sorry`, no `axiom`; `#print axioms` is standard (`research/D01/axioms_p2.lean`).
-/

noncomputable section

namespace NSFormalization.Section4.D01.Leray

open scoped RealInnerProductSpace
open NavierStokes.ProblemStatement (Space)

/-- **The Leray complement fiber symbol** at frequency `ξ`: the orthogonal projection
of `Space` onto the longitudinal line `ℝ ∙ ξ`.  This is the `(I−P)` Fourier multiplier
`ξξᵀ/|ξ|²`; HeliCorgi's `MNS2.r3LeraySymbol ξ` is the complementary solenoidal
projection `P(ξ)` onto `(ℝ ∙ ξ)ᗮ`. -/
def complementSymbol (ξ : Space) : Space →L[ℝ] Space :=
  (ℝ ∙ ξ).starProjection

/-- The explicit rank-one formula `(I−P)(ξ)v = (⟨ξ,v⟩/‖ξ‖²) ξ`, i.e. the matrix
`ξξᵀ/‖ξ‖²`.  Direct from `Submodule.starProjection_singleton`. -/
theorem complementSymbol_apply (ξ v : Space) :
    complementSymbol ξ v = (inner ℝ ξ v / ‖ξ‖ ^ 2) • ξ := by
  simpa [complementSymbol] using (Submodule.starProjection_singleton (𝕜 := ℝ) (v := ξ) v)

/-- Every output of the complement symbol is longitudinal (a gradient direction). -/
theorem complementSymbol_apply_mem (ξ v : Space) : complementSymbol ξ v ∈ ℝ ∙ ξ := by
  simp only [complementSymbol]
  exact Submodule.starProjection_apply_mem (ℝ ∙ ξ) v

/-- The complement symbol fixes every longitudinal vector. -/
theorem complementSymbol_fixed_of_mem (ξ v : Space) (hv : v ∈ ℝ ∙ ξ) :
    complementSymbol ξ v = v := by
  simpa [complementSymbol] using
    (Submodule.starProjection_eq_self_iff (K := ℝ ∙ ξ) (v := v)).2 hv

/-- **Projection.**  The complement symbol is idempotent at every frequency. -/
theorem complementSymbol_idempotent (ξ v : Space) :
    complementSymbol ξ (complementSymbol ξ v) = complementSymbol ξ v :=
  complementSymbol_fixed_of_mem ξ (complementSymbol ξ v) (complementSymbol_apply_mem ξ v)

/-- **Operator norm ≤ 1** (pointwise contraction form): orthogonal projection is
norm non-increasing at each frequency. -/
theorem norm_complementSymbol_le (ξ v : Space) :
    ‖complementSymbol ξ v‖ ≤ ‖v‖ := by
  simpa [complementSymbol] using (ℝ ∙ ξ).norm_starProjection_apply_le v

/-- **Operator norm ≤ 1** (bundled form): the complement symbol has operator norm at
most one at every frequency. -/
theorem complementSymbol_opNorm_le_one (ξ : Space) :
    ‖complementSymbol ξ‖ ≤ 1 := by
  simpa [complementSymbol] using (ℝ ∙ ξ).starProjection_norm_le

/-- **Complementarity with HeliCorgi's solenoidal symbol** (the reused declaration):
`P(ξ) + (I−P)(ξ) = I` pointwise.  Both explicit formulas coincide with
`v − (⟨ξ,v⟩/‖ξ‖²)ξ` and `(⟨ξ,v⟩/‖ξ‖²)ξ`. -/
theorem leraySymbol_add_complementSymbol (ξ v : Space) :
    MNS2.r3LeraySymbol ξ v + complementSymbol ξ v = v := by
  rw [MNS2.r3LeraySymbol_apply, complementSymbol_apply]; abel

/-- The solenoidal symbol is `I` minus the complement symbol. -/
theorem leraySymbol_eq_sub (ξ v : Space) :
    MNS2.r3LeraySymbol ξ v = v - complementSymbol ξ v := by
  rw [MNS2.r3LeraySymbol_apply, complementSymbol_apply]

/-- The complement symbol is `I` minus HeliCorgi's solenoidal symbol. -/
theorem complementSymbol_eq_sub (ξ v : Space) :
    complementSymbol ξ v = v - MNS2.r3LeraySymbol ξ v := by
  rw [MNS2.r3LeraySymbol_apply, complementSymbol_apply]; abel

/-- **Even in `ξ`.**  `(I−P)(−ξ) = (I−P)(ξ)` — the longitudinal line `ℝ ∙ ξ` does not
see the sign of `ξ`.  Together with real-linearity (`complementSymbol ξ : _ →L[ℝ] _`,
i.e. real matrix entries) this is what makes the multiplier preserve the reality
subspace of `L²`. -/
theorem complementSymbol_neg (ξ : Space) :
    complementSymbol (-ξ) = complementSymbol ξ := by
  ext v
  simp only [complementSymbol_apply, inner_neg_left, norm_neg, neg_div, neg_smul,
    smul_neg, neg_neg]

/-- The complement symbol fixes the longitudinal frequency vector itself. -/
@[simp]
theorem complementSymbol_self (ξ : Space) : complementSymbol ξ ξ = ξ :=
  complementSymbol_fixed_of_mem ξ ξ (Submodule.mem_span_singleton_self ξ)

/-! ## Fibre facts: the complement kills transverse vectors and fixes longitudinal ones

These are the pointwise-fibre content of "`(I−P)` kills a solenoidal field" (P2 split
sub-lemma SL4) and "`(I−P)` fixes a gradient" (SL5).  Once `(I−P)` is realized as a
*symbol* multiplier (route B of `P2_SPLIT.md`), neither needs the closed solenoidal
subspace (D01 unit L3): both are one line from the explicit formula. -/

/-- **Kills transverse vectors.**  `(I−P)(ξ)` annihilates every vector orthogonal to `ξ`,
i.e. every divergence-free (solenoidal) Fourier direction. -/
theorem complementSymbol_eq_zero_of_inner_eq_zero (ξ v : Space)
    (h : inner ℝ ξ v = 0) : complementSymbol ξ v = 0 := by
  rw [complementSymbol_apply, h, zero_div, zero_smul]

/-- **Fixes longitudinal vectors.**  `(I−P)(ξ)` fixes every real multiple of `ξ`, i.e.
every gradient (curl-free) Fourier direction. -/
theorem complementSymbol_smul_self (c : ℝ) (ξ : Space) :
    complementSymbol ξ (c • ξ) = c • ξ :=
  complementSymbol_fixed_of_mem ξ (c • ξ)
    (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self ξ))

/-- **0-homogeneity.**  Rescaling the frequency by a nonzero factor leaves the symbol
unchanged: `(I−P)(c·ξ) = (I−P)(ξ)` for `c ≠ 0`.  This is why the cycles↔angular frequency
dilation is invisible to the multiplier (and the radial Sobolev weight, being scalar,
commutes with it as well): route A and route B build the *same* operator.
`complementSymbol_neg` is the `c = −1` case. -/
theorem complementSymbol_smul (c : ℝ) (hc : c ≠ 0) (ξ : Space) :
    complementSymbol (c • ξ) = complementSymbol ξ := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · rw [smul_zero]
  · ext v
    rw [complementSymbol_apply, complementSymbol_apply, real_inner_smul_left,
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, smul_smul]
    have hN : ‖ξ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hξ)
    have hcoeff : c * inner ℝ ξ v / (c ^ 2 * ‖ξ‖ ^ 2) * c = inner ℝ ξ v / ‖ξ‖ ^ 2 := by
      field_simp
    rw [hcoeff]

end NSFormalization.Section4.D01.Leray
