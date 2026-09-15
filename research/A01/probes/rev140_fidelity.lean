-- Reviewer probe (lane 140 review, REVIEW_EULER_PAIRING.md), preserved verbatim; compiles on this branch.
import NSFormalization.Section4.A01.EulerPairing
import Euler.MeanSmoothRepresentative
import Euler.MeanSpatialDerivative
import Euler.MeanOrbitSmoothL2Field

open NSFormalization.Section4.A01 NSFormalization.Section4.D01
open MeasureTheory NavierStokes.ProblemStatement
open EulerMeanSmoothRepresentative EulerLpTranslation
open scoped LineDeriv SchwartzMap

/-! ### F1. `HasWeakDerivsL2 z 1` unfolds to exactly the clause E2 concludes -/
example (z : Space → Space) :
    HasWeakDerivsL2 z 1 ↔
      (MemLp z 2 volume ∧ ∀ j : Fin 3, ∃ w : Space → Space,
        MemLp w 2 volume ∧
        (∀ (i : Fin 3) (ψ : SchwartzMap Space ℂ),
          ∫ x, ψ x * ((w x i : ℝ) : ℂ)
            = ∫ x, (-∂_{coordinateVector j} ψ) x * ((z x i : ℝ) : ℂ))) := Iff.rfl

/-! ### F2. E2's conclusion IS the pairing clause: build `HasWeakDerivsL2` from E2 alone,
by the anonymous constructor (no rewriting, no `convert`). -/
example (z : EulerMeanSolenoidal.L2) (W : Fin 3 → EulerMeanSolenoidal.L2)
    (h : ∀ j : Fin 3,
      HasDerivAt (fun t : ℝ => EulerMeanSolenoidal.translation (t • coordinateVector j) z) (W j) 0) :
    HasWeakDerivsL2 (⇑z) 1 :=
  ⟨Lp.memLp z, fun j => ⟨⇑(W j), Lp.memLp (W j),
    fun i ψ => weakDeriv_pairing_of_translation_hasDerivAt j (h j) i ψ⟩⟩

/-! ### F3. SIGN TEST.  On a genuinely smooth `L²` field, E2's `w` is the **classical**
`+∂ⱼz` (`fderiv … (coordinateVector j)`), and the identity it yields is the textbook
`∫ψ·∂ⱼz = ∫(−∂ⱼψ)·z`.  Proved twice: once from E2 (lane 140), once from D01's independently
written smooth-case pairing `smoothField_weakDeriv_pairing` (lane 132). -/

/-- Route A: from lane 140's E2. -/
theorem sign_test_from_E2 (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) (j i : Fin 3)
    (ψ : SchwartzMap Space ℂ) :
    ∫ x, ψ x * ((fderiv ℝ (representative u hu) x (coordinateVector j) i : ℝ) : ℂ)
      = ∫ x, (-∂_{coordinateVector j} ψ) x * ((representative u hu x i : ℝ) : ℂ) := by
  have hE2 := weakDeriv_pairing_of_translation_hasDerivAt j
    (orbitDerivative_hasDerivAt u hu (coordinateVector j)) i ψ
  have hL : ∫ x, ψ x * ((orbitDerivative u (coordinateVector j) x i : ℝ) : ℂ)
      = ∫ x, ψ x * ((fderiv ℝ (representative u hu) x (coordinateVector j) i : ℝ) : ℂ) := by
    refine integral_congr_ae ?_
    filter_upwards [orbitDerivative_ae_fderiv u hu (coordinateVector j)] with x hx
    rw [hx]
  have hR : ∫ x, (-∂_{coordinateVector j} ψ) x * ((u x i : ℝ) : ℂ)
      = ∫ x, (-∂_{coordinateVector j} ψ) x * ((representative u hu x i : ℝ) : ℂ) := by
    refine integral_congr_ae ?_
    filter_upwards [representative_ae u hu] with x hx
    rw [hx]
  rw [← hL, ← hR]; exact hE2

/-- Route B: from lane 132's smooth-case pairing, via `smoothL2Field`. -/
theorem sign_test_from_D01 (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) (j i : Fin 3)
    (ψ : SchwartzMap Space ℂ) :
    ∫ x, ψ x * ((fderiv ℝ (representative u hu) x (coordinateVector j) i : ℝ) : ℂ)
      = ∫ x, (-∂_{coordinateVector j} ψ) x * ((representative u hu x i : ℝ) : ℂ) :=
  smoothField_weakDeriv_pairing (EulerMeanSmoothRepresentative.smoothL2Field u hu) j i ψ

/-! ### F4. NEGATIVE CHECK.  Drop E2's `HasDerivAt` hypothesis and the statement collapses:
every `L²` field would pair to zero against every Schwartz test function. -/
set_option autoImplicit false in
theorem E2_hypothesis_is_load_bearing
    (H : ∀ (j : Fin 3) (z w : EulerMeanSolenoidal.L2) (i : Fin 3) (ψ : SchwartzMap Space ℂ),
      ∫ x, ψ x * ((w x i : ℝ) : ℂ)
        = ∫ x, (-∂_{coordinateVector j} ψ) x * ((z x i : ℝ) : ℂ)) :
    ∀ (w : EulerMeanSolenoidal.L2) (i : Fin 3) (ψ : SchwartzMap Space ℂ),
      ∫ x, ψ x * ((w x i : ℝ) : ℂ) = 0 := by
  intro w i ψ
  rw [H 0 0 w i ψ]
  have : ∫ x, (-∂_{coordinateVector 0} ψ) x * (((0 : EulerMeanSolenoidal.L2) x i : ℝ) : ℂ)
      = ∫ _x : Space, (0 : ℂ) := by
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_zero Space 2 (volume : Measure Space)] with x hx
    rw [hx]; simp
  rw [this, integral_zero]
