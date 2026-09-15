import NSFormalization.Section4.C01.H2TimeIntegral
import NSFormalization.Section4.A04.Continuation
import NSFormalization.Section4.R43.Pieces

/-! R43 G5: the C01 bound on the open interval at a finite maximal endpoint.
The supplied maximal family is used only at strictly shorter horizons. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace NSFormalization.Section4.R43

theorem maximal_h2TimeIntegral {ν S : ℝ} {a : A02.SpatialField}
    {f u : A02.SpaceTimeField} {p : A02.SpaceTimeScalar}
    (hν : 0 < ν) (_ha : a ∈ A02.initialClassR) (hf : A02.MemForceR f)
    (hu : A02.IsMaximalSolution ν a f u p) (hS : 0 < S)
    (hSL : ENNReal.ofReal S ≤ A02.maximalLifespanR ν a f)
    (hsmall : ∀ t ∈ Ico (0 : ℝ) S,
      ENNReal.ofReal A05.gradientL6Const * C01.criticalL3 (C01.slice u t) ≤
        ENNReal.ofReal (ν / 4)) :
    ∫⁻ t in Ioo (0 : ℝ) S, D01.sobolevENorm 2 (C01.slice u t) ^ (2 : ℝ) ≤
      ENNReal.ofReal (32 * S * C01.energyBudget a f S ^ 2 +
        32 * ν⁻¹ * C01.gradientSq a +
        32 * (ν⁻¹) ^ 2 * ∫ s in (0 : ℝ)..S, C01.l2Sq (C01.slice f s)) := by
  apply C01.lintegral_Ioo_le_of_Ioc
  intro t ht htS
  obtain ⟨r, htr, hrS⟩ := exists_between htS
  have hrL : ENNReal.ofReal r < A02.maximalLifespanR ν a f :=
    ((ENNReal.ofReal_lt_ofReal_iff hS).mpr hrS).trans_le hSL
  obtain ⟨w, hw, _⟩ := hu.2 r (ht.trans htr) hrL
  have hb := C01.h2TimeIntegral_Ioc hν w hf ⟨ht.le, htr⟩ htS.le
    (fun s hs => by simpa only [hw] using hsmall s hs)
  simpa only [hw] using hb

/-- The same canonical H² norm in A04's natural-square vocabulary. -/
theorem maximal_squaredHTwoIntegral_ne_top {ν S : ℝ} {a : A02.SpatialField}
    {f u : A02.SpaceTimeField} {p : A02.SpaceTimeScalar}
    (hν : 0 < ν) (ha : a ∈ A02.initialClassR) (hf : A02.MemForceR f)
    (hu : A02.IsMaximalSolution ν a f u p) (hS : 0 < S)
    (hSL : ENNReal.ofReal S ≤ A02.maximalLifespanR ν a f)
    (hsmall : ∀ t ∈ Ico (0 : ℝ) S,
      ENNReal.ofReal A05.gradientL6Const * C01.criticalL3 (C01.slice u t) ≤
        ENNReal.ofReal (ν / 4)) :
    A04.squaredHTwoIntegral S u ≠ ⊤ := by
  have hb := maximal_h2TimeIntegral hν ha hf hu hS hSL hsmall
  have hn : A04.squaredHTwoIntegral S u =
      ∫⁻ t in Ioo (0 : ℝ) S, D01.sobolevENorm 2 (C01.slice u t) ^ (2 : ℝ) := by
    simp only [A04.squaredHTwoIntegral, enorm_npow_two_eq_rpow_two]
    rfl
  rw [hn]
  exact ne_of_lt (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)

end NSFormalization.Section4.R43
