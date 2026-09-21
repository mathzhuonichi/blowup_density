import Mathlib.MeasureTheory.Function.Holder
import Formal.R3StokesL2Operator

namespace MNS2

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

abbrev R3L2ScalarAux := Lp (α := R3) ℂ 2 (volume : Measure R3)

def r3L2ScalarMultiplierAux
    (m : Lp ℂ ⊤ (volume : Measure R3)) :
    R3L2ScalarAux →L[ℂ] R3L2ScalarAux := by
  letI : ENNReal.HolderTriple (⊤ : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞) := ⟨by simp⟩
  let L : R3L2ScalarAux →ₗ[ℂ] R3L2ScalarAux :=
    { toFun := fun f => (m • f : R3L2ScalarAux)
      map_add' := by intro f g; exact Lp.add_smul m f g
      map_smul' := by intro c f; exact (Lp.smul_comm c m f).symm }
  exact L.mkContinuous ‖m‖ (fun f => Lp.norm_smul_le m f)

theorem r3L2ScalarMultiplierAux_ae
    (m : Lp ℂ ⊤ (volume : Measure R3)) (f : R3L2ScalarAux) :
    r3L2ScalarMultiplierAux m f =ᵐ[volume] fun ξ => m ξ * f ξ := by
  letI : ENNReal.HolderTriple (⊤ : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞) := ⟨by simp⟩
  change ((m • f : R3L2ScalarAux) : R3 → ℂ) =ᵐ[volume] fun ξ => m ξ * f ξ
  filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) m f] with ξ hξ
  simpa [smul_eq_mul] using hξ

end

end MNS2
