import Mathlib
import Formal.R3StokesL2Operator

namespace MNS2

noncomputable section

def r3CoordinateLinearAux (i : Fin 3) : R3C →ₗ[ℂ] ℂ where
  toFun v := v i
  map_add' x y := rfl
  map_smul' c x := rfl

def r3CoordinateFiberAux (i : Fin 3) : R3C →L[ℂ] ℂ where
  toFun v := v i
  map_add' x y := rfl
  map_smul' c x := rfl
  cont := by fun_prop

end

end MNS2
