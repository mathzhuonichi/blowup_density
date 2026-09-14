import NSFormalization.Section4.A01.CarrierWords

/-! Conformance for lane 151 (`Section4/A01/CarrierWords.lean`).

`#print axioms` for every declaration of the module must be exactly
`[propext, Classical.choice, Quot.sound]`.  Non-vacuity: each theorem fires on a cheap concrete
instance (`u = 0`, `U = 0`, `Z = zeroField`).  The order-restricted descent identities and assembly
(`word_descent_ae`, `word_descent_ae_partial`, `hword_jet_of_descent`) were retired in lane 155
(subsumed by `L2Descent`); only the shared descent helpers remain here. -/

noncomputable section

namespace Axioms151

open Set MeasureTheory
open NSFormalization.Section4.A01
open NSFormalization.Section4.D01
open NavierStokes.ProblemStatement (Space coordinateVector)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerCylinderSobolev
open EulerLpTranslation
open scoped ENNReal ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-! ### Axiom audit -/

#print axioms eLpNorm_jet_component_le
#print axioms word_angular_eq_zero
#print axioms word_eq_zero_of_mem_zero
#print axioms locInt_component_lp
#print axioms locInt_component_smooth
#print axioms descent_step_ae
#print axioms wordField
#print axioms wordField_field

/-! ### Non-vacuity -/

-- (b) fires and gives a real ENNReal inequality.
example (z : Space → Space) :
    eLpNorm (fun x => iteratedFDeriv ℝ 2 z x (fun i => coordinateVector (![0, 1] i))) 2 volume
      ≤ eLpNorm (iteratedFDeriv ℝ 2 z) 2 volume :=
  eLpNorm_jet_component_le 2 z ![0, 1]

-- (c) fires on the zero cylinder field (angle-invariant), giving a real equality.
example (q n : ℕ) (hn : n < q) (w : Fin n → Fin 4) :
    word 1 (0 : SobolevSpace 1 q) (Nat.succ_le_of_lt hn) (Fin.cons 0 w) = 0 :=
  word_angular_eq_zero (0 : SobolevSpace 1 q) (fun _ => map_zero _) hn w

-- general angular vanishing fires on the zero field.
example (q n : ℕ) (hn : n ≤ q) (w : Fin n → Fin 4) (hex : ∃ k, w k = 0) :
    word 1 (0 : SobolevSpace 1 q) hn w = 0 :=
  word_eq_zero_of_mem_zero (0 : SobolevSpace 1 q) (fun _ => map_zero _) n hn w hex

-- (The order-restricted assembly `hword_jet_of_descent` that used to be exercised here was retired
-- in lane 155; its full-order successor lives in `L2Descent` and is exercised by
-- `research/A01/probes/rev153_subsumes.lean`.)

end Axioms151
