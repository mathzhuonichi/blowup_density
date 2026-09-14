-- Reviewer probe from lane-125 review (research/D01/REVIEW_FINITE_ORDER.md), preserved verbatim.
-- Original reviewer path: /tmp/rev125/p3_nonvac.lean . Compiles under `lake env lean` from verification/.
-- Exploratory probe (not a registered module): shows row D-b and the Schwartz-duality removal
-- of the smoothness hypothesis are reachable from in-tree lemmas.
import NSFormalization.Section4.D01.FiniteOrderDatum

open MeasureTheory NavierStokes.ProblemStatement EulerLpTranslation
open NSFormalization.Paper3 NSFormalization.Source.RealSobolev
open NSFormalization.Section4.D01
open NSFormalization.Section4.D01.Leray (angularOrderLowering_coeFn' isSobolevDatum_lower)
open NSFormalization.Section4.A03 (lowerDatum coe_lowerDatum)

noncomputable section

/-- (b0) A concrete inhabitant of the hypothesis class: the zero smooth `L²` field. -/
def zeroField : SmoothL2Field Space where
  field := fun _ => 0
  smooth := contDiff_const
  integrable n := by
    have : iteratedFDeriv ℝ n (fun _ : Space => (0 : Space)) = 0 := iteratedFDeriv_zero_fun
    rw [this]
    exact MemLp.zero

/-- (b1) **The witness is satisfiable, non-degenerately**: every smooth `L²` field satisfies
`RaisableWitness` for its order-`s` datum, whenever it also has an order-`(s+1)` datum. -/
theorem witness_smooth (m : ℕ) (s : ℝ) (hs1 : s + 1 ≤ (m : ℝ)) (Z : SmoothL2Field Space)
    (i : Fin 3) :
    RaisableWitness
      ((smoothAngularDatum m s (by linarith) Z i : RealSobolevHilbert s) : FourierData) := by
  have hle : s ≤ s + 1 := by linarith
  have hAs : IsSobolevDatum s Z.field (smoothAngularDatum m s (by linarith) Z) :=
    smoothAngularDatum_isSobolevDatum m s (by linarith) Z
  have hlow : IsSobolevDatum s Z.field
      (lowerVectorL (s + 1) s hle (smoothAngularDatum m (s + 1) hs1 Z)) :=
    isSobolevDatum_lower hle (smoothAngularDatum_isSobolevDatum m (s + 1) hs1 Z)
  have heq := isSobolevDatum_unique hAs hlow
  have hcoe : ((smoothAngularDatum m s (by linarith) Z i : RealSobolevHilbert s) : FourierData)
      = angularOrderLowering (s + 1) s hle
        ((smoothAngularDatum m (s + 1) hs1 Z i : RealSobolevHilbert (s + 1)) : FourierData) := by
    rw [heq, lowerVectorL_apply, coe_lowerDatum]
  show MemLp _ 2 volume
  refine (memLp_congr_ae ?_).mp
    (Lp.memLp ((smoothAngularDatum m (s + 1) hs1 Z i : RealSobolevHilbert (s + 1)) : FourierData))
  filter_upwards [angularOrderLowering_coeFn' (s + 1) s hle
    ((smoothAngularDatum m (s + 1) hs1 Z i : RealSobolevHilbert (s + 1)) : FourierData)] with ξ e
  rw [hcoe, e, smul_smul]
  have hmul : sobolevBesselWeight 1 ξ * sobolevBesselWeight (s - (s + 1)) ξ = 1 := by
    have := congrFun (sobolevBesselWeight_mul 1 (s - (s + 1))) ξ
    simp only [Pi.mul_apply] at this
    rw [this]; norm_num [sobolevBesselWeight]
  rw [hmul, one_smul]

/-- (b2) **Running the order-raising step on it, and the uniqueness pin**: the raised order-`s`
smooth datum is *the* order-`(s+1)` smooth datum `smoothAngularDatum m (s+1)`. -/
theorem raise_pins (m : ℕ) (s : ℝ) (hs1 : s + 1 ≤ (m : ℝ)) (Z : SmoothL2Field Space) :
    (WithLp.toLp 2 fun i =>
        raiseHilbert (smoothAngularDatum m s (by linarith) Z i) (witness_smooth m s hs1 Z i))
      = smoothAngularDatum m (s + 1) hs1 Z :=
  isSobolevDatum_unique
    (isSobolevDatum_raise (smoothAngularDatum_isSobolevDatum m s (by linarith) Z)
      (witness_smooth m s hs1 Z))
    (smoothAngularDatum_isSobolevDatum m (s + 1) hs1 Z)

/-- (b3) The raise really does produce an order-`(s+1)` datum of the *same* field. -/
theorem raise_fires (m : ℕ) (s : ℝ) (hs1 : s + 1 ≤ (m : ℝ)) (Z : SmoothL2Field Space) :
    IsSobolevDatum (s + 1) Z.field
      (WithLp.toLp 2 fun i =>
        raiseHilbert (smoothAngularDatum m s (by linarith) Z i) (witness_smooth m s hs1 Z i)) :=
  isSobolevDatum_raise (smoothAngularDatum_isSobolevDatum m s (by linarith) Z)
    (witness_smooth m s hs1 Z)

/-- (b4) Instantiated at a concrete field and concrete orders `s = 1 → 2`. -/
example : IsSobolevDatum ((1 : ℝ) + 1) zeroField.field
    (WithLp.toLp 2 fun i =>
      raiseHilbert (smoothAngularDatum 2 (1 : ℝ) (by norm_num) zeroField i)
        (witness_smooth 2 (1 : ℝ) (by norm_num) zeroField i)) :=
  raise_fires 2 1 (by norm_num) zeroField
