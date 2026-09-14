-- Reviewer probe from lane-125 review (research/D01/REVIEW_FINITE_ORDER.md), preserved verbatim.
-- Original reviewer path: /tmp/rev125/p10_conv.lean . Compiles under `lake env lean` from verification/.
-- Exploratory probe (not a registered module): shows row D-b and the Schwartz-duality removal
-- of the smoothness hypothesis are reachable from in-tree lemmas.
import NSFormalization.Section4.D01.FiniteOrderDatum

open MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3 NSFormalization.Source.RealSobolev
open NSFormalization.Section4.D01
open NSFormalization.Section4.D01.Leray (angularOrderLowering_coeFn' isSobolevDatum_lower)
open NSFormalization.Section4.A03 (lowerDatum coe_lowerDatum)

noncomputable section

/-- **The converse of `isSobolevDatum_raise`**: if `z` has an order-`s` datum `A` *and* an
order-`(s+1)` datum, then `RaisableWitness (A i)` holds for every `i`.  So the witness is
*equivalent* to the conclusion (modulo datum uniqueness): `isSobolevDatum_raise` is a faithful
translation of "the raised raw datum is in `L²`" into "there is a datum at order `s+1`", and
carries no analysis of its own. -/
theorem raisableWitness_of_higher {s : ℝ} {z : Space → Space} {A : RealVectorSobolev s}
    (hA : IsSobolevDatum s z A) {B : RealVectorSobolev (s + 1)}
    (hB : IsSobolevDatum (s + 1) z B) (i : Fin 3) :
    RaisableWitness ((A i : RealSobolevHilbert s) : FourierData) := by
  have hle : s ≤ s + 1 := by linarith
  have heq := isSobolevDatum_unique hA (isSobolevDatum_lower hle hB)
  have hcoe : ((A i : RealSobolevHilbert s) : FourierData)
      = angularOrderLowering (s + 1) s hle ((B i : RealSobolevHilbert (s + 1)) : FourierData) := by
    rw [heq, lowerVectorL_apply, coe_lowerDatum]
  show MemLp _ 2 volume
  refine (memLp_congr_ae ?_).mp (Lp.memLp ((B i : RealSobolevHilbert (s + 1)) : FourierData))
  filter_upwards [angularOrderLowering_coeFn' (s + 1) s hle
    ((B i : RealSobolevHilbert (s + 1)) : FourierData)] with ξ e
  rw [hcoe, e, smul_smul]
  have hmul : sobolevBesselWeight 1 ξ * sobolevBesselWeight (s - (s + 1)) ξ = 1 := by
    have := congrFun (sobolevBesselWeight_mul 1 (s - (s + 1))) ξ
    simp only [Pi.mul_apply] at this
    rw [this]; norm_num [sobolevBesselWeight]
  rw [hmul, one_smul]
