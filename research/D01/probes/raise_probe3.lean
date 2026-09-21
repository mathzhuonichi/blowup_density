import NSFormalization.Section4.D01.LerayLowering

open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source NSFormalization.Source.RealSobolev
open NSFormalization.Section4.D01.Leray (angularOrderLowering_coeFn')
open scoped ENNReal ComplexConjugate

namespace NSFormalization.Section4.D01
noncomputable section

/-- The pointwise witness: `(1+‖ξ‖²)^{1/2}·h(ξ)` is square integrable. -/
def RaisableWitness (h : FourierData) : Prop :=
  MemLp (fun ξ => sobolevBesselWeight 1 ξ • (h : Space → ℂ) ξ) 2 volume

-- membership of the raised element
theorem raise_mem {s : ℝ} (a : RealSobolevHilbert s) (hg : RaisableWitness (a : FourierData)) :
    (hg.toLp _) ∈ realSubspace (s+1) := by
  rw [mem_realSubspace_iff]
  apply Lp.ext
  have hqmp : Measure.QuasiMeasurePreserving (fun ξ : Space => -ξ) volume volume :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving
  have hHeq : (realSymmetry (a : FourierData) : Space → ℂ) =ᵐ[volume] ((a : FourierData) : Space → ℂ) := by
    rw [(mem_realSubspace_iff s _).mp (SetLike.coe_mem a)]
  filter_upwards [realSymmetry_ae (hg.toLp _), hg.coeFn_toLp, hqmp.ae hg.coeFn_toLp,
    realSymmetry_ae (a : FourierData), hHeq] with ξ eSg eg egN eSh eHeq
  rw [eSg, egN, eg, smul_eq_mul, map_mul, smul_eq_mul]
  have hconjh : (starRingEnd ℂ) (((a : FourierData) : Space→ℂ) (-ξ)) = ((a : FourierData) : Space→ℂ) ξ := by
    rw [← eSh, eHeq]
  rw [hconjh]
  have hw : (starRingEnd ℂ) (sobolevBesselWeight 1 (-ξ)) = sobolevBesselWeight 1 ξ := by
    simp [sobolevBesselWeight, norm_neg]
  rw [hw]

/-- Raise a real Sobolev datum element by one order, given the L² witness. -/
def raiseHilbert {s : ℝ} (a : RealSobolevHilbert s) (hg : RaisableWitness (a : FourierData)) :
    RealSobolevHilbert (s+1) :=
  ⟨hg.toLp _, raise_mem a hg⟩

theorem coe_raiseHilbert {s : ℝ} (a : RealSobolevHilbert s) (hg : RaisableWitness (a : FourierData)) :
    ((raiseHilbert a hg : RealSobolevHilbert (s+1)) : FourierData) = hg.toLp _ := rfl

theorem angularRealization_raiseHilbert {s : ℝ} (a : RealSobolevHilbert s)
    (hg : RaisableWitness (a : FourierData)) :
    angularRealization (s+1) ((raiseHilbert a hg : RealSobolevHilbert (s+1)) : FourierData) =
      angularRealization s (a : FourierData) := by
  rw [coe_raiseHilbert]
  have hlow : angularOrderLowering (s+1) s (by linarith) (hg.toLp _) = (a : FourierData) := by
    apply Lp.ext
    filter_upwards [angularOrderLowering_coeFn' (s+1) s (by linarith) (hg.toLp _), hg.coeFn_toLp]
      with ξ e1 e2
    rw [e1, e2, smul_smul]
    have hmul : sobolevBesselWeight (s-(s+1)) ξ * sobolevBesselWeight 1 ξ = 1 := by
      have := congrFun (sobolevBesselWeight_mul (s-(s+1)) 1) ξ
      simp only [Pi.mul_apply] at this
      rw [this]; norm_num [sobolevBesselWeight]
    rw [hmul, one_smul]
  rw [← angularRealization_orderLowering (s+1) s (by linarith) (hg.toLp _), hlow]

/-- **Induction step (raising with a witness).** -/
theorem isSobolevDatum_raise {s : ℝ} {z : Space → Space} {A : RealVectorSobolev s}
    (hA : IsSobolevDatum s z A)
    (hg : ∀ i : Fin 3, RaisableWitness ((A i : FourierData))) :
    IsSobolevDatum (s+1) z (WithLp.toLp 2 (fun i => raiseHilbert (A i) (hg i))) := by
  intro i ψ
  have : ((WithLp.toLp 2 (fun i => raiseHilbert (A i) (hg i)) : RealVectorSobolev (s+1)) i
      : FourierData) = ((raiseHilbert (A i) (hg i) : RealSobolevHilbert (s+1)) : FourierData) := rfl
  rw [this, angularRealization_raiseHilbert (A i) (hg i)]
  exact hA i ψ

end
end NSFormalization.Section4.D01
