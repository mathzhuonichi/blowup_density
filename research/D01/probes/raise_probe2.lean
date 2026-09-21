import NSFormalization.Section4.D01.LerayLowering

open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source NSFormalization.Source.RealSobolev
open NSFormalization.Section4.D01.Leray (angularOrderLowering_coeFn')
open scoped ENNReal ComplexConjugate

namespace Probe
noncomputable section

variable (s : ℝ) (h : FourierData)
  (hg : MemLp (fun ξ => sobolevBesselWeight 1 ξ • (h : Space → ℂ) ξ) 2 volume)

-- weight is even and real
example (ξ : Space) : sobolevBesselWeight 1 (-ξ) = sobolevBesselWeight 1 ξ := by
  simp [sobolevBesselWeight, norm_neg]
example (ξ : Space) : (starRingEnd ℂ) (sobolevBesselWeight 1 ξ) = sobolevBesselWeight 1 ξ := by
  simp [sobolevBesselWeight]

-- REALITY PRESERVATION
example (hh : realSymmetry h = h) : realSymmetry (hg.toLp _) = hg.toLp _ := by
  apply Lp.ext
  have hqmp : Measure.QuasiMeasurePreserving (fun ξ : Space => -ξ) volume volume :=
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving
  have hcoe := hg.coeFn_toLp
  have hcoeNeg := hqmp.ae hg.coeFn_toLp
  have hSymH := realSymmetry_ae h
  have hHeq : (realSymmetry h : Space → ℂ) =ᵐ[volume] (h : Space → ℂ) := by rw [hh]
  filter_upwards [realSymmetry_ae (hg.toLp _), hcoe, hcoeNeg, hSymH, hHeq]
    with ξ eSg eg egN eSh eHeq
  -- eSg : realSymmetry g ξ = conj (g (-ξ))
  -- eg  : g ξ = w1 ξ • h ξ
  -- egN : g (-ξ) = w1 (-ξ) • h (-ξ)
  -- eSh : realSymmetry h ξ = conj (h (-ξ))
  -- eHeq: realSymmetry h ξ = h ξ
  rw [eSg, egN, eg]
  have hconjh : (starRingEnd ℂ) ((h : Space→ℂ) (-ξ)) = (h : Space→ℂ) ξ := by
    rw [← eSh, eHeq]
  rw [smul_eq_mul, map_mul, smul_eq_mul, hconjh]
  have hw : (starRingEnd ℂ) (sobolevBesselWeight 1 (-ξ)) = sobolevBesselWeight 1 ξ := by
    simp [sobolevBesselWeight, norm_neg]
  rw [hw]

-- REALIZATION IDENTITY
example (hh : realSymmetry h = h) :
    angularRealization (s+1) (hg.toLp _) = angularRealization s h := by
  have hlow : angularOrderLowering (s+1) s (by linarith) (hg.toLp _) = h := by
    apply Lp.ext
    filter_upwards [angularOrderLowering_coeFn' (s+1) s (by linarith) (hg.toLp _), hg.coeFn_toLp]
      with ξ e1 e2
    rw [e1, e2, smul_smul]
    have hmul : sobolevBesselWeight (s-(s+1)) ξ * sobolevBesselWeight 1 ξ = 1 := by
      have := congrFun (sobolevBesselWeight_mul (s-(s+1)) 1) ξ
      simp only [Pi.mul_apply] at this
      rw [this]; norm_num [sobolevBesselWeight]
    rw [hmul, one_smul]
  calc angularRealization (s+1) (hg.toLp _)
      = angularRealization s (angularOrderLowering (s+1) s (by linarith) (hg.toLp _)) :=
        (angularRealization_orderLowering (s+1) s (by linarith) (hg.toLp _)).symm
    _ = angularRealization s h := by rw [hlow]

end
end Probe
