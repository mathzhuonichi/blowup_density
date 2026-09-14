import NSFormalization.Section4.D01.LerayLowering

open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source NSFormalization.Source.RealSobolev
open scoped ENNReal ComplexConjugate

namespace Probe
noncomputable section

-- Can I build a RealSobolevHilbert element from a FourierData + membership?
example (s : ℝ) (g : FourierData) (hg : g ∈ realSubspace s) : RealSobolevHilbert s := ⟨g, hg⟩
example (s : ℝ) (g : FourierData) (hg : g ∈ realSubspace s) :
    ((⟨g, hg⟩ : RealSobolevHilbert s) : FourierData) = g := rfl

-- realSubspace independent of order (defeq)?
example (s : ℝ) (g : FourierData) (hg : g ∈ realSubspace s) : g ∈ realSubspace (s+1) := hg

-- The raising: given h : FourierData and a MemLp witness for (w1 • h), build g and show lowering gives h.
variable (s : ℝ) (h : FourierData)
  (hg : MemLp (fun ξ => sobolevBesselWeight 1 ξ • (h : Space → ℂ) ξ) 2 volume)

-- lowering computation
example : angularOrderLowering (s+1) s (by linarith) (hg.toLp _) = h := by
  apply Lp.ext
  have hcoe := hg.coeFn_toLp
  filter_upwards [NSFormalization.Section4.D01.Leray.angularOrderLowering_coeFn' (s+1) s (by linarith) (hg.toLp _), hcoe]
    with ξ e1 e2
  rw [e1, e2]
  -- goal: sobolevBesselWeight (s - (s+1)) ξ • (sobolevBesselWeight 1 ξ • h ξ) = h ξ
  have : sobolevBesselWeight (s - (s+1)) ξ • (sobolevBesselWeight 1 ξ • (h : Space→ℂ) ξ)
      = (sobolevBesselWeight (s-(s+1)) ξ * sobolevBesselWeight 1 ξ) • (h : Space→ℂ) ξ := by
    rw [smul_smul]
  rw [this]
  have hmul : sobolevBesselWeight (s-(s+1)) ξ * sobolevBesselWeight 1 ξ = 1 := by
    have := congrFun (sobolevBesselWeight_mul (s-(s+1)) 1) ξ
    simp only [Pi.mul_apply] at this
    rw [this]
    norm_num [sobolevBesselWeight]
  rw [hmul, one_smul]

end
end Probe
