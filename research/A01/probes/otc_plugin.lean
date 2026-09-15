-- Plug-in check: `kbnd_of_sup_bound`'s output has EXACTLY the `hkbnd` shape that
-- `GronwallInstance.highOrder_bddAbove_of_kbnd` consumes (with `v := w.velocity`,
-- `Kbnd := 256*R^2*T₀`).  Everything is taken as hypotheses (no construction of a real
-- cylinder solution), so this certifies the shape match only.
-- Run: cd verification && lake env lean ../research/A01/probes/otc_plugin.lean
import NSFormalization.Section4.A01.OrderTwoCap
import NSFormalization.Section4.A01.GronwallInstance

noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory
open NSFormalization.Section4.A04
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR initialClassR)
open NSFormalization.Section4.D01 (MemForceR)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

example {q : ℕ} {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f) (hf1 : MemL1Hm f)
    (w : ClassicalSolutionR ν a f T) (hpath : HasSmoothSobolevPath T w.velocity)
    {m : ℕ} (hm : 3 ≤ m) {T₀ : ℝ} (hT₀ : 0 < T₀) (hT₀T : T₀ ≤ T)
    -- cylinder ingredients for `kbnd_of_sup_bound`, with `v := w.velocity`:
    (u : C(Icc (0:ℝ) T, SobolevSpace 1 (q+1))) (U : C(Icc (0:ℝ) T, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1:ℝ)) t, sobolevTranslation 1 (q+1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t)) (hq : 4 ≤ q)
    (hslice : ∀ t : Icc (0:ℝ) T, (fun x => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t))
    {R : ℝ} (hR : ‖u‖ ≤ R) :
    ∀ t ∈ Ico (0:ℝ) T₀,
      sobolevNormAt (m : ℝ) w.velocity t ≤
        (sobolevNormAt (m : ℝ) w.velocity 0 + (forceSobolevENormL1 (m : ℝ) f).toReal)
          * Real.exp (A04.Cgron m ν * (256 * R ^ 2 * T₀)) :=
  highOrder_bddAbove_of_kbnd hν ha hf hf1 w hpath hm hT₀ hT₀T
    (kbnd_of_sup_bound u U hu hU hq w.velocity hslice hR
      (continuousOn_sobolevNormAt_velocity w 2) hT₀ hT₀T)

end NSFormalization.Section4.A01
