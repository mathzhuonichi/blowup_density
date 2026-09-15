import NSFormalization.Section4.A01.GronwallEndpoint

noncomputable section
namespace NSFormalization.Section4.A01

open Set MeasureTheory
open NSFormalization.Section4.D01
open NSFormalization.Section4.A04
open NSFormalization.Section4.A02
  (SpaceTimeField SpatialField ClassicalSolutionR initialClassR)
open NavierStokes.ProblemStatement (Space)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerCylinderSobolev

set_option autoImplicit false

/-- Negative review mutation: widening the proved full-horizon output from
`Ico 0 T` to `Icc 0 T` requires the unavailable strict inequality at `t = T`. -/
theorem rev179_mutated_closed_endpoint
    {ν T R : ℝ} {a : SpatialField} {f : SpaceTimeField} {q m : ℕ}
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f)
    (w : ClassicalSolutionR ν a f T) (hpath : HasSmoothSobolevPath T w.velocity)
    (hT : 0 < T)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) T, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t)) (hq : 4 ≤ q)
    (hslice : ∀ t : Icc (0 : ℝ) T,
      (fun x : Space => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t))
    (hR : ‖u‖ ≤ R) (hm : 3 ≤ m) :
    ∀ t ∈ Icc (0 : ℝ) T,
      sobolevNormAt (m : ℝ) w.velocity t ≤
        (sobolevNormAt (m : ℝ) w.velocity 0 +
            (A04.forceSobolevENormL1 (m : ℝ) f).toReal) *
          Real.exp (A04.Cgron m ν * (256 * R ^ 2 * T)) := by
  have hbase := highOrder_bddAbove_of_kbnd_Ico_full hν ha hf w hpath hT
    u U hu hU hq hslice hR hm
  intro t ht
  exact hbase t ⟨ht.1, ht.2⟩

end NSFormalization.Section4.A01
