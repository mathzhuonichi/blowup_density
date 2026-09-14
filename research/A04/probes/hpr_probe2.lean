import NSFormalization.Section4.D01.PressureJets
import NSFormalization.Section4.A04.RealPairing
import Mathlib.Analysis.InnerProductSpace.Adjoint

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3 (RealVectorSobolev real_inner_eq_re_complex realSobolev_inner_eq_ambient)
open NSFormalization.Source.RealSobolev (FourierData RealSobolevHilbert)
open NSFormalization.Section4.D01
open NSFormalization.Section4.D01.Leray
open NSFormalization.Source.FiniteHilbertBochner (assemble coordinates coord Product)
open scoped ComplexConjugate

namespace Probe2

-- H3: carrier real inner = re of ambient complex inner
theorem carrier_inner_eq (s : ℝ) (A B : RealVectorSobolev s) :
    (inner ℝ A B : ℝ) = RCLike.re (inner ℂ
      (WithLp.toLp 2 (fun i => ((A i : FourierData))) : Product (Fin 3) (Lp ℂ 2 (volume : Measure MNS2.R3)))
      (WithLp.toLp 2 (fun i => ((B i : FourierData))))) := by
  simp only [PiLp.inner_apply]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [realSobolev_inner_eq_ambient, real_inner_eq_re_complex]

-- WithLp round trip sanity
example (X : Product (Fin 3) (Lp ℂ 2 (volume : Measure MNS2.R3))) :
    WithLp.toLp 2 (WithLp.ofLp X) = X := rfl

end Probe2
