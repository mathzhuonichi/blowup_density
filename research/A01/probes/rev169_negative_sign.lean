import NSFormalization.Section4.A01.DatumPathDeriv

noncomputable section

namespace NSFormalization.Section4.A01

open Set
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Source.ForcedCylinderLocal
open NavierStokes.ProblemStatement (Space)
open EulerLpTranslation EulerCylinderSobolevSpace EulerSobolevLaplacian
  EulerLiftedGradientSpace EulerSmoothFieldSobolevTime

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- Reviewer negative mutation: flip the viscous sign in the displayed R2 residual.
set_option autoImplicit false in
example {q m : ℕ} (hq : 6 ≤ q) (hm : m ≤ q - 1)
    (ν : ℝ) {S : ℝ} (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))) (t : Icc (0 : ℝ) S) :
    projectedResidualPath hq hm ν F hF u t =
      (-ν) • laplacianOperator 1 m (restrictOperator 1 (by omega) (u t)) +
        restrictOperator 1 (by omega : m ≤ q)
          (leray 1 q (sobolevPath F hF q t - advection 1 hq (u t) (u t))) := by
  exact projectedResidualPath_eq hq hm ν F hF u t

end NSFormalization.Section4.A01
