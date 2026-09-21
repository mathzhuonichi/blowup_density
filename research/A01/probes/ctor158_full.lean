import NSFormalization.Section4.A01.SliceWiring
import NSFormalization.Section4.A01.Horizon

/-! Corrected lane-158 constructor target, retaining every local-theory output.
This definition is a research obligation, not an existence theorem. -/

noncomputable section

namespace Ctor158Full

open Set MeasureTheory EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerCylinderSobolev EulerQuadraticSource EulerSobolevHeat EulerVolterraConvolution
open EulerSmoothFieldSobolevTime
open NSFormalization.Source.ForcedCylinderLocal
open NSFormalization.Section4.A01
open NSFormalization.Section4.D01 (jetSobolevConst)
open NSFormalization.Section4.A04 (sobolevNormAt)
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR)
open NavierStokes.ProblemStatement (Space)
open scoped Topology ENNReal ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The full supply-side target. All local-theory conclusions are available. -/
def CarrierConstructorFull {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n) : Prop :=
  ∀ (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2)),
      ‖u‖ ≤ R →
      u ⟨0, le_rfl, hS.le⟩ = ordinarySobolev (q + 1) a.toLp a.translation_contDiff →
      U ⟨0, le_rfl, hS.le⟩ = a.toLp →
      (∀ t, ordinaryLift (U t) = value 1 (u t)) →
      (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) →
      (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
        (coefficients 1 hq (sobolevPath F hF q))
        (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) →
      (∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) →
      ∃ (a' : SpatialField) (f' : SpaceTimeField) (T : ℝ) (_hST : S < T)
        (w : ClassicalSolutionR ν a' f' T),
        ∀ t : Icc (0 : ℝ) S, (fun x : Space => w.velocity (↑t, x)) =ᵐ[volume] ⇑(U t)

theorem rows_from_constructor_full {q : ℕ} (hq : 6 ≤ q) {ν S R : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (hR : 0 ≤ R)
    (a : SmoothL2Field Space) (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space) (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (hu₀ : ‖ordinarySobolev (q + 1) a.toLp a.translation_contDiff‖ ≤ R)
    (hb : HasAprioriBound hq hν a F hF R)
    (hctor : CarrierConstructorFull (R := R) hq hν hS a F hF) :
    ∃ (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
      (a' : SpatialField) (f' : SpaceTimeField) (T : ℝ) (w : ClassicalSolutionR ν a' f' T),
      ‖u‖ ≤ R ∧
      (∀ t : Icc (0 : ℝ) S, sobolevNormAt (2 : ℝ) w.velocity ↑t ≤ 16 * ‖u t‖) ∧
      (∀ t : Icc (0 : ℝ) S,
        ‖u t‖ ≤ jetSobolevConst (q + 1) * sobolevNormAt ((q + 1 : ℕ) : ℝ) w.velocity ↑t) := by
  obtain ⟨u, U, hR', hu0, hU0, hU, hdiv, hduh, hu⟩ :=
    localTheory_on_prescribed_horizon hq hν hS hR a ha F hF hu₀ hb
  obtain ⟨a', f', T, hST, w, hslice⟩ := hctor u U hR' hu0 hU0 hU hdiv hduh hu
  obtain ⟨hfwd, hconv⟩ := apriori_rows_of_hslice hST (by omega) w u U hu hU hslice
  exact ⟨u, a', f', T, w, hR', hfwd, hconv⟩

#print axioms rows_from_constructor_full

end Ctor158Full
