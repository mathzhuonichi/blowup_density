import NSFormalization.Section4.A01.ConstructorAssembly
import NSFormalization.Section4.A01.ComplementPath

/-! Reviewer reproduction for the sixth-brief pipeline mismatch.  The premise
below is the conclusion of lane 197's current `hprojected_of_cylinder'`; the
goal is the older generic `hcomplement`-choice shape assumed by the committed
pipeline probe.  Direct handoff must fail because these are not the same type. -/

noncomputable section

namespace Rev180SixthBridgeMismatch

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.A01
open NSFormalization.Section4.D01
open NSFormalization.Source.ForcedCylinderLocal
open EulerLpTranslation EulerMeanOrdinaryLift EulerMeanSmoothRepresentative
open EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerQuadraticSource EulerVolterraConvolution EulerSmoothFieldSobolevTime
open scoped ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

example {f : NSFormalization.Section4.A02.SpaceTimeField} (hf : MemForceR f)
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S) (a : SmoothL2Field Space)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hpairs : ∀ p (hp : 6 ≤ p),
      ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (p + 1)),
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
        (∀ (θ : AddCircle (1 : ℝ)) t,
          sobolevTranslation 1 (p + 1) (0, θ) (u t) = u t) ∧
        ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
          (coefficients 1 hp
            (sobolevPath (NSFormalization.Section4.C01.forcePath (S := S) hf)
              (NSFormalization.Section4.C01.forcePath_jetLp_continuous
                (S := S) hf) p))
          (ordinarySobolev (p + 1) a.toLp a.translation_contDiff) u t)
    (R : C(Icc (0 : ℝ) S, RealVectorSobolev (6 : ℝ)))
    (h197 : ∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S),
      lowerVectorL (6 : ℝ) 0 (Nat.cast_nonneg 6)
          (R ⟨t, ht.1.le, ht.2.le⟩) =
        ComplementPath.residualDatum hf hν hS a U hpairs ⟨t, ht.1.le, ht.2.le⟩ -
          Leray.lerayComplement 0
            (ComplementPath.residualDatum hf hν hS a U hpairs
              ⟨t, ht.1.le, ht.2.le⟩))
    (w : ℝ → (Space → Space))
    (hcomplement :
      (∀ j m : ℕ, ∃ H : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ j H (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (w t.1) (H t.1)) ∧
      ∀ t : Icc (0 : ℝ) S, ∃ A : RealVectorSobolev 0,
        IsSobolevDatum 0
          (⇑(ComplementPath.residualCarrier hf hν hS a U hpairs t)) A ∧
        IsSobolevDatum 0 (w t.1) (Leray.lerayComplement 0 A)) :
    ∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S),
      lowerVectorL (6 : ℝ) 0 (Nat.cast_nonneg 6)
          (R ⟨t, ht.1.le, ht.2.le⟩) =
        Classical.choose (hcomplement.2 ⟨t, ht.1.le, ht.2.le⟩) -
          Leray.lerayComplement 0
            (Classical.choose (hcomplement.2 ⟨t, ht.1.le, ht.2.le⟩)) := by
  exact h197

end Rev180SixthBridgeMismatch
