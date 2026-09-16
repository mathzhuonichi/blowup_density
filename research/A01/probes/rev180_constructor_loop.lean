import NSFormalization.Section4.A01.ConstructorAssembly

/-! The comparison-row consumer closes from the landed all-order bound and the
scoped lane-189 obligation; lanes 192 and 190 are invoked in production. -/

noncomputable section

namespace Rev180ConstructorLoop

open Set MeasureTheory EulerLpTranslation EulerMeanSmoothRepresentative
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerQuadraticSource EulerSobolevHeat EulerVolterraConvolution
open EulerSmoothFieldSobolevTime
open NSFormalization.Section4.A01
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Source.ForcedCylinderLocal
open NavierStokes.ProblemStatement (Space)
open scoped ContDiff

example {q : ℕ} (hq : 6 ≤ q)
    {f : NSFormalization.Section4.A02.SpaceTimeField}
    (hf : NSFormalization.Section4.D01.MemForceR f)
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (R : ℕ → ℝ)
    (hb : ∀ p (hp : 6 ≤ p), HasAprioriBound hp hν a
      (NSFormalization.Section4.C01.forcePath (S := S) hf)
      (NSFormalization.Section4.C01.forcePath_jetLp_continuous (S := S) hf) (R p))
    (h189 : ∀
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
      (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1))
      (velocity : NSFormalization.Section4.A02.SpaceTimeField)
      (hslice : ∀ t : Icc (0 : ℝ) S,
        (fun x : Space => velocity (t.1, x)) =ᵐ[volume] ⇑(U t))
      (hc3 : ContDiffOn ℝ ∞ velocity
        (Ico (0 : ℝ) S ×ˢ (univ : Set Space))),
      PressureSupply hq hν hS f hf a ha U hpairs hpaths velocity hslice hc3) :
    ∃ (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
      (a' : NSFormalization.Section4.A02.SpatialField)
      (f' : NSFormalization.Section4.A02.SpaceTimeField)
      (w : NSFormalization.Section4.A02.ClassicalSolutionR ν a' f' S),
      ‖u‖ ≤ R q ∧
      (∀ t : Icc (0 : ℝ) S,
        NSFormalization.Section4.A04.sobolevNormAt (2 : ℝ) w.velocity ↑t ≤ 16 * ‖u t‖) ∧
      ∀ t : Icc (0 : ℝ) S,
        ‖u t‖ ≤ NSFormalization.Section4.D01.jetSobolevConst (q + 1) *
          NSFormalization.Section4.A04.sobolevNormAt ((q + 1 : ℕ) : ℝ)
            w.velocity ↑t := by
  exact rows_from_constructor_full hq hf hν hS a ha R hb h189

#print axioms NSFormalization.Section4.A01.PressureSupply
#print axioms NSFormalization.Section4.A01.rows_from_constructor_full
#print axioms NSFormalization.Section4.A01.carrierConstructorFull_of_hyps

end Rev180ConstructorLoop
