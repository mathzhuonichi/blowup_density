import NSFormalization.Section4.A01.LerayBridge
import NSFormalization.Section4.A01.InteriorMomentum

noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory
open NavierStokes.ProblemStatement NSFormalization.Paper3 NSFormalization.Section4.D01
open NSFormalization.Source NSFormalization.Source.RealSobolev
open NSFormalization.Source.OrdinaryCylinderDescent NSFormalization.Source.ForcedCylinderLocal
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerLpTranslation EulerSmoothFieldSobolevTime EulerQuadraticSource EulerVolterraConvolution
open EulerSobolevLaplacian EulerSobolevHeatGenerator EulerMeanSmoothRepresentative
open scoped ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- Replay the landed complement-path adapter within the hard ceiling.
set_option maxHeartbeats 400000 in
set_option linter.unusedVariables false in
theorem canonical_interior_momentum_identity {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (f : A02.SpaceTimeField)
    (hf : NSFormalization.Section4.D01.MemForceR f) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
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
    (velocity : A02.SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) S,
      (fun x : Space => velocity (t.1, x)) =ᵐ[volume] ⇑(U t))
    (hc3 : ContDiffOn ℝ ∞ velocity
      (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    {m : ℕ} (hm : m + 2 ≤ q + 1) (hm2 : 2 ≤ (m : ℝ))
    (B R : C(Icc (0 : ℝ) S, RealVectorSobolev (m : ℝ)))
    (hB : ∀ t, IsSobolevDatum (m : ℝ) (⇑(U t)) (B t))
    (hR : ∀ t, IsSobolevDatum (m : ℝ)
      (⇑(ordinaryResidualPath hq hm ν
        (sobolevPath (C01.forcePath (S := S) hf)
          (C01.forcePath_jetLp_continuous (S := S) hf) q) (Classical.choose (hpairs q hq)) t)) (R t))
    (G : VelocityField)
    (hG : ContDiffOn ℝ ∞ G (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (hGs : ∀ t : Icc (0 : ℝ) S, (fun x => G (t.1, x)) =ᵐ[volume]
      ComplementPath.physicalComplement hf hν hS a U hpairs t.1) :
    ∀ t ∈ Ioo (0 : ℝ) S, ∀ x,
      G (t, x) = pressureGradientOfVelocity ν f (jointRepresentative U hpaths) (t, x) := by
  let W := ComplementPath.residualCarrier hf hν hS a U hpairs
  let w := ComplementPath.physicalComplement hf hν hS a U hpairs
  have hcanonical :
      (∀ j m : ℕ, ∃ H : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ j H (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (w t.1) (H t.1)) ∧
      ∀ t : Icc (0 : ℝ) S, ∃ A : RealVectorSobolev 0,
        IsSobolevDatum 0 (⇑(W t)) A ∧
        IsSobolevDatum 0 (w t.1) (Leray.lerayComplement 0 A) := by
    constructor
    · intro j m
      obtain ⟨H, hc, hd⟩ := ComplementPath.complementCarrier_paths W
        (ComplementPath.residualCarrier_paths hf hν hS a U hpairs) j m
      refine ⟨H, hc, fun t => ?_⟩
      simpa only [w, ComplementPath.physicalComplement, projIcc_of_mem hS.le t.property] using hd t
    · intro t
      refine ⟨ComplementPath.residualDatum hf hν hS a U hpairs t, ?_⟩
      simpa only [w, W, ComplementPath.physicalComplement, ComplementPath.residualDatum,
        projIcc_of_mem hS.le t.property] using ComplementPath.complementCarrier_identity W t
  obtain ⟨hU, hdiv, _, hduh⟩ := Classical.choose_spec (hpairs q hq)
  refine interior_momentum_identity_of_complement_paths hq hm hm2 hν hS
    (ordinarySobolev (q + 1) a.toLp a.translation_contDiff)
    (sobolevPath (C01.forcePath (S := S) hf)
      (C01.forcePath_jetLp_continuous (S := S) hf) q)
    (Classical.choose (hpairs q hq)) U hU hduh hpaths B R hB hR f
    (hf.1.mono (fun z hz => ⟨hz.1.1, mem_univ z.2⟩))
    (fun t => ⇑(W t)) w hcanonical ?_ G hG hGs ?_
  · intro t
    have hs : ContDiff ℝ ∞ (fun x => jointRepresentative U hpaths (t.1, x)) := by
      rw [← contDiffOn_univ]
      exact (jointRepresentative_contDiffOn hS U hpaths).comp
        (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => ⟨t.2, mem_univ x⟩)
    have he := ComplementPath.residualCarrier_physical hf hν hS a U hpairs t _ hs
      (jointRepresentative_slice U hpaths t)
    filter_upwards [he] with x hx
    exact hx.trans (add_comm _ _)
  · intro t ht
    have heq := isSobolevDatum_unique (Classical.choose_spec (hcanonical.2 ⟨t, ht.1.le, ht.2.le⟩)).1
      (ComplementPath.complementCarrier_identity W ⟨t, ht.1.le, ht.2.le⟩).1
    rw [heq]
    exact hprojected_of_cylinder'' hq hν hS f hf a ha U hpairs hpaths
      velocity hslice hc3 hm hm2 B R hB hR t ht

end NSFormalization.Section4.A01
#print axioms NSFormalization.Section4.A01.canonical_interior_momentum_identity
