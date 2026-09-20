import NSFormalization.Section4.A01.ConstructorAssembly
import NSFormalization.Section4.A01.ComplementPath
import NSFormalization.Section4.A01.InteriorMomentum

/-! A real 194 → 195 → 197 → `PressureSupply` composition check.

Lane 194's two exported existentials are opened below and their witnesses are
passed to lane 195's landed `interior_momentum_identity_of_complement_paths`.
Because lane 197 is not landed, `hprojected_of_cylinder` is represented by a
hypothesis with its current exported conclusion, verbatim.  The residual
agreement and the closed-slab slice package are the other explicit downstream
premises; no second carrier or single-order substitute is introduced. -/

noncomputable section

namespace Rev180Pipeline194195197

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

example {q : ℕ} (hq : 6 ≤ q)
    {f : NSFormalization.Section4.A02.SpaceTimeField} (hf : MemForceR f)
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space)
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
    (hpaths : ∀ j m : ℕ, ∃ H : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j H (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (H t.1))
    (B R : C(Icc (0 : ℝ) S, RealVectorSobolev (6 : ℝ)))
    (hB : ∀ t, IsSobolevDatum (6 : ℝ) (⇑(U t)) (B t))
    (hR : ∀ t, IsSobolevDatum (6 : ℝ)
      (⇑(ordinaryResidualPath (by omega : 6 ≤ 7) (by omega : 6 + 2 ≤ 7 + 1) ν
        (sobolevPath (NSFormalization.Section4.C01.forcePath (S := S) hf)
          (NSFormalization.Section4.C01.forcePath_jetLp_continuous (S := S) hf) 7)
        (Classical.choose (hpairs 7 (by omega))) t)) (R t))
    (hresidualAgreement : ∀ t : Icc (0 : ℝ) S,
      (⇑(ComplementPath.residualCarrier hf hν hS a U hpairs t)) =ᵐ[volume]
        fun x => momentumResidualOfVelocity ν f (jointRepresentative U hpaths) (t.1, x))
    (hprojected_of_cylinder : ∀
      (w : ℝ → (Space → Space))
      (hcomplement :
        (∀ j m : ℕ, ∃ H : ℝ → RealVectorSobolev (m : ℝ),
          ContDiffOn ℝ j H (Icc (0 : ℝ) S) ∧
          ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (w t.1) (H t.1)) ∧
        ∀ t : Icc (0 : ℝ) S, ∃ A : RealVectorSobolev 0,
          IsSobolevDatum 0
            (⇑(ComplementPath.residualCarrier hf hν hS a U hpairs t)) A ∧
          IsSobolevDatum 0 (w t.1) (Leray.lerayComplement 0 A)),
      ∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S),
        lowerVectorL (6 : ℝ) 0 (Nat.cast_nonneg 6)
            (R ⟨t, ht.1.le, ht.2.le⟩) =
          Classical.choose (hcomplement.2 ⟨t, ht.1.le, ht.2.le⟩) -
            Leray.lerayComplement 0
              (Classical.choose (hcomplement.2 ⟨t, ht.1.le, ht.2.le⟩)))
    (hclosedSlices : ∀
      (G : NSFormalization.Section4.A02.SpaceTimeField),
      ContDiffOn ℝ ∞ G (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) →
      (∀ t : Icc (0 : ℝ) S, (fun x => G (t.1, x)) =ᵐ[volume]
        ComplementPath.physicalComplement hf hν hS a U hpairs t.1) →
      ∀ t ∈ Ico (0 : ℝ) S,
        MemLp (fun x : Space => G (t, x)) 2 volume ∧
        RadialPotential.HasSymmetricJacobian (fun x : Space => G (t, x))) :
    PressureSupply hq hν hS f hf a ha U hpairs hpaths
      (jointRepresentative U hpaths) (jointRepresentative_slice U hpaths)
      ((jointRepresentative_contDiffOn hS U hpaths).mono
        (prod_mono_left Ico_subset_Icc_self)) := by
  obtain ⟨u7, hU7, _hdiv7, _hinv7, hduh7⟩ := hpairs 7 (by omega)
  have hu7 : u7 = Classical.choose (hpairs 7 (by omega)) := by
    apply ContinuousMap.ext
    intro t
    apply value_injective 1
    exact (hU7 t).symm.trans ((Classical.choose_spec (hpairs 7 (by omega))).1 t)
  have hR7 : ∀ t, IsSobolevDatum (6 : ℝ)
      (⇑(ordinaryResidualPath (by omega : 6 ≤ 7) (by omega : 6 + 2 ≤ 7 + 1) ν
        (sobolevPath (NSFormalization.Section4.C01.forcePath (S := S) hf)
          (NSFormalization.Section4.C01.forcePath_jetLp_continuous (S := S) hf) 7)
        u7 t)) (R t) := by
    simpa only [hu7] using hR
  have _h194_paths := exists_complement_paths hf hν hS a U hpairs
  let w : ℝ → (Space → Space) :=
    ComplementPath.physicalComplement hf hν hS a U hpairs
  have hcomplement :
      (∀ j m : ℕ, ∃ H : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ j H (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (w t.1) (H t.1)) ∧
      ∀ t : Icc (0 : ℝ) S, ∃ A : RealVectorSobolev 0,
        IsSobolevDatum 0
          (⇑(ComplementPath.residualCarrier hf hν hS a U hpairs t)) A ∧
        IsSobolevDatum 0 (w t.1) (Leray.lerayComplement 0 A) := by
    constructor
    · intro j m
      obtain ⟨H, hc, hd⟩ := ComplementPath.complementCarrier_paths _
        (ComplementPath.residualCarrier_paths hf hν hS a U hpairs) j m
      refine ⟨H, hc, fun t => ?_⟩
      simpa only [w, ComplementPath.physicalComplement,
        projIcc_of_mem hS.le t.property] using hd t
    · intro t
      refine ⟨ComplementPath.residualDatum hf hν hS a U hpairs t, ?_⟩
      simpa only [w, ComplementPath.physicalComplement,
        ComplementPath.residualDatum, projIcc_of_mem hS.le t.property] using
        ComplementPath.complementCarrier_identity
          (ComplementPath.residualCarrier hf hν hS a U hpairs) t
  obtain ⟨G, hG_smooth, hG_slice⟩ :=
    exists_complement_joint_representative hf hν hS a U hpairs
  have hf_smooth : ContDiffOn ℝ ∞ f
      (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) :=
    hf.1.mono (prod_mono_left Ico_subset_Ici_self)
  have hG_int := interior_momentum_identity_of_complement_paths
    (q := 7) (m := 6) (by omega) (by omega) (by norm_num) hν hS
    (ordinarySobolev 8 a.toLp a.translation_contDiff)
    (sobolevPath (NSFormalization.Section4.C01.forcePath (S := S) hf)
      (NSFormalization.Section4.C01.forcePath_jetLp_continuous (S := S) hf) 7)
    u7 U hU7 hduh7 hpaths B R hB hR7 f hf_smooth
    (fun t => ⇑(ComplementPath.residualCarrier hf hν hS a U hpairs t))
    w hcomplement hresidualAgreement G hG_smooth hG_slice
    (hprojected_of_cylinder w hcomplement)
  exact ⟨G, hG_int, hG_smooth, hclosedSlices G hG_smooth hG_slice⟩

end Rev180Pipeline194195197
