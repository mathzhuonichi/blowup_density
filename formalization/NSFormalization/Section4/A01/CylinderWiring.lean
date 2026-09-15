import NSFormalization.Section4.A01.MildUniqueness
import NSFormalization.Section4.A01.ForcePathSmooth
import NSFormalization.Section4.A01.DatumPathSmooth

/-!
# Wiring all-order bounds to the constructor cylinder data

The only analytic hypothesis in this module is the family of a-priori bounds, one at every
cylinder order.  Whole-interval mild uniqueness identifies the resulting ordinary carriers,
the canonical force path supplies all time derivatives required by the datum bootstrap, and
the forced mild equation supplies divergence-freeness at every order.
-/

noncomputable section

namespace NSFormalization.Section4.A01

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.D01
open NSFormalization.Source.ForcedCylinderLocal
open EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource EulerVolterraConvolution
open scoped Topology ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

variable {f : A02.SpaceTimeField} {S : ℝ}

/-- All-order unrestricted a-priori bounds produce one ordinary carrier, the complete
seven-clause cylinder data at every order (apart from the norm bound and redundant initial
cylinder value), and a `C^j_t H^m_x` datum path for every pair `j,m`.

This is the direct interface between A3's all-order bounds and lanes 178/180. -/
theorem cylinderPair_of_bounds (hf : D01.MemForceR f) (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (R : ℕ → ℝ)
    (hb : ∀ q (hq : 6 ≤ q), HasAprioriBound hq hν a (C01.forcePath (S := S) hf)
      (C01.forcePath_jetLp_continuous (S := S) hf) (R q)) :
    ∃ U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
      (∀ q (hq : 6 ≤ q),
        ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)),
          (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
          (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
          (∀ (θ : AddCircle (1 : ℝ)) t,
            sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
          ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
            (coefficients 1 hq
              (sobolevPath (C01.forcePath (S := S) hf)
                (C01.forcePath_jetLp_continuous (S := S) hf) q))
            (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) ∧
      (∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)) := by
  let F := C01.forcePath (S := S) hf
  let hF := C01.forcePath_jetLp_continuous (S := S) hf
  have hfs : ∀ q (_hq : 6 ≤ q),
      ContDiffOn ℝ ∞ (extendPath S hS.le (sobolevPath F hF q)) (Icc (0 : ℝ) S) := by
    intro q _hq
    exact forcePath_sobolevPath_contDiffOn hf hS q
  obtain ⟨U, hU0, horders⟩ :=
    compatible_carriers_of_bounds' hν hS a ha F hF R hb hfs
  have hall : ∀ (q : ℕ) (hq : 6 ≤ q),
      ∃ (u₀ : SobolevSpace 1 (q + 1))
        (fq : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
        (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))),
        ContDiffOn ℝ ∞ (extendPath S hS.le fq) (Icc (0 : ℝ) S) ∧
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        (∀ (θ : AddCircle (1 : ℝ)) t,
          sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
        ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
          (coefficients 1 hq fq) u₀ u t := by
    intro q hq
    obtain ⟨u, hs, hU, hinv, hduh⟩ := horders q hq
    exact ⟨ordinarySobolev (q + 1) a.toLp a.translation_contDiff,
      sobolevPath F hF q, u, hs, hU, hinv, hduh⟩
  refine ⟨U, hU0, ?_, datumPath_contDiffOn_all_orders hν hS U hall⟩
  intro q hq
  obtain ⟨u, _hs, hU, hinv, hduh⟩ := horders q hq
  exact ⟨u, hU, forced_mild_divergenceFree hq hν hS a ha F hF u hduh, hinv, hduh⟩

/-- Invariant-solution a-priori bounds give the same complete cylinder pair. -/
theorem cylinderPair_of_boundsInv (hf : D01.MemForceR f) (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (R : ℕ → ℝ)
    (hb : ∀ q (hq : 6 ≤ q), HasAprioriBoundInv hq hν a (C01.forcePath (S := S) hf)
      (C01.forcePath_jetLp_continuous (S := S) hf) (R q)) :
    ∃ U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
      (∀ q (hq : 6 ≤ q),
        ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)),
          (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
          (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
          (∀ (θ : AddCircle (1 : ℝ)) t,
            sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
          ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
            (coefficients 1 hq
              (sobolevPath (C01.forcePath (S := S) hf)
                (C01.forcePath_jetLp_continuous (S := S) hf) q))
            (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) ∧
      (∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)) := by
  let F := C01.forcePath (S := S) hf
  let hF := C01.forcePath_jetLp_continuous (S := S) hf
  have hfs : ∀ q (_hq : 6 ≤ q),
      ContDiffOn ℝ ∞ (extendPath S hS.le (sobolevPath F hF q)) (Icc (0 : ℝ) S) := by
    intro q _hq
    exact forcePath_sobolevPath_contDiffOn hf hS q
  obtain ⟨U, hU0, horders⟩ :=
    compatible_carriers_of_boundsInv' hν hS a ha F hF R hb hfs
  have hall : ∀ (q : ℕ) (hq : 6 ≤ q),
      ∃ (u₀ : SobolevSpace 1 (q + 1))
        (fq : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
        (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))),
        ContDiffOn ℝ ∞ (extendPath S hS.le fq) (Icc (0 : ℝ) S) ∧
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        (∀ (θ : AddCircle (1 : ℝ)) t,
          sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
        ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
          (coefficients 1 hq fq) u₀ u t := by
    intro q hq
    obtain ⟨u, hs, hU, hinv, hduh⟩ := horders q hq
    exact ⟨ordinarySobolev (q + 1) a.toLp a.translation_contDiff,
      sobolevPath F hF q, u, hs, hU, hinv, hduh⟩
  refine ⟨U, hU0, ?_, datumPath_contDiffOn_all_orders hν hS U hall⟩
  intro q hq
  obtain ⟨u, _hs, hU, hinv, hduh⟩ := horders q hq
  exact ⟨u, hU, forced_mild_divergenceFree hq hν hS a ha F hF u hduh, hinv, hduh⟩

/-! ## Constructor-shaped exports -/

/-- All of lane 180's constructor inputs at order `q`, together with the all-order datum paths
needed by lane 190, with one shared carrier witness. -/
theorem constructorInputs_of_bounds {q : ℕ} (hq : 6 ≤ q) (hf : D01.MemForceR f)
    (hν : 0 < ν) (hS : 0 < S) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0) (R : ℕ → ℝ)
    (hb : ∀ p (hp : 6 ≤ p), HasAprioriBound hp hν a (C01.forcePath (S := S) hf)
      (C01.forcePath_jetLp_continuous (S := S) hf) (R p)) :
    ∃ (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
      (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
      (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
      (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
      (∀ (θ : AddCircle (1 : ℝ)) t,
        sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
      (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
        (coefficients 1 hq
          (sobolevPath (C01.forcePath (S := S) hf)
            (C01.forcePath_jetLp_continuous (S := S) hf) q))
        (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) ∧
      (∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ 0 G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)) ∧
      ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1) := by
  obtain ⟨U, hU0, hpairs, hsob⟩ := cylinderPair_of_bounds hf hν hS a ha R hb
  obtain ⟨u, hU, hdiv, hinv, hduh⟩ := hpairs q hq
  exact ⟨U, u, hU0, hU, hdiv, hinv, hduh, hsob 0, hsob⟩

/-- Invariant-bound version of `constructorInputs_of_bounds`. -/
theorem constructorInputs_of_boundsInv {q : ℕ} (hq : 6 ≤ q) (hf : D01.MemForceR f)
    (hν : 0 < ν) (hS : 0 < S) (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0) (R : ℕ → ℝ)
    (hb : ∀ p (hp : 6 ≤ p), HasAprioriBoundInv hp hν a (C01.forcePath (S := S) hf)
      (C01.forcePath_jetLp_continuous (S := S) hf) (R p)) :
    ∃ (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
      (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
      (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
      (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
      (∀ (θ : AddCircle (1 : ℝ)) t,
        sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
      (∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
        (coefficients 1 hq
          (sobolevPath (C01.forcePath (S := S) hf)
            (C01.forcePath_jetLp_continuous (S := S) hf) q))
        (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) ∧
      (∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ 0 G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)) ∧
      ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1) := by
  obtain ⟨U, hU0, hpairs, hsob⟩ := cylinderPair_of_boundsInv hf hν hS a ha R hb
  obtain ⟨u, hU, hdiv, hinv, hduh⟩ := hpairs q hq
  exact ⟨U, u, hU0, hU, hdiv, hinv, hduh, hsob 0, hsob⟩

end NSFormalization.Section4.A01
