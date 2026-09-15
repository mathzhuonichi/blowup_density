import NSFormalization.Section4.A01.JointRepresentative
import NSFormalization.Section4.A01.ForcePathSmooth

/-! # Leray-complement paths of the unprojected cylinder residual

The unprojected residual formula and its smoothness proof below are adapted
from lane 189, `PressureRegularity.lean`; that branch is not imported.
-/
noncomputable section
namespace NSFormalization.Section4.A01
namespace ComplementPath
open Set MeasureTheory
open NSFormalization.Section4.D01 NSFormalization.Section4.D01.Leray
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Source NSFormalization.Source.RealSobolev
open NSFormalization.Source.ForcedCylinderLocal
open NSFormalization.Source.OrdinaryCylinderDescent
open NavierStokes.ProblemStatement (Space)
open EulerLpTranslation EulerMeanOrdinaryLift EulerMeanSmoothRepresentative
  EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerCylinderSobolev
  EulerPressureSpatialRegularity EulerQuadraticSource EulerSobolevLaplacian
  EulerVolterraConvolution EulerSmoothFieldSobolevTime
open scoped Topology ContDiff
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The unprojected residual at a fixed cylinder order.  The product and the
restriction maps are exactly those of lane 178's reduced residual. -/
def unprojectedResidualPath {q k : ℕ} (hk : 6 ≤ k)
    (hkq : k + 2 ≤ q + 1) (ν : ℝ) {S : ℝ}
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))) :
    C(Icc (0 : ℝ) S, SobolevSpace 1 k) :=
  ν • (laplacianOperator 1 k).compLeftContinuous ℝ _
      (restrictPath (by omega : k + 2 ≤ q + 1) u) +
    (restrictPath (by omega : k ≤ q) f -
      reducedAdvectionPath hk (by omega : k + 1 ≤ q + 1) u)

/-- Evaluation of the residual path without unfolding continuous-map instances. -/
theorem unprojectedResidualPath_apply {q k : ℕ} (hk : 6 ≤ k)
    (hkq : k + 2 ≤ q + 1) (ν : ℝ) {S : ℝ}
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (t : Icc (0 : ℝ) S) :
    unprojectedResidualPath hk hkq ν f u t =
      ν • laplacianOperator 1 k (restrictOperator 1 hkq (u t)) +
        (restrictOperator 1 (by omega : k ≤ q) (f t) -
          advection 1 hk (restrictOperator 1 (by omega : k + 1 ≤ q + 1) (u t))
            (restrictOperator 1 (by omega : k + 1 ≤ q + 1) (u t))) := rfl

/-- Smoothness of the unprojected residual loses two spatial orders and no
time orders.  Unlike `reducedResidualPath`, no Leray projection is applied. -/
theorem unprojectedResidualPath_contDiffOn {q k n : ℕ} (hk : 6 ≤ k)
    (hkq : k + 2 ≤ q + 1) (ν : ℝ) {S : ℝ} (hS : 0 < S)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (hf : ContDiffOn ℝ n (extendPath S hS.le (restrictPath (by omega : k ≤ q) f))
      (Icc (0 : ℝ) S))
    (hu₁ : ContDiffOn ℝ n
      (extendPath S hS.le (restrictPath (by omega : k + 1 ≤ q + 1) u))
      (Icc (0 : ℝ) S))
    (hu₂ : ContDiffOn ℝ n
      (extendPath S hS.le (restrictPath (by omega : k + 2 ≤ q + 1) u))
      (Icc (0 : ℝ) S)) :
    ContDiffOn ℝ n (extendPath S hS.le (unprojectedResidualPath hk hkq ν f u))
      (Icc (0 : ℝ) S) := by
  have hlap := ((laplacianOperator 1 k).contDiff.comp_contDiffOn hu₂).const_smul ν
  have hadv : ContDiffOn ℝ n
      (fun t => NSFormalization.Source.ForcedCylinderLocal.advection 1 hk
        (extendPath S hS.le (restrictPath (by omega : k + 1 ≤ q + 1) u) t)
        (extendPath S hS.le (restrictPath (by omega : k + 1 ≤ q + 1) u) t))
      (Icc (0 : ℝ) S) :=
    (((NSFormalization.Source.ForcedCylinderLocal.advection 1 hk).contDiff.comp_contDiffOn hu₁).clm_apply hu₁)
  apply (hlap.add (hf.sub hadv)).congr
  intro t ht
  rfl


/-- Physical reconstruction of order-zero data, using the fixed cylinder reconstruction. -/
def datumPhysical : RealVectorSobolev 0 →L[ℝ] EulerMeanSolenoidal.L2 :=
  (ordinaryValue 0).comp (datumSobolevCLM 0)

/-- Physical reconstruction on smooth data. -/
theorem datumPhysical_smooth (Z : SmoothL2Field Space) (A : RealVectorSobolev 0)
    (hA : IsSobolevDatum 0 Z.field A) : datumPhysical A = Z.toLp := by
  have hA' : IsSobolevDatum ((0 : ℕ) : ℝ) Z.field A := by
    rw [Nat.cast_zero]
    exact hA
  have he := datumSobolevCLM_eq_ordinarySobolev 0 Z A hA'
  have hv := congrArg (value 1) he
  have hv' : value 1 (datumSobolevCLM 0 A) = ordinaryLift Z.toLp :=
    hv.trans (ordinarySobolev_value 0 Z.toLp Z.translation_contDiff)
  change ordinaryLift.toContinuousLinearMap.adjoint (value 1 (datumSobolevCLM 0 A)) = _
  rw [hv']
  exact congrArg (fun L : EulerMeanSolenoidal.L2 →L[ℝ] EulerMeanSolenoidal.L2 =>
    L Z.toLp) ordinaryLift.adjoint_comp_self

-- Density compares the two complete-carrier reconstructions.
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
/-- Reconstruction is a right inverse of the order-zero datum map. -/
theorem datumPhysical_rightInverse (A : RealVectorSobolev 0) :
    orderZeroDatumCLM (datumPhysical A) = A := by
  have : T2Space (RealVectorSobolev (0 : ℝ)) :=
    TopologicalSpace.t2Space_of_metrizableSpace
  have hc : IsClosed {B : RealVectorSobolev (0 : ℝ) |
      orderZeroDatumCLM (datumPhysical B) = B} :=
    isClosed_eq (orderZeroDatumCLM.continuous.comp datumPhysical.continuous) continuous_id
  refine (denseRange_schwartzDatum 0).induction_on A hc ?_
  intro φ
  have hd := schwartzDatum_isSobolevDatum 0 φ
  rw [Nat.cast_zero] at hd
  have he := datumPhysical_smooth (schwartzSmoothField φ) (schwartzDatum 0 φ) hd
  rw [he]
  apply isSobolevDatum_unique
  · rw [← orderZeroDatum_memLp_eq]
    exact isSobolevDatum_zero_ordinaryL2 _
  · exact IsSobolevDatum.congr_field hd (schwartzSmoothField φ).toLp_ae.symm

/-- Every order-zero datum has an actual physical `L²` realization. -/
theorem datumPhysical_datum (A : RealVectorSobolev 0) :
    IsSobolevDatum 0 (⇑(datumPhysical A)) A := by
  have h := isSobolevDatum_zero_ordinaryL2 (datumPhysical A)
  rw [orderZeroDatum_memLp_eq, datumPhysical_rightInverse] at h
  exact h

/-- Complementing a smooth datum path preserves its time regularity. -/
theorem complement_contDiffOn {m j : ℕ} {S : ℝ}
    {A : ℝ → RealVectorSobolev (m : ℝ)}
    (hA : ContDiffOn ℝ j A (Icc (0 : ℝ) S)) :
    ContDiffOn ℝ j (fun t => lerayComplement (m : ℝ) (A t)) (Icc (0 : ℝ) S) :=
  (lerayComplement (m : ℝ)).contDiff.comp_contDiffOn hA

/-- The complement of any residual datum at order `m` realizes one fixed physical field. -/
theorem complement_datum {m : ℕ} (R : EulerMeanSolenoidal.L2)
    (A : RealVectorSobolev (m : ℝ)) (hA : IsSobolevDatum (m : ℝ) (⇑R) A) :
    IsSobolevDatum (m : ℝ)
      (⇑(datumPhysical (lerayComplement 0 (orderZeroDatumCLM R))))
      (lerayComplement (m : ℝ) A) := by
  have he : lowerVectorL (m : ℝ) 0 (by positivity) A = orderZeroDatumCLM R := by
    apply isSobolevDatum_unique (Leray.isSobolevDatum_lower (by positivity) hA)
    rw [← orderZeroDatum_memLp_eq]
    exact isSobolevDatum_zero_ordinaryL2 R
  apply (isSobolevDatum_lower_iff (show (0 : ℝ) ≤ m by positivity)).mp
  rw [← lerayComplement_lowerVectorL, he]
  exact datumPhysical_datum _

/-- Linear maps preserve the three-term residual formula. -/
theorem map_residual {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (L : E →L[ℝ] H) (ν : ℝ) (x y z : E) :
    L (ν • x + (y - z)) = ν • L x + (L y - L z) := by
  rw [map_add, map_smul, map_sub]

/-- Invariance of the three-term residual follows termwise. -/
theorem residual_fixed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] E) (ν : ℝ) (x y z : E)
    (hx : L x = x) (hy : L y = y) (hz : L z = z) :
    L (ν • x + (y - z)) = ν • x + (y - z) := by
  rw [map_residual, hx, hy, hz]

/-- Advection preserves angular invariance. -/
theorem advection_invariant {k : ℕ} (hk : 6 ≤ k)
    (v : SobolevSpace 1 (k + 1)) (θ : AddCircle (1 : ℝ))
    (hv : sobolevTranslation 1 (k + 1) (0, θ) v = v) :
    sobolevTranslation 1 k (0, θ) (advection 1 hk v v) = advection 1 hk v v := by
  exact (advection_translation 1 hk (0, θ) v v).symm.trans
    (congrArg₂ (fun a b => advection 1 hk a b) hv hv)

-- Dependent restrictions are normalized in the translation identity.
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
/-- Angular invariance of the unprojected residual. -/
theorem unprojectedResidualPath_invariant {q k : ℕ} (hk : 6 ≤ k)
    (hkq : k + 2 ≤ q + 1) (ν : ℝ) {S : ℝ}
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (hf : ∀ (θ : AddCircle (1 : ℝ)) (t : Icc (0 : ℝ) S), sobolevTranslation 1 q (0, θ) (f t) = f t)
    (hu : ∀ (θ : AddCircle (1 : ℝ)) (t : Icc (0 : ℝ) S), sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (θ : AddCircle (1 : ℝ)) (t : Icc (0 : ℝ) S) :
    sobolevTranslation 1 k (0, θ) (unprojectedResidualPath hk hkq ν f u t) =
      unprojectedResidualPath hk hkq ν f u t := by
  have hur (p : ℕ) (hp : p ≤ q + 1) :
      sobolevTranslation 1 p (0, θ) (restrictOperator 1 hp (u t)) =
        restrictOperator 1 hp (u t) := by
    rw [← restrictOperator_translation, hu θ t]
  have hfr : sobolevTranslation 1 k (0, θ)
      (restrictOperator 1 (by omega : k ≤ q) (f t)) =
      restrictOperator 1 (by omega : k ≤ q) (f t) := by
    rw [← restrictOperator_translation, hf θ t]
  have hl : sobolevTranslation 1 k (0, θ)
      (laplacianOperator 1 k (restrictOperator 1 hkq (u t))) =
      laplacianOperator 1 k (restrictOperator 1 hkq (u t)) := by
    rw [laplacianOperator_translation_local, hur]
  have hb : sobolevTranslation 1 k (0, θ)
      (advection 1 hk (restrictOperator 1 (by omega : k + 1 ≤ q + 1) (u t))
        (restrictOperator 1 (by omega : k + 1 ≤ q + 1) (u t))) =
      advection 1 hk (restrictOperator 1 (by omega : k + 1 ≤ q + 1) (u t))
        (restrictOperator 1 (by omega : k + 1 ≤ q + 1) (u t)) := by
    exact advection_invariant hk _ θ (hur _ _)
  simpa only [unprojectedResidualPath_apply] using
    residual_fixed (sobolevTranslation 1 k (0, θ)) ν _ _ _ hl hfr hb

/-- Continuous ordinary carrier of the unprojected residual. -/
def residualOrdinaryPath {q k : ℕ} (hk : 6 ≤ k)
    (hkq : k + 2 ≤ q + 1) (ν : ℝ) {S : ℝ}
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))) :
    C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2) :=
  (ordinaryValue k).compLeftContinuous ℝ _ (unprojectedResidualPath hk hkq ν f u)

/-- Honest order loss: the residual at order `k` costs `k+2+2*j` velocity orders. -/
theorem residual_datumPath {q k j : ℕ} (hq : 6 ≤ q) (hk : 6 ≤ k)
    (hkj : k + 2 + 2 * j ≤ q + 1) {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (u₀ : SobolevSpace 1 (q + 1))
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (hfs : ContDiffOn ℝ ∞ (extendPath S hS.le f) (Icc (0 : ℝ) S))
    (hf : ∀ (θ : AddCircle (1 : ℝ)) (t : Icc (0 : ℝ) S), sobolevTranslation 1 q (0, θ) (f t) = f t)
    (hu : ∀ (θ : AddCircle (1 : ℝ)) (t : Icc (0 : ℝ) S), sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hduh : ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 hq f) u₀ u t) :
    ∃ G : ℝ → RealVectorSobolev (k : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (k : ℝ)
        (⇑(residualOrdinaryPath hk (by omega) ν f u t)) (G t.1) := by
  have hfc : ContDiffOn ℝ j
      (extendPath S hS.le (restrictPath (by omega : k ≤ q) f)) (Icc (0 : ℝ) S) := by
    exact ((restrictOperator 1 (by omega : k ≤ q)).contDiff.comp_contDiffOn
      (hfs.of_le (by simp))).congr (fun _ _ => rfl)
  have hc := unprojectedResidualPath_contDiffOn hk (by omega) ν hS f u hfc
    (cylinderPath_contDiffOn hq (by omega) (by omega) hν hS u₀ f u hfs hduh)
    (cylinderPath_contDiffOn hq (by omega) hkj hν hS u₀ f u hfs hduh)
  have hi := unprojectedResidualPath_invariant hk (by omega) ν f u hf hu
  exact exists_contDiff_datumPath_of_cylinder hS
    (unprojectedResidualPath hk (by omega) ν f u)
    (residualOrdinaryPath hk (by omega) ν f u) hi
    (fun t => ordinaryValue_lift (by omega) _ (fun θ => hi θ t)) hc

-- Restriction proofs occur in several dependent cylinder orders.
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
/-- The residual at high order restricts to the same order-six formula. -/
theorem residual_restrict_six {q k : ℕ} (hk : 6 ≤ k)
    (hkq : k + 2 ≤ q + 1) (ν : ℝ) {S : ℝ}
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (t : Icc (0 : ℝ) S) :
    restrictOperator 1 hk (unprojectedResidualPath hk hkq ν f u t) =
      unprojectedResidualPath (by omega : 6 ≤ 6) (by omega) ν f u t := by
  simp only [unprojectedResidualPath_apply]
  rw [map_residual]
  have ha := restrict_advection hk (by omega : 6 ≤ 6) hk
    (restrictOperator 1 (by omega : k + 1 ≤ q + 1) (u t))
    (restrictOperator 1 (by omega : k + 1 ≤ q + 1) (u t))
  have hl : restrictOperator 1 hk
      (laplacianOperator 1 k (restrictOperator 1 hkq (u t))) =
      laplacianOperator 1 6 (restrictOperator 1 (by omega : 6 + 2 ≤ q + 1) (u t)) := by
    apply value_injective 1
    rw [value_restrictOperator, laplacianOperator_value, laplacianOperator_value]
    rfl
  exact congrArg₂ (fun a b : SobolevSpace 1 6 => a + b)
    (congrArg (fun a : SobolevSpace 1 6 => ν • a) hl)
    (congrArg (fun a : SobolevSpace 1 6 =>
      restrictOperator 1 (by omega : 6 ≤ q) (f t) - a) ha)

-- Comparing two orders elaborates dependent restriction maps.
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
/-- Residuals of two cylinder realizations of the same velocity and force agree in `L²`. -/
theorem residualOrdinaryPath_eq {q p k : ℕ} (hk : 6 ≤ k)
    (hkq : k + 2 ≤ q + 1) (hp : 6 + 2 ≤ p + 1) (ν : ℝ) {S : ℝ}
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (g : C(Icc (0 : ℝ) S, SobolevSpace 1 p))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (v : C(Icc (0 : ℝ) S, SobolevSpace 1 (p + 1)))
    (hf : ∀ t, value 1 (f t) = value 1 (g t))
    (hu : ∀ t, value 1 (u t) = value 1 (v t)) :
    residualOrdinaryPath hk hkq ν f u =
      residualOrdinaryPath (by omega : 6 ≤ 6) hp ν g v := by
  apply ContinuousMap.ext
  intro t
  have h6 : unprojectedResidualPath (by omega : 6 ≤ 6) (by omega) ν f u t =
      unprojectedResidualPath (by omega : 6 ≤ 6) hp ν g v t := by
    have hf6 : restrictOperator 1 (by omega : 6 ≤ q) (f t) =
        restrictOperator 1 (by omega : 6 ≤ p) (g t) := by
      apply value_injective 1
      exact hf t
    have hu8 : restrictOperator 1 (by omega : 8 ≤ q + 1) (u t) =
        restrictOperator 1 (by omega : 8 ≤ p + 1) (v t) := by
      apply value_injective 1
      exact hu t
    have hu7 : restrictOperator 1 (by omega : 7 ≤ q + 1) (u t) =
        restrictOperator 1 (by omega : 7 ≤ p + 1) (v t) := by
      apply value_injective 1
      exact hu t
    simp only [unprojectedResidualPath_apply]
    exact congrArg₂ (fun a b : SobolevSpace 1 6 => a + b)
      (congrArg (fun z => ν • laplacianOperator 1 6 z) hu8)
      (congrArg₂ (fun a b : SobolevSpace 1 6 => a - b) hf6
        (congrArg₂ (fun a b => advection 1 (by omega : 6 ≤ 6) a b) hu7 hu7))
  change ordinaryLift.toContinuousLinearMap.adjoint
    (value 1 (unprojectedResidualPath hk hkq ν f u t)) = _
  rw [← value_restrictOperator 1 hk, residual_restrict_six, h6]
  rfl

/-- The fixed physical complement carrier uses only the order-zero residual datum. -/
def complementCarrier {S : ℝ} (R : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2)) :
    C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2) :=
  (datumPhysical.comp ((lerayComplement 0).comp orderZeroDatumCLM)).compLeftContinuous ℝ _ R

/-- Compatible residual paths give compatible complement paths for one physical carrier. -/
theorem complementCarrier_paths {S : ℝ}
    (R : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hpaths : ∀ j m : ℕ, ∃ A : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j A (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(R t)) (A t.1)) :
    ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ)
        (⇑(complementCarrier R t)) (G t.1) := by
  intro j m
  obtain ⟨A, hAc, hAd⟩ := hpaths j m
  exact ⟨fun t => lerayComplement (m : ℝ) (A t), complement_contDiffOn hAc,
    fun t => complement_datum (R t) (A t.1) (hAd t)⟩

/-- The complement identity holds at both endpoints as well as in the interior. -/
theorem complementCarrier_identity {S : ℝ}
    (R : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2)) (t : Icc (0 : ℝ) S) :
    IsSobolevDatum 0 (⇑(R t)) (orderZeroDatumCLM (R t)) ∧
    IsSobolevDatum 0 (⇑(complementCarrier R t))
      (lerayComplement 0 (orderZeroDatumCLM (R t))) := by
  constructor
  · rw [← orderZeroDatum_memLp_eq]
    exact isSobolevDatum_zero_ordinaryL2 _
  · exact datumPhysical_datum _

/-- Joint smoothness follows from lane 190: its `L2` carrier has no divergence constraint. -/
theorem complementCarrier_joint {S : ℝ} (hS : 0 < S)
    (R : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hpaths : ∀ j m : ℕ, ∃ A : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j A (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(R t)) (A t.1)) :
    ∃ G : A02.SpaceTimeField,
      ContDiffOn ℝ ∞ G (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) ∧
      ∀ t : Icc (0 : ℝ) S,
        (fun x => G (t.1, x)) =ᵐ[volume] ⇑(complementCarrier R t) := by
  obtain ⟨G, hs, hc⟩ := exists_joint_smooth_representative hS
    (complementCarrier R) (complementCarrier_paths R hpaths)
  exact ⟨G, hc, hs⟩

/-- The ordinary lift differentiates only in the spatial component. -/
theorem fieldDerivative_lift (z : Space → Space) (hz : ContDiff ℝ ∞ z)
    (v : (Space × ℝ)) (x : LiftDomain 1) :
    EulerTransportDerivatives.fieldDerivative 1 v (fun y : LiftDomain 1 => z y.1) x =
      fderiv ℝ z x.1 v.1 := by
  have hi : HasFDerivAt (fun y : Space × ℝ => x.1 + y.1)
      (ContinuousLinearMap.fst ℝ Space ℝ) 0 := by
    exact (ContinuousLinearMap.fst ℝ Space ℝ).hasFDerivAt.const_add x.1
  have ho : HasFDerivAt z (fderiv ℝ z x.1) (x.1 + (0 : Space × ℝ).1) := by
    simpa only [Prod.fst_zero, add_zero] using
      (hz.differentiable (by simp) x.1).hasFDerivAt
  have hd := ho.comp (0 : Space × ℝ) hi
  exact congrArg (fun L : (Space × ℝ) →L[ℝ] Space => L v) hd.fderiv


/-- Smoothness of an ordinary smooth field in every cylinder chart. -/
theorem lift_smooth (z : Space → Space) (hz : ContDiff ℝ ∞ z) (x : LiftDomain 1) :
    ContDiff ℝ ∞ (EulerMetricTransport.localFieldLift 1
      (fun y : LiftDomain 1 => z y.1) x) :=
  hz.comp (contDiff_const.add contDiff_fst)

/-- The physical Laplacian of a spatial slice. -/
def sliceLaplacian (z : Space → Space) (x : Space) : Space :=
  ∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ z y
    (NavierStokes.ProblemStatement.coordinateVector i)) x
      (NavierStokes.ProblemStatement.coordinateVector i)

/-- Value of the Laplacian as the sum of second derivative values. -/
theorem laplacian_value_sum {k : ℕ} (u : SobolevSpace 1 (k + 2)) :
    value 1 (laplacianOperator 1 k u) =
      ∑ i : Fin 4, value 1 (derivativeOperator 1 k i
        (derivativeOperator 1 (k + 1) i u)) := by
  exact (congrArg (value 1) (laplacianOperator_apply 1 u)).trans
    (map_sum (valueOperator 1 k)
      (fun i : Fin 4 => derivativeOperator 1 k i (derivativeOperator 1 (k + 1) i u))
      Finset.univ)

-- Two derivative comparisons and the finite sum normalize cylinder instances.
set_option maxHeartbeats 400000 in
/-- The cylinder Laplacian has the expected physical representative. -/
theorem laplacian_value_lift_ae {k : ℕ} (u : SobolevSpace 1 (k + 2))
    (z : Space → Space) (hz : ContDiff ℝ ∞ z)
    (hu : (⇑(value 1 u)) =ᵐ[liftMeasure 1] (fun y : LiftDomain 1 => z y.1)) :
    (⇑(value 1 (laplacianOperator 1 k u))) =ᵐ[liftMeasure 1]
      (fun y : LiftDomain 1 => sliceLaplacian z y.1) := by
  have hd (i : Fin 4) := derivative_value_ae 1 i u _ hu (lift_smooth z hz)
  have hdd (i : Fin 4) := derivative_value_ae 1 i (derivativeOperator 1 (k + 1) i u)
    _ (hd i) (EulerTransportDerivatives.fieldDerivative_smooth 1
      (standardDirection i) _ (lift_smooth z hz))
  have he (i : Fin 4) : EulerTransportDerivatives.fieldDerivative 1 (standardDirection i)
      (fun y : LiftDomain 1 => z y.1) =
      fun y : LiftDomain 1 => fderiv ℝ z y.1 (standardDirection i).1 :=
    funext (fieldDerivative_lift z hz (standardDirection i))
  have hder (i : Fin 4) : ContDiff ℝ ∞
      (fun x => fderiv ℝ z x (standardDirection i).1) :=
    (hz.fderiv_right (by simp)).clm_apply contDiff_const
  rw [laplacian_value_sum]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin 4 =>
    value 1 (derivativeOperator 1 k i (derivativeOperator 1 (k + 1) i u))),
    ae_all_iff.mpr hdd] with x hx hx'
  rw [hx]
  simp only [Finset.sum_apply]
  calc
    _ = ∑ i : Fin 4, fderiv ℝ (fun y => fderiv ℝ z y (standardDirection i).1)
        x.1 (standardDirection i).1 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hx' i, he i, fieldDerivative_lift _ (hder i)]
    _ = sliceLaplacian z x.1 := by
      rw [Fin.sum_univ_succ]
      simp only [standardDirection_zero, standardDirection_succ, map_zero, zero_add]
      rfl

/-- The spatial advection has the expected physical representative. -/
theorem advection_value_lift_ae {k : ℕ} (hk : 6 ≤ k)
    (u : SobolevSpace 1 (k + 1)) (z : Space → Space) (hz : ContDiff ℝ ∞ z)
    (hu : (⇑(value 1 u)) =ᵐ[liftMeasure 1] (fun y : LiftDomain 1 => z y.1)) :
    (⇑(value 1 (advection 1 hk u u))) =ᵐ[liftMeasure 1]
      (fun y : LiftDomain 1 => fderiv ℝ z y.1 (z y.1)) := by
  have h := EulerSobolevTransport.transportBilinear_ae 1 hk
    (EulerSobolevTransport.velocityComponents 1 0)
    (EulerSobolevTransport.velocityComponents_norm 1 0 (by norm_num) (by simp))
    u u _ _ hu hu (lift_smooth z hz)
  filter_upwards [h] with x hx
  change value 1 (EulerSobolevTransport.transportBilinear 1 hk _ _ u u) x = _
  rw [hx]
  simp only [fieldDerivative_lift z hz]
  have he := congrArg (ContinuousLinearMap.fst ℝ Space ℝ) (EulerSobolevTransport.velocityComponents_direction 1 0 (z x.1))
  have he' : (∑ i : Fin 4,
      EulerSobolevTransport.velocityComponents 1 0 i (z x.1) • (standardDirection i).1) =
        z x.1 := by
    simp only [map_sum, map_smul,
      EulerMetricTransport.transportDirection, one_smul] at he
    exact he
  calc
    _ = (fderiv ℝ z x.1) (∑ i : Fin 4,
        EulerSobolevTransport.velocityComponents 1 0 i (z x.1) • (standardDirection i).1) := by
      simp only [map_sum, map_smul]
    _ = _ := congrArg (fderiv ℝ z x.1) he'



/-- Descending an equality between two ordinary lifts requires no pointwise cylinder section. -/
theorem ae_of_lift_ae {z w : Space → Space}
    (h : (fun x : LiftDomain 1 => z x.1) =ᵐ[liftMeasure 1]
      (fun x : LiftDomain 1 => w x.1)) : z =ᵐ[volume] w := by
  have : IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) := by
    constructor
    simp [AddCircle.measure_univ]
  exact (Measure.ae_ae_of_ae_prod h).mono (fun _ hx => hx.exists.choose_spec)

/-- Physical residual formula on an arbitrary smooth representative of the velocity slice. -/
theorem residualOrdinaryPath_physical {q k : ℕ} (hk : 6 ≤ k)
    (hkq : k + 2 ≤ q + 1) (ν : ℝ) {S : ℝ}
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (hf : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 q (0, θ) (f t) = f t)
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (t : Icc (0 : ℝ) S) (z g : Space → Space) (hz : ContDiff ℝ ∞ z)
    (huz : (⇑(value 1 (u t))) =ᵐ[liftMeasure 1] (fun x : LiftDomain 1 => z x.1))
    (hfg : (⇑(value 1 (f t))) =ᵐ[liftMeasure 1] (fun x : LiftDomain 1 => g x.1)) :
    (⇑(residualOrdinaryPath hk hkq ν f u t)) =ᵐ[volume]
      (fun x => ν • sliceLaplacian z x + (g x - fderiv ℝ z x (z x))) := by
  let l := laplacianOperator 1 k (restrictOperator 1 hkq (u t))
  let b := advection 1 hk (restrictOperator 1 (by omega : k + 1 ≤ q + 1) (u t))
    (restrictOperator 1 (by omega : k + 1 ≤ q + 1) (u t))
  let d := restrictOperator 1 (by omega : k ≤ q) (f t)
  have hl := laplacian_value_lift_ae (restrictOperator 1 hkq (u t)) z hz huz
  have hb := advection_value_lift_ae hk
    (restrictOperator 1 (by omega : k + 1 ≤ q + 1) (u t)) z hz huz
  have hv : value 1 (unprojectedResidualPath hk hkq ν f u t) =
      ν • value 1 l + (value 1 d - value 1 b) := by
    rw [unprojectedResidualPath_apply]
    exact map_residual (valueOperator 1 k) ν l d b
  have hlift : ordinaryLift (residualOrdinaryPath hk hkq ν f u t) =
      value 1 (unprojectedResidualPath hk hkq ν f u t) :=
    ordinaryValue_lift (by omega) _
      (fun θ => unprojectedResidualPath_invariant hk hkq ν f u hf hu θ t)
  have hphys : (⇑(value 1 (unprojectedResidualPath hk hkq ν f u t))) =ᵐ[liftMeasure 1]
      (fun x : LiftDomain 1 => ν • sliceLaplacian z x.1 +
        (g x.1 - fderiv ℝ z x.1 (z x.1))) := by
    rw [hv]
    filter_upwards [Lp.coeFn_add (ν • value 1 l) (value 1 d - value 1 b),
      Lp.coeFn_smul ν (value 1 l), Lp.coeFn_sub (value 1 d) (value 1 b),
      hl, hb, hfg] with x h1 h2 h3 h4 h5 h6
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply] at h1 h2 h3
    change value 1 l x = _ at h4
    change value 1 b x = _ at h5
    change value 1 d x = _ at h6
    rw [h1, h2, h3, h4, h5, h6]
  apply ae_of_lift_ae
  exact (ordinaryLift_ae (residualOrdinaryPath hk hkq ν f u t)).symm.trans
    (hlift ▸ hphys)


section Supply

variable {f : A02.SpaceTimeField} {ν S : ℝ}
variable (hf : MemForceR f) (hν : 0 < ν) (hS : 0 < S)
-- `a` is the standard smooth square-integrable initial velocity.
variable (a : SmoothL2Field Space)
-- `U` is the ordinary L² velocity path restricted to the common closed horizon.
variable (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
-- `hpairs` is precisely the all-order cylinder-pair conjunction exported by lane 192:
-- ordinary realization, divergence freedom, angular invariance, and the forced mild equation.
variable (hpairs : ∀ q (hq : 6 ≤ q),
  ∃ u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)),
    (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
    (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
    (∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
    ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 hq
        (sobolevPath (C01.forcePath (S := S) hf)
          (C01.forcePath_jetLp_continuous (S := S) hf) q))
      (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t)

/-- A fixed residual carrier, formed at order six from the order-eight velocity.
It is independent of all later choices of differentiation and Sobolev order. -/
def residualCarrier : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2) :=
  residualOrdinaryPath (by omega : 6 ≤ 6) (by omega : 6 + 2 ≤ 7 + 1) ν
    (sobolevPath (C01.forcePath (S := S) hf)
      (C01.forcePath_jetLp_continuous (S := S) hf) 7)
    (Classical.choose (hpairs 7 (by omega)))

/-- All finite time orders and spatial orders refer to the same physical residual.
`hf` restricts the standard smooth force class; `hν` and `hS` are positivity restrictions. -/
theorem residualCarrier_paths :
    ∀ j m : ℕ, ∃ A : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j A (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S,
        IsSobolevDatum (m : ℝ) (⇑(residualCarrier hf hν hS a U hpairs t)) (A t.1) := by
  intro j m
  let k := max 6 m
  let q := k + 2 + 2 * j
  have hk : 6 ≤ k := le_max_left _ _
  have hmk : m ≤ k := le_max_right _ _
  have hq : 6 ≤ q := by dsimp [q]; omega
  obtain ⟨u, hU, _hdiv, hu, hduh⟩ := hpairs q hq
  let F := C01.forcePath (S := S) hf
  let hF := C01.forcePath_jetLp_continuous (S := S) hf
  let fq := sobolevPath F hF q
  obtain ⟨A, hAc, hAd⟩ := residual_datumPath hq hk
    (by dsimp [q]; omega : k + 2 + 2 * j ≤ q + 1) hν hS
    (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) fq u
    (forcePath_sobolevPath_contDiffOn hf hS q)
    (fun θ t => sobolevPath_angle_invariant F hF θ t) hu hduh
  have he : residualOrdinaryPath hk (by dsimp [q]; omega) ν fq u =
      residualCarrier hf hν hS a U hpairs := by
    apply residualOrdinaryPath_eq
    · intro t
      change value 1 (ordinarySobolev q (F t).toLp (F t).translation_contDiff) =
        value 1 (ordinarySobolev 7 (F t).toLp (F t).translation_contDiff)
      exact (ordinarySobolev_value q _ _).trans (ordinarySobolev_value 7 _ _).symm
    · intro t
      exact (hU t).symm.trans ((Classical.choose_spec (hpairs 7 (by omega))).1 t)
  have hmkR : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
  refine ⟨fun t => lowerVectorL (k : ℝ) (m : ℝ) hmkR (A t),
    (lowerVectorL (k : ℝ) (m : ℝ) hmkR).contDiff.comp_contDiffOn hAc, ?_⟩
  intro t
  rw [he] at hAd
  exact Leray.isSobolevDatum_lower hmkR (hAd t)

/-- The order-zero residual datum used by the complement identity. -/
def residualDatum (t : Icc (0 : ℝ) S) : RealVectorSobolev 0 :=
  orderZeroDatumCLM (residualCarrier hf hν hS a U hpairs t)

/-- The fixed residual carrier agrees a.e. with the physical residual of any smooth
velocity representative; this is a spatial statement at each time, including both endpoints. -/
theorem residualCarrier_physical (t : Icc (0 : ℝ) S) (z : Space → Space)
    (hz : ContDiff ℝ ∞ z) (hzu : z =ᵐ[volume] ⇑(U t)) :
    (⇑(residualCarrier hf hν hS a U hpairs t)) =ᵐ[volume]
      (fun x => ν • sliceLaplacian z x + (f (t.1, x) - fderiv ℝ z x (z x))) := by
  apply residualOrdinaryPath_physical (by omega : 6 ≤ 6)
    (by omega : 6 + 2 ≤ 7 + 1) ν _ _
    (fun θ t => sobolevPath_angle_invariant _ _ θ t)
    (Classical.choose_spec (hpairs 7 (by omega))).2.2.1 t z
    (fun x => f (t.1, x)) hz
  · rw [← (Classical.choose_spec (hpairs 7 (by omega))).1 t]
    exact (ordinaryLift_ae (U t)).trans
      (ordinaryProjection_measurePreserving.quasiMeasurePreserving.ae hzu.symm)
  · have he : value 1 (sobolevPath (C01.forcePath (S := S) hf)
        (C01.forcePath_jetLp_continuous (S := S) hf) 7 t) =
        ordinaryLift (C01.forcePath (S := S) hf t).toLp :=
      ordinarySobolev_value 7 _ _
    rw [he]
    exact (ordinaryLift_ae _).trans
      (ordinaryProjection_measurePreserving.quasiMeasurePreserving.ae
        (C01.forcePath (S := S) hf t).toLp_ae)

/-- Exact order-zero datum of the physical residual, expressed through the selected
velocity carrier and the prescribed force, with no time derivative. -/
theorem residualDatum_physical (t : Icc (0 : ℝ) S) (z : Space → Space)
    (hz : ContDiff ℝ ∞ z) (hzu : z =ᵐ[volume] ⇑(U t)) :
    IsSobolevDatum 0
      (fun x => ν • sliceLaplacian z x + (f (t.1, x) - fderiv ℝ z x (z x)))
      (residualDatum hf hν hS a U hpairs t) := by
  apply IsSobolevDatum.congr_field
    (complementCarrier_identity (residualCarrier hf hν hS a U hpairs) t).1
  exact residualCarrier_physical hf hν hS a U hpairs t z hz hzu

/-- Consumer-facing physical formula in the standard velocity-field notation. -/
theorem residualDatum_physicalSlice (velocity : A02.SpaceTimeField)
    (t : Icc (0 : ℝ) S)
    (hz : ContDiff ℝ ∞ (fun x => velocity (t.1, x)))
    (hzu : (fun x => velocity (t.1, x)) =ᵐ[volume] ⇑(U t)) :
    IsSobolevDatum 0
      (fun x => ν • NavierStokes.ProblemStatement.spatialLaplacian velocity t.1 x +
        (f (t.1, x) - NavierStokes.ProblemStatement.advection velocity t.1 x))
      (residualDatum hf hν hS a U hpairs t) :=
  residualDatum_physical hf hν hS a U hpairs t _ hz hzu

/-- One physical complement path, defined at every real time by clamping the carrier. -/
def physicalComplement (t : ℝ) : Space → Space :=
  ⇑(complementCarrier (residualCarrier hf hν hS a U hpairs) (projIcc 0 S hS.le t))

/-- The complement path has all time and spatial datum orders and the exact residual
complement identity at every closed-interval time. -/
theorem exists_complement_paths :
    ∃ w : ℝ → (Space → Space),
      (∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (w t.1) (G t.1)) ∧
      ∀ t : Icc (0 : ℝ) S, ∃ A : RealVectorSobolev 0,
        IsSobolevDatum 0 (⇑(residualCarrier hf hν hS a U hpairs t)) A ∧
        IsSobolevDatum 0 (w t.1) (lerayComplement 0 A) := by
  refine ⟨physicalComplement hf hν hS a U hpairs, ?_, ?_⟩
  · intro j m
    obtain ⟨G, hc, hd⟩ := complementCarrier_paths _
      (residualCarrier_paths hf hν hS a U hpairs) j m
    refine ⟨G, hc, fun t => ?_⟩
    simpa only [physicalComplement, projIcc_of_mem hS.le t.property] using hd t
  · intro t
    refine ⟨residualDatum hf hν hS a U hpairs t, ?_⟩
    simpa only [physicalComplement, residualDatum, projIcc_of_mem hS.le t.property] using
      complementCarrier_identity (residualCarrier hf hν hS a U hpairs) t

/-- Lane 190 applied to the fixed complement carrier, including the slice at `S`. -/
theorem exists_complement_joint_representative :
    ∃ G : A02.SpaceTimeField,
      ContDiffOn ℝ ∞ G (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) ∧
      ∀ t : Icc (0 : ℝ) S, (fun x => G (t.1, x)) =ᵐ[volume]
        physicalComplement hf hν hS a U hpairs t.1 := by
  obtain ⟨G, hc, hd⟩ := complementCarrier_joint hS _
    (residualCarrier_paths hf hν hS a U hpairs)
  refine ⟨G, hc, fun t => ?_⟩
  simpa only [physicalComplement, projIcc_of_mem hS.le t.property] using hd t

end Supply
end ComplementPath

export ComplementPath (exists_complement_paths exists_complement_joint_representative)

end NSFormalization.Section4.A01
