import NSFormalization.Section4.A01.ConstructorPressure
import NSFormalization.Section4.A01.ConstructorAssembly
import NSFormalization.Section4.D01.OrderZeroCurl
import NSFormalization.Section4.D01.LerayLowering
import Euler.CompactSmoothTimeField
import NSFormalization.Section4.A01.JointRepresentative
import NSFormalization.Section4.A01.LerayBridge

/-!
# Pressure-gradient regularity on an honest slab

This module supplies the missing, non-circular direction of the order-zero
Helmholtz bridge: a smooth `L²` field whose datum is in the range of the Leray
complement has symmetric spatial Jacobian.  The proof reads longitudinality
from the fibre symbol, transports it back through the angular-frequency
dilation, and then uses Fourier injectivity plus classical integration by parts.

The assembly combines lanes 194, 195, and 197 with this Helmholtz converse.
It supplies the exact fix6 pressure contract for arbitrary smooth velocity
representatives. Spatial regularity includes time zero; the momentum identity
is asserted only in the open interior.
-/

noncomputable section

namespace NSFormalization.Section4.A01

open Set MeasureTheory FourierTransform
open NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Source RealSobolev
open NSFormalization.Section4.D01
open NSFormalization.Section4.D01.Leray
open scoped ContDiff SchwartzMap LineDeriv ENNReal

/-! ## 1. The range of the complement symbol is longitudinal -/

/-- The datum-level Leray complement has longitudinal angular Fourier fibres.
This is the converse-facing counterpart of
`Leray.lerayComplement_eq_self_of_longitudinal`. -/
theorem lerayComplement_longitudinal (s : ℝ) (A : RealVectorSobolev s) :
    ∀ᵐ ξ : Space ∂volume, ∀ i j : Fin 3,
      ((ξ i : ℝ) : ℂ) * (((lerayComplement s A) j : FourierData) ξ) =
        ((ξ j : ℝ) : ℂ) * (((lerayComplement s A) i : FourierData) ξ) := by
  refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
  filter_upwards [lerayComplement_ae s A i, lerayComplement_ae s A j] with ξ hi hj
  rw [hi, hj]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (complementSymbolComplex_apply_mem ξ
      (NSFormalization.Source.FiniteHilbertBochner.assemble 2 volume
        (fun k => ((A k : FourierData))) ξ))
  have hcoord : ∀ k : Fin 3,
      (complementSymbolComplex ξ
        (NSFormalization.Source.FiniteHilbertBochner.assemble 2 volume
          (fun l => ((A l : FourierData))) ξ)) k = c * ((ξ k : ℝ) : ℂ) := by
    intro k
    have hk := congrArg (fun v : MNS2.R3C => v k) hc
    simpa [MNS2.r3FrequencyVectorComplex, PiLp.smul_apply, smul_eq_mul] using hk.symm
  rw [hcoord i, hcoord j]
  ring

/-! ## 2. Reverse angular-dilation transport -/

/-- Longitudinality is preserved when moving from the angular convention back
to the cycles convention.  `D01.longitudinal_of_longitudinal_symm` proves the
opposite direction. -/
theorem longitudinal_symm_of_longitudinal {g : Fin 3 → FourierData}
    (h : ∀ᵐ ξ : Space ∂volume, ∀ i j : Fin 3,
      ((ξ i : ℝ) : ℂ) * (g j ξ) = ((ξ j : ℝ) : ℂ) * (g i ξ)) :
    ∀ᵐ ξ : Space ∂volume, ∀ i j : Fin 3,
      ((ξ i : ℝ) : ℂ) * (angularFrequencyDilation.symm (g j) ξ) =
        ((ξ j : ℝ) : ℂ) * (angularFrequencyDilation.symm (g i) ξ) := by
  have hc0 : (0 : ℝ) < frequencyUnit := frequencyUnit_pos
  set κ : ℝ≥0∞ := ENNReal.ofReal (|(frequencyUnit ^ (Module.finrank ℝ Space))⁻¹|) with hκ
  have hMP : MeasurePreserving (fun ξ : Space => frequencyUnit • ξ) volume (κ • volume) :=
    ⟨(continuous_const_smul _).measurable,
      Measure.map_addHaar_smul volume hc0.ne'⟩
  have hback : ∀ k : Fin 3, ∀ᵐ ξ : Space ∂volume,
      (g k (frequencyUnit • ξ)) =
        (frequencyUnit ^ (-3/2 : ℝ) : ℝ) •
          angularFrequencyDilation.symm (g k) ξ := by
    intro k
    have hd := NSFormalization.Paper3.angularFrequencyDilation_coeFn
      (angularFrequencyDilation.symm (g k))
    rw [LinearIsometryEquiv.apply_symm_apply] at hd
    have hd' := hMP.quasiMeasurePreserving.ae (Measure.ae_smul_measure hd κ)
    filter_upwards [hd'] with ξ hξ
    convert hξ using 1
    rw [smul_smul, inv_mul_cancel₀ hc0.ne', one_smul]
  refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
  have hij : ∀ᵐ ξ : Space ∂volume,
      ((ξ i : ℝ) : ℂ) * (g j ξ) = ((ξ j : ℝ) : ℂ) * (g i ξ) := by
    filter_upwards [h] with ξ hξ
    exact hξ i j
  have hscaled := hMP.quasiMeasurePreserving.ae (Measure.ae_smul_measure hij κ)
  filter_upwards [hscaled, hback i, hback j] with ξ hs hi hj
  have hcoord : ∀ k : Fin 3,
      (((frequencyUnit • ξ) k : ℝ) : ℂ) =
        ((frequencyUnit : ℝ) : ℂ) * ((ξ k : ℝ) : ℂ) := fun k => by
    change (((frequencyUnit * ξ k : ℝ) : ℂ)) = _
    push_cast
    rfl
  rw [hcoord i, hcoord j, hi, hj] at hs
  have hc : ((frequencyUnit : ℝ) : ℂ) *
      (((frequencyUnit ^ (-3/2 : ℝ) : ℝ) : ℂ)) ≠ 0 := by
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hc0.ne')
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos hc0 _)))
  have hzero : (((frequencyUnit : ℝ) : ℂ) *
        (((frequencyUnit ^ (-3/2 : ℝ) : ℝ) : ℂ))) *
      (((ξ i : ℝ) : ℂ) * angularFrequencyDilation.symm (g j) ξ -
        ((ξ j : ℝ) : ℂ) * angularFrequencyDilation.symm (g i) ξ) = 0 := by
    simp only [Complex.real_smul] at hs
    linear_combination hs
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hc)

/-! ## 3. Longitudinal order-zero data give classical curl-freeness -/

/-- The raw Fourier longitudinal identity implies equality of the corresponding
distributional partial derivatives. -/
theorem tempered_antisym_eq_of_fourier_longitudinal {z : Space → Space}
    (hz : MemLp z 2 volume) (p q : Fin 3)
    (h : ∀ᵐ ξ : Space ∂volume,
      ((ξ p : ℝ) : ℂ) * (𝓕 (componentLp hz q) : FourierData) ξ =
        ((ξ q : ℝ) : ℂ) * (𝓕 (componentLp hz p) : FourierData) ξ) :
    (∂_{coordinateVector p} ((componentLp hz q : FourierData) : 𝓢'(Space, ℂ))) =
      (∂_{coordinateVector q} ((componentLp hz p : FourierData) : 𝓢'(Space, ℂ))) := by
  apply (fourierEquiv ℂ 𝓢'(Space, ℂ)).injective
  change (fourierCLM ℂ 𝓢'(Space, ℂ))
      (∂_{coordinateVector p} ((componentLp hz q : FourierData) : 𝓢'(Space, ℂ))) =
    (fourierCLM ℂ 𝓢'(Space, ℂ))
      (∂_{coordinateVector q} ((componentLp hz p : FourierData) : 𝓢'(Space, ℂ)))
  ext ψ
  rw [fourier_lineDeriv_apply hz p q, fourier_lineDeriv_apply hz q p]
  congr 1
  apply integral_congr_ae
  filter_upwards [h] with ξ hξ
  calc
    ((ξ p : ℝ) : ℂ) * ψ ξ * (𝓕 (componentLp hz q) : FourierData) ξ
        = ψ ξ * (((ξ p : ℝ) : ℂ) * (𝓕 (componentLp hz q) : FourierData) ξ) := by ring
    _ = ψ ξ * (((ξ q : ℝ) : ℂ) * (𝓕 (componentLp hz p) : FourierData) ξ) := by rw [hξ]
    _ = ((ξ q : ℝ) : ℂ) * ψ ξ * (𝓕 (componentLp hz p) : FourierData) ξ := by ring

/-- A smooth `L²` field with longitudinal order-zero Fourier data is curl-free
pointwise.  No `L²` assumption on its derivatives is used. -/
theorem curl_free_of_orderZeroDatum_longitudinal {z : Space → Space}
    (hz : MemLp z 2 volume) (hsmooth : ContDiff ℝ ∞ z)
    (hlong : ∀ᵐ ξ : Space ∂volume, ∀ i j : Fin 3,
      ((ξ i : ℝ) : ℂ) * (((orderZeroDatum hz) j : FourierData) ξ) =
        ((ξ j : ℝ) : ℂ) * (((orderZeroDatum hz) i : FourierData) ξ)) :
    ∀ i j : Fin 3, ∀ x : Space,
      A03.partialDeriv i z x j = A03.partialDeriv j z x i := by
  have hcycles := longitudinal_symm_of_longitudinal hlong
  intro i j
  have hraw : ∀ᵐ ξ : Space ∂volume,
      ((ξ i : ℝ) : ℂ) * (𝓕 (componentLp hz j) : FourierData) ξ =
        ((ξ j : ℝ) : ℂ) * (𝓕 (componentLp hz i) : FourierData) ξ := by
    have hij : ∀ᵐ ξ : Space ∂volume,
        ((ξ i : ℝ) : ℂ) *
            (angularFrequencyDilation.symm ((orderZeroDatum hz) j : FourierData) ξ) =
          ((ξ j : ℝ) : ℂ) *
            (angularFrequencyDilation.symm ((orderZeroDatum hz) i : FourierData) ξ) := by
      filter_upwards [hcycles] with ξ hξ
      exact hξ i j
    filter_upwards [hij, orderZeroDatum_symm_ae hz i,
      orderZeroDatum_symm_ae hz j] with ξ hij hi hj
    rwa [hi, hj] at hij
  have hdist := tempered_antisym_eq_of_fourier_longitudinal hz i j hraw
  let fi : Space → ℂ := D01.Cut.zc z j
  let fj : Space → ℂ := D01.Cut.zc z i
  have hfi : ContDiff ℝ ∞ fi := D01.Cut.zc_smooth hsmooth j
  have hfj : ContDiff ℝ ∞ fj := D01.Cut.zc_smooth hsmooth i
  have hdi : Continuous (fun x => fderiv ℝ fi x (coordinateVector i)) :=
    (hfi.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdj : Continuous (fun x => fderiv ℝ fj x (coordinateVector j)) :=
    (hfj.continuous_fderiv (by simp)).clm_apply continuous_const
  have hae : (fun x => fderiv ℝ fi x (coordinateVector i)) =ᵐ[volume]
      (fun x => fderiv ℝ fj x (coordinateVector j)) := by
    apply ae_eq_of_integral_contDiff_smul_eq hdi.locallyIntegrable hdj.locallyIntegrable
    intro g hg hgc
    let ψ : SchwartzMap Space ℂ :=
      (hgc.comp_left (g := fun r : ℝ => ((r : ℝ) : ℂ)) (by simp)).toSchwartzMap
        (Complex.ofRealCLM.contDiff.comp hg)
    have hψc : HasCompactSupport (ψ : Space → ℂ) := by
      exact hgc.comp_left (g := fun r : ℝ => ((r : ℝ) : ℂ)) (by simp)
    have hψd : Continuous (fun x => fderiv ℝ (ψ : Space → ℂ) x (coordinateVector i)) :=
      ((ψ.smooth 1).continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hψd' : Continuous (fun x => fderiv ℝ (ψ : Space → ℂ) x (coordinateVector j)) :=
      ((ψ.smooth 1).continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hibpi : (∫ x, ψ x • fderiv ℝ fi x (coordinateVector i)) =
        -∫ x, fderiv ℝ (ψ : Space → ℂ) x (coordinateVector i) • fi x := by
      exact integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
        ((hψd.smul hfi.continuous).integrable_of_hasCompactSupport
          (hψc.fderiv_apply ℝ (coordinateVector i)).smul_right)
        ((ψ.continuous.smul hdi).integrable_of_hasCompactSupport hψc.smul_right)
        ((ψ.continuous.smul hfi.continuous).integrable_of_hasCompactSupport hψc.smul_right)
        (fun x _ => ψ.differentiableAt)
        (fun x _ => (hfi.differentiable (by simp)).differentiableAt)
    have hibpj : (∫ x, ψ x • fderiv ℝ fj x (coordinateVector j)) =
        -∫ x, fderiv ℝ (ψ : Space → ℂ) x (coordinateVector j) • fj x := by
      exact integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
        ((hψd'.smul hfj.continuous).integrable_of_hasCompactSupport
          (hψc.fderiv_apply ℝ (coordinateVector j)).smul_right)
        ((ψ.continuous.smul hdj).integrable_of_hasCompactSupport hψc.smul_right)
        ((ψ.continuous.smul hfj.continuous).integrable_of_hasCompactSupport hψc.smul_right)
        (fun x _ => ψ.differentiableAt)
        (fun x _ => (hfj.differentiable (by simp)).differentiableAt)
    have heval := congrArg (fun U : 𝓢'(Space, ℂ) => U ψ) hdist
    have hdistint :
        (∫ x, fderiv ℝ (ψ : Space → ℂ) x (coordinateVector i) • fi x) =
          ∫ x, fderiv ℝ (ψ : Space → ℂ) x (coordinateVector j) • fj x := by
      simp only [TemperedDistribution.lineDerivOp_apply_apply, map_neg,
        Lp.toTemperedDistribution_apply] at heval
      have hi_int :
          (∫ x, (∂_{coordinateVector i} ψ) x • (componentLp hz j : Space → ℂ) x) =
            ∫ x, fderiv ℝ (ψ : Space → ℂ) x (coordinateVector i) • fi x := by
        apply integral_congr_ae
        filter_upwards [componentLp_ae hz j] with x hx
        rw [hx, SchwartzMap.lineDerivOp_apply_eq_fderiv]
        rfl
      have hj_int :
          (∫ x, (∂_{coordinateVector j} ψ) x • (componentLp hz i : Space → ℂ) x) =
            ∫ x, fderiv ℝ (ψ : Space → ℂ) x (coordinateVector j) • fj x := by
        apply integral_congr_ae
        filter_upwards [componentLp_ae hz i] with x hx
        rw [hx, SchwartzMap.lineDerivOp_apply_eq_fderiv]
        rfl
      rw [hi_int, hj_int] at heval
      exact neg_inj.mp heval
    have hmain : (∫ x, ψ x • fderiv ℝ fi x (coordinateVector i)) =
        ∫ x, ψ x • fderiv ℝ fj x (coordinateVector j) := by
      rw [hibpi, hibpj, hdistint]
    calc
      (∫ x, g x • fderiv ℝ fi x (coordinateVector i)) =
          ∫ x, ψ x • fderiv ℝ fi x (coordinateVector i) := by
            apply integral_congr_ae
            filter_upwards with x
            change ((g x : ℝ) : ℂ) * _ = ψ x * _
            rfl
      _ = ∫ x, ψ x • fderiv ℝ fj x (coordinateVector j) := hmain
      _ = ∫ x, g x • fderiv ℝ fj x (coordinateVector j) := by
            apply integral_congr_ae
            filter_upwards with x
            change ψ x * _ = ((g x : ℝ) : ℂ) * _
            rfl
  have heq : (fun x => fderiv ℝ fi x (coordinateVector i)) =
      (fun x => fderiv ℝ fj x (coordinateVector j)) :=
    (hdi.ae_eq_iff_eq volume hdj).mp hae
  intro x
  have hx := congrFun heq x
  have hzi := D01.Cut.hasFDeriv_zc hsmooth j x
  have hzj := D01.Cut.hasFDeriv_zc hsmooth i x
  rw [hzi.fderiv, hzj.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply] at hx
  exact Complex.ofReal_inj.mp hx

/-- A smooth `L²` realization of a Leray-complement datum has symmetric
Jacobian.  This is the missing converse direction needed by the radial pressure
constructor. -/
theorem hasSymmetricJacobian_of_lerayComplement_orderZeroDatum {z : Space → Space}
    (hz : MemLp z 2 volume) (hsmooth : ContDiff ℝ ∞ z) (A : RealVectorSobolev 0)
    (hdatum : IsSobolevDatum 0 z (lerayComplement 0 A)) :
    RadialPotential.HasSymmetricJacobian z := by
  have hcanonical : orderZeroDatum hz = lerayComplement 0 A :=
    isSobolevDatum_unique (isSobolevDatum_orderZeroDatum hz) hdatum
  have hlong : ∀ᵐ ξ : Space ∂volume, ∀ i j : Fin 3,
      ((ξ i : ℝ) : ℂ) * (((orderZeroDatum hz) j : FourierData) ξ) =
        ((ξ j : ℝ) : ℂ) * (((orderZeroDatum hz) i : FourierData) ξ) := by
    rw [hcanonical]
    exact lerayComplement_longitudinal 0 A
  refine ⟨hsmooth.differentiable (by simp), ?_⟩
  intro x i j
  exact curl_free_of_orderZeroDatum_longitudinal hz hsmooth hlong i j x

/-- The lightweight order-zero specialization of `D01.memLp_of_isSobolevDatum`.
It uses the already available component theorem and finite-dimensional `PiLp`
assembly, avoiding reconstruction of higher physical jets. -/
theorem memLp_of_isSobolevDatum_zero {z : Space → Space} (hz : Continuous z)
    {A : RealVectorSobolev 0} (hA : IsSobolevDatum 0 z A) :
    MemLp z 2 volume := by
  apply memLp_piLp_iff.mpr
  intro i
  have hi := memLp_component_of_isSobolevDatum (s := 0) (by norm_num) hz hA i
  exact hi.congr_norm
    ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp hz).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simp)

/-- Transport an ordinary-carrier datum to the chosen physical slice.  This is
only the a.e. representative bridge, not a projected-momentum theorem. -/
theorem carrierDatum_physicalSlice {S m : ℝ}
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2)) (velocity : A02.SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) S,
      (fun x => velocity (t.1, x)) =ᵐ[volume] ⇑(U t))
    (A : ℝ → RealVectorSobolev m)
    (hA : ∀ t : Icc (0 : ℝ) S, IsSobolevDatum m (⇑(U t)) (A t.1))
    (t : Icc (0 : ℝ) S) :
    IsSobolevDatum m (fun x => velocity (t.1, x)) (A t.1) :=
  IsSobolevDatum.congr_field (hA t) (hslice t).symm

/-- Once a complement carrier and its compatible all-order datum paths have
been constructed, its joint representative has the required endpoint regularity.
`EulerMeanSolenoidal.L2` is plain `Lp Space 2 volume`; it imposes no solenoidality.
This helper does not identify the carrier with the momentum residual. -/
theorem exists_smooth_lerayComplement_representative {S : ℝ} (hS : 0 < S)
    (W : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hpaths : ∀ j m : ℕ, ∃ A : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j A (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(W t)) (A t.1))
    (A₀ : Icc (0 : ℝ) S → RealVectorSobolev 0)
    (hcomplement : ∀ t, IsSobolevDatum 0 (⇑(W t)) (lerayComplement 0 (A₀ t))) :
    ∃ G : A02.SpaceTimeField,
      (∀ t : Icc (0 : ℝ) S, (fun x => G (t.1, x)) =ᵐ[volume] ⇑(W t)) ∧
      (ContDiffOn ℝ ∞ G (Ico (0 : ℝ) S ×ˢ (univ : Set Space)) ∧
        ∀ t ∈ Ico (0 : ℝ) S,
          MemLp (fun x => G (t, x)) 2 volume ∧
          RadialPotential.HasSymmetricJacobian (fun x => G (t, x))) := by
  obtain ⟨G, hslice, hG⟩ := exists_joint_smooth_representative hS W hpaths
  refine ⟨G, hslice, hG, ?_⟩
  intro t ht
  let τ : Icc (0 : ℝ) S := ⟨t, ht.1, ht.2.le⟩
  have hmem : MemLp (fun x => G (t, x)) 2 volume :=
    (memLp_congr_ae (hslice τ)).mpr (Lp.memLp (W τ))
  refine ⟨hmem, hasSymmetricJacobian_of_lerayComplement_orderZeroDatum
    hmem (D01.contDiff_slice hG ht) (A₀ τ) ?_⟩
  exact IsSobolevDatum.congr_field (hcomplement τ) (hslice τ).symm


/-- Continuous slices upgrade a.e. equality to equality; time derivatives agree locally
in the open interior. No endpoint time derivative is asserted. -/
theorem pressureGradientOfVelocity_eq_of_slices {S : ℝ} (ν : ℝ)
    (f u v : VelocityField)
    (hu : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (hv : ContDiffOn ℝ ∞ v (Ico (0 : ℝ) S ×ˢ (univ : Set Space)))
    (he : ∀ t ∈ Ico (0 : ℝ) S,
      (fun x => u (t, x)) =ᵐ[volume] (fun x => v (t, x))) :
    ∀ t ∈ Ioo (0 : ℝ) S, ∀ x,
      pressureGradientOfVelocity ν f u (t, x) =
        pressureGradientOfVelocity ν f v (t, x) := by
  have hs : ∀ t ∈ Ico (0 : ℝ) S, (fun x => u (t, x)) = (fun x => v (t, x)) :=
    fun t ht => ((D01.contDiff_slice hu ht).continuous.ae_eq_iff_eq volume
      (D01.contDiff_slice hv ht).continuous).mp (he t ht)
  intro t ht x
  have ht' : t ∈ Ico (0 : ℝ) S := ⟨ht.1.le, ht.2⟩
  have htime : (fun r => u (r, x)) =ᶠ[nhds t] (fun r => v (r, x)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact congrFun (hs r ⟨hr.1.le, hr.2⟩) x
  have hd : temporalDerivative u t x = temporalDerivative v t x :=
    congrArg (fun L : ℝ →L[ℝ] Space => L 1) htime.fderiv_eq
  have hx := congrFun (hs t ht') x
  simp only [pressureGradientOfVelocity, momentumResidualOfVelocity,
    advection, spatialLaplacian, spatialDerivative, hs t ht', hx, hd]

open EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerMeanOrdinaryLift
open EulerLpTranslation EulerSmoothFieldSobolevTime EulerQuadraticSource EulerVolterraConvolution
open NSFormalization.Source.OrdinaryCylinderDescent
open NSFormalization.Source.ForcedCylinderLocal
open EulerMeanSmoothRepresentative
open A02 (SpaceTimeField)

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

set_option maxHeartbeats 400000 in
theorem pressureSupply_of_pieces {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ}
    (hν : 0 < ν) (hS : 0 < S) (f : SpaceTimeField)
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
    (velocity : SpaceTimeField)
    (hslice : ∀ t : Icc (0 : ℝ) S,
      (fun x : Space => velocity (t.1, x)) =ᵐ[volume] ⇑(U t))
    (hc3 : ContDiffOn ℝ ∞ velocity
      (Ico (0 : ℝ) S ×ˢ (univ : Set Space))) :
    PressureSupply hq hν hS f hf a ha U hpairs hpaths velocity hslice hc3 := by
  let u := Classical.choose (hpairs q hq)
  obtain ⟨hU, hdiv, hinv, hduh⟩ := Classical.choose_spec (hpairs q hq)
  let F := C01.forcePath (S := S) hf
  let hF := C01.forcePath_jetLp_continuous (S := S) hf
  obtain ⟨B, R, hB, hR, _⟩ := exists_differentiable_datumPath
    (m := 2) hq (by omega) hν hS a F hF u U hinv hU hduh
  obtain ⟨G, hG, hGs⟩ := exists_complement_joint_representative hf hν hS a U hpairs
  let W := ComplementPath.residualCarrier hf hν hS a U hpairs
  let A := ComplementPath.residualDatum hf hν hS a U hpairs
  have hcomp (t : Icc (0 : ℝ) S) :
      IsSobolevDatum 0 (fun x => G (t.1, x)) (Leray.lerayComplement 0 (A t)) := by
    have hd := (ComplementPath.complementCarrier_identity W t).2
    apply IsSobolevDatum.congr_field hd
    simpa only [ComplementPath.physicalComplement, projIcc_of_mem hS.le t.property]
      using (hGs t).symm
  have hJ := (jointRepresentative_contDiffOn hS U hpaths).mono
    (prod_mono_left Ico_subset_Icc_self)
  have hid := interior_momentum_identity_of_datums ν f (jointRepresentative U hpaths) G
    (hf.1.mono (fun z hz => ⟨hz.1.1, hz.2⟩)) hJ hG A
    (fun t ht => hcomp ⟨t, ht.1.le, ht.2.le⟩)
    (residualDatum_jointRepresentative hf hν hS a U hpairs hpaths)
  have htime : ∀ t (ht : t ∈ Ioo (0 : ℝ) S),
      IsSobolevDatum 0 (fun x => temporalDerivative (jointRepresentative U hpaths) t x)
        (A ⟨t, ht.1.le, ht.2.le⟩ -
          Leray.lerayComplement 0 (A ⟨t, ht.1.le, ht.2.le⟩)) := by
    intro t ht
    let τ : Icc (0 : ℝ) S := ⟨t, ht.1.le, ht.2.le⟩
    have hd := Leray.isSobolevDatum_lower (by norm_num : (0 : ℝ) ≤ 2) (hR τ)
    change IsSobolevDatum 0 _ (lowerVectorL (2 : ℕ) 0 (Nat.cast_nonneg 2)
      (R ⟨t, ht.1.le, ht.2.le⟩)) at hd
    rw [hprojected_of_cylinder'' hq hν hS f hf a ha U hpairs hpaths velocity hslice hc3
      (by omega) (by norm_num) B R hB hR t ht] at hd
    apply IsSobolevDatum.congr_field hd
    have hae := vectorRepresentative_ae (by norm_num : 2 ≤ (2 : ℝ))
      (Lp.memLp (ordinaryResidualPath hq (m := 2) (by omega) ν (sobolevPath F hF q) u τ))
      (hR τ)
    filter_upwards [hae] with x hx
    exact hx.symm.trans (jointRepresentative_temporalDerivative_of_cylinder hq
      (m := 2) (by omega) (by norm_num) hν hS
      (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) (sobolevPath F hF q)
      u U hU hduh hpaths B R hB hR ht x).symm
  refine ⟨G, ?_, hG, ?_⟩
  · intro t ht x
    apply (hid htime t ht x).trans
    apply pressureGradientOfVelocity_eq_of_slices ν f _ velocity hJ hc3
      (fun r hr => (jointRepresentative_slice U hpaths ⟨r, hr.1, hr.2.le⟩).trans
        (hslice ⟨r, hr.1, hr.2.le⟩).symm) t ht x
  · intro t ht
    have hd := hcomp ⟨t, ht.1, ht.2.le⟩
    have hs := D01.contDiff_slice hG ht
    have hm := memLp_of_isSobolevDatum_zero hs.continuous hd
    exact ⟨hm, hasSymmetricJacobian_of_lerayComplement_orderZeroDatum hm hs _ hd⟩

end NSFormalization.Section4.A01
