import NSFormalization.Section4.A01.InteriorMomentum
import NSFormalization.Section4.A01.ComplementPath
import NSFormalization.Section4.A01.DatumPathDeriv
import NSFormalization.Section4.A01.ConstructorDivergence
import NSFormalization.Section4.A01.ConstructorPressure
import NSFormalization.Section4.D01.OrderZeroCurl
import Euler.MeanCylinderSolenoidal
import Euler.ClassicalPressureCurl

/-!
Cylinder-to-Fourier projector bridge. `ordinaryResidualPath` is already projected.
The canonical export derives the cylinder Helmholtz memberships, constructs both
smooth representatives, and uses lane 194's fixed physical residual datum.
The earlier conditional comparison remains available as an algebraic helper.
-/
noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Section4.D01
open NSFormalization.Section4.A03 (partialDeriv)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
open NSFormalization.Source.ForcedCylinderLocal
open scoped ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Datum uniqueness after physical descent. `hagreement` is precisely the
restriction of the physical residual identity to one spatial slice. -/
theorem physicalResidual_datum_eq (ν : ℝ) (f v : VelocityField) (t : ℝ)
    (z : Space → Space) (A D : RealVectorSobolev 0)
    (hres : IsSobolevDatum 0 (fun x => momentumResidualOfVelocity ν f v (t, x)) A)
    (hD : IsSobolevDatum 0 z D)
    (hagreement : (fun x => momentumResidualOfVelocity ν f v (t, x)) =ᵐ[volume] z) :
    A = D := by
  exact isSobolevDatum_unique (IsSobolevDatum.congr_field hres hagreement) hD

/-- Any selected datum of a smooth L² curl-free field is fixed by the complement.
The hypotheses are the standard spatial smoothness, integrability and curl identity. -/
theorem gradient_datum_fixed {z : Space → Space} (hz : MemLp z 2 volume)
    (hsmooth : ContDiff ℝ ∞ z)
    (hcurl : ∀ (i j : Fin 3) (x : Space), partialDeriv i z x j = partialDeriv j z x i)
    (A : RealVectorSobolev 0) (hA : IsSobolevDatum 0 z A) :
    Leray.lerayComplement 0 A = A := by
  have heq := isSobolevDatum_unique hA (isSobolevDatum_orderZeroDatum hz)
  rw [heq]
  exact Leray.lerayComplement_zero_orderZeroDatum_eq_self hz hsmooth hcurl

/-- Any selected datum of a smooth L² solenoidal field is killed by the complement. -/
theorem solenoidal_datum_zero {z : Space → Space} (hz : MemLp z 2 volume)
    (hsmooth : ContDiff ℝ ∞ z)
    (hdiv : ∀ x, ∑ j : Fin 3, partialDeriv j z x j = 0)
    (A : RealVectorSobolev 0) (hA : IsSobolevDatum 0 z A) :
    Leray.lerayComplement 0 A = 0 := by
  have heq := isSobolevDatum_unique hA (isSobolevDatum_orderZeroDatum hz)
  rw [heq]
  exact Leray.lerayComplement_eq_zero_of_transverse 0 _
    (orderZeroDatum_transverse_of_divergence_free hz hsmooth hdiv)

/-- Cylinder orthogonality suffices for the Fourier solenoidal identity when a
smooth ordinary representative is supplied. -/
theorem solenoidal_datum_zero_of_cylinder (U : EulerMeanSolenoidal.L2)
    (hU : ordinaryLift U ∈ divergenceFreeSpace 1 1 0)
    (z : Space → Space) (hsmooth : ContDiff ℝ ∞ z)
    (hrep : (⇑U) =ᵐ[volume] z)
    (A : RealVectorSobolev 0) (hA : IsSobolevDatum 0 z A) :
    Leray.lerayComplement 0 A = 0 := by
  apply solenoidal_datum_zero ((memLp_congr_ae hrep).mp (Lp.memLp U)) hsmooth _ A hA
  intro x
  have h := divergence_eq_zero_of_ordinaryLift U hU z hsmooth hrep x
  rw [EulerSmoothLimit.divergence_eq_coordinate_sum] at h
  exact h

/-- A smooth ordinary representative of a cylinder gradient has a fixed Fourier
complement. This uses cylinder weak curl directly, without reversing an embedding. -/
theorem gradient_datum_fixed_of_cylinder (U : EulerMeanSolenoidal.L2)
    (hU : ordinaryLift U ∈ gradientSpace 1 1 0)
    (z : Space → Space) (hsmooth : ContDiff ℝ ∞ z)
    (hrep : (⇑U) =ᵐ[volume] z)
    (A : RealVectorSobolev 0) (hA : IsSobolevDatum 0 z A) :
    Leray.lerayComplement 0 A = A := by
  apply gradient_datum_fixed ((memLp_congr_ae hrep).mp (Lp.memLp U)) hsmooth _ A hA
  have hlift : (⇑(ordinaryLift U)) =ᵐ[liftMeasure 1] fun x => z x.1 := by
    rw [ordinaryLift_eq_embedding]
    exact EulerMeanCylinderSolenoidal.embedding_representative 1 U z hrep
  intro i j x
  have h := EulerClassicalPressureCurl.gradientSpace_classical_curl_zero
    1 1 0 (ordinaryLift U) hU (fun x => z x.1) hlift
    (fun y => hsmooth.comp (contDiff_const.add contDiff_fst)) (x, 0) i j
  simp only [EulerMeanCylinderSolenoidal.fieldDerivative_spatial 1 z hsmooth] at h
  simpa [partialDeriv, EulerMetricTransport.coordinateDirection,
    spatialDerivative, A03.lift, coordinateVector] using h

/-- The finite-dimensional decomposition argument, independent of any choice of
physical representatives. It does not assume the desired projector equality. -/
theorem projected_datum_of_decomposition (A P G : RealVectorSobolev 0)
    (hdecomp : A = P + G)
    (hsol : Leray.lerayComplement 0 P = 0)
    (hgrad : Leray.lerayComplement 0 G = G) :
    P = A - Leray.lerayComplement 0 A := by
  rw [hdecomp, map_add, hsol, hgrad, zero_add, add_sub_cancel_right]

/-- The two projectors agree on a smooth ordinary Helmholtz decomposition.
`hsol` and `hgrad` are restrictions of cylinder orthogonality and gradient
membership; `hp` and `hz` identify smooth representatives of the carriers. -/
theorem lowered_projected_datum_of_cylinder {m : ℕ}
    (U W : EulerMeanSolenoidal.L2)
    (hsol : ordinaryLift U ∈ divergenceFreeSpace 1 1 0)
    (hgrad : ordinaryLift (W - U) ∈ gradientSpace 1 1 0)
    (p z : Space → Space) (hps : ContDiff ℝ ∞ p) (hzs : ContDiff ℝ ∞ z)
    (hp : (⇑U) =ᵐ[volume] p) (hz : (⇑W) =ᵐ[volume] z)
    (R : RealVectorSobolev (m : ℝ)) (A : RealVectorSobolev 0)
    (hR : IsSobolevDatum (m : ℝ) (⇑U) R)
    (hA : IsSobolevDatum 0 (⇑W) A) :
    lowerVectorL (m : ℝ) 0 (Nat.cast_nonneg m) R = A - Leray.lerayComplement 0 A := by
  let P := lowerVectorL (m : ℝ) 0 (Nat.cast_nonneg m) R
  have hP : IsSobolevDatum 0 (⇑U) P :=
    Leray.isSobolevDatum_lower (Nat.cast_nonneg m) hR
  have hPz : IsSobolevDatum 0 p P := IsSobolevDatum.congr_field hP hp
  have hAz : IsSobolevDatum 0 z A := IsSobolevDatum.congr_field hA hz
  have hpLp : MemLp p 2 volume := (memLp_congr_ae hp).mp (Lp.memLp U)
  have hzLp : MemLp z 2 volume := (memLp_congr_ae hz).mp (Lp.memLp W)
  have hd : IsSobolevDatum 0 (z - p) (A - P) :=
    D01.isSobolevDatum_sub
      (schwartzPairable_of_memLp (fun i => memLp_component hzLp i))
      (schwartzPairable_of_memLp (fun i => memLp_component hpLp i)) hAz hPz
  have hrep : (⇑(W - U)) =ᵐ[volume] z - p := by
    filter_upwards [Lp.coeFn_sub W U, hz, hp] with x hx hzx hpx
    exact hx.trans (congrArg₂ (· - ·) hzx hpx)
  have hcP := solenoidal_datum_zero_of_cylinder U hsol p hps hp P hPz
  have hcG := gradient_datum_fixed_of_cylinder (W - U) hgrad (z - p)
    (hzs.sub hps) hrep (A - P) hd
  exact projected_datum_of_decomposition A P (A - P) (by abel) hcP hcG

/-- Interior path form of the cylinder Helmholtz comparison. The conclusion is
lane 195's `hprojected` verbatim. This theorem still requires the actual cylinder
Helmholtz decomposition and smooth representatives; it does not construct them.
All additional path hypotheses are restricted to strictly interior times. -/
theorem hprojected_of_cylinder {q m : ℕ}
    (hq : 6 ≤ q) (hm : m + 2 ≤ q + 1) {ν S : ℝ}
    (fc : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (uc : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (R : C(Icc (0 : ℝ) S, RealVectorSobolev (m : ℝ)))
    (hR : ∀ t, IsSobolevDatum (m : ℝ)
      (⇑(ordinaryResidualPath hq hm ν fc uc t)) (R t))
    (A : Icc (0 : ℝ) S → RealVectorSobolev 0)
    (W : Icc (0 : ℝ) S → EulerMeanSolenoidal.L2)
    (p z : Icc (0 : ℝ) S → Space → Space)
    (hA : ∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S),
      IsSobolevDatum 0 (⇑(W ⟨t, ht.1.le, ht.2.le⟩)) (A ⟨t, ht.1.le, ht.2.le⟩))
    (hsol : ∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S),
      ordinaryLift (ordinaryResidualPath hq hm ν fc uc ⟨t, ht.1.le, ht.2.le⟩)
        ∈ divergenceFreeSpace 1 1 0)
    (hgrad : ∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S),
      ordinaryLift (W ⟨t, ht.1.le, ht.2.le⟩ -
        ordinaryResidualPath hq hm ν fc uc ⟨t, ht.1.le, ht.2.le⟩) ∈ gradientSpace 1 1 0)
    (hps : ∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S),
      ContDiff ℝ ∞ (p ⟨t, ht.1.le, ht.2.le⟩))
    (hzs : ∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S),
      ContDiff ℝ ∞ (z ⟨t, ht.1.le, ht.2.le⟩))
    (hp : ∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S),
      (⇑(ordinaryResidualPath hq hm ν fc uc ⟨t, ht.1.le, ht.2.le⟩))
        =ᵐ[volume] p ⟨t, ht.1.le, ht.2.le⟩)
    (hz : ∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S),
      (⇑(W ⟨t, ht.1.le, ht.2.le⟩)) =ᵐ[volume] z ⟨t, ht.1.le, ht.2.le⟩) :
    ∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S),
      lowerVectorL (m : ℝ) 0 (Nat.cast_nonneg m) (R ⟨t, ht.1.le, ht.2.le⟩) =
        A ⟨t, ht.1.le, ht.2.le⟩ - Leray.lerayComplement 0 (A ⟨t, ht.1.le, ht.2.le⟩) := by
  intro t ht
  exact lowered_projected_datum_of_cylinder _ _ (hsol t ht) (hgrad t ht)
    _ _ (hps t ht) (hzs t ht) (hp t ht) (hz t ht) _ _
    (hR ⟨t, ht.1.le, ht.2.le⟩) (hA t ht)

/-- Explicitly expose the cylinder gradient removed from the source. -/
theorem cylinder_source_complement_value {q : ℕ} (w : SobolevSpace 1 q) :
    value 1 w - value 1 (leray 1 q w) =
      gradientProjection 1 1 0 (value 1 w) := by
  rw [leray_value]
  abel

/-- The orthogonal cylinder projector has solenoidal range. -/
theorem leray_value_solenoidal {q : ℕ} (w : SobolevSpace 1 q) :
    value 1 (leray 1 q w) ∈ divergenceFreeSpace 1 1 0 := by
  exact (EulerDivergenceFreeHeat.gradientEvaluation_zero_iff 1 1 0 _).mp
    (leray_gradient_zero 1 w)

/-- The removed component belongs to the closed cylinder gradient subspace. -/
theorem leray_value_complement_gradient {q : ℕ} (w : SobolevSpace 1 q) :
    value 1 w - value 1 (leray 1 q w) ∈ gradientSpace 1 1 0 := by
  rw [cylinder_source_complement_value]
  exact (gradientSpace 1 1 0).starProjection_apply_mem _

/-- Second derivative words preserve the cylinder divergence constraint. -/
theorem laplacianEvaluation_solenoidal {q : ℕ} (hq : 2 ≤ q)
    (u : SobolevSpace 1 q) (hu : value 1 u ∈ divergenceFreeSpace 1 1 0) :
    EulerSobolevHeatGenerator.laplacianEvaluation 1 q hq u ∈
      divergenceFreeSpace 1 1 0 := by
  rw [EulerSobolevHeatGenerator.laplacianEvaluation_apply]
  exact Submodule.sum_mem _ (fun i _ =>
    EulerSobolevWordConstraints.word_divergenceFree 1 hq 1 0 u hu (fun _ => i))

/-- Solenoidality of the actual projected residual, including its viscous term. -/
theorem cylinderResidual_solenoidal {q m : ℕ} (hq : 6 ≤ q)
    (hm : m + 2 ≤ q + 1) (ν : ℝ) {S : ℝ}
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (hu : ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0)
    (t : Icc (0 : ℝ) S) :
    value 1 (cylinderResidual hq hm ν f u t) ∈ divergenceFreeSpace 1 1 0 := by
  rw [cylinderResidual_value, source_eq]
  exact (divergenceFreeSpace 1 1 0).add_mem
    ((divergenceFreeSpace 1 1 0).smul_mem ν
      (laplacianEvaluation_solenoidal (by omega) (u t) (hu t)))
    (leray_value_solenoidal _)

open EulerSobolevLaplacian EulerSobolevHeatGenerator
open NSFormalization.Source.RealSobolev

/-- Linear value evaluation, isolated before substituting the large residual terms. -/
theorem value_residual_linear {k : ℕ} (ν : ℝ) (L F A : SobolevSpace 1 k) :
    value 1 (ν • L + (F - A)) = ν • value 1 L + (value 1 F - value 1 A) := by
  change (valueOperator 1 k) (ν • L + (F - A)) = _
  rw [map_add, map_smul, map_sub]
  rfl

-- Split value transport from membership to keep elaboration within the hard cap.
set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
theorem unprojectedResidual_value {q k : ℕ} (hq : 6 ≤ q) (hk : 6 ≤ k)
    (hkq : k + 2 ≤ q + 1) (ν : ℝ) {S : ℝ}
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (t : Icc (0 : ℝ) S) :
    value 1 (ComplementPath.unprojectedResidualPath hk hkq ν f u t) =
      ν • laplacianEvaluation 1 (q + 1) (by omega) (u t) +
        value 1 (f t - advection 1 hq (u t) (u t)) := by
  have ha := congrArg (value 1) (restrict_advection hq hk (by omega) (u t) (u t))
  rw [value_restrictOperator] at ha
  have hl : value 1 (laplacianOperator 1 k (restrictOperator 1 hkq (u t))) =
      laplacianEvaluation 1 (q + 1) (by omega) (u t) :=
    laplacianOperator_value 1 _
  have hlin := value_residual_linear ν
    (laplacianOperator 1 k (restrictOperator 1 hkq (u t)))
    (restrictOperator 1 (by omega : k ≤ q) (f t))
    (advection 1 hk (restrictOperator 1 (by omega) (u t))
      (restrictOperator 1 (by omega) (u t)))
  have hsub : value 1 (restrictOperator 1 (by omega : k ≤ q) (f t)) -
      value 1 (advection 1 hk (restrictOperator 1 (by omega) (u t))
        (restrictOperator 1 (by omega) (u t))) =
      value 1 (f t - advection 1 hq (u t) (u t)) :=
    congrArg₂ (· - ·) (value_restrictOperator 1 (by omega : k ≤ q) (f t)) ha.symm
  exact (congrArg (value 1)
    (ComplementPath.unprojectedResidualPath_apply hk hkq ν f u t)).trans
    (hlin.trans (congrArg₂ (· + ·) (congrArg (ν • ·) hl) hsub))

-- Membership is checked separately from value transport under the hard ceiling.
set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- The unprojected residual and the projected residual differ by exactly the
orthogonal gradient projection of the nonlinear source. -/
theorem residual_difference_gradient {q k m : ℕ} (hq : 6 ≤ q) (hk : 6 ≤ k)
    (hkq : k + 2 ≤ q + 1) (hm : m + 2 ≤ q + 1) (ν : ℝ) {S : ℝ}
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (t : Icc (0 : ℝ) S) :
    value 1 (ComplementPath.unprojectedResidualPath hk hkq ν f u t) -
      value 1 (cylinderResidual hq hm ν f u t) ∈ gradientSpace 1 1 0 := by
  have hv := unprojectedResidual_value hq hk hkq ν f u t
  have hp := cylinderResidual_value hq hm ν f u t
  rw [source_eq] at hp
  change value 1 (cylinderResidual hq hm ν f u t) =
    ν • laplacianEvaluation 1 (q + 1) (by omega) (u t) +
      value 1 (leray 1 q (f t - advection 1 hq (u t) (u t))) at hp
  have he := congrArg₂ (· - ·) hv hp
  rw [add_sub_add_left_eq_sub] at he
  exact he.symm ▸ leray_value_complement_gradient (f t - advection 1 hq (u t) (u t))

set_option backward.isDefEq.respectTransparency false in
/-- Descent of lane 194's full unprojected residual. -/
theorem ordinaryLift_unprojectedResidual {q k : ℕ} (hk : 6 ≤ k)
    (hkq : k + 2 ≤ q + 1) (ν : ℝ) {S : ℝ}
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (hf : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 q (0, θ) (f t) = f t)
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (t : Icc (0 : ℝ) S) :
    ordinaryLift (ComplementPath.residualOrdinaryPath hk hkq ν f u t) =
      value 1 (ComplementPath.unprojectedResidualPath hk hkq ν f u t) := by
  change ordinaryLift (ordinaryLift.toContinuousLinearMap.adjoint
    (value 1 (ComplementPath.unprojectedResidualPath hk hkq ν f u t))) = _
  apply ordinaryLift_adjoint_of_invariant
  intro θ
  simpa only [translation_value] using congrArg (value 1)
    (ComplementPath.unprojectedResidualPath_invariant hk hkq ν f u hf hu θ t)

/-- Both Helmholtz memberships at the ordinary carrier level are consequences
of the cylinder projector, angular invariance and velocity solenoidality. -/
theorem ordinaryResidual_helmholtz {q k m : ℕ} (hq : 6 ≤ q) (hk : 6 ≤ k)
    (hkq : k + 2 ≤ q + 1) (hm : m + 2 ≤ q + 1) (ν : ℝ) {S : ℝ}
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (hf : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 q (0, θ) (f t) = f t)
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hdiv : ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0)
    (t : Icc (0 : ℝ) S) :
    ordinaryLift (ordinaryResidualPath hq hm ν f u t) ∈ divergenceFreeSpace 1 1 0 ∧
    ordinaryLift (ComplementPath.residualOrdinaryPath hk hkq ν f u t -
      ordinaryResidualPath hq hm ν f u t) ∈ gradientSpace 1 1 0 := by
  constructor
  · rw [ordinaryLift_ordinaryResidualPath hq hm ν f hf u hu]
    exact cylinderResidual_solenoidal hq hm ν f u hdiv t
  · rw [map_sub, ordinaryLift_unprojectedResidual hk hkq ν f u hf hu,
      ordinaryLift_ordinaryResidualPath hq hm ν f hf u hu]
    exact residual_difference_gradient hq hk hkq hm ν f u t

open EulerQuadraticSource EulerVolterraConvolution EulerMeanSmoothRepresentative
open NSFormalization.Source NSFormalization.Source.OrdinaryCylinderDescent

open EulerLpTranslation EulerSmoothFieldSobolevTime

section Canonical
variable {f : A02.SpaceTimeField} {ν S : ℝ}
variable (hf : D01.MemForceR f) (hν : 0 < ν) (hS : 0 < S)
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


/-- Lane 194's order-zero datum is exactly lane 195's physical `A`, including
both endpoints. The force is the canonical force path; no agreement is assumed. -/
theorem residualDatum_jointRepresentative
    (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1))
    (t : Icc (0 : ℝ) S) :
    IsSobolevDatum 0
      (fun x => momentumResidualOfVelocity ν f (jointRepresentative U hpaths) (t.1, x))
      (ComplementPath.residualDatum hf hν hS a U hpairs t) := by
  have hs : ContDiff ℝ ∞ (fun x => jointRepresentative U hpaths (t.1, x)) := by
    rw [← contDiffOn_univ]
    exact (jointRepresentative_contDiffOn hS U hpaths).comp
      (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => ⟨t.2, mem_univ x⟩)
  simpa only [momentumResidualOfVelocity, add_comm] using
    ComplementPath.residualDatum_physicalSlice hf hν hS a U hpairs
      (jointRepresentative U hpaths) t hs (jointRepresentative_slice U hpaths t)

/-- The physical-datum uniqueness bridge now has its agreement discharged by
lane 194, with the same canonical force and the same joint velocity. -/
theorem physicalResidual_eq_residualDatum
    (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1))
    (t : Icc (0 : ℝ) S) (A : RealVectorSobolev 0)
    (hres : IsSobolevDatum 0
      (fun x => momentumResidualOfVelocity ν f (jointRepresentative U hpaths) (t.1, x)) A) :
    A = ComplementPath.residualDatum hf hν hS a U hpairs t := by
  exact isSobolevDatum_unique hres
    (residualDatum_jointRepresentative hf hν hS a U hpairs hpaths t)

/-- Canonical cylinder-to-Fourier bridge. The fixed carrier and physical datum
come from lane 194; the projected representative is supplied by lane 195's
proved time-derivative calculation, not by a Helmholtz hypothesis. -/
theorem hprojected_of_canonical_pairs {q m : ℕ} (hq : 6 ≤ q)
    (hm : m + 2 ≤ q + 1) (hm2 : 2 ≤ (m : ℝ))
    (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (_hdiv : ∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0)
    (hduh : ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 hq (sobolevPath (C01.forcePath (S := S) hf)
        (C01.forcePath_jetLp_continuous (S := S) hf) q))
      (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t)
    (B R : C(Icc (0 : ℝ) S, RealVectorSobolev (m : ℝ)))
    (hB : ∀ t, IsSobolevDatum (m : ℝ) (⇑(U t)) (B t))
    (hR : ∀ t, IsSobolevDatum (m : ℝ)
      (⇑(ordinaryResidualPath hq hm ν
        (sobolevPath (C01.forcePath (S := S) hf)
          (C01.forcePath_jetLp_continuous (S := S) hf) q) u t)) (R t)) :
    ∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S),
      lowerVectorL (m : ℝ) 0 (Nat.cast_nonneg m) (R ⟨t, ht.1.le, ht.2.le⟩) =
        ComplementPath.residualDatum hf hν hS a U hpairs ⟨t, ht.1.le, ht.2.le⟩ -
          Leray.lerayComplement 0
            (ComplementPath.residualDatum hf hν hS a U hpairs ⟨t, ht.1.le, ht.2.le⟩) := by
  let F := C01.forcePath (S := S) hf
  let hF := C01.forcePath_jetLp_continuous (S := S) hf
  let v := Classical.choose (hpairs 7 (by omega))
  obtain ⟨hvU, hvdiv, hvinv, hvduh⟩ := Classical.choose_spec (hpairs 7 (by omega))
  obtain ⟨B₇, R₇, hB₇, hR₇, _⟩ := exists_differentiable_datumPath
    (m := 2) (by omega : 6 ≤ 7) (by omega) hν hS a F hF v U hvinv hvU hvduh
  intro t ht
  let τ : Icc (0 : ℝ) S := ⟨t, ht.1.le, ht.2.le⟩
  let W := ComplementPath.residualCarrier hf hν hS a U hpairs
  let wp := ComplementPath.residualCarrier_paths hf hν hS a U hpairs
  let z := fun x => jointRepresentative W wp (t, x)
  let p := fun x => temporalDerivative (jointRepresentative U hpaths) t x
  have hzs : ContDiff ℝ ∞ z :=
    D01.contDiff_slice ((jointRepresentative_contDiffOn hS W wp).mono
      (prod_mono_left Ico_subset_Icc_self)) ⟨ht.1.le, ht.2⟩
  have hps : ContDiff ℝ ∞ p := by
    rw [← contDiffOn_univ]
    have hs := NavierStokes.ResidualRegularity.contDiffOn_temporalDerivative
      ((isOpen_Ioo : IsOpen (Ioo (0 : ℝ) S)).prod isOpen_univ)
      ((jointRepresentative_contDiffOn hS U hpaths).mono
        (prod_mono_left Ioo_subset_Icc_self))
    exact hs.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩)
  have hp₇ : (⇑(ordinaryResidualPath (m := 2) (by omega : 6 ≤ 7) (by omega)
      ν (sobolevPath F hF 7) v τ)) =ᵐ[volume] p := by
    have hae := vectorRepresentative_ae (by norm_num : 2 ≤ (2 : ℝ))
      (Lp.memLp (ordinaryResidualPath (m := 2) (by omega : 6 ≤ 7) (by omega)
        ν (sobolevPath F hF 7) v τ)) (hR₇ τ)
    filter_upwards [hae] with x hx
    exact hx.symm.trans (jointRepresentative_temporalDerivative_of_cylinder
      (m := 2) (by omega : 6 ≤ 7) (by omega) (by norm_num) hν hS
      (ordinarySobolev 8 a.toLp a.translation_contDiff) (sobolevPath F hF 7)
      v U hvU hvduh hpaths B₇ R₇ hB₇ hR₇ ht x).symm
  have hh := ordinaryResidual_helmholtz (m := 2) (by omega : 6 ≤ 7)
    (by omega : 6 ≤ 6) (by omega) (by omega) ν (sobolevPath F hF 7) v
    (fun θ t => sobolevPath_angle_invariant F hF θ t) hvinv hvdiv τ
  have he := lowered_projected_datum_of_cylinder
    (ordinaryResidualPath (m := 2) (by omega : 6 ≤ 7) (by omega) ν (sobolevPath F hF 7) v τ)
    (W τ) hh.1 hh.2 p z hps hzs hp₇ (jointRepresentative_slice W wp τ).symm
    (R₇ τ) (ComplementPath.residualDatum hf hν hS a U hpairs τ) (hR₇ τ)
    (ComplementPath.complementCarrier_identity W τ).1
  have hp : (⇑(ordinaryResidualPath hq hm ν (sobolevPath F hF q) u τ)) =ᵐ[volume] p := by
    have hae := vectorRepresentative_ae hm2
      (Lp.memLp (ordinaryResidualPath hq hm ν (sobolevPath F hF q) u τ)) (hR τ)
    filter_upwards [hae] with x hx
    exact hx.symm.trans (jointRepresentative_temporalDerivative_of_cylinder hq hm hm2 hν hS
      (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) (sobolevPath F hF q)
      u U hU hduh hpaths B R hB hR ht x).symm
  have heq := isSobolevDatum_unique
    (IsSobolevDatum.congr_field (Leray.isSobolevDatum_lower (Nat.cast_nonneg m) (hR τ)) hp)
    (IsSobolevDatum.congr_field (Leray.isSobolevDatum_lower (by norm_num : (0 : ℝ) ≤ 2) (hR₇ τ)) hp₇)
  exact heq.trans he

end Canonical
-- The fix6 prefix retains interface-only initial divergence and representative inputs.
set_option linter.unusedVariables false in
theorem hprojected_of_cylinder'' {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ}
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
          (C01.forcePath_jetLp_continuous (S := S) hf) q) (Classical.choose (hpairs q hq)) t)) (R t)) :
    ∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S),
      lowerVectorL (m : ℝ) 0 (Nat.cast_nonneg m) (R ⟨t, ht.1.le, ht.2.le⟩) =
        ComplementPath.residualDatum hf hν hS a U hpairs ⟨t, ht.1.le, ht.2.le⟩ -
          Leray.lerayComplement 0
            (ComplementPath.residualDatum hf hν hS a U hpairs ⟨t, ht.1.le, ht.2.le⟩) := by
  obtain ⟨hU, hdiv, _, hduh⟩ := Classical.choose_spec (hpairs q hq)
  exact hprojected_of_canonical_pairs hf hν hS a U hpairs hq hm hm2
    hpaths (Classical.choose (hpairs q hq)) hU hdiv hduh B R hB hR

end NSFormalization.Section4.A01
