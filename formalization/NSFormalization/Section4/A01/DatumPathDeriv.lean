import NSFormalization.Section4.A01.DatumPathContinuous
import NSFormalization.Section4.A01.DatumPathContinuity
import NSFormalization.Source.OrdinaryForcedTime
import NSFormalization.Source.ForcedCylinderInvariant
import Euler.InjectivePathDerivative
import Euler.SobolevLaplacian
import Euler.QuadraticSourceLimit

/-!
# A01 unit B1, time-regularity ladder R2

The exact forced Duhamel identity differentiates first in the cylinder `L²` carrier
(`Source.OrdinaryForcedTime.realization_hasDerivAt`).  Its right-hand side is

`ν Δu + P(F - (u · ∇)u)`,

where `P` is the cylinder Leray projector.  At every order `m ≤ q - 1`, two spatial
derivatives are available for `Δu`, so this residual is a continuous `H^m` cylinder
path.  Angle invariance descends it to ordinary `L²`, and the R1 quantitative datum
constructor supplies a continuous order-`m` residual datum path.

The crucial final lift does not assume a classical solution.  Order lowering
`lowerVectorL m 0` is injective; after lowering, both selected data are the canonical
order-zero Fourier data of their ordinary `L²` fields.  The ordinary Duhamel derivative
therefore lifts through this injective bounded map to a genuine `H^m`-datum derivative.

`exists_differentiable_datumPath` is the R2 deliverable.  It covers exactly
`m ≤ q - 1`, returns continuous velocity and projected-residual datum paths on the
closed interval, and proves the `HasDerivAt` equation at every interior time.
`residualDatum_is_timeDerivative` records the conditional physical identification
needed by R3: once a representative has this residual as its pointwise time derivative,
the same `R` is the datum of its physical `∂ₜ`.
-/

noncomputable section

namespace NSFormalization.Section4.A01

open Set MeasureTheory
open NSFormalization.Section4.D01
open NSFormalization.Section4.D01.Leray
open NSFormalization.Section4.A03 (lowerDatum coe_lowerDatum)
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Source NSFormalization.Source.RealSobolev
open NSFormalization.Source.ForcedCylinderLocal
open NSFormalization.Source.OrdinaryForcedTime
open NSFormalization.Source.OrdinaryCylinderDescent
open NavierStokes.ProblemStatement (Space)
open EulerLpTranslation EulerMeanOrdinaryLift EulerMeanSmoothRepresentative
  EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity EulerQuadraticSource
  EulerSmoothFieldSobolevTime EulerSobolevLaplacian EulerSobolevHeatGenerator
  EulerVolterraConvolution EulerQuadraticSourceLimit
  EulerInjectivePathDerivative
open scoped Topology ContDiff LineDeriv SchwartzMap

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

theorem lowerDatumL_injective (s r : ℝ) (hrs : r ≤ s) :
    Function.Injective (lowerDatumL s r hrs) := by
  intro A B h
  apply Subtype.ext
  apply NSFormalization.Paper3.angularRealization_injective s
  have h' := congrArg
    (fun Z : NSFormalization.Source.RealSobolev.RealSobolevHilbert r =>
      NSFormalization.Paper3.angularRealization r (Z : FourierData)) h
  change NSFormalization.Paper3.angularRealization r
      ((lowerDatum s r hrs A : _) : FourierData) =
    NSFormalization.Paper3.angularRealization r
      ((lowerDatum s r hrs B : _) : FourierData) at h'
  simpa only [coe_lowerDatum, NSFormalization.Paper3.angularRealization_orderLowering] using h'

theorem lowerVectorL_injective (s r : ℝ) (hrs : r ≤ s) :
    Function.Injective (lowerVectorL s r hrs) := by
  intro A B h
  apply PiLp.ext
  intro i
  apply lowerDatumL_injective s r hrs
  exact congrArg (fun Z : RealVectorSobolev r => Z i) h

/-- The nonlinear projected source, bundled as a continuous order-`q` path. -/
def cylinderSourcePath {q : ℕ} (hq : 6 ≤ q) {S : ℝ}
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))) :
    C(Icc (0 : ℝ) S, SobolevSpace 1 q) :=
  sourcePath ((coefficients 1 hq f).comp (timeInclusion (le_refl S))) u

/-- The projected momentum residual is continuous in every available order. -/
def cylinderResidualPath {q m : ℕ} (hq : 6 ≤ q) (hm : m + 2 ≤ q + 1)
    (ν : ℝ) {S : ℝ} (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))) :
    C(Icc (0 : ℝ) S, SobolevSpace 1 m) :=
  ν • (laplacianOperator 1 m).compLeftContinuous ℝ _
      ((restrictOperator 1 hm).compLeftContinuous ℝ _ u) +
    (restrictOperator 1 (by omega : m ≤ q)).compLeftContinuous ℝ _
      (cylinderSourcePath hq f u)

/-- The order-`m` cylinder right-hand side of the projected momentum equation. -/
abbrev cylinderResidual {q m : ℕ} (hq : 6 ≤ q) (hm : m + 2 ≤ q + 1)
    (ν : ℝ) {S : ℝ} (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (t : Icc (0 : ℝ) S) : SobolevSpace 1 m :=
  cylinderResidualPath hq hm ν f u t

theorem cylinderResidual_value {q m : ℕ} (hq : 6 ≤ q) (hm : m + 2 ≤ q + 1)
    (ν : ℝ) {S : ℝ} (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (t : Icc (0 : ℝ) S) :
    value 1 (cylinderResidual hq hm ν f u t) =
      ν • laplacianEvaluation 1 (q + 1) (by omega) (u t) +
        value 1 ((coefficients 1 hq f).apply (timeInclusion (le_refl S) t) (u t)) := by
  change (valueOperator 1 m)
      (ν • laplacianOperator 1 m (restrictOperator 1 hm (u t)) +
        restrictOperator 1 (by omega : m ≤ q)
          ((coefficients 1 hq f).apply (timeInclusion (le_refl S) t) (u t))) = _
  rw [map_add, map_smul]
  have hlap := laplacianOperator_value 1 (restrictOperator 1 hm (u t))
  change (valueOperator 1 m) (laplacianOperator 1 m (restrictOperator 1 hm (u t))) = _ at hlap
  rw [hlap]
  have hsource := value_restrictOperator 1 (by omega : m ≤ q)
    ((coefficients 1 hq f).apply (timeInclusion (le_refl S) t) (u t))
  change (valueOperator 1 m)
      (restrictOperator 1 (by omega : m ≤ q)
        ((coefficients 1 hq f).apply (timeInclusion (le_refl S) t) (u t))) = _ at hsource
  rw [hsource]
  rfl

theorem laplacianOperator_translation_local {m : ℕ} (a : LiftDomain 1)
    (v : SobolevSpace 1 (m + 2)) :
    sobolevTranslation 1 m a (laplacianOperator 1 m v) =
      laplacianOperator 1 m (sobolevTranslation 1 (m + 2) a v) := by
  rw [laplacianOperator_apply, map_sum, laplacianOperator_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [derivativeOperator_translation, derivativeOperator_translation]

-- The two dependent Sobolev restriction rewrites need extra elaboration budget.
set_option maxHeartbeats 400000 in
theorem cylinderResidual_invariant {q m : ℕ} (hq : 6 ≤ q)
    (hm : m + 2 ≤ q + 1) (ν : ℝ) {S : ℝ}
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (hf : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 q (0, θ) (f t) = f t)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (θ : AddCircle (1 : ℝ)) (t : Icc (0 : ℝ) S) :
    sobolevTranslation 1 m (0, θ) (cylinderResidual hq hm ν f u t) =
      cylinderResidual hq hm ν f u t := by
  have hu' : sobolevTranslation 1 (m + 2) (0, θ) (restrictOperator 1 hm (u t)) =
      restrictOperator 1 hm (u t) := by
    rw [← restrictOperator_translation, hu θ t]
  have hs := source_translation 1 hq f (0, θ) (hf θ)
    (timeInclusion (le_refl S) t) (u t)
  rw [hu θ t] at hs
  let z : SobolevSpace 1 m := restrictOperator 1 (by omega : m ≤ q)
    ((coefficients 1 hq f).apply (timeInclusion (le_refl S) t) (u t))
  have hs' : sobolevTranslation 1 m (0, θ) z = z := by
    dsimp only [z]
    rw [← restrictOperator_translation, ← hs]
  change sobolevTranslation 1 m (0, θ)
      (ν • laplacianOperator 1 m (restrictOperator 1 hm (u t)) +
        z) =
    ν • laplacianOperator 1 m (restrictOperator 1 hm (u t)) +
      z
  rw [map_add, map_smul]
  rw [laplacianOperator_translation_local]
  rw [hu']
  rw [hs']

/-- The ordinary residual is the adjoint descent of the cylinder residual. -/
def ordinaryResidualPath {q m : ℕ} (hq : 6 ≤ q) (hm : m + 2 ≤ q + 1)
    (ν : ℝ) {S : ℝ} (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))) :
    C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2) :=
  ordinaryLift.toContinuousLinearMap.adjoint.compLeftContinuous ℝ _
    ((valueOperator 1 m).compLeftContinuous ℝ _ (cylinderResidualPath hq hm ν f u))

theorem ordinaryResidualPath_eq_ordinaryDerivative {q m : ℕ} (hq : 6 ≤ q)
    (hm : m + 2 ≤ q + 1) (ν : ℝ) {S : ℝ}
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))) (t : Icc (0 : ℝ) S) :
    ordinaryResidualPath hq hm ν f u t =
      ordinaryDerivative hq ν (le_refl S) f u t := by
  change ordinaryLift.toContinuousLinearMap.adjoint
      (value 1 (cylinderResidual hq hm ν f u t)) =
    ordinaryLift.toContinuousLinearMap.adjoint
      (ν • laplacianEvaluation 1 (q + 1) (by omega) (u t) +
        value 1 ((coefficients 1 hq f).apply (timeInclusion (le_refl S) t) (u t)))
  rw [cylinderResidual_value]

/-- The adjoint of `ordinaryLift` is an actual inverse on the invariant subspace. -/
theorem ordinaryLift_adjoint_of_invariant (g : LiftL2 1)
    (hg : ∀ θ : AddCircle (1 : ℝ), translation 1 (0, θ) g = g) :
    ordinaryLift (ordinaryLift.toContinuousLinearMap.adjoint g) = g := by
  obtain ⟨G, hG⟩ := exists_ordinaryLift_of_invariant g hg
  rw [← hG]
  have h := congrArg
    (fun L : EulerMeanSolenoidal.L2 →L[ℝ] EulerMeanSolenoidal.L2 => L G)
    ordinaryLift.adjoint_comp_self
  exact congrArg ordinaryLift h

/-- The ordinary residual really lifts to the full cylinder residual. -/
theorem ordinaryLift_ordinaryResidualPath {q m : ℕ} (hq : 6 ≤ q)
    (hm : m + 2 ≤ q + 1) (ν : ℝ) {S : ℝ}
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (hf : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 q (0, θ) (f t) = f t)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (t : Icc (0 : ℝ) S) :
    ordinaryLift (ordinaryResidualPath hq hm ν f u t) =
      value 1 (cylinderResidual hq hm ν f u t) := by
  change ordinaryLift (ordinaryLift.toContinuousLinearMap.adjoint
      (value 1 (cylinderResidual hq hm ν f u t))) = _
  apply ordinaryLift_adjoint_of_invariant
  intro θ
  have h := congrArg (value 1) (cylinderResidual_invariant hq hm ν f hf u hu θ t)
  simpa only [translation_value] using h

/-- The cylinder force made from ordinary smooth slices is angle-independent. -/
theorem sobolevPath_angle_invariant {q : ℕ} {S : ℝ}
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (θ : AddCircle (1 : ℝ)) (t : Icc (0 : ℝ) S) :
    sobolevTranslation 1 q (0, θ) (sobolevPath F hF q t) = sobolevPath F hF q t := by
  exact ordinarySobolev_angle q (F t).toLp (F t).translation_contDiff θ

/-- The exact projected residual from `Horizon`: `νΔu + P(F - (u·∇)u)`,
as a continuous order-`m` cylinder path. -/
def projectedResidualPath {q m : ℕ} (hq : 6 ≤ q) (hm : m ≤ q - 1)
    (ν : ℝ) {S : ℝ} (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))) :
    C(Icc (0 : ℝ) S, SobolevSpace 1 m) :=
  cylinderResidualPath hq (by omega) ν (sobolevPath F hF q) u

/-- The ordinary `L²` descent of `projectedResidualPath`. -/
def projectedResidualOrdinaryPath {q m : ℕ} (hq : 6 ≤ q) (hm : m ≤ q - 1)
    (ν : ℝ) {S : ℝ} (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))) :
    C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2) :=
  ordinaryResidualPath (m := m) hq (by omega) ν (sobolevPath F hF q) u

/-- The displayed formula for the residual is literally the Leray-projected source
plus the viscous Laplacian. -/
theorem projectedResidualPath_eq {q m : ℕ} (hq : 6 ≤ q) (hm : m ≤ q - 1)
    (ν : ℝ) {S : ℝ} (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))) (t : Icc (0 : ℝ) S) :
    projectedResidualPath hq hm ν F hF u t =
      ν • laplacianOperator 1 m (restrictOperator 1 (by omega) (u t)) +
        restrictOperator 1 (by omega : m ≤ q)
          (leray 1 q (sobolevPath F hF q t - advection 1 hq (u t) (u t))) := by
  change ν • laplacianOperator 1 m (restrictOperator 1 (by omega) (u t)) +
      restrictOperator 1 (by omega : m ≤ q)
        ((coefficients 1 hq (sobolevPath F hF q)).apply
          (timeInclusion (le_refl S) t) (u t)) = _
  have ht : timeInclusion (le_refl S) t = t := Subtype.ext rfl
  have hs := source_eq 1 hq (sobolevPath F hF q)
    (timeInclusion (le_refl S) t) (u t)
  rw [ht] at hs
  exact congrArg (fun z => ν • laplacianOperator 1 m
    (restrictOperator 1 (by omega) (u t)) + restrictOperator 1 (by omega : m ≤ q) z) hs

/-- The ordinary residual lifts to the exact projected cylinder residual at every
time, including both endpoints. -/
theorem ordinaryLift_projectedResidualOrdinaryPath {q m : ℕ}
    (hq : 6 ≤ q) (hm : m ≤ q - 1) (ν : ℝ) {S : ℝ}
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (t : Icc (0 : ℝ) S) :
    ordinaryLift (projectedResidualOrdinaryPath hq hm ν F hF u t) =
      value 1 (projectedResidualPath hq hm ν F hF u t) := by
  change ordinaryLift (ordinaryResidualPath (m := m) hq (by omega) ν
      (sobolevPath F hF q) u t) =
    value 1 (cylinderResidual hq (by omega) ν (sobolevPath F hF q) u t)
  exact ordinaryLift_ordinaryResidualPath hq (by omega) ν (sobolevPath F hF q)
    (fun θ s => sobolevPath_angle_invariant F hF θ s) u hu t

/-- Quantitative weak derivatives for an invariant cylinder field at any finite order. -/
theorem weakDerivsBound_cylinder {p : ℕ} (u : SobolevSpace 1 p)
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 p (0, θ) u = u)
    (U : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    (m : ℕ) (hm : m ≤ p) : HasWeakDerivsL2Bound (⇑U) (‖u‖ ^ 2) m := by
  exact weakDerivsBound_word_top u hu m 0 (Nat.zero_le _) (by simpa using hm) Fin.elim0 U hU

/-- The datum-increment estimate without the historical `q+1` presentation. -/
theorem datum_sub_norm_sq_le_general {p m : ℕ} (hm : m ≤ p)
    (u v : SobolevSpace 1 p)
    (hu : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 p (0, θ) u = u)
    (hv : ∀ θ : AddCircle (1 : ℝ), sobolevTranslation 1 p (0, θ) v = v)
    (U V : EulerMeanSolenoidal.L2) (hU : ordinaryLift U = value 1 u)
    (hV : ordinaryLift V = value 1 v)
    (A B : RealVectorSobolev (m : ℝ))
    (hA : IsSobolevDatum (m : ℝ) (⇑U) A) (hB : IsSobolevDatum (m : ℝ) (⇑V) B) :
    ‖A - B‖ ^ 2 ≤ (4 : ℝ) ^ m * ‖u - v‖ ^ 2 := by
  have hinv : ∀ θ : AddCircle (1 : ℝ),
      sobolevTranslation 1 p (0, θ) (u - v) = u - v := by
    intro θ
    rw [map_sub, hu θ, hv θ]
  have hlift : ordinaryLift (U - V) = value 1 (u - v) := by
    rw [map_sub, hU, hV]
    rfl
  have hd := D01.isSobolevDatum_sub
    (schwartzPairable_of_memLp (fun i => memLp_component (Lp.memLp U) i))
    (schwartzPairable_of_memLp (fun i => memLp_component (Lp.memLp V) i)) hA hB
  have hd' : IsSobolevDatum (m : ℝ) (⇑(U - V)) (A - B) :=
    IsSobolevDatum.congr_field hd (Lp.coeFn_sub U V).symm
  exact norm_isSobolevDatum_le_of_memLp_derivs_sharp m _ _
    (weakDerivsBound_cylinder (u - v) hinv (U - V) hlift m hm) (A - B) hd'

/-- A continuous datum selection from an invariant cylinder path, at any available order. -/
theorem exists_continuous_datumPath_general {p m : ℕ} {S : ℝ}
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 p))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 p (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t)) (hm : m ≤ p) :
    ∃ A : Icc (0 : ℝ) S → RealVectorSobolev (m : ℝ),
      (∀ t, IsSobolevDatum (m : ℝ) (⇑(U t)) (A t)) ∧ Continuous A := by
  choose A hA hbound using fun t => exists_isSobolevDatum_norm_le_sharp m _ _
    (weakDerivsBound_cylinder (u t) (fun θ => hu θ t) (U t) (hU t) m hm)
  refine ⟨A, hA, continuous_iff_continuousAt.mpr (fun t => ?_)⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ s, ‖A s - A t‖ ≤ (2 : ℝ) ^ m * ‖u s - u t‖ := by
    intro s
    have h := datum_sub_norm_sq_le_general hm (u s) (u t) (fun θ => hu θ s)
      (fun θ => hu θ t) (U s) (U t) (hU s) (hU t) (A s) (A t) (hA s) (hA t)
    have hp : ((2 : ℝ) ^ m) ^ 2 = (4 : ℝ) ^ m := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    have hs : ‖A s - A t‖ ^ 2 ≤ ((2 : ℝ) ^ m * ‖u s - u t‖) ^ 2 := by
      simpa only [mul_pow, hp] using h
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hs
  have ht : Filter.Tendsto (fun s => (2 : ℝ) ^ m * ‖u s - u t‖)
      (nhds t) (nhds 0) := by
    simpa using (((u.continuous.continuousAt (x := t)).sub
      (continuousAt_const (y := u t))).norm.tendsto.const_mul ((2 : ℝ) ^ m))
  exact squeeze_zero (fun s => norm_nonneg _) hb ht

/-- R2, in reusable form: any continuous velocity/residual datum selections obey the
time derivative equation forced by the Duhamel identity. -/
theorem datumPath_hasDerivAt {q m : ℕ} (hq : 6 ≤ q) (hm : m + 2 ≤ q + 1)
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (u₀ : SobolevSpace 1 (q + 1))
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hduh : ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 hq f) u₀ u t)
    (A R : C(Icc (0 : ℝ) S, RealVectorSobolev (m : ℝ)))
    (hA : ∀ t, IsSobolevDatum (m : ℝ) (⇑(U t)) (A t))
    (hR : ∀ t, IsSobolevDatum (m : ℝ)
      (⇑(ordinaryResidualPath hq hm ν f u t)) (R t)) :
    ∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S),
      HasDerivAt (extendPath S hS.le A) (R ⟨t, ht.1.le, ht.2.le⟩) t := by
  have h0m : (0 : ℝ) ≤ (m : ℝ) := by positivity
  let L := lowerVectorL (m : ℝ) 0 h0m
  have hLA : ∀ s : Icc (0 : ℝ) S, L (A s) = orderZeroDatumCLM (U s) := by
    intro s
    apply isSobolevDatum_unique
    · exact Leray.isSobolevDatum_lower h0m (hA s)
    · rw [← orderZeroDatum_memLp_eq]
      exact isSobolevDatum_zero_ordinaryL2 (U s)
  have hLR : ∀ s : Icc (0 : ℝ) S,
      L (R s) = orderZeroDatumCLM (ordinaryResidualPath hq hm ν f u s) := by
    intro s
    apply isSobolevDatum_unique
    · exact Leray.isSobolevDatum_lower h0m (hR s)
    · rw [← orderZeroDatum_memLp_eq]
      exact isSobolevDatum_zero_ordinaryL2 (ordinaryResidualPath hq hm ν f u s)
  have hdweak : ∀ t ∈ Ioo (0 : ℝ) S,
      HasDerivAt (fun r => L (extendPath S hS.le A r))
        (L (extendPath S hS.le R t)) t := by
    intro t ht
    have hdU := realization_hasDerivAt hq hν hS.le le_rfl u₀ f u U hU hduh t ht
    rw [← ordinaryResidualPath_eq_ordinaryDerivative hq hm ν f u
      ⟨t, ht.1.le, ht.2.le⟩] at hdU
    have hd0 := orderZeroDatumCLM.hasFDerivAt.comp_hasDerivAt t hdU
    have hfun : (fun r => L (extendPath S hS.le A r)) =
        fun r => orderZeroDatumCLM (extendPath S hS.le U r) := by
      funext r
      exact hLA (projIcc 0 S hS.le r)
    have hval : L (extendPath S hS.le R t) =
        orderZeroDatumCLM (ordinaryResidualPath hq hm ν f u ⟨t, ht.1.le, ht.2.le⟩) := by
      change L (R (projIcc 0 S hS.le t)) = _
      rw [projIcc_of_mem hS.le ⟨ht.1.le, ht.2.le⟩]
      exact hLR ⟨t, ht.1.le, ht.2.le⟩
    rw [hfun, hval]
    exact hd0
  intro t ht
  have hd := hasDerivAt_of_injective_map L
    (lowerVectorL_injective (m : ℝ) 0 h0m) S hS.le A R hdweak t ht
  simpa only [extendPath, projIcc_of_mem hS.le ⟨ht.1.le, ht.2.le⟩] using hd

/-- R2 at the exact `Horizon` force path, for every `m ≤ q-1`.  Both the velocity
datum path and the projected-residual datum path are continuous on the closed interval. -/
theorem exists_differentiable_datumPath {q m : ℕ} (hq : 6 ≤ q) (hm : m ≤ q - 1)
    {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hduh : ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 hq (sobolevPath F hF q))
      (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) u t) :
    ∃ A R : C(Icc (0 : ℝ) S, RealVectorSobolev (m : ℝ)),
      (∀ t, IsSobolevDatum (m : ℝ) (⇑(U t)) (A t)) ∧
      (∀ t, IsSobolevDatum (m : ℝ)
        (⇑(projectedResidualOrdinaryPath hq hm ν F hF u t)) (R t)) ∧
      ∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S),
        HasDerivAt (extendPath S hS.le A) (R ⟨t, ht.1.le, ht.2.le⟩) t := by
  have hm' : m + 2 ≤ q + 1 := by omega
  obtain ⟨A, hA, hAc⟩ := exists_continuous_datumPath u U hu hU m (by omega)
  let f := sobolevPath F hF q
  let V := cylinderResidualPath hq hm' ν f u
  let D := ordinaryResidualPath hq hm' ν f u
  have hf : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 q (0, θ) (f t) = f t :=
    fun θ t => sobolevPath_angle_invariant F hF θ t
  have hV : ∀ (θ : AddCircle (1 : ℝ)) t, sobolevTranslation 1 m (0, θ) (V t) = V t :=
    fun θ t => cylinderResidual_invariant hq hm' ν f hf u hu θ t
  have hD : ∀ t, ordinaryLift (D t) = value 1 (V t) :=
    fun t => ordinaryLift_ordinaryResidualPath hq hm' ν f hf u hu t
  obtain ⟨R, hR, hRc⟩ := exists_continuous_datumPath_general V D hV hD (le_refl m)
  let Ac : C(Icc (0 : ℝ) S, RealVectorSobolev (m : ℝ)) := ⟨A, hAc⟩
  let Rc : C(Icc (0 : ℝ) S, RealVectorSobolev (m : ℝ)) := ⟨R, hRc⟩
  refine ⟨Ac, Rc, hA, ?_, ?_⟩
  · exact hR
  · exact datumPath_hasDerivAt hq hm' hν hS
      (ordinarySobolev (q + 1) a.toLp a.translation_contDiff) f u U hU hduh Ac Rc hA hR

/-- Conditional identification for R3: once a representative has the ordinary residual
as its pointwise time derivative, the R2 derivative datum is its physical `∂ₜ` datum. -/
theorem residualDatum_is_timeDerivative {q m : ℕ} (hq : 6 ≤ q)
    (hm : m + 2 ≤ q + 1) (ν : ℝ) {S : ℝ}
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (R : C(Icc (0 : ℝ) S, RealVectorSobolev (m : ℝ)))
    (hR : ∀ t, IsSobolevDatum (m : ℝ)
      (⇑(ordinaryResidualPath hq hm ν f u t)) (R t))
    (v : ℝ × Space → Space) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S)
    (hd : ∀ x : Space, HasDerivAt (fun r => v (r, x))
      ((ordinaryResidualPath hq hm ν f u ⟨t, ht⟩ : EulerMeanSolenoidal.L2) x) t) :
    IsSobolevDatum (m : ℝ) (fun x => deriv (fun r => v (r, x)) t) (R ⟨t, ht⟩) := by
  apply IsSobolevDatum.congr_field (hR ⟨t, ht⟩)
  filter_upwards with x
  exact (hd x).deriv.symm

end NSFormalization.Section4.A01
