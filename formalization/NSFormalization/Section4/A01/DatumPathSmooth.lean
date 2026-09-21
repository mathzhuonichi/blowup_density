import NSFormalization.Section4.A01.DatumPathDeriv
import Euler.AsymmetricTransport
import Euler.SobolevNonlinearCompatibility
import Euler.InjectivePathDerivativeWithin
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# A01 unit B1, time-regularity ladder R3

This module bootstraps the forced cylinder equation in time.  At target order `k ≥ 6`,
the projected residual is a smooth expression of the order-`k+2` velocity, the order-`k`
force, and the bounded bilinear order-`k` advection.  Consequently every time derivative
costs two spatial orders.  The result is then transported to the unique angular datum of
the ordinary slice.

The finite carrier supplied by `Horizon` has order `q+1`.  The current all-`j`
implementation closes the range `max 6 m + 2*j ≤ q+1`; the order-six floor comes from
forming every differentiated residual at one fixed cylinder order and is not asserted to
be the sharp mathematical range when `m < 6`.  The extra hypothesis `hfs` records the
genuinely necessary time-smoothness of the cylinder force path; `Horizon.hF` alone states
only continuity of spatial jets and cannot imply even a second time derivative.
-/

noncomputable section

namespace NSFormalization.Section4.A01

open Set MeasureTheory
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Source NSFormalization.Source.RealSobolev
open NSFormalization.Source.ForcedCylinderLocal
open NSFormalization.Source.OrdinaryCylinderDescent
open NavierStokes.ProblemStatement (Space)
open EulerLpTranslation EulerMeanOrdinaryLift EulerMeanSmoothRepresentative
  EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerCylinderSobolev
  EulerPressureSpatialRegularity EulerQuadraticSource EulerSobolevTransport
  EulerAsymmetricTransport EulerSobolevNonlinearCompatibility
  EulerSobolevLaplacian EulerVolterraConvolution EulerInjectivePathDerivative
open scoped Topology ContDiff LineDeriv SchwartzMap

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-! ## Restriction-compatible forms of the fixed cylinder operators -/

/-- Restrict a continuous cylinder Sobolev path to a lower order. -/
def restrictPath {p k : ℕ} (hkp : k ≤ p) {S : ℝ}
    (v : C(Icc (0 : ℝ) S, SobolevSpace 1 p)) :
    C(Icc (0 : ℝ) S, SobolevSpace 1 k) :=
  (restrictOperator 1 hkp).compLeftContinuous ℝ _ v

@[simp] theorem restrictPath_apply {p k : ℕ} (hkp : k ≤ p) {S : ℝ}
    (v : C(Icc (0 : ℝ) S, SobolevSpace 1 p)) (t : Icc (0 : ℝ) S) :
    restrictPath hkp v t = restrictOperator 1 hkp (v t) := rfl

/-- Leray projection commutes with restriction in the fixed unit-cylinder scale. -/
theorem restrict_leray {p k : ℕ} (hkp : k ≤ p) (v : SobolevSpace 1 p) :
    restrictOperator 1 hkp (leray 1 p v) = leray 1 k (restrictOperator 1 hkp v) := by
  apply value_injective 1
  simp only [value_restrictOperator, leray_value]

-- The dependent restriction identities in the vendor compatibility theorem need extra elaboration.
set_option maxHeartbeats 400000 in
/-- The literal advection is the same operator after restriction to any lower algebra
level.  The lower level is required to be at least six, exactly as in the vendor's
complete Sobolev product. -/
theorem restrict_advection {q k : ℕ} (hq : 6 ≤ q) (hk : 6 ≤ k) (hkq : k ≤ q)
    (u v : SobolevSpace 1 (q + 1)) :
    restrictOperator 1 hkq (advection 1 hq u v) =
      advection 1 hk (restrictOperator 1 (by omega : k + 1 ≤ q + 1) u)
        (restrictOperator 1 (by omega : k + 1 ≤ q + 1) v) := by
  apply value_injective 1
  simp only [value_restrictOperator, advection, transportBilinear_value]
  apply Finset.sum_congr rfl
  intro i _
  have hc : value 1 (truncateOperator 1 q u) =
      value 1 (truncateOperator 1 k
        (restrictOperator 1 (by omega : k + 1 ≤ q + 1) u)) := rfl
  have hd : value 1 (derivativeOperator 1 q i v) =
      value 1 (derivativeOperator 1 k i
        (restrictOperator 1 (by omega : k + 1 ≤ q + 1) v)) := rfl
  rw [← hd]
  exact EulerSobolevL2Product.scalarProduct_of_value_eq 1 (by omega : 3 ≤ q)
    (by omega : 3 ≤ k) _ _ _ hc _

/-! ## The residual at its natural target order -/

/-- The quadratic advection path formed after restriction to the target algebra level. -/
def reducedAdvectionPath {q k : ℕ} (hk : 6 ≤ k) (hkq : k + 1 ≤ q + 1) {S : ℝ}
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))) :
    C(Icc (0 : ℝ) S, SobolevSpace 1 k) :=
  ⟨fun t => advection 1 hk (restrictOperator 1 hkq (u t))
      (restrictOperator 1 hkq (u t)),
    (((advection 1 hk).continuous.comp
      ((restrictOperator 1 hkq).continuous.comp u.continuous)).clm_apply
        ((restrictOperator 1 hkq).continuous.comp u.continuous))⟩

/-- The projected residual written entirely at its target Sobolev order `k`. -/
def reducedResidualPath {q k : ℕ} (_hq : 6 ≤ q) (hk : 6 ≤ k)
    (hkq : k + 2 ≤ q + 1) (ν : ℝ) {S : ℝ}
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))) :
    C(Icc (0 : ℝ) S, SobolevSpace 1 k) :=
  ν • (laplacianOperator 1 k).compLeftContinuous ℝ _
      (restrictPath (by omega : k + 2 ≤ q + 1) u) +
    (leray 1 k).compLeftContinuous ℝ _
      (restrictPath (by omega : k ≤ q) f -
        reducedAdvectionPath hk (by omega : k + 1 ≤ q + 1) u)

-- Normalizing the two dependent Sobolev restriction proofs requires extra elaboration.
set_option maxHeartbeats 400000 in
/-- The target-order formula is exactly R2's cylinder residual, not a new equation. -/
theorem reducedResidualPath_eq {q k : ℕ} (hq : 6 ≤ q) (hk : 6 ≤ k)
    (hkq : k + 2 ≤ q + 1) (ν : ℝ) {S : ℝ}
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (t : Icc (0 : ℝ) S) :
    reducedResidualPath hq hk hkq ν f u t = cylinderResidualPath hq hkq ν f u t := by
  change ν • laplacianOperator 1 k (restrictOperator 1 hkq (u t)) +
      leray 1 k (restrictOperator 1 (by omega : k ≤ q) (f t) -
        advection 1 hk (restrictOperator 1 (by omega : k + 1 ≤ q + 1) (u t))
          (restrictOperator 1 (by omega : k + 1 ≤ q + 1) (u t))) = _
  change _ = ν • laplacianOperator 1 k (restrictOperator 1 hkq (u t)) +
      restrictOperator 1 (by omega : k ≤ q)
        ((coefficients 1 hq f).apply (timeInclusion (le_refl S) t) (u t))
  have ht : timeInclusion (le_refl S) t = t := Subtype.ext rfl
  have hs : restrictOperator 1 (by omega : k ≤ q)
        ((coefficients 1 hq f).apply (timeInclusion (le_refl S) t) (u t)) =
      leray 1 k (restrictOperator 1 (by omega : k ≤ q) (f t) -
        advection 1 hk (restrictOperator 1 (by omega : k + 1 ≤ q + 1) (u t))
          (restrictOperator 1 (by omega : k + 1 ≤ q + 1) (u t))) := by
    have hs0 := source_eq 1 hq f (timeInclusion (le_refl S) t) (u t)
    rw [ht] at hs0
    have happ : (coefficients 1 hq f).apply (timeInclusion (le_refl S) t) (u t) =
        (coefficients 1 hq f).apply t (u t) :=
      congrArg (fun s => (coefficients 1 hq f).apply s (u t)) ht
    calc
      restrictOperator 1 (by omega : k ≤ q)
          ((coefficients 1 hq f).apply (timeInclusion (le_refl S) t) (u t)) =
          restrictOperator 1 (by omega : k ≤ q)
            ((coefficients 1 hq f).apply t (u t)) := congrArg _ happ
      _ = restrictOperator 1 (by omega : k ≤ q)
          (leray 1 q (f t - advection 1 hq (u t) (u t))) := congrArg _ hs0
      _ =
          leray 1 k (restrictOperator 1 (by omega : k ≤ q)
            (f t - advection 1 hq (u t) (u t))) := restrict_leray _ _
      _ = leray 1 k (restrictOperator 1 (by omega : k ≤ q) (f t) -
            restrictOperator 1 (by omega : k ≤ q) (advection 1 hq (u t) (u t))) := by
          rw [map_sub]
      _ = _ := by
        have ha := restrict_advection hq hk (by omega : k ≤ q) (u t) (u t)
        exact congrArg (fun z : SobolevSpace 1 k =>
          leray 1 k (restrictOperator 1 (by omega : k ≤ q) (f t) - z)) ha
  exact congrArg (fun z : SobolevSpace 1 k =>
    ν • laplacianOperator 1 k (restrictOperator 1 hkq (u t)) + z) hs.symm

/-! ## The strong finite-order cylinder equation -/

/-- The mild equation has its genuine closed-interval within derivative in every order
`k ≤ q-1`.  This is the cylinder analogue of R2's datum derivative, upgraded to the
endpoints by the continuous right-hand side and injectivity of `valueOperator`. -/
theorem cylinderVelocity_hasDerivWithinAt {q k : ℕ} (hq : 6 ≤ q)
    (hkq : k + 2 ≤ q + 1) {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (u₀ : SobolevSpace 1 (q + 1))
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (hduh : ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 hq f) u₀ u t)
    (t : Icc (0 : ℝ) S) :
    HasDerivWithinAt (extendPath S hS.le (restrictPath (by omega : k ≤ q + 1) u))
      (cylinderResidualPath hq hkq ν f u t) (Icc (0 : ℝ) S) t := by
  apply hasDerivWithinAt_of_injective_map (valueOperator 1 k) (value_injective 1)
    S hS.le (restrictPath (by omega : k ≤ q + 1) u)
      (cylinderResidualPath hq hkq ν f u)
  intro r hr
  have hd := EulerMildEquationBridge.viscous_mild_hasDerivAt 1 (by omega : 2 ≤ q)
    ν hν S hS.le u₀ (coefficients 1 hq f).apply
      (coefficients 1 hq f).continuous u hduh r hr
  change HasDerivAt
    (fun s => value 1 (restrictOperator 1 (by omega : k ≤ q + 1)
      (u (projIcc 0 S hS.le s))))
    (value 1 (cylinderResidual hq hkq ν f u (projIcc 0 S hS.le r))) r
  rw [projIcc_of_mem hS.le ⟨hr.1.le, hr.2.le⟩]
  have hval := cylinderResidual_value hq hkq ν f u
    (⟨r, hr.1.le, hr.2.le⟩ : Icc (0 : ℝ) S)
  rw [hval]
  convert hd using 1
  · funext s
    rfl
  · rfl

/-! ## Smoothness of the target-order residual and the parabolic bootstrap -/

/-- Smooth higher-order velocity paths and a smooth force make the reduced residual smooth.
The two velocity inputs are separated because the Laplacian reads order `k+2`, while the
bilinear advection reads order `k+1`. -/
theorem reducedResidualPath_contDiffOn {q k n : ℕ} (hq : 6 ≤ q) (hk : 6 ≤ k)
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
    ContDiffOn ℝ n (extendPath S hS.le (reducedResidualPath hq hk hkq ν f u))
      (Icc (0 : ℝ) S) := by
  have hlap : ContDiffOn ℝ n
      (fun t => ν • laplacianOperator 1 k
        (extendPath S hS.le (restrictPath (by omega : k + 2 ≤ q + 1) u) t))
      (Icc (0 : ℝ) S) :=
    ((laplacianOperator 1 k).contDiff.comp_contDiffOn hu₂).const_smul ν
  have hadv : ContDiffOn ℝ n
      (fun t => advection 1 hk
        (extendPath S hS.le (restrictPath (by omega : k + 1 ≤ q + 1) u) t)
        (extendPath S hS.le (restrictPath (by omega : k + 1 ≤ q + 1) u) t))
      (Icc (0 : ℝ) S) :=
    (((advection 1 hk).contDiff.comp_contDiffOn hu₁).clm_apply hu₁)
  have hsource : ContDiffOn ℝ n
      (fun t => leray 1 k
        (extendPath S hS.le (restrictPath (by omega : k ≤ q) f) t -
          advection 1 hk
            (extendPath S hS.le (restrictPath (by omega : k + 1 ≤ q + 1) u) t)
            (extendPath S hS.le (restrictPath (by omega : k + 1 ≤ q + 1) u) t)))
      (Icc (0 : ℝ) S) :=
    (leray 1 k).contDiff.comp_contDiffOn (hf.sub hadv)
  apply (hlap.add hsource).congr
  intro t ht
  rfl

-- The induction normalizes several dependent Sobolev restriction witnesses.
set_option maxHeartbeats 400000 in
/-- R3 at cylinder level: on a finite order-`q+1` carrier, the velocity is `C^j`
at every algebra order `k ≥ 6` satisfying `k + 2*j ≤ q+1`. -/
theorem cylinderPath_contDiffOn {q k j : ℕ} (hq : 6 ≤ q) (hk : 6 ≤ k)
    (hkj : k + 2 * j ≤ q + 1) {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (u₀ : SobolevSpace 1 (q + 1))
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (hfs : ContDiffOn ℝ ∞ (extendPath S hS.le f) (Icc (0 : ℝ) S))
    (hduh : ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 hq f) u₀ u t) :
    ContDiffOn ℝ j (extendPath S hS.le (restrictPath (by omega : k ≤ q + 1) u))
      (Icc (0 : ℝ) S) := by
  induction j generalizing k with
  | zero =>
      exact contDiffOn_zero.mpr (extendPath_continuous S hS.le
        (restrictPath (by omega : k ≤ q + 1) u)).continuousOn
  | succ j ih =>
      have hkj' : k + 2 + 2 * j ≤ q + 1 := by omega
      have hu₂ := ih (k := k + 2) (by omega) hkj'
      have hu₁full := ih (k := k + 1) (by omega) (by omega : k + 1 + 2 * j ≤ q + 1)
      have hu₁ : ContDiffOn ℝ j
          (extendPath S hS.le (restrictPath (by omega : k + 1 ≤ q + 1) u))
          (Icc (0 : ℝ) S) := hu₁full
      have hf : ContDiffOn ℝ j
          (extendPath S hS.le (restrictPath (by omega : k ≤ q) f))
          (Icc (0 : ℝ) S) := by
        have hf' := (restrictOperator 1 (by omega : k ≤ q)).contDiff.comp_contDiffOn
          (hfs.of_le (m := (j : ℕ∞ω)) (by simp))
        exact hf'.congr (fun _ _ => rfl)
      have hres := reducedResidualPath_contDiffOn hq hk (by omega) ν hS f u hf hu₁ hu₂
      rw [show ((j + 1 : ℕ) : ℕ∞ω) = (j : ℕ∞ω) + 1 by simp]
      rw [contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hS)]
      refine ⟨?_, by simp, ?_⟩
      · intro t ht
        exact (cylinderVelocity_hasDerivWithinAt (k := k) hq (by omega) hν hS u₀ f u hduh
          ⟨t, ht⟩).differentiableWithinAt
      · apply hres.congr
        intro t ht
        have hd := cylinderVelocity_hasDerivWithinAt (k := k) hq (by omega) hν hS u₀ f u hduh
          ⟨t, ht⟩
        have hdval := hd.derivWithin ((uniqueDiffOn_Icc hS).uniqueDiffWithinAt ht)
        calc
          _ = cylinderResidualPath hq (by omega) ν f u ⟨t, ht⟩ := hdval
          _ = reducedResidualPath hq hk (by omega) ν f u ⟨t, ht⟩ :=
            (reducedResidualPath_eq hq hk (by omega) ν f u ⟨t, ht⟩).symm
          _ = _ := by simp only [extendPath, projIcc_of_mem hS.le ht]

/-! ## The first differentiated residual -/

/-- The explicitly differentiated target-order residual.  Its three terms are
`ν Δuₜ`, the force derivative, and the two Leibniz terms
`-P(B(uₜ,u)+B(u,uₜ))`. -/
def reducedResidualDerivativePath {q k : ℕ} (hq : 6 ≤ q) (hk : 6 ≤ k)
    (hkq : k + 4 ≤ q + 1) (ν : ℝ) {S : ℝ}
    (f f₁ : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))) :
    C(Icc (0 : ℝ) S, SobolevSpace 1 k) :=
  let w := restrictPath (by omega : k + 1 ≤ q + 1) u
  let d₁ := cylinderResidualPath hq (by omega : k + 1 + 2 ≤ q + 1) ν f u
  let d₂ := cylinderResidualPath hq (by omega : k + 2 + 2 ≤ q + 1) ν f u
  let b : C(Icc (0 : ℝ) S, SobolevSpace 1 k) :=
    ⟨fun t => advection 1 hk (d₁ t) (w t) + advection 1 hk (w t) (d₁ t),
      ((((advection 1 hk).continuous.comp d₁.continuous).clm_apply w.continuous).add
        (((advection 1 hk).continuous.comp w.continuous).clm_apply d₁.continuous))⟩
  ν • (laplacianOperator 1 k).compLeftContinuous ℝ _ d₂ +
    (leray 1 k).compLeftContinuous ℝ _
      (restrictPath (by omega : k ≤ q) f₁ - b)

-- The pointwise product rule elaborates dependent cylinder restriction witnesses.
set_option maxHeartbeats 400000 in
/-- The reduced projected residual has the computed closed-interval within derivative.
The hypothesis `hfder` is exactly the missing cylinder force-time bridge. -/
theorem reducedResidualPath_hasDerivWithinAt {q k : ℕ} (hq : 6 ≤ q) (hk : 6 ≤ k)
    (hkq : k + 4 ≤ q + 1) {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (u₀ : SobolevSpace 1 (q + 1))
    (f f₁ : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (hfder : ∀ t, HasDerivWithinAt (extendPath S hS.le f) (f₁ t)
      (Icc (0 : ℝ) S) t)
    (hduh : ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 hq f) u₀ u t)
    (t : Icc (0 : ℝ) S) :
    HasDerivWithinAt (extendPath S hS.le (reducedResidualPath hq hk (by omega) ν f u))
      (reducedResidualDerivativePath hq hk hkq ν f f₁ u t)
      (Icc (0 : ℝ) S) t := by
  let w := restrictPath (by omega : k + 1 ≤ q + 1) u
  let d₁ := cylinderResidualPath hq (by omega : k + 1 + 2 ≤ q + 1) ν f u
  let d₂ := cylinderResidualPath hq (by omega : k + 2 + 2 ≤ q + 1) ν f u
  have hd₁ : HasDerivWithinAt (extendPath S hS.le w) (d₁ t)
      (Icc (0 : ℝ) S) t := by
    exact cylinderVelocity_hasDerivWithinAt (k := k + 1) hq (by omega)
      hν hS u₀ f u hduh t
  have hd₂ : HasDerivWithinAt
      (extendPath S hS.le (restrictPath (by omega : k + 2 ≤ q + 1) u)) (d₂ t)
      (Icc (0 : ℝ) S) t := by
    exact cylinderVelocity_hasDerivWithinAt (k := k + 2) hq (by omega)
      hν hS u₀ f u hduh t
  have hdf : HasDerivWithinAt
      (extendPath S hS.le (restrictPath (by omega : k ≤ q) f))
      (restrictOperator 1 (by omega : k ≤ q) (f₁ t)) (Icc (0 : ℝ) S) t := by
    have h := (restrictOperator 1 (by omega : k ≤ q)).hasFDerivAt.comp_hasDerivWithinAt
      (t : ℝ) (hfder t)
    convert h using 1 <;> ext r <;> rfl
  have hlap : HasDerivWithinAt
      (fun r => ν • laplacianOperator 1 k
        (extendPath S hS.le (restrictPath (by omega : k + 2 ≤ q + 1) u) r))
      (ν • laplacianOperator 1 k (d₂ t)) (Icc (0 : ℝ) S) t :=
    ((laplacianOperator 1 k).hasFDerivAt.comp_hasDerivWithinAt (t : ℝ) hd₂).const_smul ν
  have hadv : HasDerivWithinAt
      (fun r => advection 1 hk (extendPath S hS.le w r) (extendPath S hS.le w r))
      (advection 1 hk (d₁ t) (w t) + advection 1 hk (w t) (d₁ t))
      (Icc (0 : ℝ) S) t := by
    have h := ContinuousLinearMap.hasDerivWithinAt_of_bilinear
      (B := advection 1 hk) hd₁ hd₁
    convert h using 1
    · ext r
      rfl
    · simp only [extendPath, projIcc_of_mem hS.le t.property]
      abel
  have hsource : HasDerivWithinAt
      (fun r => leray 1 k
        (extendPath S hS.le (restrictPath (by omega : k ≤ q) f) r -
          advection 1 hk (extendPath S hS.le w r) (extendPath S hS.le w r)))
      (leray 1 k (restrictOperator 1 (by omega : k ≤ q) (f₁ t) -
        (advection 1 hk (d₁ t) (w t) + advection 1 hk (w t) (d₁ t))))
      (Icc (0 : ℝ) S) t :=
    (leray 1 k).hasFDerivAt.comp_hasDerivWithinAt (t : ℝ) (hdf.sub hadv)
  have hformula := hlap.add hsource
  convert hformula.congr_of_mem (fun r hr => by
    simp only [extendPath]
    rfl) t.property using 1 <;> rfl

/-- The ordinary `L²` descent of the explicitly differentiated residual. -/
def reducedResidualDerivativeOrdinaryPath {q k : ℕ} (hq : 6 ≤ q) (hk : 6 ≤ k)
    (hkq : k + 4 ≤ q + 1) (ν : ℝ) {S : ℝ}
    (f f₁ : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))) :
    C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2) :=
  ordinaryLift.toContinuousLinearMap.adjoint.compLeftContinuous ℝ _
    ((valueOperator 1 k).compLeftContinuous ℝ _
      (reducedResidualDerivativePath hq hk hkq ν f f₁ u))

-- The proof repeats R2's injective order-zero lift for the differentiated residual.
set_option maxHeartbeats 400000 in
/-- The **datum path of the projected residual** is differentiable, with derivative
the datum of the computed path `νΔuₜ + P(fₜ-B(uₜ,u)-B(u,uₜ))`.
This selection-independent form accepts any continuous datum paths `R,D` carrying the
residual and its displayed derivative. -/
theorem residualPath_hasDerivAt {q k : ℕ} (hq : 6 ≤ q) (hk : 6 ≤ k)
    (hkq : k + 4 ≤ q + 1) {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (u₀ : SobolevSpace 1 (q + 1))
    (f f₁ : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (hfder : ∀ t, HasDerivWithinAt (extendPath S hS.le f) (f₁ t)
      (Icc (0 : ℝ) S) t)
    (hduh : ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 hq f) u₀ u t)
    (R D : C(Icc (0 : ℝ) S, RealVectorSobolev (k : ℝ)))
    (hR : ∀ t, IsSobolevDatum (k : ℝ)
      (⇑(ordinaryResidualPath (m := k) hq (by omega) ν f u t)) (R t))
    (hD : ∀ t, IsSobolevDatum (k : ℝ)
      (⇑(reducedResidualDerivativeOrdinaryPath hq hk hkq ν f f₁ u t)) (D t)) :
    ∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S),
      HasDerivAt (extendPath S hS.le R) (D ⟨t, ht.1.le, ht.2.le⟩) t := by
  have h0k : (0 : ℝ) ≤ (k : ℝ) := by positivity
  let L := lowerVectorL (k : ℝ) 0 h0k
  have hLR : ∀ t, L (R t) =
      orderZeroDatumCLM (ordinaryResidualPath (m := k) hq (by omega) ν f u t) := by
    intro t
    apply isSobolevDatum_unique
    · exact Leray.isSobolevDatum_lower h0k (hR t)
    · rw [← orderZeroDatum_memLp_eq]
      exact isSobolevDatum_zero_ordinaryL2 _
  have hLD : ∀ t, L (D t) = orderZeroDatumCLM
      (reducedResidualDerivativeOrdinaryPath hq hk hkq ν f f₁ u t) := by
    intro t
    apply isSobolevDatum_unique
    · exact Leray.isSobolevDatum_lower h0k (hD t)
    · rw [← orderZeroDatum_memLp_eq]
      exact isSobolevDatum_zero_ordinaryL2 _
  have hdweak : ∀ t ∈ Ioo (0 : ℝ) S,
      HasDerivAt (fun r => L (extendPath S hS.le R r))
        (L (extendPath S hS.le D t)) t := by
    intro t ht
    let M : SobolevSpace 1 k →L[ℝ] EulerMeanSolenoidal.L2 :=
      ordinaryLift.toContinuousLinearMap.adjoint.comp (valueOperator 1 k)
    have hcyl := (reducedResidualPath_hasDerivWithinAt hq hk hkq hν hS
      u₀ f f₁ u hfder hduh ⟨t, ht.1.le, ht.2.le⟩).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)
    have hM := M.hasFDerivAt.comp_hasDerivAt t hcyl
    have hfun : (fun r => M (extendPath S hS.le
        (reducedResidualPath hq hk (by omega) ν f u) r)) =
        extendPath S hS.le (ordinaryResidualPath (m := k) hq (by omega) ν f u) := by
      funext r
      change ordinaryLift.toContinuousLinearMap.adjoint
          (value 1 (reducedResidualPath hq hk (by omega) ν f u
            (projIcc 0 S hS.le r))) =
        ordinaryLift.toContinuousLinearMap.adjoint
          (value 1 (cylinderResidualPath hq (by omega) ν f u
            (projIcc 0 S hS.le r)))
      rw [reducedResidualPath_eq]
    have hord : HasDerivAt
        (extendPath S hS.le (ordinaryResidualPath (m := k) hq (by omega) ν f u))
        (reducedResidualDerivativeOrdinaryPath hq hk hkq ν f f₁ u
          ⟨t, ht.1.le, ht.2.le⟩) t := by
      rw [← hfun]
      exact hM
    have hd0 := orderZeroDatumCLM.hasFDerivAt.comp_hasDerivAt t hord
    have hmapR : (fun r => L (extendPath S hS.le R r)) = fun r =>
        orderZeroDatumCLM
          (extendPath S hS.le (ordinaryResidualPath (m := k) hq (by omega) ν f u) r) := by
      funext r
      exact hLR (projIcc 0 S hS.le r)
    have hmapD : L (extendPath S hS.le D t) = orderZeroDatumCLM
        (reducedResidualDerivativeOrdinaryPath hq hk hkq ν f f₁ u
          ⟨t, ht.1.le, ht.2.le⟩) := by
      change L (D (projIcc 0 S hS.le t)) = _
      rw [projIcc_of_mem hS.le ⟨ht.1.le, ht.2.le⟩]
      exact hLD ⟨t, ht.1.le, ht.2.le⟩
    rwa [hmapR, hmapD]
  intro t ht
  have hd := hasDerivAt_of_injective_map L
    (lowerVectorL_injective (k : ℝ) 0 h0k) S hS.le R D hdweak t ht
  simpa only [extendPath, projIcc_of_mem hS.le ⟨ht.1.le, ht.2.le⟩] using hd

/-! ## Descent of arbitrary-order time regularity to angular data -/

-- The successor step carries dependent continuous-map restrictions at every derivative order.
set_option maxHeartbeats 400000 in
/-- An invariant cylinder Sobolev path which is `C^j` in time has a `C^j` path of
its unique order-`p` angular data.  This is the reusable descent step: at a successor
order, the within derivative is again invariant, is descended through the adjoint of
`ordinaryLift`, and supplies the derivative datum path. -/
theorem exists_contDiff_datumPath_of_cylinder {p j : ℕ} {S : ℝ} (hS : 0 < S)
    (v : C(Icc (0 : ℝ) S, SobolevSpace 1 p))
    (V : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hv : ∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 p (0, θ) (v t) = v t)
    (hV : ∀ t, ordinaryLift (V t) = value 1 (v t))
    (hcv : ContDiffOn ℝ j (extendPath S hS.le v) (Icc (0 : ℝ) S)) :
    ∃ G : ℝ → RealVectorSobolev (p : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (p : ℝ) (⇑(V t)) (G t.1) := by
  induction j generalizing v V with
  | zero =>
      obtain ⟨A, hA, hAc⟩ :=
        exists_continuous_datumPath_general v V hv hV (le_refl p)
      let Ac : C(Icc (0 : ℝ) S, RealVectorSobolev (p : ℝ)) := ⟨A, hAc⟩
      refine ⟨extendPath S hS.le Ac,
        contDiffOn_zero.mpr (extendPath_continuous S hS.le Ac).continuousOn, ?_⟩
      intro t
      simpa only [extendPath, projIcc_of_mem hS.le t.property, Ac,
        ContinuousMap.coe_mk] using hA t
  | succ j ih =>
      have hdc : ContDiffOn ℝ j
          (derivWithin (extendPath S hS.le v) (Icc (0 : ℝ) S))
          (Icc (0 : ℝ) S) := by
        apply hcv.derivWithin (uniqueDiffOn_Icc hS)
        rw [show ((j + 1 : ℕ) : ℕ∞ω) = (j : ℕ∞ω) + 1 by simp]
      let v₁ : C(Icc (0 : ℝ) S, SobolevSpace 1 p) :=
        ⟨fun t => derivWithin (extendPath S hS.le v) (Icc (0 : ℝ) S) t,
          hdc.continuousOn.domRestrict⟩
      have hvder (t : Icc (0 : ℝ) S) :
          HasDerivWithinAt (extendPath S hS.le v) (v₁ t)
            (Icc (0 : ℝ) S) t := by
        exact (hcv.differentiableOn (by
          rw [show ((j + 1 : ℕ) : ℕ∞ω) = (j : ℕ∞ω) + 1 by simp]
          simp) t t.property).hasDerivWithinAt
      have hv₁ : ∀ (θ : AddCircle (1 : ℝ)) t,
          sobolevTranslation 1 p (0, θ) (v₁ t) = v₁ t := by
        intro θ t
        let τ := sobolevTranslation 1 p (0, θ)
        have hτ := τ.hasFDerivAt.comp_hasDerivWithinAt (t : ℝ) (hvder t)
        have heq : Set.EqOn (fun r => τ (extendPath S hS.le v r))
            (extendPath S hS.le v) (Icc (0 : ℝ) S) := by
          intro r hr
          simpa only [extendPath, projIcc_of_mem hS.le hr] using hv θ ⟨r, hr⟩
        calc
          τ (v₁ t) = derivWithin (fun r => τ (extendPath S hS.le v r))
              (Icc (0 : ℝ) S) t :=
            (hτ.derivWithin ((uniqueDiffOn_Icc hS).uniqueDiffWithinAt t.property)).symm
          _ = derivWithin (extendPath S hS.le v) (Icc (0 : ℝ) S) t :=
            derivWithin_congr heq (heq t.property)
          _ = v₁ t := rfl
      let V₁ : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2) :=
        ordinaryLift.toContinuousLinearMap.adjoint.compLeftContinuous ℝ _
          ((valueOperator 1 p).compLeftContinuous ℝ _ v₁)
      have hV₁ : ∀ t, ordinaryLift (V₁ t) = value 1 (v₁ t) := by
        intro t
        exact ordinaryLift_adjoint_of_invariant (value 1 (v₁ t)) (fun θ => by
          have h := congrArg (value 1) (hv₁ θ t)
          simpa only [translation_value] using h)
      have hcv₁ : ContDiffOn ℝ j (extendPath S hS.le v₁) (Icc (0 : ℝ) S) := by
        apply hdc.congr
        intro t ht
        simp only [extendPath, projIcc_of_mem hS.le ht]
        change (fun s : Icc (0 : ℝ) S =>
          derivWithin (extendPath S hS.le v) (Icc (0 : ℝ) S) s.1) ⟨t, ht⟩ = _
        rfl
      obtain ⟨G₁, hG₁, hdatum₁⟩ := ih v₁ V₁ hv₁ hV₁ hcv₁
      obtain ⟨A, hA, hAc⟩ :=
        exists_continuous_datumPath_general v V hv hV (le_refl p)
      let Ac : C(Icc (0 : ℝ) S, RealVectorSobolev (p : ℝ)) := ⟨A, hAc⟩
      let Rc : C(Icc (0 : ℝ) S, RealVectorSobolev (p : ℝ)) :=
        ⟨fun t => G₁ t.1, hG₁.continuousOn.domRestrict⟩
      have hR : ∀ t, IsSobolevDatum (p : ℝ) (⇑(V₁ t)) (Rc t) := hdatum₁
      have h0p : (0 : ℝ) ≤ (p : ℝ) := by positivity
      let L := lowerVectorL (p : ℝ) 0 h0p
      have hLA : ∀ t, L (Ac t) = orderZeroDatumCLM (V t) := by
        intro t
        apply isSobolevDatum_unique
        · exact Leray.isSobolevDatum_lower h0p (hA t)
        · rw [← orderZeroDatum_memLp_eq]
          exact isSobolevDatum_zero_ordinaryL2 (V t)
      have hLR : ∀ t, L (Rc t) = orderZeroDatumCLM (V₁ t) := by
        intro t
        apply isSobolevDatum_unique
        · exact Leray.isSobolevDatum_lower h0p (hR t)
        · rw [← orderZeroDatum_memLp_eq]
          exact isSobolevDatum_zero_ordinaryL2 (V₁ t)
      have hdweak : ∀ t ∈ Ioo (0 : ℝ) S,
          HasDerivAt (fun r => L (extendPath S hS.le Ac r))
            (L (extendPath S hS.le Rc t)) t := by
        intro t ht
        let M : SobolevSpace 1 p →L[ℝ] EulerMeanSolenoidal.L2 :=
          ordinaryLift.toContinuousLinearMap.adjoint.comp (valueOperator 1 p)
        have hdv := (hvder ⟨t, ht.1.le, ht.2.le⟩).hasDerivAt
          (Icc_mem_nhds ht.1 ht.2)
        have hdM := M.hasFDerivAt.comp_hasDerivAt t hdv
        have hMV : (fun r => M (extendPath S hS.le v r)) =
            extendPath S hS.le V := by
          funext r
          apply ordinaryLift.injective
          have hinv : ∀ θ : AddCircle (1 : ℝ),
              translation 1 (0, θ) (value 1 (v (projIcc 0 S hS.le r))) =
                value 1 (v (projIcc 0 S hS.le r)) := by
            intro θ
            have h := congrArg (value 1) (hv θ (projIcc 0 S hS.le r))
            simpa only [translation_value] using h
          change ordinaryLift (ordinaryLift.toContinuousLinearMap.adjoint
              (value 1 (v (projIcc 0 S hS.le r)))) =
            ordinaryLift (V (projIcc 0 S hS.le r))
          rw [ordinaryLift_adjoint_of_invariant _ hinv, hV]
        have hdV : HasDerivAt (extendPath S hS.le V)
            (V₁ ⟨t, ht.1.le, ht.2.le⟩) t := by
          rw [← hMV]
          exact hdM
        have hd0 := orderZeroDatumCLM.hasFDerivAt.comp_hasDerivAt t hdV
        have hfun : (fun r => L (extendPath S hS.le Ac r)) =
            fun r => orderZeroDatumCLM (extendPath S hS.le V r) := by
          funext r
          exact hLA (projIcc 0 S hS.le r)
        have hval : L (extendPath S hS.le Rc t) =
            orderZeroDatumCLM (V₁ ⟨t, ht.1.le, ht.2.le⟩) := by
          change L (Rc (projIcc 0 S hS.le t)) = _
          rw [projIcc_of_mem hS.le ⟨ht.1.le, ht.2.le⟩]
          exact hLR ⟨t, ht.1.le, ht.2.le⟩
        rwa [hfun, hval]
      have hdA (t : Icc (0 : ℝ) S) :
          HasDerivWithinAt (extendPath S hS.le Ac) (Rc t)
            (Icc (0 : ℝ) S) t :=
        hasDerivWithinAt_of_injective_map L
          (lowerVectorL_injective (p : ℝ) 0 h0p) S hS.le Ac Rc hdweak t
      refine ⟨extendPath S hS.le Ac, ?_, ?_⟩
      · rw [show ((j + 1 : ℕ) : ℕ∞ω) = (j : ℕ∞ω) + 1 by simp]
        apply (contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hS)).mpr
        refine ⟨fun t ht => (hdA ⟨t, ht⟩).differentiableWithinAt, by simp, ?_⟩
        apply hG₁.congr
        intro t ht
        exact (hdA ⟨t, ht⟩).derivWithin
          ((uniqueDiffOn_Icc hS).uniqueDiffWithinAt ht)
      · intro t
        simpa only [extendPath, projIcc_of_mem hS.le t.property, Ac,
          ContinuousMap.coe_mk] using hA t

/-! ## The finite R3 statement and its all-order supply form -/

/-- **R3 in the range closed by one finite cylinder carrier.**  The carrier has spatial
order `q+1`; each time derivative costs two orders.  The current all-`j` implementation
retains order six at the single cylinder order where it forms the complete Sobolev
product, and therefore has range `max 6 m + 2*j ≤ q+1`.  This is not claimed to be the
sharp mathematical range at `m < 6`. -/
theorem datumPath_contDiffOn {q m j : ℕ} (hq : 6 ≤ q)
    (hmj : max 6 m + 2 * j ≤ q + 1) {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (u₀ : SobolevSpace 1 (q + 1))
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hfs : ContDiffOn ℝ ∞ (extendPath S hS.le f) (Icc (0 : ℝ) S))
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hduh : ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 hq f) u₀ u t) :
    ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1) := by
  let k := max 6 m
  have hk : 6 ≤ k := le_max_left 6 m
  have hmk : m ≤ k := le_max_right 6 m
  have hkq : k ≤ q + 1 := by omega
  let v := restrictPath hkq u
  have hv : ∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 k (0, θ) (v t) = v t := by
    intro θ t
    change sobolevTranslation 1 k (0, θ) (restrictOperator 1 hkq (u t)) =
      restrictOperator 1 hkq (u t)
    rw [← restrictOperator_translation, hu θ t]
  have hVU : ∀ t, ordinaryLift (U t) = value 1 (v t) := by
    intro t
    rw [hU]
    exact (value_restrictOperator 1 hkq (u t)).symm
  have hcv : ContDiffOn ℝ j (extendPath S hS.le v) (Icc (0 : ℝ) S) :=
    cylinderPath_contDiffOn hq hk hmj hν hS u₀ f u hfs hduh
  obtain ⟨G, hG, hdatum⟩ :=
    exists_contDiff_datumPath_of_cylinder hS v U hv hVU hcv
  have hmkR : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
  refine ⟨fun t => lowerVectorL (k : ℝ) (m : ℝ) hmkR (G t), ?_, ?_⟩
  · exact (lowerVectorL (k : ℝ) (m : ℝ) hmkR).contDiff.comp_contDiffOn hG
  · intro t
    exact Leray.isSobolevDatum_lower hmkR (hdatum t)

/-- The unconditional positive part of R3 from the original `Horizon` inputs: continuity
of the force suffices for one time derivative.  In the sharp range `m + 2 ≤ q+1`, the
datum path is `C¹` on the closed interval, including one-sided within derivatives at both
endpoints.  No order-six algebra floor is needed because the already constructed R2
residual is merely used as the derivative. -/
theorem datumPath_contDiffOn_one {q m : ℕ} (hq : 6 ≤ q)
    (hm : m + 2 ≤ q + 1) {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (u₀ : SobolevSpace 1 (q + 1))
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
    (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1)))
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hU : ∀ t, ordinaryLift (U t) = value 1 (u t))
    (hu : ∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t)
    (hduh : ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 hq f) u₀ u t) :
    ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ 1 G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1) := by
  let v := restrictPath (by omega : m ≤ q + 1) u
  have hres : ContDiffOn ℝ 0
      (extendPath S hS.le (cylinderResidualPath hq hm ν f u)) (Icc (0 : ℝ) S) :=
    contDiffOn_zero.mpr
      (extendPath_continuous S hS.le (cylinderResidualPath hq hm ν f u)).continuousOn
  have hcv : ContDiffOn ℝ 1 (extendPath S hS.le v) (Icc (0 : ℝ) S) := by
    rw [show (1 : ℕ∞ω) = 0 + 1 by rfl]
    apply (contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hS)).mpr
    refine ⟨?_, by simp, ?_⟩
    · intro t ht
      exact (cylinderVelocity_hasDerivWithinAt (k := m) hq hm
        hν hS u₀ f u hduh ⟨t, ht⟩).differentiableWithinAt
    · apply hres.congr
      intro t ht
      have hd := cylinderVelocity_hasDerivWithinAt (k := m) hq hm
        hν hS u₀ f u hduh ⟨t, ht⟩
      have hdval := hd.derivWithin ((uniqueDiffOn_Icc hS).uniqueDiffWithinAt ht)
      calc
        _ = cylinderResidualPath hq hm ν f u ⟨t, ht⟩ := hdval
        _ = _ := by simp only [extendPath, projIcc_of_mem hS.le ht]
  have hv : ∀ (θ : AddCircle (1 : ℝ)) t,
      sobolevTranslation 1 m (0, θ) (v t) = v t := by
    intro θ t
    change sobolevTranslation 1 m (0, θ)
      (restrictOperator 1 (by omega : m ≤ q + 1) (u t)) =
      restrictOperator 1 (by omega : m ≤ q + 1) (u t)
    rw [← restrictOperator_translation, hu θ t]
  have hVU : ∀ t, ordinaryLift (U t) = value 1 (v t) := by
    intro t
    rw [hU]
    exact (value_restrictOperator 1 (by omega : m ≤ q + 1) (u t)).symm
  exact exists_contDiff_datumPath_of_cylinder hS v U hv hVU hcv

/-- **Conditional all-order R3.**  The hypothesis is the honest supply needed beyond a
single finite `Horizon` carrier: for every cylinder order it provides a realization of
the same ordinary path `U`, an exact Duhamel equation, angle invariance, and a smooth
force path.  A family of `HasAprioriBound` propositions alone does not contain these
cross-order compatibility and force-smoothness facts. -/
theorem datumPath_contDiffOn_all_orders {ν S : ℝ} (hν : 0 < ν) (hS : 0 < S)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hall : ∀ (q : ℕ) (hq : 6 ≤ q),
      ∃ (u₀ : SobolevSpace 1 (q + 1))
        (f : C(Icc (0 : ℝ) S, SobolevSpace 1 q))
        (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))),
        ContDiffOn ℝ ∞ (extendPath S hS.le f) (Icc (0 : ℝ) S) ∧
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        (∀ (θ : AddCircle (1 : ℝ)) t,
          sobolevTranslation 1 (q + 1) (0, θ) (u t) = u t) ∧
        ∀ t, u t = quadraticDuhamel 1 ν hν hS.le le_rfl
          (coefficients 1 hq f) u₀ u t) :
    ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1) := by
  intro j m
  let q := max 6 m + 2 * j
  have hq : 6 ≤ q := le_trans (le_max_left 6 m) (Nat.le_add_right _ _)
  obtain ⟨u₀, f, u, hfs, hU, hu, hduh⟩ := hall q hq
  exact datumPath_contDiffOn hq (by omega) hν hS u₀ f u U hfs hU hu hduh

end NSFormalization.Section4.A01
