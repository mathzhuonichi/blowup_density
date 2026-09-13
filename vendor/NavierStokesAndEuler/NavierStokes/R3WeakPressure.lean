import NavierStokes.R3SpaceTimePressure
import NavierStokes.SchwartzCompactApproximation
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Recovering the physical pressure gradient

A distribution represented on compact tests by a smooth pressure gradient
is curl-free. The finite-energy momentum equation places that gradient in
negative Sobolev space, where its Poisson equation determines it uniquely.
No growth condition on the physical pressure is assumed.
-/

noncomputable section
namespace NavierStokes.R3WeakPressure

open Set Filter MeasureTheory TemperedDistribution FourierTransform
open R3SpaceTime R3SpaceTimePressure
open scoped SchwartzMap LineDeriv Topology ContDiff ENNReal

def Represents (T : 𝓢'(Domain, ℂ)) (f : Domain → ℂ) : Prop :=
  ∀ φ : 𝓢(Domain, ℂ), HasCompactSupport (φ : Domain → ℂ) →
    T φ = ∫ z : Domain, φ z * f z

theorem represents_lp {q : ℝ≥0∞} [Fact (1 ≤ q)] {f : Domain → ℂ} (hf : MemLp f q) :
    Represents (hf.toLp f : 𝓢'(Domain, ℂ)) f := by
  intro φ _
  rw [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with z hz
  simp only [hz, smul_eq_mul]

theorem Represents.ext {S T : 𝓢'(Domain, ℂ)} {f : Domain → ℂ}
    (hS : Represents S f) (hT : Represents T f) : S = T :=
  SchwartzCompactApproximation.tempered_eq_of_compact_tests fun φ hφ =>
    (hS φ hφ).trans (hT φ hφ).symm

def directional (m : Domain) (f : Domain → ℂ) (z : Domain) : ℂ := fderiv ℝ f z m

theorem partial_contDiff {f : Domain → ℂ} (hf : ContDiff ℝ ∞ f) (m : Domain) :
    ContDiff ℝ ∞ (directional m f) := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem compact_lineDeriv (φ : 𝓢(Domain, ℂ)) (hφ : HasCompactSupport (φ : Domain → ℂ))
    (m : Domain) : HasCompactSupport ((∂_{m} φ : 𝓢(Domain, ℂ)) : Domain → ℂ) := by
  convert! hφ.fderiv_apply ℝ m using 1

theorem integration_by_parts {f : Domain → ℂ} (hf : ContDiff ℝ 1 f)
    (φ : 𝓢(Domain, ℂ)) (hφ : HasCompactSupport (φ : Domain → ℂ)) (m : Domain) :
    (∫ z : Domain, φ z * directional m f z) = -(∫ z : Domain, (∂_{m} φ) z * f z) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact ((∂_{m} φ).continuous.mul hf.continuous).integrable_of_hasCompactSupport
      (compact_lineDeriv φ hφ m).mul_right
  · exact (φ.continuous.mul ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)).integrable_of_hasCompactSupport hφ.mul_right
  · exact (φ.continuous.mul hf.continuous).integrable_of_hasCompactSupport hφ.mul_right
  · intro z _
    exact φ.differentiableAt
  · intro z _
    exact hf.differentiable (by norm_num) z

theorem Represents.lineDeriv {T : 𝓢'(Domain, ℂ)} {f : Domain → ℂ}
    (hT : Represents T f) (hf : ContDiff ℝ 1 f) (m : Domain) :
    Represents (∂_{m} T) (directional m f) := by
  intro φ hφ
  rw [TemperedDistribution.lineDerivOp_apply_apply, map_neg,
    hT (∂_{m} φ) (compact_lineDeriv φ hφ m)]
  exact (integration_by_parts hf φ hφ m).symm

theorem schwartz_derivatives_commute (φ : 𝓢(Domain, ℂ)) (m n : Domain) :
    ∂_{m} (∂_{n} φ) = ∂_{n} (∂_{m} φ) := by
  ext z
  change (∂^{![m, n]} φ) z = (∂^{![n, m]} φ) z
  rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
    SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  exact IsSymmSndFDerivAt.iteratedFDeriv_cons
    (hf := (φ.smooth ⊤).contDiffAt.isSymmSndFDerivAt (by simp))

theorem derivatives_commute (T : 𝓢'(Domain, ℂ)) (m n : Domain) :
    ∂_{m} (∂_{n} T) = ∂_{n} (∂_{m} T) := by
  ext φ
  simp only [TemperedDistribution.lineDerivOp_apply_apply, map_neg,
    neg_neg, schwartz_derivatives_commute φ n m]

def divergence (U : Fin 3 → 𝓢'(Domain, ℂ)) : 𝓢'(Domain, ℂ) :=
  ∑ i, ∂_{spaceDirection i} (U i)

def momentumGradient (U V : Fin 3 → Lp ℂ 2 (volume : Measure Domain))
    (G : Fin 3 → Fin 3 → Lp ℂ 1 (volume : Measure Domain)) (i : Fin 3) : 𝓢'(Domain, ℂ) :=
  spatialLaplacian (U i) - ∂_{timeDirection} (U i : 𝓢'(Domain, ℂ)) + V i -
    ∑ j, ∂_{spaceDirection j} (G i j : 𝓢'(Domain, ℂ))

theorem lp_two_memSobolev (u : Lp ℂ 2 (volume : Measure Domain)) :
    MemSobolev 0 2 (u : 𝓢'(Domain, ℂ)) := by
  use u
  simp

theorem momentumGradient_memSobolev
    (U V : Fin 3 → Lp ℂ 2 (volume : Measure Domain))
    (G : Fin 3 → Fin 3 → Lp ℂ 1 (volume : Measure Domain)) (i : Fin 3) :
    MemSobolev (-5) 2 (momentumGradient U V G i) := by
  apply MemSobolev.sub
  · apply MemSobolev.add
    · apply MemSobolev.sub
      · unfold spatialLaplacian
        apply memSobolev_finset_sum
        intro j _
        exact MemSobolev.mono (by norm_num) (lp_two_memSobolev (U i)).lineDerivOp.lineDerivOp
      · exact MemSobolev.mono (by norm_num) (lp_two_memSobolev (U i)).lineDerivOp
    · exact MemSobolev.mono (by norm_num) (lp_two_memSobolev (V i))
  · apply memSobolev_finset_sum
    intro j _
    convert! (lp_memSobolev (G i j)).lineDerivOp using 1
    norm_num

theorem spatialLaplacian_sum {ι : Type*} (s : Finset ι) (f : ι → 𝓢'(Domain, ℂ)) :
    spatialLaplacian (∑ i ∈ s, f i) = ∑ i ∈ s, spatialLaplacian (f i) :=
  spatialLaplacian_finset_sum s f

theorem momentumGradient_divergence
    (U V : Fin 3 → Lp ℂ 2 (volume : Measure Domain))
    (G : Fin 3 → Fin 3 → Lp ℂ 1 (volume : Measure Domain))
    (hU : divergence (fun i => (U i : 𝓢'(Domain, ℂ))) = 0)
    (hV : divergence (fun i => (V i : 𝓢'(Domain, ℂ))) = 0) :
    divergence (momentumGradient U V G) =
      -(∑ i, ∑ j, ∂_{spaceDirection i} (∂_{spaceDirection j} (G i j : 𝓢'(Domain, ℂ)))) := by
  have hLap : (∑ i, ∂_{spaceDirection i} (spatialLaplacian (U i))) = 0 := by
    simp_rw [← spatialLaplacian_lineDeriv]
    rw [← spatialLaplacian_sum]
    change spatialLaplacian (divergence (fun i => (U i : 𝓢'(Domain, ℂ)))) = 0
    rw [hU]
    simp [spatialLaplacian, LineDeriv.lineDerivOp_zero]
  have hTime : (∑ i, ∂_{spaceDirection i} (∂_{timeDirection} (U i : 𝓢'(Domain, ℂ)))) = 0 := by
    simp_rw [derivatives_commute (U _) (spaceDirection _) timeDirection]
    rw [← LineDeriv.lineDerivOp_sum]
    change ∂_{timeDirection} (divergence (fun i => (U i : 𝓢'(Domain, ℂ)))) = 0
    rw [hU, LineDeriv.lineDerivOp_zero]
  unfold divergence momentumGradient
  simp only [sub_eq_add_neg, LineDeriv.lineDerivOp_add, LineDeriv.lineDerivOp_neg,
    LineDeriv.lineDerivOp_sum, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  change (∑ i, ∂_{spaceDirection i} (spatialLaplacian (U i))) +
    -(∑ i, ∂_{spaceDirection i} (∂_{timeDirection} (U i : 𝓢'(Domain, ℂ)))) +
    divergence (fun i => (V i : 𝓢'(Domain, ℂ))) + _ = _
  rw [hLap, hTime, hV]
  simp

/-- A physical pressure specified only through compact tests gives a
curl-free tempered gradient. -/
theorem curl_free_of_pressure (P : Fin 3 → 𝓢'(Domain, ℂ)) (p : Domain → ℂ)
    (hP : ∀ i (φ : 𝓢(Domain, ℂ)), HasCompactSupport (φ : Domain → ℂ) →
      P i φ = -(∫ z : Domain, (∂_{spaceDirection i} φ) z * p z)) (i j : Fin 3) :
    ∂_{spaceDirection j} (P i) = ∂_{spaceDirection i} (P j) := by
  apply SchwartzCompactApproximation.tempered_eq_of_compact_tests
  intro φ hφ
  simp only [TemperedDistribution.lineDerivOp_apply_apply, map_neg]
  rw [hP i _ (compact_lineDeriv φ hφ _), hP j _ (compact_lineDeriv φ hφ _),
    schwartz_derivatives_commute φ (spaceDirection i) (spaceDirection j)]

/-- The physical pressure gradient in the finite-energy equation equals the
canonical Fourier pressure gradient. -/
theorem pressure_gradient_unique
    (U V : Fin 3 → Lp ℂ 2 (volume : Measure Domain))
    (G : Fin 3 → Fin 3 → Lp ℂ 1 (volume : Measure Domain)) (p : Domain → ℂ)
    (hU : divergence (fun i => (U i : 𝓢'(Domain, ℂ))) = 0)
    (hV : divergence (fun i => (V i : 𝓢'(Domain, ℂ))) = 0)
    (hP : ∀ i (φ : 𝓢(Domain, ℂ)), HasCompactSupport (φ : Domain → ℂ) →
      momentumGradient U V G i φ = -(∫ z : Domain, (∂_{spaceDirection i} φ) z * p z))
    (m : Fin 3) :
    momentumGradient U V G m = ∂_{spaceDirection m} (stressPressure G) := by
  apply stressPressure_gradient_unique G (spaceDirection m) (momentumGradient_memSobolev U V G m)
  calc
    spatialLaplacian (momentumGradient U V G m) =
        ∑ i, ∂_{spaceDirection i} (∂_{spaceDirection m} (momentumGradient U V G i)) := by
      unfold spatialLaplacian
      apply Finset.sum_congr rfl
      intro i _
      rw [curl_free_of_pressure _ p hP m i]
    _ = ∂_{spaceDirection m} (divergence (momentumGradient U V G)) := by
      simp only [divergence, LineDeriv.lineDerivOp_sum]
      exact Finset.sum_congr rfl fun i _ => derivatives_commute _ _ _
    _ = _ := by rw [momentumGradient_divergence U V G hU hV, LineDeriv.lineDerivOp_neg]

end NavierStokes.R3WeakPressure
