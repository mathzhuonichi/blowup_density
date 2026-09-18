import NSFormalization.Section3.T24.AffineBasics
import NavierStokes.SpatialCurl
import NavierStokes.OscillatoryCurl
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# T24a — the canonical nonzero admissible variation `b = ∇ × (θ(t) φ(x) e₁)`

`paper/sections/03-torus.tex:688-691` asks for "a smooth compactly supported
vector potential with nonzero curl" in a small ball, multiplied by "a fixed
nonzero time bump in `(τ₀,τ₁)`".  This module is exactly that construction,
parameterised by an arbitrary time bump `θ : ContDiffBump t₀` and an arbitrary
spatial bump `φ : ContDiffBump x₀`:

* `AffineWitness.potential θ φ (t,x) = (θ t * φ x) • e₁`,
* `AffineWitness.curlBump θ φ = spatialCurl (potential θ φ)`.

The four facts a T24a unit needs are proved once here:
`curlBump_contDiff`, `curlBump_hasCompactSupport`, `tsupport_curlBump_subset`
(inside the closed product `closedBall t₀ θ.rOut ×ˢ closedBall x₀ φ.rOut`),
`curlBump_divergence_free`, hence `curlBump_admissible`; and
`curlBump_ne_zero`, which is what makes the perturbation class nontrivial.

This generalises the single-bump witness of
`research/T24/probes/affine_momentum_nonzero.lean` (lane 398, cylinder
`ball 0 1 × (1/4,3/4)`): that probe is the instance `t₀ = 1/2`, `x₀ = 0`,
`θ = ⟨1/16, 1/8⟩`, `φ = ⟨1/2, 3/4⟩`.  Unit **Ua7**
(`Section3/T24/AffineFamily.lean`) uses the general form with a whole sequence
of pairwise disjoint spatial bumps.

Divergence-freeness is the vendored
`NavierStokes.SpatialCurl.spatialDivergence_spatialCurl`; support control is the
vendored `NavierStokes.OscillatoryCurl.spatialCurl_tsupport_subset`.
-/

noncomputable section

namespace NSFormalization.Section3.T24
namespace AffineWitness

open Set
open NavierStokes.ProblemStatement NavierStokes.SpatialCurl
open scoped ContDiff

variable {t₀ : ℝ} {x₀ : Space}

/-- `paper/sections/03-torus.tex:688-691`: the smooth compactly supported vector
potential `A(t,x) = θ(t) φ(x) e₁`. -/
def potential (θ : ContDiffBump t₀) (φ : ContDiffBump x₀) : VelocityField :=
  fun z => (θ z.1 * φ z.2) • coordinateVector 0

/-- The variation `b = ∇ × A`; solenoidal by construction. -/
def curlBump (θ : ContDiffBump t₀) (φ : ContDiffBump x₀) : VelocityField :=
  spatialCurl (potential θ φ)

/-- The compact carrier `closedBall t₀ θ.rOut ×ˢ closedBall x₀ φ.rOut`. -/
def carrier (θ : ContDiffBump t₀) (φ : ContDiffBump x₀) : Set SpaceTime :=
  Metric.closedBall t₀ θ.rOut ×ˢ Metric.closedBall x₀ φ.rOut

theorem isCompact_carrier (θ : ContDiffBump t₀) (φ : ContDiffBump x₀) :
    IsCompact (carrier θ φ) :=
  (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)

theorem potential_contDiff (θ : ContDiffBump t₀) (φ : ContDiffBump x₀) :
    ContDiff ℝ ∞ (potential θ φ) := by
  have hw : ContDiff ℝ ∞ (fun z : SpaceTime => θ z.1 * φ z.2) :=
    (θ.contDiff.comp contDiff_fst).mul (φ.contDiff.comp contDiff_snd)
  exact hw.smul contDiff_const

theorem tsupport_potential_subset (θ : ContDiffBump t₀) (φ : ContDiffBump x₀) :
    tsupport (potential θ φ) ⊆ carrier θ φ := by
  apply closure_minimal _ (Metric.isClosed_closedBall.prod Metric.isClosed_closedBall)
  intro z hz
  have hne : θ z.1 * φ z.2 ≠ 0 := by
    intro h0
    apply hz
    show (θ z.1 * φ z.2) • coordinateVector 0 = 0
    rw [h0, zero_smul]
  have h1 : θ z.1 ≠ 0 := fun h => hne (by rw [h, zero_mul])
  have h2 : φ z.2 ≠ 0 := fun h => hne (by rw [h, mul_zero])
  have hz1 : z.1 ∈ tsupport (⇑θ) := subset_tsupport _ (Function.mem_support.mpr h1)
  have hz2 : z.2 ∈ tsupport (⇑φ) := subset_tsupport _ (Function.mem_support.mpr h2)
  rw [θ.tsupport_eq] at hz1
  rw [φ.tsupport_eq] at hz2
  exact ⟨hz1, hz2⟩

theorem potential_hasCompactSupport (θ : ContDiffBump t₀) (φ : ContDiffBump x₀) :
    HasCompactSupport (potential θ φ) := by
  apply HasCompactSupport.intro (isCompact_carrier θ φ)
  intro z hz
  by_contra h
  exact hz (tsupport_potential_subset θ φ (subset_tsupport _ h))

theorem curlBump_contDiff (θ : ContDiffBump t₀) (φ : ContDiffBump x₀) :
    ContDiff ℝ ∞ (curlBump θ φ) :=
  contDiff_spatialCurl (potential_contDiff θ φ) (by simp)

theorem tsupport_curlBump_subset (θ : ContDiffBump t₀) (φ : ContDiffBump x₀) :
    tsupport (curlBump θ φ) ⊆ carrier θ φ :=
  (NavierStokes.OscillatoryCurl.spatialCurl_tsupport_subset _).trans
    (tsupport_potential_subset θ φ)

theorem curlBump_hasCompactSupport (θ : ContDiffBump t₀) (φ : ContDiffBump x₀) :
    HasCompactSupport (curlBump θ φ) :=
  (potential_hasCompactSupport θ φ).of_isClosed_subset (isClosed_tsupport _)
    (NavierStokes.OscillatoryCurl.spatialCurl_tsupport_subset _)

theorem curlBump_divergence_free (θ : ContDiffBump t₀) (φ : ContDiffBump x₀) :
    ∀ t : ℝ, ∀ x : Space, spatialDivergence (curlBump θ φ) t x = 0 := by
  intro t x
  have hslice : ContDiffAt ℝ 2 (fun y : Space => potential θ φ (t, y)) x :=
    (((potential_contDiff θ φ).comp (contDiff_const.prodMk contDiff_id)).contDiffAt).of_le
      (by norm_num)
  exact spatialDivergence_spatialCurl _ t x hslice

/-- Outside the carrier the variation vanishes. -/
theorem curlBump_eq_zero_of_notMem (θ : ContDiffBump t₀) (φ : ContDiffBump x₀)
    {z : SpaceTime} (hz : z ∉ carrier θ φ) : curlBump θ φ z = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hz (tsupport_curlBump_subset θ φ h))

/-- `03-torus.tex:671`: the variation is admissible for any cylinder containing
its carrier. -/
theorem curlBump_admissible (θ : ContDiffBump t₀) (φ : ContDiffBump x₀)
    {c : Space} {r τ₀ τ₁ : ℝ}
    (ht : Metric.closedBall t₀ θ.rOut ⊆ Ioo τ₀ τ₁)
    (hx : Metric.closedBall x₀ φ.rOut ⊆ Metric.ball c r) :
    AffineAdmissible c r τ₀ τ₁ (curlBump θ φ) :=
  ⟨curlBump_contDiff θ φ, curlBump_hasCompactSupport θ φ,
    (tsupport_curlBump_subset θ φ).trans (Set.prod_mono ht hx),
    curlBump_divergence_free θ φ⟩

/-- The `e₂`-component of the curl of `g • e₁` is `∂₃ g`. -/
theorem curl_component_one (g : Space → ℝ) (x : Space)
    (hg : DifferentiableAt ℝ g x) :
    (curl (fun y => g y • coordinateVector 0) x) 1 =
      fderiv ℝ g x (coordinateVector 2) := by
  unfold curl
  rw [fderiv_smul_const hg, curlLinear_apply_one]
  simp [coordinateVector, ContinuousLinearMap.smulRight_apply]

/-- The variation is **not** the zero field: if `∇ × (θ φ e₁) ≡ 0` then on the
plateau slice `t = t₀` the `e₂`-component gives `∂₃ φ ≡ 0`, so `φ` would be
constant along the `e₃`-line through `x₀`, contradicting `φ x₀ = 1` and the
compact support of `φ`. -/
theorem curlBump_ne_zero (θ : ContDiffBump t₀) (φ : ContDiffBump x₀) :
    curlBump θ φ ≠ 0 := by
  intro hb0
  have hφsmooth : ContDiff ℝ ∞ (⇑φ) := φ.contDiff
  have hθ₀ : θ t₀ = 1 := θ.one_of_mem_closedBall (Metric.mem_closedBall_self θ.rIn_pos.le)
  -- On the plateau slice `t = t₀` the potential is `φ • e₁`, so its curl vanishes.
  have hcurl0 : ∀ x : Space,
      curl (fun y => φ y • coordinateVector 0) x = 0 := by
    intro x
    have hslice : (fun y : Space => potential θ φ (t₀, y)) =
        (fun y : Space => φ y • coordinateVector 0) := by
      funext y
      show (θ t₀ * φ y) • coordinateVector 0 = φ y • coordinateVector 0
      rw [hθ₀, one_mul]
    have hz : spatialCurl (potential θ φ) (t₀, x) = 0 := by
      have := congrFun hb0 (t₀, x)
      simpa [curlBump] using this
    calc curl (fun y => φ y • coordinateVector 0) x
        = curl (fun y => potential θ φ (t₀, y)) x := by rw [hslice]
      _ = spatialCurl (potential θ φ) (t₀, x) := rfl
      _ = 0 := hz
  -- Hence `∂₃ φ ≡ 0`.
  have hpartial : ∀ x : Space, fderiv ℝ (⇑φ) x (coordinateVector 2) = 0 := by
    intro x
    have hcomp := curl_component_one (⇑φ) x (hφsmooth.differentiable (by simp) x)
    have hzero := congrArg (fun v : Space => v 1) (hcurl0 x)
    rw [hcomp] at hzero
    simpa using hzero
  -- `ψ s := φ (x₀ + s • e₃)` has zero derivative, so it is constant `= φ x₀ = 1`.
  have hψ_diff : Differentiable ℝ (fun s : ℝ => φ (x₀ + s • coordinateVector 2)) :=
    (hφsmooth.differentiable (by simp)).comp
      ((differentiable_id.smul_const _).const_add x₀)
  have hψ_deriv : ∀ s : ℝ,
      deriv (fun s : ℝ => φ (x₀ + s • coordinateVector 2)) s = 0 := by
    intro s
    have hline : HasDerivAt (fun r : ℝ => x₀ + r • coordinateVector 2)
        (coordinateVector 2) s := by
      simpa using ((hasDerivAt_id s).smul_const (coordinateVector 2)).const_add x₀
    have hd : DifferentiableAt ℝ (⇑φ) (x₀ + s • coordinateVector 2) :=
      (hφsmooth.differentiable (by simp)).differentiableAt
    have hcomp := hd.hasFDerivAt.comp_hasDerivAt s hline
    have hderiv := hcomp.deriv
    rw [hpartial (x₀ + s • coordinateVector 2)] at hderiv
    exact hderiv
  have hconst := is_const_of_deriv_eq_zero hψ_diff hψ_deriv
  have hrOut : 0 < φ.rOut := φ.rIn_pos.trans φ.rIn_lt_rOut
  have h10 : (fun s : ℝ => φ (x₀ + s • coordinateVector 2)) (φ.rOut + 1) =
      (fun s : ℝ => φ (x₀ + s • coordinateVector 2)) 0 := hconst _ 0
  have hψ0 : (fun s : ℝ => φ (x₀ + s • coordinateVector 2)) 0 = 1 := by
    show φ (x₀ + (0 : ℝ) • coordinateVector 2) = 1
    rw [zero_smul, add_zero]
    exact φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le)
  have hψ1 : (fun s : ℝ => φ (x₀ + s • coordinateVector 2)) (φ.rOut + 1) = 0 := by
    show φ (x₀ + (φ.rOut + 1) • coordinateVector 2) = 0
    apply image_eq_zero_of_notMem_tsupport (f := ⇑φ)
    rw [φ.tsupport_eq]
    have hnorm : ‖coordinateVector 2‖ = 1 := by simp [coordinateVector]
    simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      hnorm, mul_one, Real.norm_eq_abs, not_le]
    rw [abs_of_nonneg (by linarith)]
    linarith
  rw [hψ0, hψ1] at h10
  exact absurd h10 (by norm_num)

end AffineWitness
end NSFormalization.Section3.T24
