import NSFormalization.Section3.T13.TorusIdentity
import Contracts.V1.Data
import Contracts.V1.HomogeneousNorm

/-!
# Lane 345 probe: `LocalizationAPI.torus_identity` closes

The first `example` is the `torus_identity` field of
`research/T13/probes/api_on_canonical.lean`, copied verbatim.  The remaining
examples supply non-vacuity: a nonconstant smooth periodic single mode that
satisfies the hypotheses, and the single-mode evaluation of both sides of the
per-frequency kernel identity that drives the proof.
-/

noncomputable section

namespace NSFormalization.Section3.T13.Probe

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open scoped ContDiff ENNReal BigOperators Topology

/-! ## 1. The API field -/

/-- `research/T13/probes/api_on_canonical.lean`, field `torus_identity`. -/
example :
    ∀ (s : ℝ), 0 < s → s < 1 → ∀ f : SpatialField,
      ContDiff ℝ ∞ f → IsPeriodicSpatial f →
        ITorus s f < ⊤ ∧
          ITorus s f = cFrac s *
            periodicHomogeneousENorm s (meanZeroPartT f) ^ (2 : ℕ) :=
  fun _s hs0 hs1 _f hfs hfp ↦ torus_identity hs0 hs1 hfs hfp

/-! ## 2. Non-vacuity: a nonconstant smooth periodic single mode -/

/-- The single mode `x ↦ cos(2π x₁) e₁`. -/
def probeMode : SpatialField :=
  fun x ↦ Real.cos (2 * Real.pi * x 0) • coordinateVector 0

theorem probeMode_contDiff : ContDiff ℝ ∞ probeMode := by
  have h1 : ContDiff ℝ ∞ (fun x : Space ↦ Real.cos (2 * Real.pi * x 0)) :=
    Real.contDiff_cos.comp
      (contDiff_const.mul ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).contDiff))
  exact h1.smul (contDiff_const : ContDiff ℝ ∞ fun _ : Space ↦ coordinateVector (0 : Fin 3))

theorem probeMode_periodic : IsPeriodicSpatial probeMode := by
  intro x j
  show Real.cos (2 * Real.pi * (x + coordinateVector j) 0) • coordinateVector 0
    = Real.cos (2 * Real.pi * x 0) • coordinateVector 0
  by_cases hj : j = 0
  · subst hj
    have hcoord : (x + coordinateVector 0) 0 = x 0 + 1 := by
      show x 0 + (coordinateVector 0 : Space) 0 = x 0 + 1
      rw [coordinateVector]
      simp
    rw [hcoord, show 2 * Real.pi * (x 0 + 1) = 2 * Real.pi * x 0 + 2 * Real.pi by ring,
      Real.cos_add_two_pi]
  · have hcoord : (x + coordinateVector j) 0 = x 0 := by
      show x 0 + (coordinateVector j : Space) 0 = x 0
      rw [coordinateVector]
      simp [Ne.symm hj]
    rw [hcoord]

/-- The mode is genuinely nonconstant: it separates `0` from `(1/2, 0, 0)`. -/
example : probeMode 0 ≠ probeMode (EuclideanSpace.single 0 (1 / 2 : ℝ)) := by
  intro hcontra
  have h := congrArg (fun v : Space ↦ v 0) hcontra
  have h0 : probeMode 0 0 = 1 := by
    show Real.cos (2 * Real.pi * (0 : Space) 0) • (coordinateVector 0 : Space) 0 = 1
    rw [coordinateVector]
    simp
  have h1 : probeMode (EuclideanSpace.single 0 (1 / 2 : ℝ)) 0 = -1 := by
    show Real.cos (2 * Real.pi * (EuclideanSpace.single 0 (1 / 2 : ℝ) : Space) 0) •
      (coordinateVector 0 : Space) 0 = -1
    have hx : (EuclideanSpace.single 0 (1 / 2 : ℝ) : Space) 0 = 1 / 2 := by simp
    have hc : (coordinateVector 0 : Space) 0 = 1 := by rw [coordinateVector]; simp
    rw [hx, hc, show 2 * Real.pi * (1 / 2 : ℝ) = Real.pi by ring, Real.cos_pi]
    norm_num
  rw [h0, h1] at h
  norm_num at h

/-- The identity applies to that nonconstant mode. -/
example (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ITorus s probeMode < ⊤ ∧
      ITorus s probeMode = cFrac s *
        periodicHomogeneousENorm s (meanZeroPartT probeMode) ^ (2 : ℕ) :=
  torus_identity hs0 hs1 probeMode_contDiff probeMode_periodic

/-! ## 3. Single-mode evaluation of both sides of the kernel identity -/

/-- The angular frequency of the first unit mode has norm `2π`. -/
theorem norm_angularVector_single :
    ‖angularVector (Pi.single 0 1 : PeriodicFrequency)‖ = 2 * Real.pi := by
  have hsq : ‖angularVector (Pi.single 0 1 : PeriodicFrequency)‖ ^ 2 = (2 * Real.pi) ^ 2 := by
    rw [norm_angularVector_sq]
    unfold periodicAngularFrequencySq
    rw [show (∑ i : Fin 3, (((Pi.single 0 1 : PeriodicFrequency) i : ℤ) : ℝ) ^ 2) = 1 by
      rw [Finset.sum_eq_single (0 : Fin 3)]
      · norm_num
      · intro b _ hb
        rw [Pi.single_eq_of_ne hb]
        norm_num
      · intro h
        exact absurd (Finset.mem_univ (0 : Fin 3)) h]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp hsq

/-- Both sides of the per-frequency identity at the first unit mode: the
left-hand difference integral against the whole-space kernel equals
`(2π)^{2s} c_s`, which is the `k = e₁` term of the torus identity. -/
example (s : ℝ) (hs : 0 < s) :
    ∫⁻ h : Space, ENNReal.ofReal
        (‖1 - NSFormalization.Paper1.periodicCharacter
          (-(Pi.single 0 1 : PeriodicFrequency)) h‖ ^ 2) *
        fractionalRadialKernel s h
      = ENNReal.ofReal ((2 * Real.pi) ^ (2 * s)) * cFrac s := by
  rw [lintegral_character_kernel hs, norm_angularVector_single]

/-- The matching `T10` coefficient weight at that mode is `(4π²)^{s/2}`, so the
right-hand side of the torus identity carries exactly the factor `|2πk|^{2s}`. -/
example (s : ℝ) :
    homogeneousDatumWeight s (Pi.single 0 1 : PeriodicFrequency) ^ 2
      = (2 * Real.pi) ^ (2 * s) := by
  rw [homogeneousDatumWeight_sq_of_ne s (by
    intro hc
    have := congrFun hc (0 : Fin 3)
    simp at this), norm_angularVector_single]

/-- The constant is finite, so the right-hand side is a genuine value. -/
example (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) : cFrac s < ⊤ := cFrac_lt_top s hs0 hs1

end NSFormalization.Section3.T13.Probe
