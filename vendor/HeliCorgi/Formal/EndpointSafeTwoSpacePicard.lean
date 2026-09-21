import Formal.EndpointSafeTwoSpaceDuhamel
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.ProjIcc

/-!
# Picard fixed point for the endpoint-safe two-space Duhamel contract

This file proves local-in-time existence and closed-ball uniqueness of mild solutions for an
arbitrary `EndpointSafeTwoSpaceDuhamelContract`, in the sense of the contract's own
`IsMildSolutionOn` predicate.

The chain is:

1. the cumulative smoothing mass `kernelPrimitive` is nonnegative, monotone, continuous, and
   vanishes at time zero, so arbitrarily small positive horizons with arbitrarily small mass
   exist;
2. the endpoint-safe Duhamel integral has an exact time-reversed representation obtained from
   `intervalIntegral.integral_comp_sub_left`; in the reversed variable the singular smoothing
   factor no longer moves with the final time;
3. for a bounded continuous trajectory the reversed representation gives quantitative bounds for
   the Duhamel integral, for its trajectory-difference at fixed time, and for its time
   difference; the last bound converts uniform continuity of the trajectory into continuity of
   the Duhamel integral on the compact horizon;
4. the Picard map therefore acts on `C(Icc 0 T, X)`; for a contractive linear evolution and a
   horizon with small enough smoothing mass it preserves the closed ball of radius `‖u₀‖ + 1`
   and contracts with constant `‖bilinear‖ * (2 * (‖u₀‖ + 1)) * kernelPrimitive T < 1`;
5. the Banach fixed point on the complete closed ball yields a mild solution on `[0, T]`, and
   every mild solution staying in the certified ball agrees with it.

The construction stays entirely inside the abstract contract: no concrete carrier, no realness
assumption, and no claim beyond `IsMildSolutionOn` is made. In particular this file proves no
local well-posedness statement for physical Navier–Stokes data and no Clay statement.
-/

namespace MNS2

open MeasureTheory Set Filter Function
open scoped Interval NNReal Topology

noncomputable section

namespace EndpointSafeTwoSpaceDuhamelContract

universe u v w

variable {𝕜 : Type u} {X : Type v} {Y : Type w}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable (C : EndpointSafeTwoSpaceDuhamelContract 𝕜 X Y)

/-! ## Cumulative smoothing mass -/

/-- Endpoint-safe totalization of the contract's scalar smoothing majorant. -/
def safeKernel : ℝ → ℝ :=
  endpointSafePositiveMajorant C.smoothingKernel

theorem safeKernel_nonneg (τ : ℝ) : 0 ≤ C.safeKernel τ :=
  endpointSafePositiveMajorant_nonneg C.smoothingKernel C.smoothingKernel_nonneg τ

theorem intervalIntegrable_safeKernel {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable C.safeKernel volume 0 T :=
  intervalIntegrable_endpointSafePositiveMajorant C.smoothingKernel hT
    (C.intervalIntegrable_smoothingKernel T hT)

theorem intervalIntegrable_safeKernel_of_subset {a b T : ℝ} (hT : 0 ≤ T)
    (hsub : Set.uIcc a b ⊆ Set.uIcc 0 T) :
    IntervalIntegrable C.safeKernel volume a b :=
  (C.intervalIntegrable_safeKernel hT).mono_set hsub

/-- Cumulative endpoint-safe smoothing mass up to time `t`. -/
def kernelPrimitive (t : ℝ) : ℝ :=
  ∫ τ in (0 : ℝ)..t, C.safeKernel τ

@[simp]
theorem kernelPrimitive_zero : C.kernelPrimitive 0 = 0 :=
  intervalIntegral.integral_same

theorem kernelPrimitive_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ C.kernelPrimitive t :=
  intervalIntegral.integral_nonneg ht fun τ _ => C.safeKernel_nonneg τ

theorem kernelPrimitive_sub_eq_integral {T t t' : ℝ} (hT : 0 ≤ T)
    (ht : t ∈ Icc (0 : ℝ) T) (ht' : t' ∈ Icc (0 : ℝ) T) :
    C.kernelPrimitive t' - C.kernelPrimitive t = ∫ τ in t..t', C.safeKernel τ := by
  have hmemt : t ∈ Set.uIcc (0 : ℝ) T := by
    rw [uIcc_of_le hT]
    exact ht
  have hmemt' : t' ∈ Set.uIcc (0 : ℝ) T := by
    rw [uIcc_of_le hT]
    exact ht'
  have h1 : IntervalIntegrable C.safeKernel volume 0 t :=
    C.intervalIntegrable_safeKernel_of_subset hT (uIcc_subset_uIcc left_mem_uIcc hmemt)
  have h2 : IntervalIntegrable C.safeKernel volume t t' :=
    C.intervalIntegrable_safeKernel_of_subset hT (uIcc_subset_uIcc hmemt hmemt')
  have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
  rw [kernelPrimitive, kernelPrimitive, ← hadd]
  ring

theorem kernelPrimitive_mono {T t t' : ℝ} (hT : 0 ≤ T)
    (ht : t ∈ Icc (0 : ℝ) T) (ht' : t' ∈ Icc (0 : ℝ) T) (htt' : t ≤ t') :
    C.kernelPrimitive t ≤ C.kernelPrimitive t' := by
  have hsub := C.kernelPrimitive_sub_eq_integral hT ht ht'
  have hnn : 0 ≤ ∫ τ in t..t', C.safeKernel τ :=
    intervalIntegral.integral_nonneg htt' fun τ _ => C.safeKernel_nonneg τ
  linarith

theorem continuousOn_kernelPrimitive {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn C.kernelPrimitive (Icc (0 : ℝ) T) := by
  have h := intervalIntegral.continuousOn_primitive_interval'
    (C.intervalIntegrable_safeKernel hT) (left_mem_uIcc (a := (0 : ℝ)) (b := T))
  rw [uIcc_of_le hT] at h
  exact h

/-- Positive horizons with arbitrarily small cumulative smoothing mass exist. -/
theorem exists_pos_time_kernelPrimitive_lt {T₀ δ : ℝ} (hT₀ : 0 < T₀) (hδ : 0 < δ) :
    ∃ T : ℝ, 0 < T ∧ T ≤ T₀ ∧ C.kernelPrimitive T < δ := by
  have hcont : ContinuousWithinAt C.kernelPrimitive (Icc (0 : ℝ) T₀) 0 :=
    (C.continuousOn_kernelPrimitive hT₀.le) 0 (left_mem_Icc.mpr hT₀.le)
  have hcont' : ContinuousWithinAt C.kernelPrimitive (Ioc (0 : ℝ) T₀) 0 :=
    hcont.mono Ioc_subset_Icc_self
  have hclosure : (0 : ℝ) ∈ closure (Ioc (0 : ℝ) T₀) := by
    rw [closure_Ioc hT₀.ne]
    exact left_mem_Icc.mpr hT₀.le
  haveI hne : (𝓝[Ioc (0 : ℝ) T₀] (0 : ℝ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp hclosure
  have hev : ∀ᶠ t in 𝓝[Ioc (0 : ℝ) T₀] (0 : ℝ), C.kernelPrimitive t < δ := by
    have htendsto := hcont'.tendsto
    rw [C.kernelPrimitive_zero] at htendsto
    exact htendsto (Iio_mem_nhds hδ)
  have hmem : ∀ᶠ t in 𝓝[Ioc (0 : ℝ) T₀] (0 : ℝ), t ∈ Ioc (0 : ℝ) T₀ :=
    eventually_mem_nhdsWithin
  obtain ⟨T, hTδ, hTmem⟩ := (hev.and hmem).exists
  exact ⟨T, hTmem.1, hTmem.2, hTδ⟩

/-! ## Bilinear diagonal difference -/

/-- Norm bound for the diagonal difference of a continuous bilinear map. -/
theorem norm_continuousBilinear_diag_sub_le (Q : X →L[𝕜] X →L[𝕜] Y) (a b : X) :
    ‖Q a a - Q b b‖ ≤ ‖Q‖ * (‖a‖ + ‖b‖) * ‖a - b‖ := by
  have hsplit : Q a a - Q b b = Q a (a - b) + Q (a - b) b := by
    have h1 : Q a (a - b) = Q a a - Q a b := map_sub (Q a) a b
    have h2 : Q (a - b) b = Q a b - Q b b := by
      have h : Q (a - b) = Q a - Q b := map_sub Q a b
      rw [h, sub_apply]
    rw [h1, h2, sub_add_sub_cancel]
  have hterm1 : ‖Q a (a - b)‖ ≤ ‖Q‖ * ‖a‖ * ‖a - b‖ :=
    norm_continuousBilinear_apply_le Q a (a - b)
  have hterm2 : ‖Q (a - b) b‖ ≤ ‖Q‖ * ‖a - b‖ * ‖b‖ :=
    norm_continuousBilinear_apply_le Q (a - b) b
  calc
    ‖Q a a - Q b b‖ = ‖Q a (a - b) + Q (a - b) b‖ := by rw [hsplit]
    _ ≤ ‖Q a (a - b)‖ + ‖Q (a - b) b‖ := norm_add_le _ _
    _ ≤ ‖Q‖ * ‖a‖ * ‖a - b‖ + ‖Q‖ * ‖a - b‖ * ‖b‖ := add_le_add hterm1 hterm2
    _ = ‖Q‖ * (‖a‖ + ‖b‖) * ‖a - b‖ := by ring

/-! ## Reversed Duhamel representation -/

/-- The time-reversed Duhamel integrand: elapsed time `τ = t - s` is the integration variable. -/
def reversedDuhamelIntegrand (t : ℝ) (u : ℝ → X) (τ : ℝ) : X :=
  C.endpointSafeSmoothing τ (C.bilinear (u (t - τ)) (u (t - τ)))

theorem duhamelIntegrand_eq_reversed_comp (t : ℝ) (u : ℝ → X) (s : ℝ) :
    C.duhamelIntegrand t u s = C.reversedDuhamelIntegrand t u (t - s) := by
  simp [duhamelIntegrand, reversedDuhamelIntegrand, endpointSafeTwoSpaceDuhamelIntegrand,
    endpointSafeSmoothing, sub_sub_cancel]

theorem intervalIntegrable_reversedDuhamelIntegrand [CompleteSpace X] {T t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) {u : ℝ → X} (hu : ContinuousOn u (Icc (0 : ℝ) T))
    {a b : ℝ} (hsub : Set.uIcc a b ⊆ Set.uIcc 0 t) :
    IntervalIntegrable (C.reversedDuhamelIntegrand t u) volume a b := by
  have hut : ContinuousOn u (Icc (0 : ℝ) t) := hu.mono (Icc_subset_Icc le_rfl ht.2)
  have h0 : IntervalIntegrable (C.duhamelIntegrand t u) volume 0 t :=
    C.intervalIntegrable_duhamelIntegrand_of_continuousOn ht.1 hut
  have h2 : IntervalIntegrable (fun s => C.duhamelIntegrand t u (t - s)) volume 0 t := by
    simpa using (h0.comp_sub_left t).symm
  have hfun : (fun s => C.duhamelIntegrand t u (t - s)) = C.reversedDuhamelIntegrand t u := by
    funext s
    rw [C.duhamelIntegrand_eq_reversed_comp, sub_sub_cancel]
  rw [hfun] at h2
  exact h2.mono_set hsub

/-- Pointwise bound for the reversed integrand. -/
theorem norm_reversedDuhamelIntegrand_le (t : ℝ) (u : ℝ → X) (τ : ℝ) :
    ‖C.reversedDuhamelIntegrand t u τ‖ ≤
      C.safeKernel τ * (‖C.bilinear‖ * ‖u (t - τ)‖ ^ 2) := by
  have hop := norm_endpointSafePositiveOperator_apply_le C.positiveSmoothing C.smoothingKernel
    C.norm_positiveSmoothing_apply_le τ (C.bilinear (u (t - τ)) (u (t - τ)))
  have hbil : ‖C.bilinear (u (t - τ)) (u (t - τ))‖ ≤ ‖C.bilinear‖ * ‖u (t - τ)‖ ^ 2 := by
    have h := norm_continuousBilinear_apply_le C.bilinear (u (t - τ)) (u (t - τ))
    calc
      ‖C.bilinear (u (t - τ)) (u (t - τ))‖ ≤ ‖C.bilinear‖ * ‖u (t - τ)‖ * ‖u (t - τ)‖ := h
      _ = ‖C.bilinear‖ * ‖u (t - τ)‖ ^ 2 := by ring
  calc
    ‖C.reversedDuhamelIntegrand t u τ‖ ≤
        endpointSafePositiveMajorant C.smoothingKernel τ *
          ‖C.bilinear (u (t - τ)) (u (t - τ))‖ := hop
    _ ≤ C.safeKernel τ * (‖C.bilinear‖ * ‖u (t - τ)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hbil (C.safeKernel_nonneg τ)

/-- Pointwise bound for a difference of reversed integrands at possibly different final times. -/
theorem norm_reversedDuhamelIntegrand_sub_le (t t' : ℝ) (u v : ℝ → X) (τ : ℝ) :
    ‖C.reversedDuhamelIntegrand t u τ - C.reversedDuhamelIntegrand t' v τ‖ ≤
      C.safeKernel τ *
        (‖C.bilinear‖ * (‖u (t - τ)‖ + ‖v (t' - τ)‖) * ‖u (t - τ) - v (t' - τ)‖) := by
  have hmap : C.reversedDuhamelIntegrand t u τ - C.reversedDuhamelIntegrand t' v τ =
      C.endpointSafeSmoothing τ
        (C.bilinear (u (t - τ)) (u (t - τ)) - C.bilinear (v (t' - τ)) (v (t' - τ))) :=
    (map_sub (C.endpointSafeSmoothing τ) _ _).symm
  have hop := norm_endpointSafePositiveOperator_apply_le C.positiveSmoothing C.smoothingKernel
    C.norm_positiveSmoothing_apply_le τ
    (C.bilinear (u (t - τ)) (u (t - τ)) - C.bilinear (v (t' - τ)) (v (t' - τ)))
  have hbil := norm_continuousBilinear_diag_sub_le C.bilinear (u (t - τ)) (v (t' - τ))
  calc
    ‖C.reversedDuhamelIntegrand t u τ - C.reversedDuhamelIntegrand t' v τ‖
        = ‖C.endpointSafeSmoothing τ
            (C.bilinear (u (t - τ)) (u (t - τ)) - C.bilinear (v (t' - τ)) (v (t' - τ)))‖ := by
          rw [hmap]
    _ ≤ endpointSafePositiveMajorant C.smoothingKernel τ *
          ‖C.bilinear (u (t - τ)) (u (t - τ)) - C.bilinear (v (t' - τ)) (v (t' - τ))‖ := hop
    _ ≤ C.safeKernel τ *
          (‖C.bilinear‖ * (‖u (t - τ)‖ + ‖v (t' - τ)‖) * ‖u (t - τ) - v (t' - τ)‖) :=
        mul_le_mul_of_nonneg_left hbil (C.safeKernel_nonneg τ)

/-! ## Trajectory extension facts -/

theorem norm_IccExtend_le {T : ℝ} (hT : (0 : ℝ) ≤ T) (f : C(Icc (0 : ℝ) T, X)) (s : ℝ) :
    ‖IccExtend hT f s‖ ≤ ‖f‖ := by
  rw [IccExtend_apply]
  exact f.norm_coe_le_norm _

theorem norm_IccExtend_sub_le {T : ℝ} (hT : (0 : ℝ) ≤ T) (f g : C(Icc (0 : ℝ) T, X)) (s : ℝ) :
    ‖IccExtend hT f s - IccExtend hT g s‖ ≤ dist f g := by
  rw [IccExtend_apply, IccExtend_apply, ← dist_eq_norm]
  exact ContinuousMap.dist_apply_le_dist _

/-! ## The reversed representation of the Duhamel integral -/

variable [NormedSpace ℝ X]

/-- The endpoint-safe Duhamel integral in the reversed elapsed-time variable. -/
theorem integral_duhamelIntegrand_eq_reversed (t : ℝ) (u : ℝ → X) :
    ∫ s in (0 : ℝ)..t, C.duhamelIntegrand t u s =
      ∫ τ in (0 : ℝ)..t, C.reversedDuhamelIntegrand t u τ := by
  calc
    ∫ s in (0 : ℝ)..t, C.duhamelIntegrand t u s
        = ∫ s in (0 : ℝ)..t, C.reversedDuhamelIntegrand t u (t - s) := by
          simp only [C.duhamelIntegrand_eq_reversed_comp t u]
    _ = ∫ τ in t - t..t - 0, C.reversedDuhamelIntegrand t u τ :=
          intervalIntegral.integral_comp_sub_left (C.reversedDuhamelIntegrand t u) t
    _ = ∫ τ in (0 : ℝ)..t, C.reversedDuhamelIntegrand t u τ := by norm_num

/-! ## Quantitative Duhamel integral bounds -/

/-- The endpoint-safe Duhamel integral as a function of the final time. -/
def duhamelIntegral (u : ℝ → X) (t : ℝ) : X :=
  ∫ s in (0 : ℝ)..t, C.duhamelIntegrand t u s

theorem duhamelIntegral_eq_reversed (u : ℝ → X) (t : ℝ) :
    C.duhamelIntegral u t = ∫ τ in (0 : ℝ)..t, C.reversedDuhamelIntegrand t u τ :=
  C.integral_duhamelIntegrand_eq_reversed t u

@[simp]
theorem duhamelIntegral_zero (u : ℝ → X) : C.duhamelIntegral u 0 = 0 := by
  simp only [duhamelIntegral]
  exact intervalIntegral.integral_same

/-- Quantitative bound for the Duhamel integral of a uniformly bounded trajectory. -/
theorem norm_duhamelIntegral_le [CompleteSpace X] {T t R : ℝ} (hT : 0 ≤ T)
    (ht : t ∈ Icc (0 : ℝ) T) {u : ℝ → X}
    (hbound : ∀ s ∈ Icc (0 : ℝ) T, ‖u s‖ ≤ R) :
    ‖C.duhamelIntegral u t‖ ≤ ‖C.bilinear‖ * R ^ 2 * C.kernelPrimitive t := by
  rw [C.duhamelIntegral_eq_reversed]
  have hmemt : t ∈ Set.uIcc (0 : ℝ) T := by
    rw [uIcc_of_le hT]
    exact ht
  have hker : IntervalIntegrable C.safeKernel volume 0 t :=
    C.intervalIntegrable_safeKernel_of_subset hT (uIcc_subset_uIcc left_mem_uIcc hmemt)
  have hmaj : IntervalIntegrable (fun τ => C.safeKernel τ * (‖C.bilinear‖ * R ^ 2)) volume 0 t :=
    hker.mul_const _
  have hpoint : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Set.Ioc (0 : ℝ) t →
      ‖C.reversedDuhamelIntegrand t u τ‖ ≤ C.safeKernel τ * (‖C.bilinear‖ * R ^ 2) := by
    refine ae_of_all _ fun τ hτ => ?_
    have hmem : t - τ ∈ Icc (0 : ℝ) T := by
      constructor
      · linarith [hτ.2]
      · linarith [hτ.1, ht.2]
    have hval : ‖u (t - τ)‖ ≤ R := hbound _ hmem
    have hsq : ‖u (t - τ)‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hval 2
    calc
      ‖C.reversedDuhamelIntegrand t u τ‖ ≤
          C.safeKernel τ * (‖C.bilinear‖ * ‖u (t - τ)‖ ^ 2) :=
        C.norm_reversedDuhamelIntegrand_le t u τ
      _ ≤ C.safeKernel τ * (‖C.bilinear‖ * R ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (C.safeKernel_nonneg τ)
        exact mul_le_mul_of_nonneg_left hsq C.bilinear.opNorm_nonneg
  calc
    ‖∫ τ in (0 : ℝ)..t, C.reversedDuhamelIntegrand t u τ‖ ≤
        ∫ τ in (0 : ℝ)..t, C.safeKernel τ * (‖C.bilinear‖ * R ^ 2) :=
      intervalIntegral.norm_integral_le_of_norm_le ht.1 hpoint hmaj
    _ = C.kernelPrimitive t * (‖C.bilinear‖ * R ^ 2) := by
      simp only [kernelPrimitive]
      exact intervalIntegral.integral_mul_const _ _
    _ = ‖C.bilinear‖ * R ^ 2 * C.kernelPrimitive t := by ring

/-- Contraction-type bound: trajectory difference at a fixed final time. -/
theorem norm_duhamelIntegral_sub_le [CompleteSpace X] {T t R d : ℝ} (hT : 0 ≤ T)
    (ht : t ∈ Icc (0 : ℝ) T) {u v : ℝ → X}
    (hu : ContinuousOn u (Icc (0 : ℝ) T)) (hv : ContinuousOn v (Icc (0 : ℝ) T))
    (hR : 0 ≤ R)
    (hRu : ∀ s ∈ Icc (0 : ℝ) T, ‖u s‖ ≤ R) (hRv : ∀ s ∈ Icc (0 : ℝ) T, ‖v s‖ ≤ R)
    (hclose : ∀ s ∈ Icc (0 : ℝ) T, ‖u s - v s‖ ≤ d) :
    ‖C.duhamelIntegral u t - C.duhamelIntegral v t‖ ≤
      ‖C.bilinear‖ * (2 * R) * d * C.kernelPrimitive t := by
  rw [C.duhamelIntegral_eq_reversed, C.duhamelIntegral_eq_reversed]
  have hIu : IntervalIntegrable (C.reversedDuhamelIntegrand t u) volume 0 t :=
    C.intervalIntegrable_reversedDuhamelIntegrand ht hu subset_rfl
  have hIv : IntervalIntegrable (C.reversedDuhamelIntegrand t v) volume 0 t :=
    C.intervalIntegrable_reversedDuhamelIntegrand ht hv subset_rfl
  rw [← intervalIntegral.integral_sub hIu hIv]
  have hmemt : t ∈ Set.uIcc (0 : ℝ) T := by
    rw [uIcc_of_le hT]
    exact ht
  have hker : IntervalIntegrable C.safeKernel volume 0 t :=
    C.intervalIntegrable_safeKernel_of_subset hT (uIcc_subset_uIcc left_mem_uIcc hmemt)
  have hmaj : IntervalIntegrable
      (fun τ => C.safeKernel τ * (‖C.bilinear‖ * (2 * R) * d)) volume 0 t :=
    hker.mul_const _
  have hpoint : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Set.Ioc (0 : ℝ) t →
      ‖C.reversedDuhamelIntegrand t u τ - C.reversedDuhamelIntegrand t v τ‖ ≤
        C.safeKernel τ * (‖C.bilinear‖ * (2 * R) * d) := by
    refine ae_of_all _ fun τ hτ => ?_
    have hmem : t - τ ∈ Icc (0 : ℝ) T := by
      constructor
      · linarith [hτ.2]
      · linarith [hτ.1, ht.2]
    have hsum : ‖u (t - τ)‖ + ‖v (t - τ)‖ ≤ 2 * R := by
      have h1 := hRu _ hmem
      have h2 := hRv _ hmem
      linarith
    have hdiff : ‖u (t - τ) - v (t - τ)‖ ≤ d := hclose _ hmem
    have hfactor : ‖C.bilinear‖ * (‖u (t - τ)‖ + ‖v (t - τ)‖) * ‖u (t - τ) - v (t - τ)‖ ≤
        ‖C.bilinear‖ * (2 * R) * d := by
      have hstep1 : ‖C.bilinear‖ * (‖u (t - τ)‖ + ‖v (t - τ)‖) ≤ ‖C.bilinear‖ * (2 * R) :=
        mul_le_mul_of_nonneg_left hsum C.bilinear.opNorm_nonneg
      exact mul_le_mul hstep1 hdiff (norm_nonneg _) (by positivity)
    calc
      ‖C.reversedDuhamelIntegrand t u τ - C.reversedDuhamelIntegrand t v τ‖ ≤
          C.safeKernel τ *
            (‖C.bilinear‖ * (‖u (t - τ)‖ + ‖v (t - τ)‖) * ‖u (t - τ) - v (t - τ)‖) :=
        C.norm_reversedDuhamelIntegrand_sub_le t t u v τ
      _ ≤ C.safeKernel τ * (‖C.bilinear‖ * (2 * R) * d) :=
        mul_le_mul_of_nonneg_left hfactor (C.safeKernel_nonneg τ)
  calc
    ‖∫ τ in (0 : ℝ)..t,
        (C.reversedDuhamelIntegrand t u τ - C.reversedDuhamelIntegrand t v τ)‖ ≤
        ∫ τ in (0 : ℝ)..t, C.safeKernel τ * (‖C.bilinear‖ * (2 * R) * d) :=
      intervalIntegral.norm_integral_le_of_norm_le ht.1 hpoint hmaj
    _ = C.kernelPrimitive t * (‖C.bilinear‖ * (2 * R) * d) := by
      simp only [kernelPrimitive]
      exact intervalIntegral.integral_mul_const _ _
    _ = ‖C.bilinear‖ * (2 * R) * d * C.kernelPrimitive t := by ring

/-- Time-difference bound for the Duhamel integral of a fixed bounded trajectory. -/
theorem norm_duhamelIntegral_time_sub_le [CompleteSpace X] {T t t' R ε : ℝ} (hT : 0 ≤ T)
    (ht : t ∈ Icc (0 : ℝ) T) (ht' : t' ∈ Icc (0 : ℝ) T) (htt' : t ≤ t')
    {u : ℝ → X} (hu : ContinuousOn u (Icc (0 : ℝ) T)) (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hRu : ∀ s ∈ Icc (0 : ℝ) T, ‖u s‖ ≤ R)
    (hmod : ∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T, |a - b| ≤ t' - t → ‖u a - u b‖ ≤ ε) :
    ‖C.duhamelIntegral u t' - C.duhamelIntegral u t‖ ≤
      ‖C.bilinear‖ * (2 * R) * ε * C.kernelPrimitive T +
        ‖C.bilinear‖ * R ^ 2 * (C.kernelPrimitive t' - C.kernelPrimitive t) := by
  rw [C.duhamelIntegral_eq_reversed, C.duhamelIntegral_eq_reversed]
  have hmemt : t ∈ Set.uIcc (0 : ℝ) t' := by
    rw [uIcc_of_le (ht.1.trans htt')]
    exact ⟨ht.1, htt'⟩
  have hI1 : IntervalIntegrable (C.reversedDuhamelIntegrand t' u) volume 0 t :=
    C.intervalIntegrable_reversedDuhamelIntegrand ht' hu
      (uIcc_subset_uIcc left_mem_uIcc hmemt)
  have hI2 : IntervalIntegrable (C.reversedDuhamelIntegrand t' u) volume t t' :=
    C.intervalIntegrable_reversedDuhamelIntegrand ht' hu
      (uIcc_subset_uIcc hmemt right_mem_uIcc)
  have hIt : IntervalIntegrable (C.reversedDuhamelIntegrand t u) volume 0 t :=
    C.intervalIntegrable_reversedDuhamelIntegrand ht hu subset_rfl
  have hsplit : ∫ τ in (0 : ℝ)..t', C.reversedDuhamelIntegrand t' u τ =
      (∫ τ in (0 : ℝ)..t, C.reversedDuhamelIntegrand t' u τ) +
        ∫ τ in t..t', C.reversedDuhamelIntegrand t' u τ :=
    (intervalIntegral.integral_add_adjacent_intervals hI1 hI2).symm
  have hdiff : (∫ τ in (0 : ℝ)..t', C.reversedDuhamelIntegrand t' u τ) -
      ∫ τ in (0 : ℝ)..t, C.reversedDuhamelIntegrand t u τ =
      (∫ τ in (0 : ℝ)..t,
        (C.reversedDuhamelIntegrand t' u τ - C.reversedDuhamelIntegrand t u τ)) +
        ∫ τ in t..t', C.reversedDuhamelIntegrand t' u τ := by
    rw [hsplit, intervalIntegral.integral_sub hI1 hIt]
    abel
  rw [hdiff]
  have hbound1 : ‖∫ τ in (0 : ℝ)..t,
      (C.reversedDuhamelIntegrand t' u τ - C.reversedDuhamelIntegrand t u τ)‖ ≤
      ‖C.bilinear‖ * (2 * R) * ε * C.kernelPrimitive T := by
    have hmemtT : t ∈ Set.uIcc (0 : ℝ) T := by
      rw [uIcc_of_le hT]
      exact ht
    have hker : IntervalIntegrable C.safeKernel volume 0 t :=
      C.intervalIntegrable_safeKernel_of_subset hT (uIcc_subset_uIcc left_mem_uIcc hmemtT)
    have hmaj : IntervalIntegrable
        (fun τ => C.safeKernel τ * (‖C.bilinear‖ * (2 * R) * ε)) volume 0 t :=
      hker.mul_const _
    have hpoint : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Set.Ioc (0 : ℝ) t →
        ‖C.reversedDuhamelIntegrand t' u τ - C.reversedDuhamelIntegrand t u τ‖ ≤
          C.safeKernel τ * (‖C.bilinear‖ * (2 * R) * ε) := by
      refine ae_of_all _ fun τ hτ => ?_
      have hmem1 : t' - τ ∈ Icc (0 : ℝ) T := by
        constructor
        · linarith [hτ.2, htt']
        · linarith [hτ.1, ht'.2]
      have hmem2 : t - τ ∈ Icc (0 : ℝ) T := by
        constructor
        · linarith [hτ.2]
        · linarith [hτ.1, ht.2]
      have habs : |t' - τ - (t - τ)| ≤ t' - t := by
        have h : t' - τ - (t - τ) = t' - t := by ring
        rw [h, abs_of_nonneg (by linarith)]
      have hsum : ‖u (t' - τ)‖ + ‖u (t - τ)‖ ≤ 2 * R := by
        have h1 := hRu _ hmem1
        have h2 := hRu _ hmem2
        linarith
      have hdiffle : ‖u (t' - τ) - u (t - τ)‖ ≤ ε := hmod _ hmem1 _ hmem2 habs
      have hfactor : ‖C.bilinear‖ * (‖u (t' - τ)‖ + ‖u (t - τ)‖) *
          ‖u (t' - τ) - u (t - τ)‖ ≤ ‖C.bilinear‖ * (2 * R) * ε := by
        have hstep1 : ‖C.bilinear‖ * (‖u (t' - τ)‖ + ‖u (t - τ)‖) ≤ ‖C.bilinear‖ * (2 * R) :=
          mul_le_mul_of_nonneg_left hsum C.bilinear.opNorm_nonneg
        exact mul_le_mul hstep1 hdiffle (norm_nonneg _) (by positivity)
      calc
        ‖C.reversedDuhamelIntegrand t' u τ - C.reversedDuhamelIntegrand t u τ‖ ≤
            C.safeKernel τ *
              (‖C.bilinear‖ * (‖u (t' - τ)‖ + ‖u (t - τ)‖) * ‖u (t' - τ) - u (t - τ)‖) :=
          C.norm_reversedDuhamelIntegrand_sub_le t' t u u τ
        _ ≤ C.safeKernel τ * (‖C.bilinear‖ * (2 * R) * ε) :=
          mul_le_mul_of_nonneg_left hfactor (C.safeKernel_nonneg τ)
    have hKt : C.kernelPrimitive t ≤ C.kernelPrimitive T :=
      C.kernelPrimitive_mono hT ht (right_mem_Icc.mpr hT) ht.2
    have hcoef : 0 ≤ ‖C.bilinear‖ * (2 * R) * ε := by positivity
    calc
      ‖∫ τ in (0 : ℝ)..t,
          (C.reversedDuhamelIntegrand t' u τ - C.reversedDuhamelIntegrand t u τ)‖ ≤
          ∫ τ in (0 : ℝ)..t, C.safeKernel τ * (‖C.bilinear‖ * (2 * R) * ε) :=
        intervalIntegral.norm_integral_le_of_norm_le ht.1 hpoint hmaj
      _ = C.kernelPrimitive t * (‖C.bilinear‖ * (2 * R) * ε) := by
        simp only [kernelPrimitive]
        exact intervalIntegral.integral_mul_const _ _
      _ ≤ C.kernelPrimitive T * (‖C.bilinear‖ * (2 * R) * ε) :=
        mul_le_mul_of_nonneg_right hKt hcoef
      _ = ‖C.bilinear‖ * (2 * R) * ε * C.kernelPrimitive T := by ring
  have hbound2 : ‖∫ τ in t..t', C.reversedDuhamelIntegrand t' u τ‖ ≤
      ‖C.bilinear‖ * R ^ 2 * (C.kernelPrimitive t' - C.kernelPrimitive t) := by
    have hmemtT : t ∈ Set.uIcc (0 : ℝ) T := by
      rw [uIcc_of_le hT]
      exact ht
    have hmemt'T : t' ∈ Set.uIcc (0 : ℝ) T := by
      rw [uIcc_of_le hT]
      exact ht'
    have hker : IntervalIntegrable C.safeKernel volume t t' :=
      C.intervalIntegrable_safeKernel_of_subset hT (uIcc_subset_uIcc hmemtT hmemt'T)
    have hmaj : IntervalIntegrable
        (fun τ => C.safeKernel τ * (‖C.bilinear‖ * R ^ 2)) volume t t' :=
      hker.mul_const _
    have hpoint : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Set.Ioc t t' →
        ‖C.reversedDuhamelIntegrand t' u τ‖ ≤
          C.safeKernel τ * (‖C.bilinear‖ * R ^ 2) := by
      refine ae_of_all _ fun τ hτ => ?_
      have hmem : t' - τ ∈ Icc (0 : ℝ) T := by
        constructor
        · linarith [hτ.2]
        · linarith [hτ.1, ht.1, ht'.2]
      have hval : ‖u (t' - τ)‖ ≤ R := hRu _ hmem
      have hsq : ‖u (t' - τ)‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hval 2
      calc
        ‖C.reversedDuhamelIntegrand t' u τ‖ ≤
            C.safeKernel τ * (‖C.bilinear‖ * ‖u (t' - τ)‖ ^ 2) :=
          C.norm_reversedDuhamelIntegrand_le t' u τ
        _ ≤ C.safeKernel τ * (‖C.bilinear‖ * R ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (C.safeKernel_nonneg τ)
          exact mul_le_mul_of_nonneg_left hsq C.bilinear.opNorm_nonneg
    calc
      ‖∫ τ in t..t', C.reversedDuhamelIntegrand t' u τ‖ ≤
          ∫ τ in t..t', C.safeKernel τ * (‖C.bilinear‖ * R ^ 2) :=
        intervalIntegral.norm_integral_le_of_norm_le htt' hpoint hmaj
      _ = (∫ τ in t..t', C.safeKernel τ) * (‖C.bilinear‖ * R ^ 2) :=
        intervalIntegral.integral_mul_const _ _
      _ = (C.kernelPrimitive t' - C.kernelPrimitive t) * (‖C.bilinear‖ * R ^ 2) := by
        rw [C.kernelPrimitive_sub_eq_integral hT ht ht']
      _ = ‖C.bilinear‖ * R ^ 2 * (C.kernelPrimitive t' - C.kernelPrimitive t) := by ring
  calc
    ‖(∫ τ in (0 : ℝ)..t,
        (C.reversedDuhamelIntegrand t' u τ - C.reversedDuhamelIntegrand t u τ)) +
        ∫ τ in t..t', C.reversedDuhamelIntegrand t' u τ‖ ≤
        ‖∫ τ in (0 : ℝ)..t,
          (C.reversedDuhamelIntegrand t' u τ - C.reversedDuhamelIntegrand t u τ)‖ +
          ‖∫ τ in t..t', C.reversedDuhamelIntegrand t' u τ‖ := norm_add_le _ _
    _ ≤ ‖C.bilinear‖ * (2 * R) * ε * C.kernelPrimitive T +
          ‖C.bilinear‖ * R ^ 2 * (C.kernelPrimitive t' - C.kernelPrimitive t) :=
        add_le_add hbound1 hbound2

/-! ## Continuity of the Duhamel integral in the final time -/

/-- The endpoint-safe Duhamel integral of a continuous trajectory is continuous on the horizon. -/
theorem continuousOn_duhamelIntegral [CompleteSpace X] {T : ℝ} (hT : 0 ≤ T)
    {u : ℝ → X} (hu : ContinuousOn u (Icc (0 : ℝ) T)) :
    ContinuousOn (C.duhamelIntegral u) (Icc (0 : ℝ) T) := by
  obtain ⟨R₀, hR₀⟩ := isCompact_Icc.bddAbove_image hu.norm
  have hR0mem : ∀ s ∈ Icc (0 : ℝ) T, ‖u s‖ ≤ R₀ := fun s hs =>
    hR₀ (mem_image_of_mem _ hs)
  set R : ℝ := max R₀ 0 with hRdef
  have hR : 0 ≤ R := le_max_right _ _
  have hRu : ∀ s ∈ Icc (0 : ℝ) T, ‖u s‖ ≤ R := fun s hs =>
    (hR0mem s hs).trans (le_max_left _ _)
  have huc : UniformContinuousOn u (Icc (0 : ℝ) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hu
  have hKc : UniformContinuousOn C.kernelPrimitive (Icc (0 : ℝ) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (C.continuousOn_kernelPrimitive hT)
  set A : ℝ := ‖C.bilinear‖ * (2 * R) * C.kernelPrimitive T with hAdef
  set B : ℝ := ‖C.bilinear‖ * R ^ 2 with hBdef
  have hA : 0 ≤ A := by
    have := C.kernelPrimitive_nonneg hT
    positivity
  have hB : 0 ≤ B := by positivity
  refine (Metric.uniformContinuousOn_iff.mpr fun ε hε => ?_).continuousOn
  set ε₁ : ℝ := ε / 3 / (A + 1) with hε₁def
  set ε₂ : ℝ := ε / 3 / (B + 1) with hε₂def
  have hε₁ : 0 < ε₁ := by
    apply div_pos (by linarith)
    linarith
  have hε₂ : 0 < ε₂ := by
    apply div_pos (by linarith)
    linarith
  obtain ⟨δ₁, hδ₁, hδ₁prop⟩ := Metric.uniformContinuousOn_iff.mp huc ε₁ hε₁
  obtain ⟨δ₂, hδ₂, hδ₂prop⟩ := Metric.uniformContinuousOn_iff.mp hKc ε₂ hε₂
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  have harith : ∀ P c : ℝ, 0 ≤ P → 0 ≤ c → P * (c / (P + 1)) ≤ c := by
    intro P c hP hc
    have hP1 : (0 : ℝ) < P + 1 := by linarith
    rw [mul_div_assoc', div_le_iff₀ hP1]
    nlinarith
  have key : ∀ x ∈ Icc (0 : ℝ) T, ∀ y ∈ Icc (0 : ℝ) T, y ≤ x → dist x y < min δ₁ δ₂ →
      dist (C.duhamelIntegral u x) (C.duhamelIntegral u y) < ε := by
    intro x hx y hy hyx hxy
    have hxyd : |x - y| < min δ₁ δ₂ := by
      rw [← Real.dist_eq]
      exact hxy
    have hmod : ∀ a ∈ Icc (0 : ℝ) T, ∀ b ∈ Icc (0 : ℝ) T, |a - b| ≤ x - y →
        ‖u a - u b‖ ≤ ε₁ := by
      intro a ha b hb hab
      have hdab : dist a b < δ₁ := by
        rw [Real.dist_eq]
        calc
          |a - b| ≤ x - y := hab
          _ = |x - y| := (abs_of_nonneg (by linarith)).symm
          _ < min δ₁ δ₂ := hxyd
          _ ≤ δ₁ := min_le_left _ _
      have := hδ₁prop a ha b hb hdab
      rw [dist_eq_norm] at this
      exact this.le
    have hKxy : C.kernelPrimitive x - C.kernelPrimitive y < ε₂ := by
      have hd := hδ₂prop x hx y hy (hxy.trans_le (min_le_right _ _))
      rw [Real.dist_eq] at hd
      calc
        C.kernelPrimitive x - C.kernelPrimitive y ≤
            |C.kernelPrimitive x - C.kernelPrimitive y| := le_abs_self _
        _ < ε₂ := hd
    have hest := C.norm_duhamelIntegral_time_sub_le hT hy hx hyx hu hR hε₁.le hRu hmod
    have hKmono : 0 ≤ C.kernelPrimitive x - C.kernelPrimitive y := by
      have := C.kernelPrimitive_mono hT hy hx hyx
      linarith
    have hterm1 : ‖C.bilinear‖ * (2 * R) * ε₁ * C.kernelPrimitive T ≤ ε / 3 := by
      have h : ‖C.bilinear‖ * (2 * R) * ε₁ * C.kernelPrimitive T = A * ε₁ := by
        rw [hAdef]
        ring
      rw [h, hε₁def]
      exact harith A (ε / 3) hA (by linarith)
    have hterm2 : ‖C.bilinear‖ * R ^ 2 * (C.kernelPrimitive x - C.kernelPrimitive y) ≤
        ε / 3 := by
      have hle : ‖C.bilinear‖ * R ^ 2 * (C.kernelPrimitive x - C.kernelPrimitive y) ≤
          B * ε₂ := by
        rw [hBdef]
        exact mul_le_mul_of_nonneg_left hKxy.le (by positivity)
      calc
        ‖C.bilinear‖ * R ^ 2 * (C.kernelPrimitive x - C.kernelPrimitive y) ≤ B * ε₂ := hle
        _ ≤ ε / 3 := by
          rw [hε₂def]
          exact harith B (ε / 3) hB (by linarith)
    rw [dist_eq_norm]
    calc
      ‖C.duhamelIntegral u x - C.duhamelIntegral u y‖ ≤
          ‖C.bilinear‖ * (2 * R) * ε₁ * C.kernelPrimitive T +
            ‖C.bilinear‖ * R ^ 2 * (C.kernelPrimitive x - C.kernelPrimitive y) := hest
      _ ≤ ε / 3 + ε / 3 := add_le_add hterm1 hterm2
      _ < ε := by linarith
  intro x hx y hy hxy
  rcases le_total y x with hyx | hxy'
  · exact key x hx y hy hyx hxy
  · rw [dist_comm]
    exact key y hy x hx hxy' (by rwa [dist_comm])

/-! ## The Picard map on continuous trajectories -/

section Picard

variable [CompleteSpace X]

variable {T : ℝ}

/-- The Picard map of the endpoint-safe two-space mild equation on `C(Icc 0 T, X)`. -/
def picardMap (hT : (0 : ℝ) ≤ T) (u₀ : X) (f : C(Icc (0 : ℝ) T, X)) :
    C(Icc (0 : ℝ) T, X) where
  toFun t :=
    C.linearEvolution (Real.toNNReal t.1) u₀ - C.duhamelIntegral (IccExtend hT f) t.1
  continuous_toFun := by
    have h1 : Continuous fun t : Icc (0 : ℝ) T =>
        C.linearEvolution (Real.toNNReal t.1) u₀ :=
      C.continuous_linear_action.comp
        ((continuous_real_toNNReal.comp continuous_subtype_val).prodMk continuous_const)
    have hext : ContinuousOn (IccExtend hT f) (Icc (0 : ℝ) T) :=
      (f.continuous.Icc_extend').continuousOn
    have h2 : ContinuousOn (C.duhamelIntegral (IccExtend hT f)) (Icc (0 : ℝ) T) :=
      C.continuousOn_duhamelIntegral hT hext
    exact h1.sub (continuousOn_iff_continuous_restrict.mp h2)

@[simp]
theorem picardMap_apply (hT : (0 : ℝ) ≤ T) (u₀ : X) (f : C(Icc (0 : ℝ) T, X))
    (t : Icc (0 : ℝ) T) :
    C.picardMap hT u₀ f t =
      C.linearEvolution (Real.toNNReal t.1) u₀ -
        C.duhamelIntegral (IccExtend hT f) t.1 :=
  rfl

/-- Ball invariance of the Picard map under a contractive linear evolution. -/
theorem norm_picardMap_le (hT : (0 : ℝ) ≤ T)
    (hcontr : ∀ (t : ℝ≥0) (x : X), ‖C.linearEvolution t x‖ ≤ ‖x‖)
    (u₀ : X) {R : ℝ} {f : C(Icc (0 : ℝ) T, X)} (hf : ‖f‖ ≤ R) :
    ‖C.picardMap hT u₀ f‖ ≤ ‖u₀‖ + ‖C.bilinear‖ * R ^ 2 * C.kernelPrimitive T := by
  have hKnn : 0 ≤ C.kernelPrimitive T := C.kernelPrimitive_nonneg hT
  have hrhs : (0 : ℝ) ≤ ‖u₀‖ + ‖C.bilinear‖ * R ^ 2 * C.kernelPrimitive T := by positivity
  rw [ContinuousMap.norm_le _ hrhs]
  intro t
  have hbound : ∀ s ∈ Icc (0 : ℝ) T, ‖IccExtend hT f s‖ ≤ R := fun s _ =>
    (norm_IccExtend_le hT f s).trans hf
  have hIle := C.norm_duhamelIntegral_le hT t.2 hbound
  have hKt : C.kernelPrimitive t.1 ≤ C.kernelPrimitive T :=
    C.kernelPrimitive_mono hT t.2 (right_mem_Icc.mpr hT) t.2.2
  calc
    ‖C.picardMap hT u₀ f t‖ ≤
        ‖C.linearEvolution (Real.toNNReal t.1) u₀‖ +
          ‖C.duhamelIntegral (IccExtend hT f) t.1‖ := by
      rw [C.picardMap_apply]
      exact norm_sub_le _ _
    _ ≤ ‖u₀‖ + ‖C.bilinear‖ * R ^ 2 * C.kernelPrimitive t.1 :=
      add_le_add (hcontr _ u₀) hIle
    _ ≤ ‖u₀‖ + ‖C.bilinear‖ * R ^ 2 * C.kernelPrimitive T := by
      have : ‖C.bilinear‖ * R ^ 2 * C.kernelPrimitive t.1 ≤
          ‖C.bilinear‖ * R ^ 2 * C.kernelPrimitive T :=
        mul_le_mul_of_nonneg_left hKt (by positivity)
      linarith

/-- Contraction estimate for the Picard map on the closed `R`-ball. -/
theorem dist_picardMap_le (hT : (0 : ℝ) ≤ T) (u₀ : X) {R : ℝ} (hR : 0 ≤ R)
    {f g : C(Icc (0 : ℝ) T, X)} (hf : ‖f‖ ≤ R) (hg : ‖g‖ ≤ R) :
    dist (C.picardMap hT u₀ f) (C.picardMap hT u₀ g) ≤
      ‖C.bilinear‖ * (2 * R) * C.kernelPrimitive T * dist f g := by
  have hKnn : 0 ≤ C.kernelPrimitive T := C.kernelPrimitive_nonneg hT
  have hdnn : 0 ≤ dist f g := dist_nonneg
  have hrhs : (0 : ℝ) ≤ ‖C.bilinear‖ * (2 * R) * C.kernelPrimitive T * dist f g := by
    positivity
  rw [ContinuousMap.dist_le hrhs]
  intro t
  have hextf : ContinuousOn (IccExtend hT f) (Icc (0 : ℝ) T) :=
    (f.continuous.Icc_extend').continuousOn
  have hextg : ContinuousOn (IccExtend hT g) (Icc (0 : ℝ) T) :=
    (g.continuous.Icc_extend').continuousOn
  have hbf : ∀ s ∈ Icc (0 : ℝ) T, ‖IccExtend hT f s‖ ≤ R := fun s _ =>
    (norm_IccExtend_le hT f s).trans hf
  have hbg : ∀ s ∈ Icc (0 : ℝ) T, ‖IccExtend hT g s‖ ≤ R := fun s _ =>
    (norm_IccExtend_le hT g s).trans hg
  have hclose : ∀ s ∈ Icc (0 : ℝ) T, ‖IccExtend hT f s - IccExtend hT g s‖ ≤ dist f g :=
    fun s _ => norm_IccExtend_sub_le hT f g s
  have hsub := C.norm_duhamelIntegral_sub_le hT t.2 hextf hextg hR hbf hbg hclose
  have hKt : C.kernelPrimitive t.1 ≤ C.kernelPrimitive T :=
    C.kernelPrimitive_mono hT t.2 (right_mem_Icc.mpr hT) t.2.2
  have hpt : C.picardMap hT u₀ f t - C.picardMap hT u₀ g t =
      C.duhamelIntegral (IccExtend hT g) t.1 - C.duhamelIntegral (IccExtend hT f) t.1 := by
    rw [C.picardMap_apply, C.picardMap_apply]
    abel
  calc
    dist (C.picardMap hT u₀ f t) (C.picardMap hT u₀ g t) =
        ‖C.duhamelIntegral (IccExtend hT g) t.1 -
          C.duhamelIntegral (IccExtend hT f) t.1‖ := by
      rw [dist_eq_norm, hpt]
    _ = ‖C.duhamelIntegral (IccExtend hT f) t.1 -
          C.duhamelIntegral (IccExtend hT g) t.1‖ := norm_sub_rev _ _
    _ ≤ ‖C.bilinear‖ * (2 * R) * dist f g * C.kernelPrimitive t.1 := hsub
    _ ≤ ‖C.bilinear‖ * (2 * R) * dist f g * C.kernelPrimitive T := by
      apply mul_le_mul_of_nonneg_left hKt
      positivity
    _ = ‖C.bilinear‖ * (2 * R) * C.kernelPrimitive T * dist f g := by ring

end Picard

/-! ## Local existence and closed-ball uniqueness -/

section Existence

variable [CompleteSpace X]

/--
Quantitative form of the local existence theorem: **any** horizon whose cumulative smoothing
mass lies below the explicit `‖u₀‖`-threshold carries a mild solution with the ball bound
and ball uniqueness.  This is the entry point for explicit lifespan bounds.
-/
theorem exists_isMildSolutionOn_of_kernelPrimitive_lt
    (hcontr : ∀ (t : ℝ≥0) (x : X), ‖C.linearEvolution t x‖ ≤ ‖x‖) (u₀ : X) {T : ℝ}
    (hTpos : 0 < T)
    (hKTδ : C.kernelPrimitive T <
      min (1 / (‖C.bilinear‖ * (‖u₀‖ + 1) ^ 2 + 1))
        (1 / (2 * (‖C.bilinear‖ * (2 * (‖u₀‖ + 1)) + 1)))) :
    ∃ u : ℝ → X,
      C.IsMildSolutionOn T u₀ u ∧
      (∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ ‖u₀‖ + 1) ∧
      ∀ v : ℝ → X, C.IsMildSolutionOn T u₀ v →
        (∀ t ∈ Icc (0 : ℝ) T, ‖v t‖ ≤ ‖u₀‖ + 1) →
        ∀ t ∈ Icc (0 : ℝ) T, v t = u t := by
  classical
  set R : ℝ := ‖u₀‖ + 1 with hRdef
  have hR0 : 0 ≤ R := by positivity
  set δ : ℝ := min (1 / (‖C.bilinear‖ * R ^ 2 + 1)) (1 / (2 * (‖C.bilinear‖ * (2 * R) + 1)))
    with hδdef
  have hT0 : (0 : ℝ) ≤ T := hTpos.le
  have hKT0 : 0 ≤ C.kernelPrimitive T := C.kernelPrimitive_nonneg hT0
  -- ball invariance constant
  have hInv : ‖C.bilinear‖ * R ^ 2 * C.kernelPrimitive T ≤ 1 := by
    have hKle : C.kernelPrimitive T ≤ 1 / (‖C.bilinear‖ * R ^ 2 + 1) :=
      (hKTδ.trans_le (min_le_left _ _)).le
    have hstep : ‖C.bilinear‖ * R ^ 2 * C.kernelPrimitive T ≤
        ‖C.bilinear‖ * R ^ 2 * (1 / (‖C.bilinear‖ * R ^ 2 + 1)) :=
      mul_le_mul_of_nonneg_left hKle (by positivity)
    have harith : ‖C.bilinear‖ * R ^ 2 * (1 / (‖C.bilinear‖ * R ^ 2 + 1)) ≤ 1 := by
      have hpos : (0 : ℝ) < ‖C.bilinear‖ * R ^ 2 + 1 := by positivity
      rw [mul_one_div, div_le_one hpos]
      linarith
    linarith
  -- contraction constant
  set θ : ℝ := ‖C.bilinear‖ * (2 * R) * C.kernelPrimitive T with hθdef
  have hθ0 : 0 ≤ θ := by positivity
  have hθlt : θ < 1 := by
    have hKle : C.kernelPrimitive T ≤ 1 / (2 * (‖C.bilinear‖ * (2 * R) + 1)) :=
      (hKTδ.trans_le (min_le_right _ _)).le
    have hstep : θ ≤ ‖C.bilinear‖ * (2 * R) * (1 / (2 * (‖C.bilinear‖ * (2 * R) + 1))) :=
      mul_le_mul_of_nonneg_left hKle (by positivity)
    have harith : ‖C.bilinear‖ * (2 * R) * (1 / (2 * (‖C.bilinear‖ * (2 * R) + 1))) < 1 := by
      have hpos : (0 : ℝ) < 2 * (‖C.bilinear‖ * (2 * R) + 1) := by positivity
      rw [mul_one_div, div_lt_one hpos]
      nlinarith [norm_nonneg C.bilinear, hR0]
    linarith
  -- the closed ball as a complete nonempty metric space
  set S : Set C(Icc (0 : ℝ) T, X) := Metric.closedBall 0 R with hSdef
  have hSclosed : IsClosed S := Metric.isClosed_closedBall
  haveI hScomplete : CompleteSpace S :=
    completeSpace_coe_iff_isComplete.mpr hSclosed.isComplete
  haveI hSnonempty : Nonempty S := ⟨⟨0, by simp [hSdef, hR0]⟩⟩
  have hmemS : ∀ {f : C(Icc (0 : ℝ) T, X)}, f ∈ S ↔ ‖f‖ ≤ R := by
    intro f
    simp [hSdef, Metric.mem_closedBall, dist_zero_right]
  -- the Picard self-map of the ball
  have hΦmaps : ∀ f : S, C.picardMap hT0 u₀ f.1 ∈ S := by
    intro f
    rw [hmemS]
    have hf : ‖f.1‖ ≤ R := hmemS.mp f.2
    have := C.norm_picardMap_le hT0 hcontr u₀ hf
    calc
      ‖C.picardMap hT0 u₀ f.1‖ ≤ ‖u₀‖ + ‖C.bilinear‖ * R ^ 2 * C.kernelPrimitive T := this
      _ ≤ ‖u₀‖ + 1 := by linarith
      _ = R := hRdef.symm
  set Φ : S → S := fun f => ⟨C.picardMap hT0 u₀ f.1, hΦmaps f⟩ with hΦdef
  have hΦlip : ∀ f g : S, dist (Φ f) (Φ g) ≤ θ * dist f g := by
    intro f g
    have hf : ‖f.1‖ ≤ R := hmemS.mp f.2
    have hg : ‖g.1‖ ≤ R := hmemS.mp g.2
    have h := C.dist_picardMap_le hT0 u₀ hR0 hf hg
    calc
      dist (Φ f) (Φ g) = dist (C.picardMap hT0 u₀ f.1) (C.picardMap hT0 u₀ g.1) :=
        Subtype.dist_eq _ _
      _ ≤ ‖C.bilinear‖ * (2 * R) * C.kernelPrimitive T * dist f.1 g.1 := h
      _ = θ * dist f g := by rw [hθdef, Subtype.dist_eq]
  have hΦcontr : ContractingWith θ.toNNReal Φ := by
    constructor
    · exact Real.toNNReal_lt_one.mpr hθlt
    · refine LipschitzWith.of_dist_le_mul fun f g => ?_
      rw [Real.coe_toNNReal θ hθ0]
      exact hΦlip f g
  -- the fixed point and its induced trajectory
  set fstar : S := ContractingWith.fixedPoint Φ hΦcontr with hfstardef
  have hfix : Function.IsFixedPt Φ fstar := hΦcontr.fixedPoint_isFixedPt
  have hfixval : C.picardMap hT0 u₀ fstar.1 = fstar.1 := congrArg Subtype.val hfix
  set u : ℝ → X := IccExtend hT0 fstar.1 with hudef
  have hucont : Continuous u := fstar.1.continuous.Icc_extend'
  have huval : ∀ t : ℝ, ∀ ht : t ∈ Icc (0 : ℝ) T, u t = fstar.1 ⟨t, ht⟩ := by
    intro t ht
    exact IccExtend_of_mem hT0 fstar.1 ht
  have hunorm : ∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ R := by
    intro t ht
    rw [huval t ht]
    exact (fstar.1.norm_coe_le_norm _).trans (hmemS.mp fstar.2)
  -- pointwise fixed-point equation
  have hueq : ∀ t : ℝ, ∀ ht : t ∈ Icc (0 : ℝ) T,
      u t = C.linearEvolution (Real.toNNReal t) u₀ - C.duhamelIntegral u t := by
    intro t ht
    have h := congrArg (fun F : C(Icc (0 : ℝ) T, X) => F ⟨t, ht⟩) hfixval
    simp only [C.picardMap_apply] at h
    rw [huval t ht, ← h, hudef]
  -- the mild solution certificate
  have hmild : C.IsMildSolutionOn T u₀ u := by
    refine ⟨hT0, hucont.continuousOn, ?_, ?_⟩
    · have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := left_mem_Icc.mpr hT0
      have h := hueq 0 h0mem
      rw [Real.toNNReal_zero, C.linear_zero] at h
      simpa using h
    · intro t ht
      have htnn : Real.toNNReal t = (⟨t, ht.1⟩ : ℝ≥0) := Real.toNNReal_of_nonneg ht.1
      constructor
      · exact C.intervalIntegrable_duhamelIntegrand_of_continuousOn ht.1
          (hucont.continuousOn)
      · have h := hueq t ht
        rw [← htnn, Real.coe_toNNReal t ht.1]
        simpa only [duhamelIntegral] using h
  refine ⟨u, hmild, fun t ht => (hunorm t ht).trans_eq rfl, ?_⟩
  -- ball uniqueness
  intro v hv hvball t ht
  have hvcont : ContinuousOn v (Icc (0 : ℝ) T) := hv.2.1
  set fv : C(Icc (0 : ℝ) T, X) :=
    ⟨fun t => v t.1, continuousOn_iff_continuous_restrict.mp hvcont⟩ with hfvdef
  have hfvnorm : ‖fv‖ ≤ R := by
    rw [ContinuousMap.norm_le _ hR0]
    intro s
    exact hvball s.1 s.2
  have hfvmem : fv ∈ S := hmemS.mpr hfvnorm
  have hextfv : ∀ s ∈ Icc (0 : ℝ) T, IccExtend hT0 fv s = v s := by
    intro s hs
    rw [IccExtend_of_mem hT0 fv hs]
    rfl
  have hfvfix : Function.IsFixedPt Φ ⟨fv, hfvmem⟩ := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro s
    have hs := s.2
    have hveq := (C.equation_at_time hv hs).2
    have hcongr : C.duhamelIntegral (IccExtend hT0 fv) s.1 = C.duhamelIntegral v s.1 := by
      simp only [duhamelIntegral]
      apply intervalIntegral.integral_congr
      intro σ hσ
      have hσmem : σ ∈ Icc (0 : ℝ) T := by
        rw [uIcc_of_le hs.1] at hσ
        exact ⟨hσ.1, hσ.2.trans hs.2⟩
      simp only [duhamelIntegrand, endpointSafeTwoSpaceDuhamelIntegrand]
      rw [hextfv σ hσmem]
    have htnn : Real.toNNReal s.1 = (⟨s.1, hs.1⟩ : ℝ≥0) := Real.toNNReal_of_nonneg hs.1
    show C.picardMap hT0 u₀ fv s = fv s
    rw [C.picardMap_apply, hcongr, htnn]
    calc
      C.linearEvolution ⟨s.1, hs.1⟩ u₀ - C.duhamelIntegral v s.1 = v s.1 := by
        simp only [duhamelIntegral]
        exact hveq.symm
      _ = fv s := rfl
  have hfveq : (⟨fv, hfvmem⟩ : S) = fstar := hΦcontr.fixedPoint_unique hfvfix
  have hfveqval : fv = fstar.1 := congrArg Subtype.val hfveq
  calc
    v t = fv ⟨t, ht⟩ := rfl
    _ = fstar.1 ⟨t, ht⟩ := by rw [hfveqval]
    _ = u t := (huval t ht).symm

/--
Local-in-time existence with closed-ball uniqueness for the endpoint-safe two-space mild
equation, for any contract whose same-space linear evolution is contractive.

The produced horizon satisfies `0 < T ≤ 1`.  The mild solution stays in the closed ball of
radius `‖u₀‖ + 1`, and any mild solution on the same horizon staying in that ball agrees with
it there.  Nothing is claimed outside `[0, T]`, and no uniqueness is claimed outside the ball.
-/
theorem exists_pos_time_isMildSolutionOn
    (hcontr : ∀ (t : ℝ≥0) (x : X), ‖C.linearEvolution t x‖ ≤ ‖x‖) (u₀ : X) :
    ∃ T : ℝ, 0 < T ∧ T ≤ 1 ∧ ∃ u : ℝ → X,
      C.IsMildSolutionOn T u₀ u ∧
      (∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ ‖u₀‖ + 1) ∧
      ∀ v : ℝ → X, C.IsMildSolutionOn T u₀ v →
        (∀ t ∈ Icc (0 : ℝ) T, ‖v t‖ ≤ ‖u₀‖ + 1) →
        ∀ t ∈ Icc (0 : ℝ) T, v t = u t := by
  have hδpos : 0 < min (1 / (‖C.bilinear‖ * (‖u₀‖ + 1) ^ 2 + 1))
      (1 / (2 * (‖C.bilinear‖ * (2 * (‖u₀‖ + 1)) + 1))) := by
    apply lt_min
    · apply div_pos one_pos
      positivity
    · apply div_pos one_pos
      positivity
  obtain ⟨T, hTpos, hT1, hKTδ⟩ := C.exists_pos_time_kernelPrimitive_lt one_pos hδpos
  obtain ⟨u, hu⟩ := C.exists_isMildSolutionOn_of_kernelPrimitive_lt hcontr u₀ hTpos hKTδ
  exact ⟨T, hTpos, hT1, u, hu⟩

end Existence

end EndpointSafeTwoSpaceDuhamelContract

end

end MNS2
