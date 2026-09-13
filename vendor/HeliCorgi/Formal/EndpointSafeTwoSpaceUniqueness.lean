import Formal.EndpointSafeTwoSpacePicard
import Formal.EndpointSafeTwoSpaceRestart
import Formal.R3RealLocalMildSolution

/-!
# Unrestricted uniqueness for the endpoint-safe two-space mild equation

Two mild solutions with the same initial datum agree on their common horizon — with **no
ball restriction**.

The proof has two layers.

* **Contraction step** (`isMildSolutionOn_eq_of_contraction`): if both solutions stay in
  the `R`-ball and the horizon satisfies `‖B‖ · 2R · K(T) < 1`, the difference norm attains
  its maximum `M` on the compact horizon, and the mild equations give `M ≤ θ M` with
  `θ < 1`, so `M = 0`.  No fixed-point machinery is used.
* **Patching** (`IsMildSolutionOn.unique`): both trajectories are continuous, hence bounded
  by some common `R` on `[0, T]`.  Small-time smallness of the cumulative smoothing mass
  produces a step `T_s > 0` with `‖B‖ · 2R · K(T_s) < 1`; the mild restart identity walks
  the agreement window forward by `T_s` at a time, and the Archimedean property finishes.

Scope guard: this closes unconditional uniqueness on a certified horizon.  No continuation
criterion, no pressure reconstruction, and no Clay statement.
-/

namespace MNS2

open MeasureTheory Set
open scoped Interval NNReal

noncomputable section

namespace EndpointSafeTwoSpaceDuhamelContract

universe u v w

variable {𝕜 : Type u} {X : Type v} {Y : Type w}
variable [RCLike 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedSpace ℝ X] [CompleteSpace X]
variable (C : EndpointSafeTwoSpaceDuhamelContract 𝕜 X Y)

omit [CompleteSpace X] in
/-- Restriction of a mild solution to a shorter horizon. -/
theorem IsMildSolutionOn.mono {T T' : ℝ} {u₀ : X} {u : ℝ → X}
    (h : C.IsMildSolutionOn T u₀ u) (hT'0 : 0 ≤ T') (hT'T : T' ≤ T) :
    C.IsMildSolutionOn T' u₀ u := by
  obtain ⟨hT0, hcont, h0, hmild⟩ := h
  exact ⟨hT'0, hcont.mono (Icc_subset_Icc le_rfl hT'T), h0, fun t ht =>
    hmild t ⟨ht.1, ht.2.trans hT'T⟩⟩

/-- **Contraction step**: two `R`-ball mild solutions with the same datum agree on any
horizon whose cumulative smoothing mass is below the contraction threshold. -/
theorem isMildSolutionOn_eq_of_contraction {T R : ℝ} {u₀ : X} {u v : ℝ → X}
    (hu : C.IsMildSolutionOn T u₀ u) (hv : C.IsMildSolutionOn T u₀ v)
    (hR : 0 ≤ R)
    (hRu : ∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ R) (hRv : ∀ t ∈ Icc (0 : ℝ) T, ‖v t‖ ≤ R)
    (hθ : ‖C.bilinear‖ * (2 * R) * C.kernelPrimitive T < 1) :
    ∀ t ∈ Icc (0 : ℝ) T, u t = v t := by
  have hT0 : (0 : ℝ) ≤ T := hu.1
  have hucont : ContinuousOn u (Icc (0 : ℝ) T) := hu.2.1
  have hvcont : ContinuousOn v (Icc (0 : ℝ) T) := hv.2.1
  have hdcont : ContinuousOn (fun t => ‖u t - v t‖) (Icc (0 : ℝ) T) :=
    (hucont.sub hvcont).norm
  obtain ⟨tm, htm, htmax⟩ :=
    isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT0) hdcont
  have hMle : ∀ t ∈ Icc (0 : ℝ) T, ‖u t - v t‖ ≤ ‖u tm - v tm‖ := fun t ht =>
    isMaxOn_iff.mp htmax t ht
  have hMle' : ∀ t ∈ Icc (0 : ℝ) T, ‖v t - u t‖ ≤ ‖u tm - v tm‖ := fun t ht => by
    rw [norm_sub_rev]
    exact hMle t ht
  have hM0 : (0 : ℝ) ≤ ‖u tm - v tm‖ := norm_nonneg _
  -- the mild equations turn the difference into a difference of Duhamel integrals
  have hueq := (C.equation_at_time hu htm).2
  have hveq := (C.equation_at_time hv htm).2
  have hdiff : u tm - v tm = C.duhamelIntegral v tm - C.duhamelIntegral u tm := by
    simp only [duhamelIntegral]
    rw [hueq, hveq]
    abel
  have hkey : ‖u tm - v tm‖ ≤
      ‖C.bilinear‖ * (2 * R) * ‖u tm - v tm‖ * C.kernelPrimitive tm := by
    calc ‖u tm - v tm‖
        = ‖C.duhamelIntegral v tm - C.duhamelIntegral u tm‖ := by rw [hdiff]
      _ ≤ ‖C.bilinear‖ * (2 * R) * ‖u tm - v tm‖ * C.kernelPrimitive tm :=
          C.norm_duhamelIntegral_sub_le hT0 htm hvcont hucont hR hRv hRu hMle'
  have hB : (0 : ℝ) ≤ ‖C.bilinear‖ := C.bilinear.opNorm_nonneg
  have hKmono : C.kernelPrimitive tm ≤ C.kernelPrimitive T :=
    C.kernelPrimitive_mono hT0 htm (right_mem_Icc.mpr hT0) htm.2
  have hchain : ‖C.bilinear‖ * (2 * R) * ‖u tm - v tm‖ * C.kernelPrimitive tm ≤
      ‖C.bilinear‖ * (2 * R) * C.kernelPrimitive T * ‖u tm - v tm‖ := by
    have h1 : (0 : ℝ) ≤ ‖C.bilinear‖ * (2 * R) * ‖u tm - v tm‖ :=
      mul_nonneg (mul_nonneg hB (by linarith)) hM0
    calc ‖C.bilinear‖ * (2 * R) * ‖u tm - v tm‖ * C.kernelPrimitive tm
        ≤ ‖C.bilinear‖ * (2 * R) * ‖u tm - v tm‖ * C.kernelPrimitive T :=
          mul_le_mul_of_nonneg_left hKmono h1
      _ = ‖C.bilinear‖ * (2 * R) * C.kernelPrimitive T * ‖u tm - v tm‖ := by ring
  have hMzero : ‖u tm - v tm‖ ≤ 0 := by
    by_contra hpos
    have hpos' : (0 : ℝ) < ‖u tm - v tm‖ := not_le.mp hpos
    have hlt : ‖C.bilinear‖ * (2 * R) * C.kernelPrimitive T * ‖u tm - v tm‖ <
        1 * ‖u tm - v tm‖ := mul_lt_mul_of_pos_right hθ hpos'
    rw [one_mul] at hlt
    linarith
  intro t ht
  exact sub_eq_zero.mp (norm_le_zero_iff.mp ((hMle t ht).trans hMzero))

/-- **Unrestricted uniqueness**: two mild solutions with the same initial datum agree on
their common horizon, with no ball restriction. -/
theorem IsMildSolutionOn.unique {T : ℝ} {u₀ : X} {u v : ℝ → X}
    (hu : C.IsMildSolutionOn T u₀ u) (hv : C.IsMildSolutionOn T u₀ v) :
    ∀ t ∈ Icc (0 : ℝ) T, u t = v t := by
  have hT0 : (0 : ℝ) ≤ T := hu.1
  -- a common bound on both trajectories
  obtain ⟨Ru, hRu⟩ := isCompact_Icc.bddAbove_image hu.2.1.norm
  obtain ⟨Rv, hRv⟩ := isCompact_Icc.bddAbove_image hv.2.1.norm
  set R : ℝ := max (max Ru Rv) 0 with hRdef
  have hR0 : (0 : ℝ) ≤ R := le_max_right _ _
  have hRu' : ∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ R := fun t ht =>
    (hRu (mem_image_of_mem _ ht)).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hRv' : ∀ t ∈ Icc (0 : ℝ) T, ‖v t‖ ≤ R := fun t ht =>
    (hRv (mem_image_of_mem _ ht)).trans ((le_max_right _ _).trans (le_max_left _ _))
  -- a positive step horizon with contraction
  have hB : (0 : ℝ) ≤ ‖C.bilinear‖ := C.bilinear.opNorm_nonneg
  have ha : (0 : ℝ) ≤ ‖C.bilinear‖ * (2 * R) := mul_nonneg hB (by linarith)
  have hδpos : (0 : ℝ) < 1 / (‖C.bilinear‖ * (2 * R) + 1) :=
    div_pos one_pos (by linarith)
  obtain ⟨Ts, hTs_pos, _hTs1, hKTs⟩ :=
    C.exists_pos_time_kernelPrimitive_lt one_pos hδpos
  have hθs : ‖C.bilinear‖ * (2 * R) * C.kernelPrimitive Ts < 1 := by
    have h1 : ‖C.bilinear‖ * (2 * R) * C.kernelPrimitive Ts ≤
        ‖C.bilinear‖ * (2 * R) * (1 / (‖C.bilinear‖ * (2 * R) + 1)) :=
      mul_le_mul_of_nonneg_left hKTs.le ha
    have h2 : ‖C.bilinear‖ * (2 * R) * (1 / (‖C.bilinear‖ * (2 * R) + 1)) < 1 := by
      rw [mul_one_div, div_lt_one (by linarith)]
      linarith
    linarith
  -- stepwise agreement along multiples of the step horizon
  have hstep : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (min ((n : ℝ) * Ts) T), u t = v t := by
    intro n
    induction n with
    | zero =>
      intro t ht
      have ht0 : t = 0 := by
        have h1 := ht.2
        rw [show ((0 : ℕ) : ℝ) * Ts = 0 by push_cast; ring, min_eq_left hT0] at h1
        exact le_antisymm h1 ht.1
      rw [ht0, hu.2.2.1, hv.2.2.1]
    | succ n ih =>
      intro t ht
      by_cases hcase : t ≤ min ((n : ℝ) * Ts) T
      · exact ih t ⟨ht.1, hcase⟩
      · set s : ℝ := min ((n : ℝ) * Ts) T with hsdef
        have hts : s < t := not_le.mp hcase
        have hs0 : (0 : ℝ) ≤ s :=
          le_min (mul_nonneg (Nat.cast_nonneg n) hTs_pos.le) hT0
        have hsT : s ≤ T := min_le_right _ _
        have htT : t ≤ T := ht.2.trans (min_le_right _ _)
        have hs_mem : s ∈ Icc (0 : ℝ) T := ⟨hs0, hsT⟩
        -- restart both trajectories at `s` with the common datum
        have husv : u s = v s := ih s ⟨hs0, le_rfl⟩
        have hus := hu.restart C hs_mem
        have hvs := hv.restart C hs_mem
        rw [husv] at hus
        -- common short horizon
        set T' : ℝ := min Ts (T - s) with hT'def
        have hT'pos : (0 : ℝ) < T' := lt_min hTs_pos (by linarith)
        have hT'Ts : T' ≤ Ts := min_le_left _ _
        have hT'Tms : T' ≤ T - s := min_le_right _ _
        have hus' := hus.mono C hT'pos.le hT'Tms
        have hvs' := hvs.mono C hT'pos.le hT'Tms
        -- bounds for the shifted trajectories
        have hRu'' : ∀ τ ∈ Icc (0 : ℝ) T', ‖u (s + τ)‖ ≤ R := fun τ hτ =>
          hRu' (s + τ) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
        have hRv'' : ∀ τ ∈ Icc (0 : ℝ) T', ‖v (s + τ)‖ ≤ R := fun τ hτ =>
          hRv' (s + τ) ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
        -- contraction on the short horizon
        have hKle : C.kernelPrimitive T' ≤ C.kernelPrimitive Ts :=
          C.kernelPrimitive_mono hTs_pos.le ⟨hT'pos.le, hT'Ts⟩
            (right_mem_Icc.mpr hTs_pos.le) hT'Ts
        have hθ' : ‖C.bilinear‖ * (2 * R) * C.kernelPrimitive T' < 1 := by
          have := mul_le_mul_of_nonneg_left hKle ha
          linarith
        have hagree :=
          C.isMildSolutionOn_eq_of_contraction hus' hvs' hR0 hRu'' hRv'' hθ'
        -- transfer the agreement back to the original time variable
        have hsnT : s = (n : ℝ) * Ts := by
          rcases min_cases ((n : ℝ) * Ts) T with ⟨h1, _⟩ | ⟨h1, _⟩
          · rw [hsdef]
            exact h1
          · exfalso
            have hsT' : s = T := by
              rw [hsdef]
              exact h1
            linarith
        have ht2 : t ≤ ((n : ℝ) + 1) * Ts := by
          have h1 := ht.2.trans (min_le_left _ _)
          push_cast at h1
          linarith
        have htsub : t - s ∈ Icc (0 : ℝ) T' := by
          refine ⟨by linarith, le_min ?_ (by linarith)⟩
          have hstep' : t ≤ s + Ts := by
            rw [hsnT]
            linarith
          linarith
        have hfin : u (s + (t - s)) = v (s + (t - s)) := hagree (t - s) htsub
        rw [show s + (t - s) = t by ring] at hfin
        exact hfin
  -- Archimedean conclusion
  intro t ht
  obtain ⟨n, hn⟩ := exists_nat_ge (T / Ts)
  have hTn : T ≤ (n : ℝ) * Ts := by
    rw [div_le_iff₀ hTs_pos] at hn
    linarith
  exact hstep n t (by rw [min_eq_right hTn]; exact ht)

end EndpointSafeTwoSpaceDuhamelContract

/-- **Unrestricted uniqueness** for the concrete `R³` endpoint-safe projected mild
equation: two mild solutions with the same datum agree on their common horizon, with no
ball restriction and no realness assumption. -/
theorem r3EndpointSafeProjectedMildSolution_unique {nu T : ℝ} {hnu : 0 < nu}
    {u0 : R3HsVelocity 3} {u v : ℝ → R3HsVelocity 3}
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 u)
    (hv : IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 v) :
    ∀ t ∈ Icc (0 : ℝ) T, u t = v t :=
  EndpointSafeTwoSpaceDuhamelContract.IsMildSolutionOn.unique
    (r3EndpointSafeProjectedDuhamelContract hnu) hu hv

/-- **Unconditional realness**: every mild solution with physically real initial datum is
pointwise physically real on its certified horizon — no ball hypothesis.  The conjugated
trajectory is a mild solution with the same datum, and unrestricted uniqueness pins it to
the original. -/
theorem IsR3EndpointSafeProjectedMildSolutionOn.isR3RealVelocity {nu T : ℝ}
    {hnu : 0 < nu} {u0 : R3HsVelocity 3} {u : ℝ → R3HsVelocity 3}
    (h : IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 u)
    (hu0 : IsR3RealVelocity u0) :
    ∀ t ∈ Icc (0 : ℝ) T, IsR3RealVelocity (u t) := by
  have hconj := h.r3L2Conj_comp hnu hu0
  have hfix := r3EndpointSafeProjectedMildSolution_unique hconj h
  intro t ht
  exact hfix t ht

end

end MNS2
