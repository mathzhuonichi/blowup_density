import Formal.R3EndpointSafeProjectedDuhamel

/-!
# Mild restart identity

A mild solution restarted at a certified time `s` is again a mild solution: the shifted
trajectory `τ ↦ u (s + τ)` satisfies the endpoint-safe two-space mild equation on
`[0, T - s]` with initial datum `u s`.

This is the shared enabling lemma for unrestricted uniqueness and for the maximal
continuation argument.  The proof splits the Duhamel integral at `s`, pushes the linear
evolution out of the head piece by `smoothing_coherent` (a.e. on `(0, s)`; the single point
`σ = s` is null), and translates the tail piece by `σ ↦ s + σ`, which matches the shifted
integrand exactly (both sides vanish at nonpositive shifted elapsed time).

Scope guard: this file proves only the restart identity, abstractly and for the concrete
`R³` contract.  No uniqueness beyond the existing ball clause, no continuation criterion,
and no Clay statement.
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

omit [NormedSpace ℝ X] [CompleteSpace X] in
/-- Value-congruence for the positive-time smoothing family (the positivity proofs are
irrelevant). -/
theorem positiveSmoothing_congr {a b : ℝ} (hab : a = b) (ha : 0 < a) :
    C.positiveSmoothing a ha = C.positiveSmoothing b (hab ▸ ha) := by
  cases hab
  rfl

omit [NormedSpace ℝ X] [CompleteSpace X] in
/-- Applied form of `positiveSmoothing_congr`, for congruence chains that avoid rewriting
under dependent positivity proofs. -/
theorem positiveSmoothing_congr_apply {a b : ℝ} (hab : a = b) (ha : 0 < a) (y : Y) :
    C.positiveSmoothing a ha y = C.positiveSmoothing b (hab ▸ ha) y := by
  cases hab
  rfl

omit [NormedSpace ℝ X] [CompleteSpace X] in
/-- The endpoint-safe Duhamel integrand of the shifted trajectory is the translate of the
original integrand — at every point, with no measure-zero exception. -/
theorem duhamelIntegrand_comp_add_left (t s : ℝ) (u : ℝ → X) (σ : ℝ) :
    C.duhamelIntegrand (s + t) u (s + σ) =
      C.duhamelIntegrand t (fun τ => u (s + τ)) σ := by
  by_cases hσ : σ < t
  · rw [C.duhamelIntegrand_of_lt t _ hσ,
      C.duhamelIntegrand_of_lt (s + t) u (by linarith : s + σ < s + t),
      C.positiveSmoothing_congr (show s + t - (s + σ) = t - σ by ring)]
  · rw [C.duhamelIntegrand_of_le t _ (not_lt.mp hσ),
      C.duhamelIntegrand_of_le (s + t) u (by linarith [not_lt.mp hσ] : s + t ≤ s + σ)]

/-- **Mild restart identity**: a mild solution restarted at a certified time `s` is a mild
solution of the shifted problem on `[0, T - s]` with initial datum `u s`. -/
theorem IsMildSolutionOn.restart {T : ℝ} {u₀ : X} {u : ℝ → X}
    (h : C.IsMildSolutionOn T u₀ u) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) T) :
    C.IsMildSolutionOn (T - s) (u s) fun τ => u (s + τ) := by
  obtain ⟨hT0, hucont, hu0, hmild⟩ := h
  have hs0 : 0 ≤ s := hs.1
  have hsT : s ≤ T := hs.2
  refine ⟨by linarith, ?_, by simp, ?_⟩
  · -- continuity of the shifted trajectory
    have hmap : MapsTo (fun τ : ℝ => s + τ) (Icc (0 : ℝ) (T - s)) (Icc (0 : ℝ) T) :=
      fun τ hτ => ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
    exact hucont.comp ((continuous_const.add continuous_id).continuousOn) hmap
  · intro τ hτ
    have hτ0 : (0 : ℝ) ≤ τ := hτ.1
    have hst : s + τ ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith [hτ.2]⟩
    obtain ⟨hint_st, heq_st⟩ := hmild (s + τ) hst
    obtain ⟨hint_s, heq_s⟩ := hmild s hs
    -- integrability clause: the shifted trajectory is continuous on `[0, τ]`
    have hvcont : ContinuousOn (fun τ' : ℝ => u (s + τ')) (Icc (0 : ℝ) τ) := by
      have hmap : MapsTo (fun τ' : ℝ => s + τ') (Icc (0 : ℝ) τ) (Icc (0 : ℝ) T) :=
        fun τ' hτ' => ⟨by linarith [hτ'.1], by linarith [hτ'.2, hτ.2]⟩
      exact hucont.comp ((continuous_const.add continuous_id).continuousOn) hmap
    have hint_v : IntervalIntegrable
        (C.duhamelIntegrand τ fun τ' => u (s + τ')) volume 0 τ :=
      C.intervalIntegrable_duhamelIntegrand_of_continuousOn hτ0 hvcont
    refine ⟨hint_v, ?_⟩
    -- split the full Duhamel integral at `s`
    have hsub1 : Set.uIcc (0 : ℝ) s ⊆ Set.uIcc (0 : ℝ) (s + τ) := by
      rw [Set.uIcc_of_le hs0, Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ s + τ)]
      exact Icc_subset_Icc le_rfl (by linarith)
    have hsub2 : Set.uIcc s (s + τ) ⊆ Set.uIcc (0 : ℝ) (s + τ) := by
      rw [Set.uIcc_of_le (by linarith : s ≤ s + τ),
        Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ s + τ)]
      exact Icc_subset_Icc hs0 le_rfl
    have hint1 : IntervalIntegrable (C.duhamelIntegrand (s + τ) u) volume 0 s :=
      hint_st.mono_set hsub1
    have hint2 : IntervalIntegrable (C.duhamelIntegrand (s + τ) u) volume s (s + τ) :=
      hint_st.mono_set hsub2
    have hsplit : (∫ σ in (0 : ℝ)..(s + τ), C.duhamelIntegrand (s + τ) u σ) =
        (∫ σ in (0 : ℝ)..s, C.duhamelIntegrand (s + τ) u σ) +
          ∫ σ in s..(s + τ), C.duhamelIntegrand (s + τ) u σ :=
      (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
    -- head piece: push the linear evolution out (a.e.; the point `σ = s` is null)
    have hone : ∀ᵐ σ ∂(volume : Measure ℝ), σ ≠ s :=
      compl_mem_ae_iff.mpr (measure_singleton s)
    have hhead : (∫ σ in (0 : ℝ)..s, C.duhamelIntegrand (s + τ) u σ) =
        ∫ σ in (0 : ℝ)..s,
          C.linearEvolution ⟨τ, hτ0⟩ (C.duhamelIntegrand s u σ) := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hone] with σ hσne hσmem
      rw [Set.uIoc_of_le hs0] at hσmem
      have hσlt : σ < s := lt_of_le_of_ne hσmem.2 hσne
      have h1 : σ < s + τ := by linarith
      have hspos : (0 : ℝ) < s - σ := by linarith
      have hcoh := congrArg (fun L : Y →L[𝕜] X => L (C.bilinear (u σ) (u σ)))
        (C.smoothing_coherent (s - σ) hspos ⟨τ, hτ0⟩)
      have hval := C.positiveSmoothing_congr_apply
        (show s + τ - σ = (s - σ) + ((⟨τ, hτ0⟩ : ℝ≥0) : ℝ) by push_cast; ring)
        (sub_pos.mpr h1) (C.bilinear (u σ) (u σ))
      rw [C.duhamelIntegrand_of_lt (s + τ) u h1, C.duhamelIntegrand_of_lt s u hσlt]
      exact hval.trans hcoh
    -- tail piece: translate by `s`
    have htail : (∫ σ in s..(s + τ), C.duhamelIntegrand (s + τ) u σ) =
        ∫ σ in (0 : ℝ)..τ, C.duhamelIntegrand τ (fun τ' => u (s + τ')) σ := by
      calc (∫ σ in s..(s + τ), C.duhamelIntegrand (s + τ) u σ)
          = ∫ σ in (0 : ℝ)..τ, C.duhamelIntegrand (s + τ) u (s + σ) := by simp
        _ = ∫ σ in (0 : ℝ)..τ, C.duhamelIntegrand τ (fun τ' => u (s + τ')) σ :=
            intervalIntegral.integral_congr fun σ _ =>
              C.duhamelIntegrand_comp_add_left τ s u σ
    -- semigroup law on the initial term
    have hsg : C.linearEvolution ⟨s + τ, hst.1⟩ u₀ =
        C.linearEvolution ⟨τ, hτ0⟩ (C.linearEvolution ⟨s, hs0⟩ u₀) := by
      have hmk : (⟨s + τ, hst.1⟩ : ℝ≥0) = ⟨τ, hτ0⟩ + ⟨s, hs0⟩ := by
        ext
        push_cast
        ring
      have happ := congrArg (fun L : X →L[𝕜] X => L u₀)
        (C.linear_add ⟨τ, hτ0⟩ ⟨s, hs0⟩)
      rw [hmk]
      exact happ
    -- assemble the shifted mild equation
    calc u (s + τ)
        = C.linearEvolution ⟨s + τ, hst.1⟩ u₀ -
            ∫ σ in (0 : ℝ)..(s + τ), C.duhamelIntegrand (s + τ) u σ := heq_st
      _ = C.linearEvolution ⟨τ, hτ0⟩ (C.linearEvolution ⟨s, hs0⟩ u₀) -
            ((∫ σ in (0 : ℝ)..s,
                C.linearEvolution ⟨τ, hτ0⟩ (C.duhamelIntegrand s u σ)) +
              ∫ σ in (0 : ℝ)..τ,
                C.duhamelIntegrand τ (fun τ' => u (s + τ')) σ) := by
          rw [hsg, hsplit, hhead, htail]
      _ = C.linearEvolution ⟨τ, hτ0⟩ (C.linearEvolution ⟨s, hs0⟩ u₀) -
            (C.linearEvolution ⟨τ, hτ0⟩
                (∫ σ in (0 : ℝ)..s, C.duhamelIntegrand s u σ) +
              ∫ σ in (0 : ℝ)..τ,
                C.duhamelIntegrand τ (fun τ' => u (s + τ')) σ) := by
          congr 1
          congr 1
          exact (C.linearEvolution ⟨τ, hτ0⟩).intervalIntegral_comp_comm hint_s
      _ = C.linearEvolution ⟨τ, hτ0⟩
            (C.linearEvolution ⟨s, hs0⟩ u₀ -
              ∫ σ in (0 : ℝ)..s, C.duhamelIntegrand s u σ) -
            ∫ σ in (0 : ℝ)..τ,
              C.duhamelIntegrand τ (fun τ' => u (s + τ')) σ := by
          rw [map_sub]
          abel
      _ = C.linearEvolution ⟨τ, hτ0⟩ (u s) -
            ∫ σ in (0 : ℝ)..τ,
              C.duhamelIntegrand τ (fun τ' => u (s + τ')) σ := by
          congr 1
          congr 1
          exact heq_s.symm

end EndpointSafeTwoSpaceDuhamelContract

/-- Concrete form of the mild restart identity on the `R³` endpoint-safe projected
contract. -/
theorem IsR3EndpointSafeProjectedMildSolutionOn.restart {nu T : ℝ} {hnu : 0 < nu}
    {u0 : R3HsVelocity 3} {u : ℝ → R3HsVelocity 3}
    (h : IsR3EndpointSafeProjectedMildSolutionOn hnu T u0 u) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) T) :
    IsR3EndpointSafeProjectedMildSolutionOn hnu (T - s) (u s) fun τ => u (s + τ) :=
  EndpointSafeTwoSpaceDuhamelContract.IsMildSolutionOn.restart
    (r3EndpointSafeProjectedDuhamelContract hnu) h hs

end

end MNS2
