import Formal.EndpointSafeTwoSpaceRestart

/-!
# Mild concatenation identity

The converse of the restart identity: a mild solution on `[0, s]` followed by a mild
solution started from the reached state `u s` glues to a mild solution on the joined
horizon `[0, s + T']`.

For times `t ≤ s` the glued trajectory agrees with `u` and the Duhamel integrand is
untouched.  For `t = s + τ` the computation of the restart identity runs in reverse: the
head piece of the split Duhamel integral absorbs the linear evolution by
`smoothing_coherent` (a.e.; the point `σ = s` is null), and the tail piece is the
translated Duhamel integral of `v`.

This is the extension device for the maximal continuation argument.

Scope guard: this file proves only the concatenation identity, abstractly and for the
concrete `R³` contract.  No continuation criterion and no Clay statement.
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

/-- **Mild concatenation identity**: a mild solution on `[0, s]` followed by a mild
solution from the reached state gives a mild solution on `[0, s + T']`. -/
theorem IsMildSolutionOn.concat {s T' : ℝ} {u₀ : X} {u v : ℝ → X}
    (hu : C.IsMildSolutionOn s u₀ u) (hv : C.IsMildSolutionOn T' (u s) v) :
    C.IsMildSolutionOn (s + T') u₀ fun t => if t ≤ s then u t else v (t - s) := by
  obtain ⟨hs0, hucont, hu0, humild⟩ := hu
  obtain ⟨hT'0, hvcont, hv0, hvmild⟩ := hv
  -- value laws of the glued trajectory
  have hw_le : ∀ t : ℝ, t ≤ s → (if t ≤ s then u t else v (t - s)) = u t :=
    fun t htle => if_pos htle
  have hw_shift : ∀ τ : ℝ, 0 ≤ τ →
      (if s + τ ≤ s then u (s + τ) else v (s + τ - s)) = v τ := by
    intro τ hτ0
    rcases eq_or_lt_of_le hτ0 with h | h
    · rw [← h, add_zero, if_pos le_rfl, hv0]
    · rw [if_neg (by linarith : ¬ s + τ ≤ s), show s + τ - s = τ by ring]
  -- continuity of the glued trajectory
  have hwcont : ContinuousOn (fun t => if t ≤ s then u t else v (t - s))
      (Icc (0 : ℝ) (s + T')) := by
    have hsplit : Icc (0 : ℝ) (s + T') = Icc 0 s ∪ Icc s (s + T') :=
      (Icc_union_Icc_eq_Icc hs0 (by linarith)).symm
    rw [hsplit]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · refine hucont.congr ?_
      intro t ht
      exact hw_le t ht.2
    · have hvs : ContinuousOn (fun t => v (t - s)) (Icc s (s + T')) := by
        have hmap : MapsTo (fun t : ℝ => t - s) (Icc s (s + T')) (Icc (0 : ℝ) T') :=
          fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
        exact hvcont.comp ((continuous_id.sub continuous_const).continuousOn) hmap
      refine hvs.congr ?_
      intro t ht
      show (if t ≤ s then u t else v (t - s)) = v (t - s)
      rcases eq_or_lt_of_le ht.1 with h | h
      · rw [← h, if_pos le_rfl, sub_self, hv0]
      · rw [if_neg (by linarith : ¬ t ≤ s)]
  refine ⟨by linarith, hwcont, ?_, ?_⟩
  · show (if (0 : ℝ) ≤ s then u 0 else v (0 - s)) = u₀
    rw [if_pos hs0, hu0]
  intro t ht
  by_cases hcase : t ≤ s
  · -- the glued trajectory satisfies `u`'s mild equation verbatim
    obtain ⟨hint_u, heq_u⟩ := humild t ⟨ht.1, hcase⟩
    have hIeq : C.duhamelIntegrand t (fun t' => if t' ≤ s then u t' else v (t' - s)) =
        C.duhamelIntegrand t u := by
      funext σ
      by_cases hσ : σ < t
      · rw [C.duhamelIntegrand_of_lt t _ hσ, C.duhamelIntegrand_of_lt t u hσ,
          hw_le σ (by linarith)]
      · rw [C.duhamelIntegrand_of_le t _ (not_lt.mp hσ),
          C.duhamelIntegrand_of_le t u (not_lt.mp hσ)]
    refine ⟨?_, ?_⟩
    · show IntervalIntegrable
        (C.duhamelIntegrand t fun t' => if t' ≤ s then u t' else v (t' - s)) volume 0 t
      rw [hIeq]
      exact hint_u
    · calc (fun t' => if t' ≤ s then u t' else v (t' - s)) t
          = u t := hw_le t hcase
        _ = C.linearEvolution ⟨t, ht.1⟩ u₀ -
              ∫ σ in (0 : ℝ)..t, C.duhamelIntegrand t u σ := heq_u
        _ = C.linearEvolution ⟨t, ht.1⟩ u₀ -
              ∫ σ in (0 : ℝ)..t,
                C.duhamelIntegrand t (fun t' => if t' ≤ s then u t' else v (t' - s)) σ := by
            rw [hIeq]
  · -- rename `t = s + τ` and reverse the restart computation
    have hst : s < t := not_le.mp hcase
    obtain ⟨τ, rfl⟩ : ∃ τ, t = s + τ := ⟨t - s, by ring⟩
    have hτpos : (0 : ℝ) < τ := by linarith
    have hτ0 : (0 : ℝ) ≤ τ := hτpos.le
    have hτT' : τ ≤ T' := by linarith [ht.2]
    obtain ⟨hint_v, heq_v⟩ := hvmild τ ⟨hτ0, hτT'⟩
    obtain ⟨hint_s, heq_s⟩ := humild s (right_mem_Icc.mpr hs0)
    -- integrability clause via continuity of the glued trajectory
    have hwcont' : ContinuousOn (fun t' => if t' ≤ s then u t' else v (t' - s))
        (Icc (0 : ℝ) (s + τ)) := hwcont.mono (Icc_subset_Icc le_rfl ht.2)
    have hint_w : IntervalIntegrable
        (C.duhamelIntegrand (s + τ) fun t' => if t' ≤ s then u t' else v (t' - s))
        volume 0 (s + τ) :=
      C.intervalIntegrable_duhamelIntegrand_of_continuousOn ht.1 hwcont'
    refine ⟨hint_w, ?_⟩
    -- split the full Duhamel integral at `s`
    have hsub1 : Set.uIcc (0 : ℝ) s ⊆ Set.uIcc (0 : ℝ) (s + τ) := by
      rw [Set.uIcc_of_le hs0, Set.uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl (by linarith)
    have hsub2 : Set.uIcc s (s + τ) ⊆ Set.uIcc (0 : ℝ) (s + τ) := by
      rw [Set.uIcc_of_le (by linarith : s ≤ s + τ), Set.uIcc_of_le ht.1]
      exact Icc_subset_Icc hs0 le_rfl
    have hint1 := hint_w.mono_set hsub1
    have hint2 := hint_w.mono_set hsub2
    have hsplit : (∫ σ in (0 : ℝ)..(s + τ),
          C.duhamelIntegrand (s + τ) (fun t' => if t' ≤ s then u t' else v (t' - s)) σ) =
        (∫ σ in (0 : ℝ)..s,
          C.duhamelIntegrand (s + τ) (fun t' => if t' ≤ s then u t' else v (t' - s)) σ) +
          ∫ σ in s..(s + τ),
            C.duhamelIntegrand (s + τ) (fun t' => if t' ≤ s then u t' else v (t' - s)) σ :=
      (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
    -- head piece: the glued integrand is `u`'s integrand pushed through the evolution
    have hone : ∀ᵐ σ ∂(volume : Measure ℝ), σ ≠ s :=
      compl_mem_ae_iff.mpr (measure_singleton s)
    have hhead : (∫ σ in (0 : ℝ)..s,
          C.duhamelIntegrand (s + τ) (fun t' => if t' ≤ s then u t' else v (t' - s)) σ) =
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
      rw [C.duhamelIntegrand_of_lt (s + τ) _ h1, C.duhamelIntegrand_of_lt s u hσlt,
        hw_le σ (by linarith : σ ≤ s)]
      exact hval.trans hcoh
    -- tail piece: translate to `v`'s Duhamel integral
    have htail : (∫ σ in s..(s + τ),
          C.duhamelIntegrand (s + τ) (fun t' => if t' ≤ s then u t' else v (t' - s)) σ) =
        ∫ σ in (0 : ℝ)..τ, C.duhamelIntegrand τ v σ := by
      calc (∫ σ in s..(s + τ),
            C.duhamelIntegrand (s + τ) (fun t' => if t' ≤ s then u t' else v (t' - s)) σ)
          = ∫ σ in (0 : ℝ)..τ,
              C.duhamelIntegrand (s + τ)
                (fun t' => if t' ≤ s then u t' else v (t' - s)) (s + σ) := by simp
        _ = ∫ σ in (0 : ℝ)..τ,
              C.duhamelIntegrand τ
                (fun x => if s + x ≤ s then u (s + x) else v (s + x - s)) σ :=
            intervalIntegral.integral_congr fun σ _ =>
              C.duhamelIntegrand_comp_add_left τ s _ σ
        _ = ∫ σ in (0 : ℝ)..τ, C.duhamelIntegrand τ v σ := by
            refine intervalIntegral.integral_congr fun σ hσ => ?_
            rw [Set.uIcc_of_le hτ0] at hσ
            by_cases hστ : σ < τ
            · rw [C.duhamelIntegrand_of_lt τ _ hστ, C.duhamelIntegrand_of_lt τ v hστ,
                hw_shift σ hσ.1]
            · rw [C.duhamelIntegrand_of_le τ _ (not_lt.mp hστ),
                C.duhamelIntegrand_of_le τ v (not_lt.mp hστ)]
    -- semigroup law on the initial term
    have hsg : C.linearEvolution ⟨s + τ, ht.1⟩ u₀ =
        C.linearEvolution ⟨τ, hτ0⟩ (C.linearEvolution ⟨s, hs0⟩ u₀) := by
      have hmk : (⟨s + τ, ht.1⟩ : ℝ≥0) = ⟨τ, hτ0⟩ + ⟨s, hs0⟩ := by
        ext
        push_cast
        ring
      have happ := congrArg (fun L : X →L[𝕜] X => L u₀)
        (C.linear_add ⟨τ, hτ0⟩ ⟨s, hs0⟩)
      rw [hmk]
      exact happ
    -- assemble the glued mild equation
    calc (fun t' => if t' ≤ s then u t' else v (t' - s)) (s + τ)
        = v τ := hw_shift τ hτ0
      _ = C.linearEvolution ⟨τ, hτ0⟩ (u s) -
            ∫ σ in (0 : ℝ)..τ, C.duhamelIntegrand τ v σ := heq_v
      _ = C.linearEvolution ⟨τ, hτ0⟩
            (C.linearEvolution ⟨s, hs0⟩ u₀ -
              ∫ σ in (0 : ℝ)..s, C.duhamelIntegrand s u σ) -
            ∫ σ in (0 : ℝ)..τ, C.duhamelIntegrand τ v σ :=
        congrArg (fun x => C.linearEvolution ⟨τ, hτ0⟩ x -
          ∫ σ in (0 : ℝ)..τ, C.duhamelIntegrand τ v σ) heq_s
      _ = C.linearEvolution ⟨τ, hτ0⟩ (C.linearEvolution ⟨s, hs0⟩ u₀) -
            (C.linearEvolution ⟨τ, hτ0⟩
                (∫ σ in (0 : ℝ)..s, C.duhamelIntegrand s u σ) +
              ∫ σ in (0 : ℝ)..τ, C.duhamelIntegrand τ v σ) := by
          rw [map_sub]
          abel
      _ = C.linearEvolution ⟨τ, hτ0⟩ (C.linearEvolution ⟨s, hs0⟩ u₀) -
            ((∫ σ in (0 : ℝ)..s,
                C.linearEvolution ⟨τ, hτ0⟩ (C.duhamelIntegrand s u σ)) +
              ∫ σ in (0 : ℝ)..τ, C.duhamelIntegrand τ v σ) := by
          congr 1
          congr 1
          exact ((C.linearEvolution ⟨τ, hτ0⟩).intervalIntegral_comp_comm hint_s).symm
      _ = C.linearEvolution ⟨s + τ, ht.1⟩ u₀ -
            ((∫ σ in (0 : ℝ)..s,
                C.duhamelIntegrand (s + τ)
                  (fun t' => if t' ≤ s then u t' else v (t' - s)) σ) +
              ∫ σ in s..(s + τ),
                C.duhamelIntegrand (s + τ)
                  (fun t' => if t' ≤ s then u t' else v (t' - s)) σ) := by
          rw [hsg, hhead, htail]
      _ = C.linearEvolution ⟨s + τ, ht.1⟩ u₀ -
            ∫ σ in (0 : ℝ)..(s + τ),
              C.duhamelIntegrand (s + τ)
                (fun t' => if t' ≤ s then u t' else v (t' - s)) σ := by
          rw [hsplit]

end EndpointSafeTwoSpaceDuhamelContract

/-- Concrete form of the mild concatenation identity on the `R³` endpoint-safe projected
contract. -/
theorem IsR3EndpointSafeProjectedMildSolutionOn.concat {nu s T' : ℝ} {hnu : 0 < nu}
    {u0 : R3HsVelocity 3} {u v : ℝ → R3HsVelocity 3}
    (hu : IsR3EndpointSafeProjectedMildSolutionOn hnu s u0 u)
    (hv : IsR3EndpointSafeProjectedMildSolutionOn hnu T' (u s) v) :
    IsR3EndpointSafeProjectedMildSolutionOn hnu (s + T') u0
      fun t => if t ≤ s then u t else v (t - s) :=
  EndpointSafeTwoSpaceDuhamelContract.IsMildSolutionOn.concat
    (r3EndpointSafeProjectedDuhamelContract hnu) hu hv

end

end MNS2
