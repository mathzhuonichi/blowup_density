import NSFormalization.Section4.A02.Uniqueness
import NSFormalization.Section4.A02.Order

/-!
# A02 units U5 and U9: patching and the maximal-lifespan bound at a blow-up

`research/A02/COMPARISON.md` §3, units **U5** and **U9**; the spec fields
`MaximalSolutionAPI.patch` (`research/A02/Spec.lean:357-367`) and
`MaximalSolutionAPI.lifespan_le_of_unbounded` (`research/A02/Spec.lean:576-582`).

* **U5** `patch`: two classical whole-space solutions of the *same* datum
  `(ν, a, f)` on horizons `T₁, T₂` patch to one solution on `[0, max T₁ T₂)`,
  agreeing with each on its own interval (velocities pointwise; pressures up to
  `PressureGaugeEquivOn`).  Route (COMPARISON row U5): **no gluing**.  WLOG the
  longer horizon — case split on `T₁ ≤ T₂`, `max` reduces by `max_eq_left/right`,
  and the patched solution `w` is *literally* whichever of `u₁, u₂` has the larger
  horizon.  Agreement with the longer one is `rfl`/reflexivity; agreement with the
  shorter one on its (shorter) interval is exactly `velocity_unique_core` (U2) and
  `pressure_gauge_core` (U3) from `Uniqueness.lean`, restricted along
  `Ico 0 Tᵢ ⊆ Ico 0 (min T₁ T₂)`.

* **U9** `lifespan_le_of_unbounded`: the field's chosen norm is the manuscript's
  `L^∞` norm `speedENorm z = eLpNorm z ⊤ volume` (`Spec.lean:148-149`), and the
  blow-up hypothesis is `limsupLeft T (fun t => speedENorm (u(t,·))) = ⊤`
  (`Spec.lean:135-136`, `Filter.limsup` over `𝓝[<] T`).  Route (COMPARISON row
  U9): by contradiction.  If `ofReal T < maximalLifespanR`, then
  `exists_horizon_gt_of_lt_lifespan` (U6, `Order.lean`) produces a solution `w` on
  a longer horizon `T' > T`; `velocity_unique_core` (U2) identifies `w.velocity`
  with `u` on all of `Ico 0 T`; and `ClassicalSolutionR.exists_velocity_bound`
  (U1b, `Bounds.lean`, the registered `A03.bounded_representative` route) bounds
  `w.velocity` uniformly on the compact `Icc 0 T ⊆ Ico 0 T'`.  A pointwise bound
  turns into `speedENorm (u(t,·)) ≤ ENNReal.ofReal B` for `t ∈ Ico 0 T`
  (`eLpNormEssSup_le_of_ae_bound`), which is eventually true on `𝓝[<] T` (the set
  `Ioo 0 T` is a member), so the left `limsup` is `≤ ENNReal.ofReal B < ⊤`,
  contradicting `= ⊤`.

`speedENorm` and `limsupLeft` are `⟪D01:normLinfty⟫` and `⟪D01:limsupLeft⟫`
(`research/section4/STATEMENTS.md:1171,1209`), which D01 does not define; they are
restated here verbatim from `research/A02/Spec.lean:135-136,148-149`, the same way
`SolutionClass.lean` restates the `Contracts.V1.Data` objects.
-/

noncomputable section

open Set MeasureTheory Filter
open NavierStokes.ProblemStatement
open scoped ENNReal

namespace NSFormalization.Section4.A02

/-! ## 0. The two D01 objects A02 owns, restated from `Spec.lean` -/

/-- `research/A02/Spec.lean:135-136` `⟪D01:limsupLeft⟫`: the left limit superior
`limsup_{t↑T} φ(t)`, valued in `ℝ≥0∞`. -/
def limsupLeft (T : ℝ) (φ : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  Filter.limsup φ (nhdsWithin T (Iio T))

/-- `research/A02/Spec.lean:148-149` `⟪D01:normLinfty⟫`: the `L^∞(R³)` norm of a
spatial field, the essential supremum over `volume`. -/
def speedENorm (z : SpatialField) : ℝ≥0∞ :=
  eLpNorm z ⊤ (volume : Measure Space)

/-! ## 1. `PressureGaugeEquivOn` is an equivalence, monotone in the interval -/

/-- The gauge relation is reflexive. -/
theorem PressureGaugeEquivOn.refl (I : Set ℝ) (p : SpaceTimeScalar) :
    PressureGaugeEquivOn I p p :=
  ⟨fun _ => 0, fun _ _ _ => by ring⟩

/-- The gauge relation is symmetric. -/
theorem PressureGaugeEquivOn.symm {I : Set ℝ} {p q : SpaceTimeScalar}
    (h : PressureGaugeEquivOn I p q) : PressureGaugeEquivOn I q p := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun t => -c t, fun t ht x => by rw [hc t ht x]; ring⟩

/-- The gauge relation is monotone in the interval: equivalence on `J` restricts
to any `I ⊆ J`. -/
theorem PressureGaugeEquivOn.mono {I J : Set ℝ} {p q : SpaceTimeScalar}
    (hIJ : I ⊆ J) (h : PressureGaugeEquivOn J p q) : PressureGaugeEquivOn I p q := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun t ht x => hc t (hIJ ht) x⟩

/-! ## 2. Unit U5: patching (spec field `patch`) -/

/-- **Spec field `MaximalSolutionAPI.patch`** (`research/A02/Spec.lean:357-367`),
verbatim.  WLOG the longer horizon; no gluing. -/
theorem patch :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField),
      0 < ν → a ∈ initialClassR → MemForceR f →
        ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionR ν a f T₁)
          (u₂ : ClassicalSolutionR ν a f T₂),
          ∃ w : ClassicalSolutionR ν a f (max T₁ T₂),
            (∀ t ∈ Ico (0 : ℝ) T₁, ∀ x : Space,
                w.velocity (t, x) = u₁.velocity (t, x)) ∧
            (∀ t ∈ Ico (0 : ℝ) T₂, ∀ x : Space,
                w.velocity (t, x) = u₂.velocity (t, x)) ∧
            PressureGaugeEquivOn (Ico (0 : ℝ) T₁) u₁.pressure w.pressure ∧
            PressureGaugeEquivOn (Ico (0 : ℝ) T₂) u₂.pressure w.pressure := by
  intro ν a f hν _ _ T₁ T₂ u₁ u₂
  have hvel := velocity_unique_core hν u₁ u₂
  have hpre := pressure_gauge_core hν u₁ u₂
  rcases le_total T₁ T₂ with h | h
  · -- `max T₁ T₂ = T₂`; the patched solution is `u₂`.
    rw [max_eq_right h]
    refine ⟨u₂, ?_, fun _ _ _ => rfl, ?_, PressureGaugeEquivOn.refl _ _⟩
    · intro t ht x
      exact (hvel t ⟨ht.1, lt_of_lt_of_le ht.2 (le_min le_rfl h)⟩ x).symm
    · exact PressureGaugeEquivOn.mono (Ico_subset_Ico le_rfl (le_min le_rfl h)) hpre
  · -- `max T₁ T₂ = T₁`; the patched solution is `u₁`.
    rw [max_eq_left h]
    refine ⟨u₁, fun _ _ _ => rfl, ?_, PressureGaugeEquivOn.refl _ _, ?_⟩
    · intro t ht x
      exact hvel t ⟨ht.1, lt_of_lt_of_le ht.2 (le_min h le_rfl)⟩ x
    · exact PressureGaugeEquivOn.mono (Ico_subset_Ico le_rfl (le_min h le_rfl)) hpre.symm

/-! ## 3. Unit U9: the maximal-lifespan bound at an `L^∞` blow-up -/

/-- A pointwise bound `‖z x‖ ≤ B` on a spatial field gives the `L^∞` bound
`speedENorm z ≤ ENNReal.ofReal B`. -/
theorem speedENorm_le_ofReal {z : SpatialField} {B : ℝ} (h : ∀ x : Space, ‖z x‖ ≤ B) :
    speedENorm z ≤ ENNReal.ofReal B := by
  rw [speedENorm, eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_bound (ae_of_all _ h)

/-- **Spec field `MaximalSolutionAPI.lifespan_le_of_unbounded`**
(`research/A02/Spec.lean:576-582`), verbatim: if `(u,p)` is a classical solution
on every `[0,S)` with `S < T` and its `L^∞` speed has `limsup_{t↑T} = ⊤`, then no
classical solution of the same datum reaches beyond `T`. -/
theorem lifespan_le_of_unbounded :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ),
      0 < ν → a ∈ initialClassR → MemForceR f → 0 < T →
      ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
        (∀ S : ℝ, 0 < S → S < T →
            ∃ w : ClassicalSolutionR ν a f S, w.velocity = u ∧ w.pressure = p) →
        limsupLeft T (fun t => speedENorm (fun x : Space => u (t, x))) = ⊤ →
          maximalLifespanR ν a f ≤ ENNReal.ofReal T := by
  intro ν a f T hν _ha _hf hT u p hex hunbdd
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨T', hTT', hne⟩ := exists_horizon_gt_of_lt_lifespan hT.le hcon
  obtain ⟨w⟩ := hne
  -- U2: `w.velocity` and `u` agree on all of `Ico 0 T`.
  have hagree : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, u (t, x) = w.velocity (t, x) := by
    intro t ht x
    obtain ⟨wS, hwv, _⟩ := hex ((t + T) / 2) (by linarith [ht.1]) (by linarith [ht.2])
    have hmem : t ∈ Ico (0 : ℝ) (min T' ((t + T) / 2)) :=
      ⟨ht.1, lt_min (lt_trans ht.2 hTT') (by linarith [ht.2])⟩
    have hvu := velocity_unique_core hν w wS t hmem x
    rw [hwv] at hvu
    exact hvu.symm
  -- U1b: `w.velocity` is bounded on the compact `Icc 0 T ⊆ Ico 0 T'`.
  obtain ⟨B, _hB0, hB⟩ := w.exists_velocity_bound hT.le hTT'
  -- The `L^∞` speed of `u` is `≤ ENNReal.ofReal B` on `Ico 0 T`.
  have hbound_slice : ∀ t ∈ Ico (0 : ℝ) T,
      speedENorm (fun x : Space => u (t, x)) ≤ ENNReal.ofReal B := by
    intro t ht
    refine speedENorm_le_ofReal (fun x => ?_)
    rw [hagree t ht x]
    exact hB t ⟨ht.1, ht.2.le⟩ x
  -- Hence the left `limsup` is `≤ ENNReal.ofReal B`.
  have hev : ∀ᶠ t in nhdsWithin T (Iio T),
      speedENorm (fun x : Space => u (t, x)) ≤ ENNReal.ofReal B := by
    have hmem : Ioo (0 : ℝ) T ∈ nhdsWithin T (Iio T) := by
      rw [← Ioi_inter_Iio]
      exact inter_mem (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hT)) self_mem_nhdsWithin
    exact Filter.eventually_of_mem hmem (fun t ht => hbound_slice t ⟨ht.1.le, ht.2⟩)
  have hlim : limsupLeft T (fun t => speedENorm (fun x : Space => u (t, x)))
      ≤ ENNReal.ofReal B := Filter.limsup_le_of_le (h := hev)
  rw [hunbdd] at hlim
  exact ENNReal.ofReal_ne_top (top_le_iff.mp hlim)

end NSFormalization.Section4.A02
