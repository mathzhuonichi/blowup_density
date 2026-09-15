import NSFormalization.Section4.R42.SolutionOnShorter

/-!
# R42, full horizon: the inserted pair is a classical solution on all of `[0,T)`

Lane 087 (`Section4/R42/SolutionOnShorter.lean`, `classicalSolutionR_of_inserted`)
inhabits `A02.ClassicalSolutionR ν a gε S` for **each** shorter horizon `0 < S < T`.
This module upgrades that to a **single** classical solution on the full horizon
`[0,T)` itself (Theorem 4.2 of `paper/sections/04-whole-space.tex:32-38,53`).

The fields `velocity_smooth`, `pressure_smooth`, `initial`, `divergence` and
`momentum` are already stated on `Ico 0 T` / `Ioo 0 T` by the hypotheses of
`classicalSolutionR_of_inserted` (they are literally the `InsertionFamilyAPI`
fields), so they feed the horizon-`T` construction directly with no restriction.
Three fields are not handed over verbatim: `horizon_pos` is the new hypothesis
`hT` (`ref.horizon_pos` only gives `0 < T + δ`); `pressure_gradient` reuses
lane 083's `memLp_pressureGradient_of_difference_support` at horizon `T`, after
restricting `ref.pressure_smooth` from `Ico 0 (T+δ)` to `Ico 0 T`; and `sobolev`
is the only field needing a *new* lemma — `classicalSolutionR_of_inserted`
produces, for each `S < T`, a datum path continuous on `Ico 0 S`, and we must
**glue** these shorter-horizon paths into one path continuous on `Ico 0 T`.

The gluing (`exists_datumPath_of_forall_shorter`) is by **datum uniqueness**
(`D01.isSobolevDatum_unique`, `Section4/D01/ForceClass.lean:286`): the glued path
at `t` is the value at `t` of the chosen `S`-path for `S := (t+T)/2`; near a base
point `t₀` it agrees with the single `((t₀+T)/2)`-path, because at each `t` both are
Sobolev data of the *same* velocity slice `u(t,·)` and the datum is unique, so the
`ContinuousWithinAt` of the fixed path transfers to the glued path
(`ContinuousWithinAt.congr_of_eventuallyEq_of_mem`).  `Ico 0 ((t₀+T)/2)` is a
neighbourhood of `t₀` within `Ico 0 T` because `t₀ < (t₀+T)/2 < T`.

The `pressure_gradient` field at horizon `T` is
`memLp_pressureGradient_of_difference_support` (lane 083,
`Section4/R42/PressureGradient.lean`) applied at horizon `T` directly, exactly as
in lane 087 but with `S` replaced by `T`.

`A02.IsSobolevDatum` and `D01.IsSobolevDatum` are definitionally equal
(`A02/SolutionClass.lean` docstring), so the D01 uniqueness lemma applies directly
to the A02-flavoured data carried by `ClassicalSolutionR.sobolev`.
-/

noncomputable section

namespace NSFormalization.Section4.R42

open Set Topology
open NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Section4.A02
open scoped ContDiff

/-- **Gluing datum paths through datum uniqueness (Lemma A).**  If, for every
shorter horizon `0 < S < T`, the velocity `u` has an order-`m` datum path
continuous on `Ico 0 S`, then `u` has an order-`m` datum path continuous on all
of `Ico 0 T`.

The glued path is `t ↦ (path chosen for S = (t+T)/2)(t)`.  At each `t ∈ Ico 0 T`
this is a Sobolev datum of `u(t,·)` (the chosen `S`-path is a datum at `t` since
`t < (t+T)/2`).  Continuity at `t₀ ∈ Ico 0 T`: on the neighbourhood
`Ico 0 ((t₀+T)/2)` of `t₀` within `Ico 0 T`, the glued path agrees with the single
`((t₀+T)/2)`-path — both are data of `u(t,·)` at every such `t`, hence equal by
`isSobolevDatum_unique` — so its `ContinuousWithinAt` transfers. -/
theorem exists_datumPath_of_forall_shorter {T : ℝ} (hT : 0 < T) {u : SpaceTimeField}
    (m : ℕ)
    (h : ∀ S : ℝ, 0 < S → S < T → ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContinuousOn G (Ico (0 : ℝ) S) ∧
          ∀ t ∈ Ico (0 : ℝ) S, IsSobolevDatum (m : ℝ) (fun x => u (t, x)) (G t)) :
    ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContinuousOn G (Ico (0 : ℝ) T) ∧
          ∀ t ∈ Ico (0 : ℝ) T, IsSobolevDatum (m : ℝ) (fun x => u (t, x)) (G t) := by
  classical
  -- For each admissible `S`, extract the datum path and its two properties.
  choose Gs hGsc hGsd using h
  -- The midpoint horizon `(t+T)/2` and its three inequalities.
  have hb0 : ∀ t : ℝ, 0 ≤ t → 0 < (t + T) / 2 := fun t ht => by linarith
  have hbT : ∀ t : ℝ, t < T → (t + T) / 2 < T := fun t ht => by linarith
  have hbt : ∀ t : ℝ, t < T → t < (t + T) / 2 := fun t ht => by linarith
  -- The glued path.
  set G : ℝ → RealVectorSobolev (m : ℝ) :=
    fun t => if ht : 0 ≤ t ∧ t < T then Gs ((t + T) / 2) (hb0 t ht.1) (hbT t ht.2) t else 0
    with hGdef
  refine ⟨G, ?_, ?_⟩
  · -- Continuity on `Ico 0 T`.
    intro t₀ ht₀
    obtain ⟨ht₀0, ht₀T⟩ := ht₀
    -- The single path used on a neighbourhood of `t₀`.
    have hcwa₀ : ContinuousWithinAt (Gs ((t₀ + T) / 2) (hb0 t₀ ht₀0) (hbT t₀ ht₀T))
        (Ico (0 : ℝ) ((t₀ + T) / 2)) t₀ :=
      (hGsc ((t₀ + T) / 2) (hb0 t₀ ht₀0) (hbT t₀ ht₀T)) t₀ ⟨ht₀0, hbt t₀ ht₀T⟩
    -- `Ico 0 ((t₀+T)/2)` is a neighbourhood of `t₀` within `Ico 0 T`.
    have hnbhd : Ico (0 : ℝ) ((t₀ + T) / 2) ∈ 𝓝[Ico (0 : ℝ) T] t₀ := by
      rw [mem_nhdsWithin]
      exact ⟨Iio ((t₀ + T) / 2), isOpen_Iio, hbt t₀ ht₀T,
        fun y hy => ⟨hy.2.1, hy.1⟩⟩
    have hcwaT : ContinuousWithinAt (Gs ((t₀ + T) / 2) (hb0 t₀ ht₀0) (hbT t₀ ht₀T))
        (Ico (0 : ℝ) T) t₀ :=
      hcwa₀.mono_of_mem_nhdsWithin hnbhd
    -- `G` agrees with the single path on that neighbourhood, by datum uniqueness.
    have heq : G =ᶠ[𝓝[Ico (0 : ℝ) T] t₀]
        Gs ((t₀ + T) / 2) (hb0 t₀ ht₀0) (hbT t₀ ht₀T) := by
      filter_upwards [hnbhd] with t ht
      have htT : t < T := lt_trans ht.2 (hbT t₀ ht₀T)
      have htc : 0 ≤ t ∧ t < T := ⟨ht.1, htT⟩
      have hGt : G t = Gs ((t + T) / 2) (hb0 t htc.1) (hbT t htc.2) t := by
        simp only [hGdef]; rw [dite_eq_left htc]
      rw [hGt]
      exact D01.isSobolevDatum_unique
        (hGsd ((t + T) / 2) (hb0 t htc.1) (hbT t htc.2) t ⟨htc.1, hbt t htc.2⟩)
        (hGsd ((t₀ + T) / 2) (hb0 t₀ ht₀0) (hbT t₀ ht₀T) t ht)
    exact hcwaT.congr_of_eventuallyEq_of_mem heq ⟨ht₀0, ht₀T⟩
  · -- Datum property on `Ico 0 T`.
    intro t ht
    obtain ⟨ht0, htT⟩ := ht
    have htc : 0 ≤ t ∧ t < T := ⟨ht0, htT⟩
    have hGt : G t = Gs ((t + T) / 2) (hb0 t htc.1) (hbT t htc.2) t := by
      simp only [hGdef]; rw [dite_eq_left htc]
    rw [hGt]
    exact hGsd ((t + T) / 2) (hb0 t htc.1) (hbT t htc.2) t ⟨htc.1, hbt t htc.2⟩

/-- **The inserted pair as a classical solution on the full horizon `[0,T)`
(Lemma B).**  With exactly the hypotheses of `classicalSolutionR_of_inserted`
(lane 087) plus `0 < T`, the inserted pair `(u, p)` is a classical solution
`ClassicalSolutionR ν a gε T` on the full horizon, with velocity `u` and pressure
`p`.

All fields except `sobolev` come straight from the hypotheses (already stated on
`Ico 0 T` / `Ioo 0 T`).  `sobolev` is `exists_datumPath_of_forall_shorter` applied
to the family of shorter-horizon solutions from `classicalSolutionR_of_inserted`.
`pressure_gradient` is `memLp_pressureGradient_of_difference_support` at horizon
`T`. -/
theorem classicalSolutionR_of_inserted_fullHorizon
    {ν : ℝ} {a : SpatialField} {g gε : SpaceTimeField} {T δ : ℝ} {x₀ : Space} {r t₁ : ℝ}
    (ref : ClassicalSolutionR ν a g (T + δ)) (hδ : 0 < δ) (ht₁ : 0 < t₁)
    (u : SpaceTimeField) (p : SpaceTimeScalar)
    (hu_smooth : ContDiffOn ℝ ∞ u (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hp_smooth : ContDiffOn ℝ ∞ p (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hinit : ∀ x, u (0, x) = a x)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) T, ∀ x, spatialDivergence u t x = 0)
    (hmom : ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = gε (t, x))
    (hhist : ∀ t : ℝ, 0 ≤ t → t ≤ t₁ → ∀ x, u (t, x) = ref.velocity (t, x))
    (hvsupp : ∀ t ∈ Ico (0 : ℝ) T,
      tsupport (fun x => u (t, x) - ref.velocity (t, x)) ⊆ Metric.ball x₀ r)
    (hpsupp : ∀ t ∈ Ico (0 : ℝ) T,
      tsupport (fun x => p (t, x) - ref.pressure (t, x)) ⊆ Metric.ball x₀ r)
    (hT : 0 < T) :
    ∃ w : ClassicalSolutionR ν a gε T, w.velocity = u ∧ w.pressure = p := by
  have hIcoT_Tδ : Ico (0 : ℝ) T ⊆ Ico (0 : ℝ) (T + δ) :=
    Set.Ico_subset_Ico le_rfl (by linarith)
  refine ⟨{
      velocity := u
      pressure := p
      horizon_pos := hT
      velocity_smooth := hu_smooth
      pressure_smooth := hp_smooth
      initial := hinit
      divergence := hdiv
      momentum := hmom
      sobolev := ?_
      pressure_gradient := ?_ }, rfl, rfl⟩
  · -- `sobolev`: glue the shorter-horizon datum paths of the family from lane 087.
    intro m
    refine exists_datumPath_of_forall_shorter hT m ?_
    intro S hS0 hST
    obtain ⟨w, hv, _⟩ := classicalSolutionR_of_inserted ref hδ ht₁ u p
      hu_smooth hp_smooth hinit hdiv hmom hhist hvsupp hpsupp hS0 hST
    obtain ⟨G, hGc, hGd⟩ := w.sobolev m
    refine ⟨G, hGc, ?_⟩
    intro t ht
    have hdat := hGd t ht
    rwa [hv] at hdat
  · -- `pressure_gradient` on `Ico 0 T` (lane 083 at horizon `T`).
    intro t ht
    have htTδ : t ∈ Ico (0 : ℝ) (T + δ) := hIcoT_Tδ ht
    have hπ : ContDiffOn ℝ ∞ ref.pressure (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) :=
      ref.pressure_smooth.mono (Set.prod_mono hIcoT_Tδ (subset_refl _))
    exact memLp_pressureGradient_of_difference_support ht hπ hp_smooth
      (ref.pressure_gradient t htTδ) (hpsupp t ht)

end NSFormalization.Section4.R42
