import NSFormalization.Section4.D01.ForceClass
import NSFormalization.Section4.A02.SolutionClass

/-!
# R42, item 1e-i: time-continuity of the correction datum path

Theorem 4.2 of `paper/sections/04-whole-space.tex` builds the inserted velocity
`u_ε = v + w_ε + U_ε` (line 33), whose difference from the reference `v` is
supported in a fixed ball `B(x₀, r)` at every time (line 35) and vanishes for
`t ≤ T − 2ε²` (line 38).  Inhabiting `Data.ClassicalSolutionR ν a g_ε S`
(`A02.ClassicalSolutionR`) requires its `sobolev` field: for every integer order
`m` a datum path `G : ℝ → RealVectorSobolev m` that is *continuous on* `Ico 0 S`
and is, at every `t ∈ Ico 0 S`, an angular Sobolev datum of the velocity slice.
`research/R42/LIFESPAN_SPLIT.md` item **1e-i** identifies the correction slice
`d = u_ε − v` as the only residual: everything else (its compact spatial support,
its smoothness on `Ico 0 T`, and the additivity of data) is already registered in
`Section4/D01/ForceClass.lean`.

This module discharges that residual with two lemmas, importing only the two D01
solution/force modules and Mathlib:

* `exists_datumPath_of_localized` — the unit.  A spacetime field `d` that is
  `ContDiffOn ℝ ∞` on `Ico 0 T × ℝ³`, spatially supported in `B(x₀, r)` at each
  `t ∈ Ico 0 T`, and identically zero for `0 ≤ t ≤ t₁` (some `t₁ > 0`), has, for
  every `S < T` and every integer order `m`, a datum path continuous on `Ico 0 S`.
  The construction multiplies `d` by a smooth time cutoff `χ` (`= 1` on `Iic S`,
  `= 0` on `Ici ((S+T)/2)`) and a hard cutoff `1_{t ≥ 0}`; the `t₁ > 0` history
  makes the product globally `ContDiff` across `t = 0` and `HasCompactSupport`,
  so `I03.angularPath` applies and `D01.contDiff_angularPath` gives continuity in
  time, while the datum at each `t ∈ Ico 0 S` (where `χ = 1`, `t ≥ 0`) is
  `I03.angularPath_pairing`.

* `sobolev_add_of_localized` — the additivity assembly.  Given the reference's
  `sobolev`-shaped hypothesis on `Ico 0 T'` (`T' ≥ S`) and the correction's on
  `Ico 0 S`, plus slice continuity of both fields on `Ico 0 S`, the sum
  `v + d` has a datum path continuous on `Ico 0 S`.  It is `G_v + G_d`, with
  continuity from `ContinuousOn.add` and the datum from `D01.isSobolevDatum_add`,
  whose `SchwartzPairable` side conditions come from
  `D01.schwartzPairable_of_isSobolevDatum` at the order-`m ≥ 0` data.

`A02.IsSobolevDatum` and `D01.IsSobolevDatum` are definitionally equal
(`A02/SolutionClass.lean` docstring), so the D01 additivity/pairability lemmas
apply directly to the A02-flavoured statements used by `ClassicalSolutionR`.
`SpaceTimeField` (`A02`) and `VelocityField` (the type `I03.angularPath` takes)
are the same abbreviation `ℝ × Space → Space`
(`NavierStokes.ProblemStatement`), so no bridge is needed.
-/

noncomputable section

namespace NSFormalization.Section4.R42

open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Section4.A02
open scoped ContDiff ENNReal SchwartzMap

/-- **Item 1e-i.**  A field `d` smooth on `[0,T) × ℝ³`, spatially supported in a
fixed ball at every time, and vanishing for `0 ≤ t ≤ t₁` (`t₁ > 0`), has for
every `S < T` and every order `m` a datum path continuous on `Ico 0 S`.  The
carrier is `I03.angularPath` of `F p = 1_{0 ≤ p.1} • χ p.1 • d p`, with `χ` a
smooth one-sided time cutoff. -/
theorem exists_datumPath_of_localized {T t₁ S : ℝ} (ht₁ : 0 < t₁) (hS : S < T)
    {x₀ : Space} {r : ℝ} (d : SpaceTimeField)
    (hd : ContDiffOn ℝ ∞ d (Ico (0 : ℝ) T ×ˢ (univ : Set Space)))
    (hsupp : ∀ t ∈ Ico (0 : ℝ) T, tsupport (fun x => d (t, x)) ⊆ Metric.ball x₀ r)
    (hhist : ∀ t : ℝ, 0 ≤ t → t ≤ t₁ → ∀ x, d (t, x) = 0) (m : ℕ) :
    ∃ G : ℝ → RealVectorSobolev (m : ℝ), ContinuousOn G (Ico (0 : ℝ) S) ∧
      ∀ t ∈ Ico (0 : ℝ) S, IsSobolevDatum (m : ℝ) (fun x => d (t, x)) (G t) := by
  -- The window `[S, (S+T)/2]` over which the time cutoff descends from `1` to `0`.
  set b : ℝ := (S + T) / 2 with hb
  have hbT : b < T := by rw [hb]; linarith
  have hbS : (0 : ℝ) < b - S := by rw [hb]; linarith
  -- The smooth time cutoff: `χ = 1` on `Iic S`, `χ = 0` on `Ici b`.
  set χ : ℝ → ℝ := fun t => Real.smoothTransition ((b - t) / (b - S)) with hχdef
  have hχ_contDiff : ContDiff ℝ ∞ χ := by
    rw [hχdef]
    exact Real.smoothTransition.contDiff.comp
      ((contDiff_const.sub contDiff_id).div_const (b - S))
  have hχ_one : ∀ t : ℝ, t ≤ S → χ t = 1 := by
    intro t ht
    simp only [hχdef]
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ hbS, one_mul]
    linarith
  have hχ_zero : ∀ t : ℝ, b ≤ t → χ t = 0 := by
    intro t ht
    simp only [hχdef]
    apply Real.smoothTransition.zero_of_nonpos
    rw [div_nonpos_iff]
    exact Or.inr ⟨by linarith, by linarith⟩
  -- The globally-defined cutoff field.
  set F : SpaceTime → Space := fun p => if 0 ≤ p.1 then χ p.1 • d p else 0 with hFdef
  -- `F` is globally smooth: it is `0` near `t < t₁` (using `t₁ > 0` and the
  -- history), equals `χ • d` on `Ioo 0 T × ℝ³`, and is `0` for `t > b`.
  have hF_smooth : ContDiff ℝ ∞ F := by
    rw [contDiff_iff_contDiffAt]
    intro p
    rcases lt_or_ge p.1 t₁ with hlt | hge
    · -- `p.1 < t₁`: `F = 0` on `Iio t₁ × ℝ³`.
      have hmem : Iio t₁ ×ˢ (univ : Set Space) ∈ 𝓝 p :=
        (isOpen_Iio.prod isOpen_univ).mem_nhds ⟨hlt, mem_univ _⟩
      refine (contDiffAt_const (c := (0 : Space))).congr_of_eventuallyEq ?_
      filter_upwards [hmem] with q hq
      simp only [hFdef]
      split_ifs with h0
      · have hdq : d q = 0 := hhist q.1 h0 (le_of_lt hq.1) q.2
        rw [hdq, smul_zero]
      · rfl
    · rcases lt_or_ge p.1 T with hltT | hgeT
      · -- `t₁ ≤ p.1 < T`: `F = χ • d` on `Ioo 0 T × ℝ³`.
        have hp1pos : 0 < p.1 := lt_of_lt_of_le ht₁ hge
        have hmem : Ioo (0 : ℝ) T ×ˢ (univ : Set Space) ∈ 𝓝 p :=
          (isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨⟨hp1pos, hltT⟩, mem_univ _⟩
        have hsub : Ioo (0 : ℝ) T ×ˢ (univ : Set Space)
            ⊆ Ico (0 : ℝ) T ×ˢ (univ : Set Space) :=
          Set.prod_mono Ioo_subset_Ico_self (subset_refl _)
        have hg : ContDiffAt ℝ ∞ (fun q : SpaceTime => χ q.1 • d q) p :=
          (((hχ_contDiff.comp contDiff_fst).contDiffOn).smul (hd.mono hsub)).contDiffAt hmem
        refine hg.congr_of_eventuallyEq ?_
        filter_upwards [hmem] with q hq
        simp only [hFdef]
        split_ifs with h0
        · rfl
        · exact absurd (le_of_lt hq.1.1) h0
      · -- `T ≤ p.1`, so `b < p.1`: `χ = 0`, hence `F = 0`, on `Ioi b × ℝ³`.
        have hpb : b < p.1 := lt_of_lt_of_le hbT hgeT
        have hmem : Ioi b ×ˢ (univ : Set Space) ∈ 𝓝 p :=
          (isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨hpb, mem_univ _⟩
        refine (contDiffAt_const (c := (0 : Space))).congr_of_eventuallyEq ?_
        filter_upwards [hmem] with q hq
        simp only [hFdef]
        have hχq : χ q.1 = 0 := hχ_zero q.1 (le_of_lt hq.1)
        split_ifs with h0
        · rw [hχq, zero_smul]
        · rfl
  -- `F` has compact spacetime support: outside `[0,b] × closedBall x₀ r` it is `0`.
  have hF_supp : HasCompactSupport F := by
    refine HasCompactSupport.intro (K := Icc (0 : ℝ) b ×ˢ Metric.closedBall x₀ r)
      (isCompact_Icc.prod (isCompact_closedBall x₀ r)) ?_
    intro p hp
    obtain ⟨pt, px⟩ := p
    simp only [hFdef]
    split_ifs with h0
    · rcases lt_or_ge b pt with hbp | hpb
      · -- `pt > b`: `χ pt = 0`.
        rw [hχ_zero pt (le_of_lt hbp), zero_smul]
      · -- `pt ≤ b`: `px ∉ closedBall`, so `d (pt, px) = 0`.
        have hpx : px ∉ Metric.closedBall x₀ r := fun hmem => hp ⟨⟨h0, hpb⟩, hmem⟩
        have hsupp' : tsupport (fun x => d (pt, x)) ⊆ Metric.ball x₀ r :=
          hsupp pt ⟨h0, lt_of_le_of_lt hpb hbT⟩
        have hnotmem : px ∉ tsupport (fun x => d (pt, x)) :=
          fun hmem => hpx (Metric.ball_subset_closedBall (hsupp' hmem))
        have hdz0 := image_eq_zero_of_notMem_tsupport hnotmem
        have hdz : d (pt, px) = 0 := hdz0
        rw [hdz, smul_zero]
    · rfl
  -- On `[0, S]` the cutoffs are trivial, so `F` agrees with `d`.
  have hFd : ∀ t : ℝ, 0 ≤ t → t ≤ S → ∀ x : Space, F (t, x) = d (t, x) := by
    intro t ht0 htS x
    simp only [hFdef]
    split_ifs
    rw [hχ_one t htS, one_smul]
  -- Conclude with `I03.angularPath F`.
  refine ⟨I03.angularPath (m : ℝ) F hF_smooth hF_supp, ?_, ?_⟩
  · exact (D01.contDiff_angularPath (m : ℝ) F hF_smooth hF_supp).continuous.continuousOn
  · intro t ht
    have ht0 : (0 : ℝ) ≤ t := ht.1
    have htS : t ≤ S := le_of_lt ht.2
    intro i ψ
    have hfun : (fun x : Space => ψ x * ((F (t, x) i : ℝ) : ℂ))
        = fun x : Space => ψ x * ((d (t, x) i : ℝ) : ℂ) := by
      funext x
      rw [hFd t ht0 htS x]
    rw [I03.angularPath_pairing (m : ℝ) F hF_smooth hF_supp t i ψ, hfun]

/-- **Additivity assembly.**  If the reference `v` has the `sobolev`-shaped datum
path on `Ico 0 T'` (`T' ≥ S`) and the correction `d` on `Ico 0 S`, and both
velocity slices are continuous on `Ico 0 S`, then `v + d` has a datum path
continuous on `Ico 0 S`.  This is exactly the `sobolev` clause of
`ClassicalSolutionR` for `u_ε = v + (w_ε + U_ε)`. -/
theorem sobolev_add_of_localized {T' S : ℝ} (hS : S ≤ T') (v d : SpaceTimeField)
    (hv : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ), ContinuousOn G (Ico (0 : ℝ) T') ∧
        ∀ t ∈ Ico (0 : ℝ) T', IsSobolevDatum (m : ℝ) (fun x => v (t, x)) (G t))
    (hvc : ∀ t ∈ Ico (0 : ℝ) S, Continuous (fun x => v (t, x)))
    (hdc : ∀ t ∈ Ico (0 : ℝ) S, Continuous (fun x => d (t, x)))
    (hd : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ), ContinuousOn G (Ico (0 : ℝ) S) ∧
        ∀ t ∈ Ico (0 : ℝ) S, IsSobolevDatum (m : ℝ) (fun x => d (t, x)) (G t)) :
    ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ), ContinuousOn G (Ico (0 : ℝ) S) ∧
        ∀ t ∈ Ico (0 : ℝ) S, IsSobolevDatum (m : ℝ) (fun x => v (t, x) + d (t, x)) (G t) := by
  intro m
  obtain ⟨Gv, hGvc, hGvd⟩ := hv m
  obtain ⟨Gd, hGdc, hGdd⟩ := hd m
  refine ⟨Gv + Gd, ?_, ?_⟩
  · exact (hGvc.mono (Set.Ico_subset_Ico le_rfl hS)).add hGdc
  · intro t ht
    have htT' : t ∈ Ico (0 : ℝ) T' := Set.Ico_subset_Ico le_rfl hS ht
    have hs : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hpv : D01.SchwartzPairable (fun x => v (t, x)) :=
      D01.schwartzPairable_of_isSobolevDatum hs (hvc t ht) (hGvd t htT')
    have hpd : D01.SchwartzPairable (fun x => d (t, x)) :=
      D01.schwartzPairable_of_isSobolevDatum hs (hdc t ht) (hGdd t ht)
    exact D01.isSobolevDatum_add hpv hpd (hGvd t htT') (hGdd t ht)

end NSFormalization.Section4.R42
