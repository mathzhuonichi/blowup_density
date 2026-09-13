import NSFormalization.Section4.R42.CorrectionPath
import NSFormalization.Section4.R42.PressureGradient
import NSFormalization.Section4.D01.DatumToJets

/-!
# R42, item 1 (`sol_on_shorter`): the inserted pair is a classical solution on each shorter horizon

Theorem 4.2 of `paper/sections/04-whole-space.tex` (lines 32-38, 53) inserts, on
top of the reference solution `(v, π, g)` that is *regular through* `T + δ`, a
velocity correction `u_ε = v + w_ε + U_ε` and a pressure correction giving
`p_ε = π + P_ε`, together with the inserted force `g_ε`.  The lifespan clauses of
Theorem 4.2 need, as their common input, that this inserted pair `(u_ε, p_ε)` is
a *classical solution* `Data.ClassicalSolutionR ν a g_ε S` on **every shorter
horizon** `0 < S < T` (`research/R42/LIFESPAN_SPLIT.md` item **1**,
`sol_on_shorter`); `Data.maximalLifespanR` is a supremum over
`Nonempty (ClassicalSolutionR …)`, so an inhabitant at each `S < T` is exactly
what both the upper (`#4`) and lower (`#5`) lifespan bounds consume.

This module discharges that item as **one** formalization-level theorem,
`classicalSolutionR_of_inserted`.  The `InsertionFamilyAPI` fields are taken as
explicit hypotheses — `formalization/` cannot import `verification/Contracts`, so
the Bindings-level instantiation (feeding these hypotheses from the registered
`InsertionFamilyAPI`) is a separate lane.  Each hypothesis mirrors a specific API
field; the exact map (with `verification/Contracts/V1/InsertionFamily.lean` line
numbers) is recorded in `research/R42/ATTEMPTS_SOL_SHORTER.md`.

The construction feeds off the three merged R42 modules:

* the `sobolev` clause is `sobolev_add_of_localized` (lane 075,
  `Section4/R42/CorrectionPath.lean`) applied to the reference's own `sobolev`
  and the correction datum path `exists_datumPath_of_localized` for
  `d = u_ε − v`, then the propositional rewrite `v + (u_ε − v) = u_ε`;
* the `pressure_gradient` clause is `memLp_pressureGradient_of_difference_support`
  (lane 083, `Section4/R42/PressureGradient.lean`);
* the remaining clauses (`velocity_smooth`, `pressure_smooth`, `initial`,
  `divergence`, `momentum`) are guard shuffling from `Ico 0 S ⊆ Ico 0 T` /
  `Ioo 0 S ⊆ Ioo 0 T`.

The slice-continuity hypotheses of `sobolev_add_of_localized` (`hvc`, `hdc`) are
on `Ico 0 S` and are consumed at `t = 0` (`ClassicalSolutionR.sobolev` runs over
`Ico 0 S`).  Lane 080's `continuous_slice_of_velocity_smooth` is stated on the
open `Ioo` and does not reach `t = 0`; the `Ico`-including-`t = 0` vector slice
smoothness we need is `D01.contDiff_slice` (`D01/DatumToJets.lean:366`), used
directly.  This module already imports `D01.ForceClass` transitively through
`R42.CorrectionPath`, so adding `D01.DatumToJets` pulls in only two further
modules (`A05.SmoothJets` and `DatumToJets` itself), both already built — a
negligible cost that lets us reuse the existing lemma rather than carry a third
byte-identical copy of it (`research/R42/REVIEW_SOL_SHORTER.md` finding 2).
-/

noncomputable section

namespace NSFormalization.Section4.R42

open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Section4.A02
open scoped ContDiff ENNReal SchwartzMap

/-- **Item 1 (`sol_on_shorter`).**  Given a reference classical solution `ref` on
`[0, T+δ)` for `(a, g)`, and the inserted pair `(u, p)` satisfying the
`InsertionFamilyAPI` fields on `[0,T)` (smoothness, initial value, divergence,
momentum against the inserted force `gε`, the reference history for `t ≤ t₁`, and
the ball localization of both `u − ref.velocity` and `p − ref.pressure`), the
inserted pair is a classical solution `ClassicalSolutionR ν a gε S` on every
shorter horizon `0 < S < T`, with velocity `u` and pressure `p`.

`t₁ > 0` abstracts `InsertionFamilyAPI.history`'s `t ≤ T − 2ε²`; positivity is
supplied at the binding level by `ScalingAPI.eps_time` (`2ε² < min T δ`,
`Contracts/V1/Scaling.lean:209`).  The momentum residual is the R³ one taking the
viscosity `ν` (`NavierStokesR3.ProblemStatement.navierStokesResidual`), exactly
the residual of `ClassicalSolutionR.momentum`. -/
theorem classicalSolutionR_of_inserted
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
    {S : ℝ} (hS0 : 0 < S) (hST : S < T) :
    ∃ w : ClassicalSolutionR ν a gε S, w.velocity = u ∧ w.pressure = p := by
  -- Interval inclusions used to restrict each clause from the longer horizon.
  have hIcoST : Ico (0 : ℝ) S ⊆ Ico (0 : ℝ) T := Set.Ico_subset_Ico le_rfl hST.le
  have hIooST : Ioo (0 : ℝ) S ⊆ Ioo (0 : ℝ) T := Set.Ioo_subset_Ioo le_rfl hST.le
  have hIcoT_Tδ : Ico (0 : ℝ) T ⊆ Ico (0 : ℝ) (T + δ) :=
    Set.Ico_subset_Ico le_rfl (by linarith)
  -- The velocity correction `d = u − v`.
  set d : SpaceTimeField := fun z => u z - ref.velocity z with hd_def
  -- `d` is smooth on `[0,T) × ℝ³` (`u` minus the reference restricted to `[0,T)`).
  have hd_smooth : ContDiffOn ℝ ∞ d (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) := by
    have hrefT : ContDiffOn ℝ ∞ ref.velocity (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) :=
      ref.velocity_smooth.mono (Set.prod_mono hIcoT_Tδ (subset_refl _))
    exact hu_smooth.sub hrefT
  -- `d` vanishes on the reference history `t ≤ t₁`.
  have hd_hist : ∀ t : ℝ, 0 ≤ t → t ≤ t₁ → ∀ x, d (t, x) = 0 := by
    intro t h0 h1 x
    simp only [hd_def]
    exact sub_eq_zero_of_eq (hhist t h0 h1 x)
  -- `d(t, ·)` is supported in the fixed ball at each `t < T`.
  have hd_supp : ∀ t ∈ Ico (0 : ℝ) T, tsupport (fun x => d (t, x)) ⊆ Metric.ball x₀ r := by
    intro t ht
    simp only [hd_def]
    exact hvsupp t ht
  -- Correction datum path on `[0,S)` (lane 075).
  have hd_datum : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContinuousOn G (Ico (0 : ℝ) S) ∧
        ∀ t ∈ Ico (0 : ℝ) S, IsSobolevDatum (m : ℝ) (fun x => d (t, x)) (G t) :=
    fun m => exists_datumPath_of_localized ht₁ hST d hd_smooth hd_supp hd_hist m
  -- Slice continuity of the reference velocity and of `d` on `[0,S)`, at `t = 0` too.
  have hvc : ∀ t ∈ Ico (0 : ℝ) S, Continuous (fun x => ref.velocity (t, x)) :=
    fun t ht => (D01.contDiff_slice ref.velocity_smooth (hIcoT_Tδ (hIcoST ht))).continuous
  have hdc : ∀ t ∈ Ico (0 : ℝ) S, Continuous (fun x => d (t, x)) :=
    fun t ht => (D01.contDiff_slice hd_smooth (hIcoST ht)).continuous
  -- Datum path of `u = v + d` on `[0,S)` (lane 075 additivity).
  have hsum_datum : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContinuousOn G (Ico (0 : ℝ) S) ∧
        ∀ t ∈ Ico (0 : ℝ) S,
          IsSobolevDatum (m : ℝ) (fun x => ref.velocity (t, x) + d (t, x)) (G t) :=
    sobolev_add_of_localized (by linarith : S ≤ T + δ) ref.velocity d
      ref.sobolev hvc hdc hd_datum
  refine ⟨{
      velocity := u
      pressure := p
      horizon_pos := hS0
      velocity_smooth := hu_smooth.mono (Set.prod_mono hIcoST (subset_refl _))
      pressure_smooth := hp_smooth.mono (Set.prod_mono hIcoST (subset_refl _))
      initial := hinit
      divergence := fun t ht x => hdiv t (hIcoST ht) x
      momentum := fun t ht x => hmom t (hIooST ht) x
      sobolev := ?_
      pressure_gradient := ?_ }, rfl, rfl⟩
  · -- `sobolev`: rewrite `v + d` to `u` in the datum from `hsum_datum`.
    intro m
    obtain ⟨G, hGc, hGd⟩ := hsum_datum m
    refine ⟨G, hGc, ?_⟩
    intro t ht
    have hfun : (fun x : Space => ref.velocity (t, x) + d (t, x)) = fun x => u (t, x) := by
      funext x
      simp only [hd_def]
      abel
    rw [← hfun]
    exact hGd t ht
  · -- `pressure_gradient`: `∇p = ∇π + ∇(p − π)` in `L²` (lane 083).
    intro t ht
    have htT : t ∈ Ico (0 : ℝ) T := hIcoST ht
    have htTδ : t ∈ Ico (0 : ℝ) (T + δ) := hIcoT_Tδ htT
    have hπ : ContDiffOn ℝ ∞ ref.pressure (Ico (0 : ℝ) T ×ˢ (univ : Set Space)) :=
      ref.pressure_smooth.mono (Set.prod_mono hIcoT_Tδ (subset_refl _))
    exact memLp_pressureGradient_of_difference_support htT hπ hp_smooth
      (ref.pressure_gradient t htTδ) (hpsupp t htT)

end NSFormalization.Section4.R42
