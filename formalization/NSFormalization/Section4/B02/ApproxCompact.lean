import NSFormalization.Section4.B02.Remaining
import NSFormalization.Section4.B02.AnnularReal
import NSFormalization.Section4.B02.SeparatedAssembly

/-!
# B02 final field (lane 110): `approxCompactHomogeneous` and its export

This module discharges the last field of `research/B02/Spec.lean`'s
`HomogeneousApproxAPI`, `approxCompactHomogeneous` (`Spec.lean:607`), together
with the intermediate export `SeparatedCompactHomogeneousDense`
(`Spec.lean:640-664`).  It is the `L²(0,∞;Ḣ^{-1}(R³))` density conclusion of
Proposition 4.6 (`paper/sections/04-whole-space.tex:218-229`), assembled from
the three inputs proved in earlier `B02` lanes:

* `temporalApprox` (`Section4/B02/Remaining.lean`, lane 097) — the Bochner stage
  `04-whole-space.tex:251-260`: any Bochner datum path is approximated by a
  finite separated sum `Σ_j φ_j(t) A'_j` with `C_c^∞((0,∞))` time factors.
* `spatialApproxHomogeneous` (`Section4/B02/AnnularReal.lean`, lane 097) — the
  spatial stage `04-whole-space.tex:241-249`: every fibre coefficient `A'_j` is
  approximated in the datum norm by the homogeneous datum `A_j` of a physical
  `h_j ∈ C_c^∞(R³;R³)`.
* `separatedAssembly` (`Section4/B02/SeparatedAssembly.lean`, lane 103) — the
  packaging `04-whole-space.tex:260`: the assembled sum lies in `F_c` with the
  homogeneous datum path `separatedPath φ A`, on `-3/2 < s`.

The one realization-independent piece proved here is the triangle-inequality
gluing `bochnerDatumENorm_separatedPath_sub_le`, the manuscript's
`04-whole-space.tex:253-255` estimate (content on line 254,
`Σ_j |E_j|^{1/q} ‖b_j - h_j‖_X`: fixed time factors, differing spatial vectors)
`‖Σ_j φ_j (A_j - A'_j)‖ ≤ Σ_j ‖φ_j‖_{L^q} ‖A_j - A'_j‖`, obtained from
`MeasureTheory.eLpNorm_sum_le` and the scalar-function/constant-vector identity
`eLpNorm (fun t => φ_j t • v) q μ = eLpNorm (φ_j) q μ * ‖v‖ₑ`.

`B01`'s `approxCompact` (`Section4/B01/Compact.lean:155`) is **monolithic** — it
consumes the source density theorem
`Paper3.exists_angular_real_vector_positive_physical_approx`, which emits an
`IsSobolevPath` directly and has no homogeneous analogue — so it cannot be
reused or parametrized for this field; the glue below is fresh.  See
`research/B02/REMAINING_SPLIT.md` row 8 and `research/B02/ATTEMPTS_APPROX_COMPACT.md`.

## Restated `Contracts.V1.Data` vocabulary

`formalization/` cannot import `Contracts.*`.  Every predicate below is the
`Section4/{B01,D01}` restatement, each definitionally equal to its
`Contracts.V1.Data` counterpart: `separatedField`, `separatedPath`,
`bochnerDatumENorm`, `MemBochnerDatum`, `CompletedDenseVia`, `forceClassCompact`
from `Section4/B01/{Separated,Compact}.lean`; `forceTimeMeasure`,
`MemForceCompact` from `Section4/D01/ForceClass.lean`; `IsHomogeneousPath` from
`Section4/D01/HomogeneousWitness.lean`; `IsHomogeneousSliceDatum`, `SplitRange`
from `Section4/B02/Cutoff.lean`.  The conformance file
`research/B02/axioms_approx_compact.lean` discharges the spec field type through
those definitional equalities.
-/

noncomputable section

namespace NSFormalization.Section4.B02

open Set MeasureTheory
open NSFormalization.Paper3 (RealVectorSobolev)
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Section4.B01
  (separatedField separatedPath bochnerDatumENorm MemBochnerDatum CompletedDenseVia
    forceClassCompact aestronglyMeasurable_separatedPath)
open NSFormalization.Section4.D01 (forceTimeMeasure MemForceCompact)
open scoped ContDiff ENNReal

/-! ## 1. The realization-independent triangle-inequality gluing

`04-whole-space.tex:253-255`.  Purely about the datum-path Bochner norm of a
difference of two separated sums with the *same* time factors, so it is stated
and proved with no realization and no `MemBochnerDatum` hypothesis. -/

/-- Scalar function times a fixed vector: the `L^q` norm factors, for every
`q` (including `q = ⊤`).  Proof: the enorm of `φ t • v` equals that of the
`ℝ`-valued `(‖v‖ • φ) t` pointwise, and `eLpNorm` of a constant scalar times a
function is `MeasureTheory.eLpNorm_const_smul`. -/
theorem eLpNorm_smul_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → ℝ) (v : E) {q : ℝ≥0∞} {μ : Measure ℝ} :
    eLpNorm (fun t => f t • v) q μ = eLpNorm f q μ * ‖v‖ₑ := by
  have hpt : ∀ t, ‖f t • v‖ₑ = ‖((‖v‖ : ℝ) • f) t‖ₑ := fun t => by
    rw [Pi.smul_apply, enorm_smul, enorm_smul, enorm_norm, mul_comm]
  rw [eLpNorm_congr_enorm_ae (Filter.Eventually.of_forall hpt), eLpNorm_const_smul, enorm_norm,
    mul_comm]

/-- **`04-whole-space.tex:253-255`** (content on line 254,
`Σ_j |E_j|^{1/q} ‖b_j - h_j‖_X`).  The datum-path Bochner norm of the difference
of two separated sums with a common family of `C_c^∞((0,∞))` time factors is
bounded by the weighted sum `Σ_j ‖φ_j‖_{L^q} ‖A_j - A'_j‖` of the fibre errors.
Realization-independent (no `MemBochnerDatum`, no homogeneity).  Route:
`separatedPath φ A - separatedPath φ A' = Σ_j φ_j • (A_j - A'_j)`,
`MeasureTheory.eLpNorm_sum_le`, then `eLpNorm_smul_const` on each term. -/
theorem bochnerDatumENorm_separatedPath_sub_le {q : ℝ≥0∞} (hq : 1 ≤ q) {s : ℝ} {J : ℕ}
    (φ : Fin J → ℝ → ℝ) (A A' : Fin J → RealVectorSobolev s)
    (hφ : ∀ j, AEStronglyMeasurable (φ j) forceTimeMeasure) :
    bochnerDatumENorm q s (separatedPath φ A - separatedPath φ A')
      ≤ ∑ j, eLpNorm (φ j) q forceTimeMeasure * ‖A j - A' j‖ₑ := by
  have hdiff : (separatedPath φ A - separatedPath φ A')
      = fun t => ∑ j, φ j t • (A j - A' j) := by
    funext t
    simp only [Pi.sub_apply, separatedPath]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => (smul_sub _ _ _).symm)
  have hfun : (fun t => ∑ j, φ j t • (A j - A' j))
      = ∑ j, (fun t => φ j t • (A j - A' j)) := by
    funext t; rw [Finset.sum_apply]
  simp only [bochnerDatumENorm]
  rw [hdiff, hfun]
  refine le_trans (eLpNorm_sum_le (fun j _ => (hφ j).smul_const _) hq) ?_
  exact le_of_eq (Finset.sum_congr rfl (fun j _ => eLpNorm_smul_const _ _))

/-! ## 2. The `B02` export shape `SeparatedCompactHomogeneousDense`

`research/B02/Spec.lean:640-664`: the homogeneous twin of `B01`'s
`SeparatedCompactDense`, exposing the separated sum `Σ_j φ_j(t) h_j(x)` together
with its homogeneous datum path. -/

/-- `research/B02/Spec.lean:653` `SeparatedCompactHomogeneousDense`.  Every
Bochner datum path is approximated, in the `L^q(0,∞;Ḣ^s)` datum norm, by the
homogeneous datum path of a finite separated sum of smooth compact time factors
and smooth compact physical spatial profiles that itself lies in `F_c`. -/
def SeparatedCompactHomogeneousDense (q : ℝ≥0∞) (s : ℝ) : Prop :=
  ∀ (b : ℝ → RealVectorSobolev s), MemBochnerDatum q s b → ∀ η : ℝ≥0∞, 0 < η →
    ∃ (J : ℕ) (φ : Fin J → ℝ → ℝ) (h : Fin J → Space → Space)
      (A : Fin J → RealVectorSobolev s),
      (∀ j, ContDiff ℝ ∞ (φ j)) ∧ (∀ j, HasCompactSupport (φ j)) ∧
      (∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ)) ∧
      (∀ j, ContDiff ℝ ∞ (h j)) ∧ (∀ j, HasCompactSupport (h j)) ∧
      (∀ j, IsHomogeneousSliceDatum s (h j) (A j)) ∧
      MemForceCompact (separatedField φ h) ∧
      NSFormalization.Section4.D01.Homogeneous.IsHomogeneousPath s
        (separatedField φ h) (separatedPath φ A) ∧
      AEStronglyMeasurable (separatedPath φ A) forceTimeMeasure ∧
      bochnerDatumENorm q s (separatedPath φ A - b) < η

/-- **`SeparatedCompactHomogeneousDense`, proved** on `1 ≤ q`, `q ≠ ⊤`,
`SplitRange s`.  The temporal approximant supplies `J`, `φ` and coefficients
`A'_j` within `η/2`; `spatialApproxHomogeneous` replaces each `A'_j` by the
homogeneous datum `A_j` of a physical `h_j` with a summed replacement error
below `η/2` (controlled through the gluing of §1); `separatedAssembly` packages
the pair as a member of `F_c` with its homogeneous datum path. -/
theorem separatedCompactHomogeneousDense (q : ℝ≥0∞) (hq1 : 1 ≤ q) (hqt : q ≠ ⊤) (s : ℝ)
    (hs : SplitRange s) : SeparatedCompactHomogeneousDense q s := by
  intro b hb η hη
  -- Reduce to a finite, positive target `η'' = min η 1 ≤ η`.
  set η'' : ℝ≥0∞ := min η 1 with hη''def
  have hη''_le : η'' ≤ η := min_le_left _ _
  have hη''_pos : 0 < η'' := lt_min hη (by norm_num)
  have hη''_ne : η'' ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) (min_le_right _ _)
  -- Its half, positive and finite.
  set η₁ : ℝ≥0∞ := η'' / 2 with hη₁def
  have hη₁_pos : 0 < η₁ := ENNReal.half_pos hη''_pos.ne'
  have hη₁_ne : η₁ ≠ ⊤ := by rw [hη₁def]; exact (ENNReal.div_lt_top hη''_ne (by norm_num)).ne
  -- Temporal stage at `η₁`.
  obtain ⟨J, φ, A', hφs, hφc, hφpos, hT⟩ :=
    temporalApprox q hq1 hqt s b hb η₁ hη₁_pos
  -- Each `‖φ_j‖_{L^q}` is finite (φ_j is smooth with compact support).
  have hEfin : ∀ j, eLpNorm (φ j) q forceTimeMeasure ≠ ⊤ := fun j =>
    (Continuous.memLp_of_hasCompactSupport (p := q) (μ := forceTimeMeasure)
      (hφs j).continuous (hφc j)).eLpNorm_lt_top.ne
  set S : ℝ≥0∞ := ∑ j, eLpNorm (φ j) q forceTimeMeasure with hSdef
  have hSne : S ≠ ⊤ := by
    rw [hSdef]; exact (ENNReal.sum_lt_top.mpr (fun j _ => (hEfin j).lt_top)).ne
  have hS1_ne_top : S + 1 ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hSne, by norm_num⟩
  have hS1_ne_zero : S + 1 ≠ 0 := by positivity
  -- Per-fibre spatial tolerance `η' = η₁ / (S + 1) > 0`.
  set η' : ℝ≥0∞ := η₁ / (S + 1) with hη'def
  have hη'_pos : 0 < η' := ENNReal.div_pos hη₁_pos.ne' hS1_ne_top
  -- Spatial stage: physical `h_j` with homogeneous datum `H_j` within `η'` of `A'_j`.
  choose h H hhs hhc hHdatum hHerr using
    fun j => spatialApproxHomogeneous s hs (A' j) η' hη'_pos
  -- The gluing bound: `‖separatedPath φ H - separatedPath φ A'‖ ≤ η₁`, in `eLpNorm` form.
  have hPe : eLpNorm (separatedPath φ H - separatedPath φ A') q forceTimeMeasure ≤ η₁ := by
    refine le_trans (bochnerDatumENorm_separatedPath_sub_le hq1 φ H A'
      (fun j => (hφs j).continuous.aestronglyMeasurable)) ?_
    have hstep : (∑ j, eLpNorm (φ j) q forceTimeMeasure * ‖H j - A' j‖ₑ)
        ≤ ∑ j, eLpNorm (φ j) q forceTimeMeasure * η' :=
      Finset.sum_le_sum (fun j _ => by gcongr; exact (hHerr j).le)
    refine le_trans hstep ?_
    rw [← Finset.sum_mul, ← hSdef]
    calc S * η' ≤ (S + 1) * η' := by gcongr; exact le_self_add
      _ = η₁ := by rw [hη'def, ENNReal.mul_div_cancel' (fun h => absurd h hS1_ne_zero)
            (fun h => absurd h hS1_ne_top)]
  -- The temporal bound in `eLpNorm` form (defeq to `hT`).
  have hTe : eLpNorm (separatedPath φ A' - b) q forceTimeMeasure < η₁ := hT
  -- Triangle inequality to `b`.
  have hmeasP : AEStronglyMeasurable (separatedPath φ H - separatedPath φ A') forceTimeMeasure :=
    (aestronglyMeasurable_separatedPath s φ H hφs).sub
      (aestronglyMeasurable_separatedPath s φ A' hφs)
  have hmeasT : AEStronglyMeasurable (separatedPath φ A' - b) forceTimeMeasure :=
    (aestronglyMeasurable_separatedPath s φ A' hφs).sub (hb : MemLp b q forceTimeMeasure).1
  have hfinal : bochnerDatumENorm q s (separatedPath φ H - b) < η'' := by
    show eLpNorm (separatedPath φ H - b) q forceTimeMeasure < η''
    rw [show separatedPath φ H - b
      = (separatedPath φ H - separatedPath φ A') + (separatedPath φ A' - b) from
      (sub_add_sub_cancel _ _ _).symm]
    refine lt_of_le_of_lt (eLpNorm_add_le hmeasP hmeasT hq1) ?_
    calc eLpNorm (separatedPath φ H - separatedPath φ A') q forceTimeMeasure
          + eLpNorm (separatedPath φ A' - b) q forceTimeMeasure
        ≤ η₁ + eLpNorm (separatedPath φ A' - b) q forceTimeMeasure := add_le_add hPe le_rfl
      _ < η₁ + η₁ := ENNReal.add_lt_add_left hη₁_ne hTe
      _ = η'' := by rw [hη₁def]; exact ENNReal.add_halves η''
  -- Package via `separatedAssembly` (computed once).
  have hasm := separatedAssembly s hs.1 φ h H hφs hφc hφpos hhs hhc hHdatum
  exact ⟨J, φ, h, H, hφs, hφc, hφpos, hhs, hhc, hHdatum,
    hasm.1, hasm.2.1, hasm.2.2, lt_of_lt_of_le hfinal hη''_le⟩

/-! ## 3. The spec field `approxCompactHomogeneous` (`research/B02/Spec.lean:607`) -/

/-- **`approxCompactHomogeneous`** (`research/B02/Spec.lean:607`).  For every
`q ∈ [1,∞)` and every `s` in `SplitRange`, smooth compactly supported forces are
dense in the completed homogeneous Bochner space `L^q(0,∞;Ḣ^s(R³))`, measured by
the datum norm — the `L²(0,∞;Ḣ^{-1})` clause of Proposition 4.6
(`04-whole-space.tex:218-229`).

This statement is **definitionally equal** to the spec field `Spec.lean:607`
(not literally token-identical: `Spec.lean:607` writes `CompletedDenseHomogeneous`,
which is the `Data.lean:752` `abbrev` for `CompletedDenseVia q s (IsHomogeneousPath s)`,
and uses the spec-local `SplitRange` / `Data.forceClassCompact` where this uses the
`formalization/` restatements).  The defeq is `rfl`-checked in
`research/B02/axioms_approx_compact.lean` (`example : specApproxCompactHomogeneous =
laneApproxCompactHomogeneous := rfl`), which is stronger than the
elaboration-unification the conformance `example` relies on.

`CompletedDenseHomogeneous q s forceClassCompact` unfolds to
`CompletedDenseVia q s (IsHomogeneousPath s) forceClassCompact`; discharged from
`separatedCompactHomogeneousDense` with witnesses `f := separatedField φ h`,
`D := separatedPath φ A`. -/
theorem approxCompactHomogeneous : ∀ (q : ℝ≥0∞), 1 ≤ q → q ≠ ⊤ → ∀ s : ℝ, SplitRange s →
    CompletedDenseVia q s (NSFormalization.Section4.D01.Homogeneous.IsHomogeneousPath s)
      forceClassCompact := by
  intro q hq1 hqt s hs b hb r hr
  obtain ⟨J, φ, h, H, _hφs, _hφc, _hφpos, _hhs, _hhc, _hHdatum, hMem, hPath, hMeas, hLt⟩ :=
    separatedCompactHomogeneousDense q hq1 hqt s hs b hb r hr
  exact ⟨separatedField φ h, hMem, separatedPath φ H, hPath, hMeas, hLt⟩

end NSFormalization.Section4.B02
