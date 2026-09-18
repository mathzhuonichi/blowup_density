import NSFormalization.Section3.T10.PeriodicData
import NSFormalization.Section4.I02.Reference
import NSFormalization.Section4.I02.Prescribed
import NSFormalization.Section4.I02.Support
import NSFormalization.Source.ParabolicScaling
import NSFormalization.Source.PacketScaling

/-!
# T16 (`lem:potential`): a local divergence-free cutoff on the three-torus

This module realizes the reconciled specification `research/T16/Spec.lean`
(`paper/sections/03-torus.tex:176-216`) over the **canonical Section 3 / Section 4
vocabulary**.  Field types, periodicity and the frequency lattice come from
`NSFormalization.Section3.T10.PeriodicData` (`SpaceTimeField`, `IsPeriodicOn`,
`PeriodicFrequency`); the differential operators (`spatialDivergence`,
`coordinateVector`, the spatial curl) come from the pinned
`NavierStokes.ProblemStatement` / `NavierStokes.SpatialCurl`; the radial
potential, the rescaled cutoffs and the packet rescaling come from
`NSFormalization.Paper1` / `NSFormalization.Source`.  Every notion the reconciled
`Spec.lean` writes through the registered `Contracts.V1` copies
(`curl`, `cross`, `scaledSpatialCutoff`, `scaledTemporalCutoff`, `scaledPacket`,
`spatialDivergence`) is definitionally equal to the canonical notion used here;
`research/T16/probes/api_on_canonical.lean` records the `rfl` bridges and the
fieldwise structure conversion.

## Scope of the present lane (honest partial)

`localPotentialStatement` (`Spec.lean:328-336`) fixes the reference velocity `v`
only on the coordinate ball `Ioo 0 (T+δ) ×ˢ Metric.ball x₀ r`.  The Section 4
`I02` construction of the *same* lemma
(`timePotential_contDiffOn`, `spatialCurl_timePotential_on`) instead assumes `v`
smooth and divergence-free on `I ×ˢ (univ : Set Space)` (all of physical space),
and the torus correction requires the periodic lift of a compactly supported
`R³` field.  Both are genuine gaps that this lane does **not** close; see
`research/T16/ATTEMPTS.md` and `research/T16/SPEC_ISSUES.md` for the exact
residual lemma statements and error text.

What is proved here and reusable downstream:

* the two Urysohn cutoffs with their full clause list including the `[0,1]`
  range (`exists_originCutoff`, `exists_timeCutoff`);
* the common small-scale threshold `ε₀` with `2ε² < min T δ` and
  `ε·θRadius < r` (`exists_threshold`);
* the definitional shape of `eq:potential` (`potential_formula` reduces to the
  radial integral by `rfl`, `centeredPotential_eq_integral`);
* the full `LocalPotentialAPI` for the zero reference `v = 0`
  (`localPotential_zero`), the concrete non-vacuity witness that exercises every
  field of the reconciled structure.
-/

noncomputable section

namespace NSFormalization.Section3.T16

open Set MeasureTheory Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 (IsPeriodicOn)
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField)
open NSFormalization.Section4.I02
open NSFormalization.Paper1.RadialPotential (cross timePotential centeredPotential_eq_integral)
open NSFormalization.Paper1.CorrectionProfile (spatialCutoff temporalCutoff)
open NSFormalization.Source (parabolicVelocity)
open NSFormalization.Source.PacketScaling (zeroPastField)
open scoped ContDiff Topology

/-! ## 1. Periodic physical-layer helpers (`Spec.lean:54-98`) -/

/-- `03-torus.tex:188,212`: the Euclidean lattice vector of a torus frequency,
the actual integer translation in the `R³` lift. -/
def latticeVector (k : NSFormalization.Section3.T10.PeriodicFrequency) : Space :=
  WithLp.toLp 2 (fun i => (k i : ℝ))

/-- `03-torus.tex:188,212`: the lift to `R³` of a spatial set on the unit torus. -/
def periodicSet (S : Set Space) : Set Space :=
  {x | ∃ k : NSFormalization.Section3.T10.PeriodicFrequency, x - latticeVector k ∈ S}

/-- `03-torus.tex:112-120,214-215`: the periodized rescaled packet consumed by
`eq:bgzero`.  `scaledPacket U x₀ T ε` is the canonical
`parabolicVelocity ε⁻¹ (T-ε²) x₀ (zeroPastField U)`
(`Contracts.V1.scaledPacket`, guarded by a `rfl` bridge). -/
def periodicScaledPacket (U : SpaceTimeField) (x₀ : Space) (T ε : ℝ) :
    SpaceTimeField :=
  fun z => ∑' k : NSFormalization.Section3.T10.PeriodicFrequency,
    parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U) (z.1, z.2 - latticeVector k)

/-- `03-torus.tex:190-192`: the corrected background `v + w_ε` of `eq:bgzero`. -/
def correctedBackground (v : SpaceTimeField) (w : ℝ → SpaceTimeField) (ε : ℝ) :
    SpaceTimeField :=
  fun z => v z + w ε z

/-! ## 2. Construction data and the reconciled API (`Spec.lean:104-318`) -/

/-- The witnesses chosen once before the small scale `ε` is quantified
(`03-torus.tex:167-188,212`), packaged as data so downstream consumers can
project the cutoffs, threshold, potential and correction. -/
structure CutoffData where
  /-- Spatial Urysohn cutoff `θ`. -/
  θ : Space → ℝ
  /-- Temporal Urysohn cutoff `η`. -/
  η : ℝ → ℝ
  /-- Open plateau on which `θ = 1`. -/
  plateau : Set Space
  /-- Fixed support radius for `θ`. -/
  θRadius : ℝ
  /-- Common upper threshold for every sufficiently small `ε`. -/
  ε₀ : ℝ
  /-- Radial vector potential `A` of `eq:potential`. -/
  potential : SpaceTimeField
  /-- Scale-indexed correction family `w_ε` of `eq:cutoff`. -/
  correction : ℝ → SpaceTimeField

/-- The reconciled clauses of Lemma `lem:potential` (`03-torus.tex:167-215`),
restated over the canonical vocabulary.  Definitionally equal, field by field,
to `BlowupDensity.T16.Spec.LocalPotentialAPI`. -/
structure LocalPotentialAPI (v U : SpaceTimeField) (K : Set Space)
    (x₀ : Space) (r T δ : ℝ) (D : CutoffData) : Prop where
  theta_smooth : ContDiff ℝ ∞ D.θ
  theta_compactSupport : HasCompactSupport D.θ
  theta_range : ∀ x, D.θ x ∈ Icc (0 : ℝ) 1
  plateau_open : IsOpen D.plateau
  prescribed_subset_plateau : K ⊆ D.plateau
  theta_one : EqOn D.θ (fun _ => 1) D.plateau
  theta_radius_pos : 0 < D.θRadius
  theta_support : tsupport D.θ ⊆ Metric.ball (0 : Space) D.θRadius
  eta_smooth : ContDiff ℝ ∞ D.η
  eta_compactSupport : HasCompactSupport D.η
  eta_range : ∀ t, D.η t ∈ Icc (0 : ℝ) 1
  eta_one : EqOn D.η (fun _ => 1) (Icc (-1 : ℝ) 1)
  eta_support : tsupport D.η ⊆ Ioo (-2 : ℝ) 2
  eps_pos : 0 < D.ε₀
  eps_time : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, 2 * ε ^ 2 < min T δ
  eps_space : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ε * D.θRadius < r
  potential_smooth : ContDiffOn ℝ ∞ D.potential
    (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ r)
  potential_formula : ∀ t x, D.potential (t, x) =
    ∫ ρ in (0 : ℝ)..1,
      ρ • cross (v (t, x₀ + ρ • (x - x₀))) (x - x₀)
  potential_curl : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
    SpatialCurl.curl (fun y => D.potential (t, y)) x = v (t, x)
  correction_formula : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t,
    ∀ x ∈ Metric.ball x₀ r,
      D.correction ε (t, x) =
        -SpatialCurl.curl (fun y =>
          (temporalCutoff D.η T ε t *
            spatialCutoff D.θ x₀ ε y) • D.potential (t, y)) x
  correction_smooth : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ContDiff ℝ ∞ (D.correction ε)
  correction_periodic : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    IsPeriodicOn univ (D.correction ε)
  correction_divergence_free : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t x,
    spatialDivergence (D.correction ε) t x = 0
  correction_support : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    tsupport (D.correction ε) ⊆
      Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ (univ : Set Space)
  correction_support_ball : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t,
    tsupport (fun x => D.correction ε (t, x)) ⊆
      periodicSet (Metric.ball x₀ r)
  correction_cancels : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
    ∀ t ∈ Ico (T - ε ^ 2) T,
      ∃ O : Set Space, IsOpen O ∧
        tsupport (fun x => periodicScaledPacket U x₀ T ε (t, x)) ⊆ O ∧
        ∀ x ∈ O, correctedBackground v D.correction ε (t, x) = 0

/-- Exact construction quantifiers for Lemma `lem:potential`
(`Spec.lean:320-336`). -/
def localPotentialStatement : Prop :=
  ∀ (v U : SpaceTimeField) (K : Set Space) (x₀ : Space) (r T δ : ℝ),
    0 < r → r < 1 / 2 → 0 < T → 0 < δ → IsCompact K →
    IsPeriodicOn univ v →
    ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ r) →
    (∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
      spatialDivergence v t x = 0) →
    (∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x => U (t, x)) ⊆ K) →
    ∃ D : CutoffData, LocalPotentialAPI v U K x₀ r T δ D

/-! ## 3. Elementary zero-field facts -/

/-- The coordinate cross product is zero in its first slot. -/
theorem cross_zero_left (b : Space) : cross (0 : Space) b = 0 := by
  ext i
  fin_cases i <;>
    simp [cross, coordinateVector]

/-- The spatial curl of a constant field vanishes. -/
theorem curl_const_zero (c : Space) (x : Space) :
    SpatialCurl.curl (fun _ : Space => c) x = 0 := by
  simp [SpatialCurl.curl]

/-- The divergence of a constant field vanishes. -/
theorem spatialDivergence_const_zero (c : Space) (t : ℝ) (x : Space) :
    spatialDivergence (fun _ : SpaceTime => c) t x = 0 := by
  have h : spatialDerivative (fun _ : SpaceTime => c) t x = 0 := by
    change fderiv ℝ (fun _ : Space => c) x = 0
    simp
  simp [spatialDivergence, h]

/-- The topological support of the zero spacetime field is empty. -/
theorem tsupport_zero_field :
    tsupport (fun _ : SpaceTime => (0 : Space)) = (∅ : Set SpaceTime) := by
  have hs : Function.support (fun _ : SpaceTime => (0 : Space)) = (∅ : Set SpaceTime) :=
    Function.support_eq_empty_iff.mpr rfl
  simp [tsupport, hs]

/-- The topological support of a zero spatial slice is empty. -/
theorem tsupport_zero_slice :
    tsupport (fun _ : Space => (0 : Space)) = (∅ : Set Space) := by
  have hs : Function.support (fun _ : Space => (0 : Space)) = (∅ : Set Space) :=
    Function.support_eq_empty_iff.mpr rfl
  simp [tsupport, hs]

/-! ## 4. Reusable Urysohn cutoffs and the scale threshold -/

/-- A smooth compactly supported spatial Urysohn cutoff centred at the origin,
with values in `[0,1]`, equal to one on an open plateau containing the
prescribed compact set, and supported in the fixed reference ball of the
produced radius (`03-torus.tex:167-172,181,212`).  This strengthens
`NSFormalization.Section4.I02.exists_prescribed_cutoff` with the range clause the
reconciled `theta_range` requires. -/
theorem exists_originCutoff {K : Set Space} (hK : IsCompact K) :
    ∃ R : ℝ, ∃ θ : Space → ℝ, ∃ O : Set Space,
      0 < R ∧ ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧
        tsupport θ ⊆ ball (0 : Space) R ∧ IsOpen O ∧ K ⊆ O ∧
        EqOn θ (fun _ => 1) O ∧ (∀ x, θ x ∈ Icc (0 : ℝ) 1) := by
  obtain ⟨B, hB, hb⟩ := hK.isBounded.exists_pos_norm_le
  have hR : (0 : ℝ) < B + 1 := by linarith
  have hKR : K ⊆ ball (0 : Space) (B + 1) := by
    intro y hy
    have := hb y hy
    rw [mem_ball, dist_zero_right]
    linarith
  obtain ⟨r₁, hr₁, hK₁⟩ := exists_pos_lt_subset_ball hR hK.isClosed hKR
  obtain ⟨r₂, hr₁₂, hr₂R⟩ := exists_between hr₁.2
  let f : ContDiffBump (0 : Space) := ⟨r₁, r₂, hr₁.1, hr₁₂⟩
  refine ⟨B + 1, f, ball (0 : Space) r₁, hR, f.contDiff, f.hasCompactSupport, ?_,
    isOpen_ball, hK₁, ?_, fun x => ?_⟩
  · rw [f.tsupport_eq]
    exact closedBall_subset_ball hr₂R
  · intro x hx
    exact f.one_of_mem_closedBall (ball_subset_closedBall hx)
  · exact ⟨f.nonneg' x, f.le_one⟩

/-- A smooth compactly supported temporal Urysohn cutoff with values in `[0,1]`,
equal to one on `[-1,1]` and supported inside `(-2,2)`
(`03-torus.tex:173-174,182,188-189`). -/
theorem exists_timeCutoff :
    ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      (∀ t, η t ∈ Icc (0 : ℝ) 1) ∧ EqOn η (fun _ => 1) (Icc (-1 : ℝ) 1) ∧
      tsupport η ⊆ Ioo (-2 : ℝ) 2 := by
  let f : ContDiffBump (0 : ℝ) := ⟨1, 3 / 2, one_pos, by norm_num⟩
  have hri : f.rIn = (1 : ℝ) := rfl
  have hro : f.rOut = (3 / 2 : ℝ) := rfl
  refine ⟨f, f.contDiff, f.hasCompactSupport, fun t => ⟨f.nonneg' t, f.le_one⟩, ?_, ?_⟩
  · intro t ht
    apply f.one_of_mem_closedBall
    rw [mem_closedBall, Real.dist_eq, hri, abs_le]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · rw [f.tsupport_eq]
    intro t ht
    rw [mem_closedBall, Real.dist_eq, hro, abs_le] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- The common small-scale threshold `ε₀ > 0` of `03-torus.tex:188,212`: for
every admissible `ε ∈ (0,ε₀]` both `2ε² < min T δ` and `ε·θRadius < r`. -/
theorem exists_threshold {θRadius r T δ : ℝ} (hθR : 0 < θRadius)
    (hr : 0 < r) (hT : 0 < T) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ (∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ) ∧
      (∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θRadius < r) := by
  have hm : 0 < min T δ := lt_min hT hδ
  refine ⟨min 1 (min (min T δ / 3) (r / (θRadius + 1))), ?_, ?_, ?_⟩
  · exact lt_min one_pos (lt_min (by positivity) (by positivity))
  · intro ε hε
    obtain ⟨hε0, hεle⟩ := hε
    have hε1 : ε ≤ 1 := le_trans hεle (min_le_left _ _)
    have hεm : ε ≤ min T δ / 3 :=
      le_trans hεle (le_trans (min_le_right _ _) (min_le_left _ _))
    have hsq : ε ^ 2 ≤ ε := by nlinarith [hε0.le, hε1]
    nlinarith [hsq, hεm, hm]
  · intro ε hε
    obtain ⟨hε0, hεle⟩ := hε
    have hεr : ε ≤ r / (θRadius + 1) :=
      le_trans hεle (le_trans (min_le_right _ _) (min_le_right _ _))
    have h1 : ε * θRadius ≤ (r / (θRadius + 1)) * θRadius :=
      mul_le_mul_of_nonneg_right hεr hθR.le
    have h2 : (r / (θRadius + 1)) * θRadius < r := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [hr, hθR]
    linarith

/-! ## 5. The full API for the zero reference (`v = 0`), the non-vacuity witness -/

/-- The reconciled `LocalPotentialAPI` holds for the zero reference velocity,
with the actual Urysohn cutoffs, the actual threshold, and the zero potential
and correction.  Every field of the structure is discharged; this is the
concrete non-vacuity instance requested by the lane brief. -/
theorem localPotential_zero (U : SpaceTimeField) (K : Set Space) (x₀ : Space)
    (r T δ : ℝ) (hr : 0 < r) (_hr2 : r < 1 / 2) (hT : 0 < T) (hδ : 0 < δ)
    (hK : IsCompact K)
    (_hU : ∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x => U (t, x)) ⊆ K) :
    ∃ D : CutoffData, LocalPotentialAPI (fun _ => (0 : Space)) U K x₀ r T δ D := by
  obtain ⟨R, θ, O, hRpos, hθsm, hθcs, hθsupp, hOopen, hKO, hθone, hθrange⟩ :=
    exists_originCutoff hK
  obtain ⟨η, hηsm, hηcs, hηrange, hηone, hηsupp⟩ := exists_timeCutoff
  obtain ⟨ε₀, hε₀pos, hεtime, hεspace⟩ := exists_threshold hRpos hr hT hδ
  refine ⟨⟨θ, η, O, R, ε₀, fun _ => 0, fun _ => fun _ => 0⟩, ?_⟩
  refine
    { theta_smooth := hθsm
      theta_compactSupport := hθcs
      theta_range := hθrange
      plateau_open := hOopen
      prescribed_subset_plateau := hKO
      theta_one := hθone
      theta_radius_pos := hRpos
      theta_support := hθsupp
      eta_smooth := hηsm
      eta_compactSupport := hηcs
      eta_range := hηrange
      eta_one := hηone
      eta_support := hηsupp
      eps_pos := hε₀pos
      eps_time := hεtime
      eps_space := hεspace
      potential_smooth := contDiffOn_const
      potential_formula := ?_
      potential_curl := ?_
      correction_formula := ?_
      correction_smooth := ?_
      correction_periodic := ?_
      correction_divergence_free := ?_
      correction_support := ?_
      correction_support_ball := ?_
      correction_cancels := ?_ }
  · -- potential_formula: the zero potential equals the radial integral of `cross 0 _`
    intro t x
    show (0 : Space) = ∫ ρ in (0 : ℝ)..1, ρ • cross (0 : Space) (x - x₀)
    simp [cross_zero_left]
  · -- potential_curl: curl of the zero field is zero, matching `v = 0`
    intro t _ x _
    exact curl_const_zero 0 x
  · -- correction_formula: the zero correction equals `-curl (c • 0)`
    intro ε _ t x _
    show (0 : Space) =
      -SpatialCurl.curl (fun y =>
        (temporalCutoff η T ε t * spatialCutoff θ x₀ ε y) • (0 : Space)) x
    have hfun : (fun y => (temporalCutoff η T ε t * spatialCutoff θ x₀ ε y) • (0 : Space))
        = fun _ : Space => (0 : Space) := by
      funext y; rw [smul_zero]
    rw [hfun, curl_const_zero, neg_zero]
  · -- correction_smooth
    intro ε _
    exact contDiff_const
  · -- correction_periodic
    intro ε _ t _ x i
    rfl
  · -- correction_divergence_free
    intro ε _ t x
    exact spatialDivergence_const_zero 0 t x
  · -- correction_support: empty support
    intro ε _
    rw [tsupport_zero_field]
    exact empty_subset _
  · -- correction_support_ball: empty slice support
    intro ε _ t
    rw [tsupport_zero_slice]
    exact empty_subset _
  · -- correction_cancels: the background is identically zero, take O = univ
    intro ε _ t _
    refine ⟨univ, isOpen_univ, subset_univ _, fun x _ => ?_⟩
    show (0 : Space) + 0 = 0
    simp

end NSFormalization.Section3.T16
