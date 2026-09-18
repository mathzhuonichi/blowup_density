import NSFormalization.Section3.T16.Assembly
import NSFormalization.Section3.T17.ForceSupport
import NSFormalization.Section3.T17.Correction

/-!
# Probe: the three support/regularity fields close on the concrete correction

The first three theorems restate the canonical `CorrectionAPI` fields
`force_smooth` / `force_periodic` / `force_support`
(`Section3/T17/Correction.lean:161-173`, `research/T17/Spec.lean:836-852`) with
`D` replaced by the concrete `correctionData` and `place.x₀`, `place.T` replaced
by the bare `x₀`, `T`; each is closed directly by `exact`.  The spatial factor
is the manuscript's **open** ball, not a closed-ball weakening.

The last theorem instantiates all three fields on T16's cutoffs at a nonzero
constant, divergence-free, periodic reference, so none of them is vacuous.
-/

noncomputable section

namespace NSFormalization.Section3.T17.Probe

open Set MeasureTheory Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 (IsPeriodicOn)
open NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff Topology BigOperators

/-! ## The Spec fields, with the concrete `D := correctionData ...` -/

theorem field_force_smooth (ν : ℝ) {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T δ r : ℝ)
    (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
      ContDiff ℝ ∞ (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε) := by
  exact force_smooth ν hv x₀ T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp
    hr2 hεtime hεspace

theorem field_force_periodic (ν : ℝ) {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T δ r : ℝ)
    (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
      IsPeriodicOn univ (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε) := by
  exact force_periodic ν hv x₀ T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp
    hr2 hεtime hεspace

theorem field_force_support (ν : ℝ) {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T δ r : ℝ)
    (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
      tsupport (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε) ⊆
        Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ
          periodicSet (Metric.ball x₀ (ε * (correctionData v x₀ T θ η O θR ε₀).θRadius)) := by
  exact force_support ν hv x₀ T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp
    hr2 hεtime hεspace

/-! ## Field conformance: the three statements are literally the record fields

For a hypothetical `CorrectionAPI` record at the concrete `correctionData`, the
projections `A.force_smooth`, `A.force_periodic`, `A.force_support` typecheck as
the statements proved in `Section3/T17/ForceSupport.lean` (with `place.x₀`,
`place.T` in place of the bare `x₀`, `T`).  These are type checks only; the
non-vacuity of the statements is the last theorem of this file. -/

example (ν : ℝ) {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (place : NSFormalization.Section3.T15.PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ) (θ : Space → ℝ) (η : ℝ → ℝ) (O : Set Space) (θR ε₀ : ℝ)
    (A : CorrectionAPI ν place v r δ
      (correctionData v place.x₀ place.T θ η O θR ε₀)) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v place.x₀ place.T θ η O θR ε₀).ε₀,
      ContDiff ℝ ∞ (correctionForce ν v (correctionData v place.x₀ place.T θ η O θR ε₀) ε) :=
  A.force_smooth

example (ν : ℝ) {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (place : NSFormalization.Section3.T15.PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ) (θ : Space → ℝ) (η : ℝ → ℝ) (O : Set Space) (θR ε₀ : ℝ)
    (A : CorrectionAPI ν place v r δ
      (correctionData v place.x₀ place.T θ η O θR ε₀)) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v place.x₀ place.T θ η O θR ε₀).ε₀,
      IsPeriodicOn univ
        (correctionForce ν v (correctionData v place.x₀ place.T θ η O θR ε₀) ε) :=
  A.force_periodic

example (ν : ℝ) {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (place : NSFormalization.Section3.T15.PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ) (θ : Space → ℝ) (η : ℝ → ℝ) (O : Set Space) (θR ε₀ : ℝ)
    (A : CorrectionAPI ν place v r δ
      (correctionData v place.x₀ place.T θ η O θR ε₀)) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v place.x₀ place.T θ η O θR ε₀).ε₀,
      tsupport (correctionForce ν v (correctionData v place.x₀ place.T θ η O θR ε₀) ε) ⊆
        Ioo (place.T - 2 * ε ^ 2) (place.T + 2 * ε ^ 2) ×ˢ
          periodicSet (Metric.ball place.x₀
            (ε * (correctionData v place.x₀ place.T θ η O θR ε₀).θRadius)) :=
  A.force_support

/-- The three U7 theorems, instantiated at `place.x₀` / `place.T`, are exactly
the three record fields: this is the `exact` probe asked for by the lane. -/
theorem fields_at_placement (ν : ℝ) {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space}
    (place : NSFormalization.Section3.T15.PlacementData u p f K)
    {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v) (δ r : ℝ)
    (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min place.T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    (∀ ε ∈ Ioc (0 : ℝ) (correctionData v place.x₀ place.T θ η O θR ε₀).ε₀,
      ContDiff ℝ ∞
        (correctionForce ν v (correctionData v place.x₀ place.T θ η O θR ε₀) ε)) ∧
    (∀ ε ∈ Ioc (0 : ℝ) (correctionData v place.x₀ place.T θ η O θR ε₀).ε₀,
      IsPeriodicOn univ
        (correctionForce ν v (correctionData v place.x₀ place.T θ η O θR ε₀) ε)) ∧
    (∀ ε ∈ Ioc (0 : ℝ) (correctionData v place.x₀ place.T θ η O θR ε₀).ε₀,
      tsupport (correctionForce ν v (correctionData v place.x₀ place.T θ η O θR ε₀) ε) ⊆
        Ioo (place.T - 2 * ε ^ 2) (place.T + 2 * ε ^ 2) ×ˢ
          periodicSet (Metric.ball place.x₀
            (ε * (correctionData v place.x₀ place.T θ η O θR ε₀).θRadius))) :=
  ⟨force_smooth ν hv place.x₀ place.T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp
      hr2 hεtime hεspace,
   force_periodic ν hv place.x₀ place.T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp
      hr2 hεtime hεspace,
   force_support ν hv place.x₀ place.T δ r hvper O θR ε₀ hθ hη hθc hηc hθsupp hηsupp
      hr2 hεtime hεspace⟩

/-! ## Non-vacuity on a nonzero constant reference and the T16 cutoffs -/

theorem nonvacuous_force_support :
    ∃ (v : SpaceTimeField) (θ : Space → ℝ) (η : ℝ → ℝ) (O : Set Space) (θR ε₀ : ℝ),
      v ≠ 0 ∧ 0 < ε₀ ∧
      (∀ t : ℝ, ∀ x : Space, spatialDivergence v t x = 0) ∧
      (∀ ε ∈ Ioc (0 : ℝ) (correctionData v 0 1 θ η O θR ε₀).ε₀,
        ContDiff ℝ ∞ (correctionForce 1 v (correctionData v 0 1 θ η O θR ε₀) ε)) ∧
      (∀ ε ∈ Ioc (0 : ℝ) (correctionData v 0 1 θ η O θR ε₀).ε₀,
        IsPeriodicOn univ (correctionForce 1 v (correctionData v 0 1 θ η O θR ε₀) ε)) ∧
      (∀ ε ∈ Ioc (0 : ℝ) (correctionData v 0 1 θ η O θR ε₀).ε₀,
        tsupport (correctionForce 1 v (correctionData v 0 1 θ η O θR ε₀) ε) ⊆
          Ioo ((1 : ℝ) - 2 * ε ^ 2) ((1 : ℝ) + 2 * ε ^ 2) ×ˢ
            periodicSet (Metric.ball (0 : Space)
              (ε * (correctionData v 0 1 θ η O θR ε₀).θRadius))) := by
  obtain ⟨θR, θ, O, hθR, hθsm, hθcs, hθsupp, hOopen, hKO, hθone, hθrange⟩ :=
    exists_originCutoff (K := (∅ : Set Space)) isCompact_empty
  obtain ⟨η, hηsm, hηcs, hηrange, hηone, hηsupp⟩ := exists_timeCutoff
  obtain ⟨ε₀, hε₀pos, hεtime, hεspace⟩ :=
    exists_threshold hθR (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
  let v : SpaceTimeField := fun _ => coordinateVector 0
  have hv : ContDiff ℝ ∞ v := contDiff_const
  have hvper : IsPeriodicOn univ v := fun _ _ _ _ => rfl
  have hvdiv : ∀ t : ℝ, ∀ x : Space, spatialDivergence v t x = 0 := by
    intro t x
    simp [spatialDivergence, spatialDerivative, v]
  have hvne : v ≠ 0 := by
    intro h
    have h0 := congrFun h ((0 : ℝ), (0 : Space))
    simp only [v, Pi.zero_apply] at h0
    have hc : (coordinateVector (0 : Fin 3)) (0 : Fin 3) = 0 := by rw [h0]; rfl
    simp [coordinateVector] at hc
  refine ⟨v, θ, η, O, θR, ε₀, hvne, hε₀pos, hvdiv, ?_, ?_, ?_⟩
  · exact force_smooth 1 hv 0 1 1 (1 / 4) hvper O θR ε₀ hθsm hηsm hθcs hηcs
      hθsupp hηsupp (by norm_num) hεtime hεspace
  · exact force_periodic 1 hv 0 1 1 (1 / 4) hvper O θR ε₀ hθsm hηsm hθcs hηcs
      hθsupp hηsupp (by norm_num) hεtime hεspace
  · exact force_support 1 hv 0 1 1 (1 / 4) hvper O θR ε₀ hθsm hηsm hθcs hηcs
      hθsupp hηsupp (by norm_num) hεtime hεspace

end NSFormalization.Section3.T17.Probe

#print axioms NSFormalization.Section3.T17.Probe.field_force_smooth
#print axioms NSFormalization.Section3.T17.Probe.field_force_periodic
#print axioms NSFormalization.Section3.T17.Probe.field_force_support
#print axioms NSFormalization.Section3.T17.Probe.fields_at_placement
#print axioms NSFormalization.Section3.T17.Probe.nonvacuous_force_support
