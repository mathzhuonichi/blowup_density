import NSFormalization.Section3.T16.Assembly
import NSFormalization.Section3.T17.CorrectionDeriv
import NSFormalization.Section3.T17.ForceDeriv

/-!
# Probe: the two derivative-bound fields close on the concrete correction

The first two theorems restate the two `CorrectionAPI` fields with `D` replaced
by the concrete `correctionData`, and close them directly by `exact`.  The last
theorem instantiates both fields on T16's cutoffs at a nonzero constant,
divergence-free, periodic reference.
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

theorem field_correction_derivative_bound {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ} (O : Set Space) (θR ε₀ r : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ Metric.ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2) (hε₀ : ε₀ ≤ 1)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ j m : ℕ,
      ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
        ∀ z : SpaceTime,
          ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
            ‖iteratedFDeriv ℝ (j + m)
                ((correctionData v x₀ T θ η O θR ε₀).correction ε) z
                (Fin.append (fun _ : Fin j => ((1 : ℝ), (0 : Space)))
                  (fun i => ((0 : ℝ), u i)))‖ ≤
              correctionDerivConst hv x₀ T hθ hη hθc hηc j m *
                (ε⁻¹) ^ (2 * j + m) := by
  exact correction_derivative_bound hv x₀ T O θR ε₀ r hθ hη hθc hηc
    hθsupp hηsupp hr2 hε₀ hεspace

theorem field_force_derivative_bound (ν : ℝ) {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T δ r : ℝ)
    (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2) (hε₀ : ε₀ ≤ 1)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ m : ℕ,
      ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
        ∀ z : SpaceTime,
          ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
            ‖iteratedFDeriv ℝ m
                (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε) z
                (fun i => ((0 : ℝ), u i))‖ ≤
              forceDerivConst ν hv x₀ T hθ hη hθc hηc m *
                (ε⁻¹) ^ (2 + m) := by
  exact force_derivative_bound ν hv x₀ T δ r hvper O θR ε₀
    hθ hη hθc hηc hθsupp hηsupp hr2 hε₀ hεtime hεspace

/-! ## Non-vacuity on a nonzero constant reference and the T16 cutoffs -/

theorem nonvacuous_derivative_bounds :
    ∃ (v : SpaceTimeField) (θ : Space → ℝ) (η : ℝ → ℝ) (O : Set Space)
        (θR ε₀ : ℝ) (Cw : ℕ → ℕ → ℝ) (Cf : ℕ → ℝ),
      v ≠ 0 ∧ 0 < ε₀ ∧
      (∀ t : ℝ, ∀ x : Space, spatialDivergence v t x = 0) ∧
      (∀ j m, 0 ≤ Cw j m) ∧ (∀ m, 0 ≤ Cf m) ∧
      (∀ j m : ℕ,
        ∀ ε ∈ Ioc (0 : ℝ) (correctionData v 0 1 θ η O θR ε₀).ε₀,
          ∀ z : SpaceTime,
            ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
              ‖iteratedFDeriv ℝ (j + m)
                  ((correctionData v 0 1 θ η O θR ε₀).correction ε) z
                  (Fin.append (fun _ : Fin j => ((1 : ℝ), (0 : Space)))
                    (fun i => ((0 : ℝ), u i)))‖ ≤
                Cw j m * (ε⁻¹) ^ (2 * j + m)) ∧
      (∀ m : ℕ,
        ∀ ε ∈ Ioc (0 : ℝ) (correctionData v 0 1 θ η O θR ε₀).ε₀,
          ∀ z : SpaceTime,
            ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
              ‖iteratedFDeriv ℝ m
                  (correctionForce 1 v (correctionData v 0 1 θ η O θR ε₀) ε) z
                  (fun i => ((0 : ℝ), u i))‖ ≤
                Cf m * (ε⁻¹) ^ (2 + m)) := by
  obtain ⟨θR, θ, O, hθR, hθsm, hθcs, hθsupp, hOopen, hKO, hθone, hθrange⟩ :=
    exists_originCutoff (K := (∅ : Set Space)) isCompact_empty
  obtain ⟨η, hηsm, hηcs, hηrange, hηone, hηsupp⟩ := exists_timeCutoff
  obtain ⟨ε₀, hε₀pos, hεtime, hεspace⟩ :=
    exists_threshold hθR (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
  let ε₁ := min ε₀ 1
  have hε₁pos : 0 < ε₁ := lt_min hε₀pos one_pos
  have hε₁le : ε₁ ≤ 1 := min_le_right _ _
  have htime₁ : ∀ ε ∈ Ioc (0 : ℝ) ε₁, 2 * ε ^ 2 < min (1 : ℝ) 1 := by
    intro ε hε
    exact hεtime ε ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have hspace₁ : ∀ ε ∈ Ioc (0 : ℝ) ε₁, ε * θR < (1 / 4 : ℝ) := by
    intro ε hε
    exact hεspace ε ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
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
  refine ⟨v, θ, η, O, θR, ε₁,
    correctionDerivConst hv 0 1 hθsm hηsm hθcs hηcs,
    forceDerivConst 1 hv 0 1 hθsm hηsm hθcs hηcs,
    hvne, hε₁pos, hvdiv,
    correctionDerivConst_nonneg hv 0 1 hθsm hηsm hθcs hηcs,
    forceDerivConst_nonneg 1 hv 0 1 hθsm hηsm hθcs hηcs, ?_, ?_⟩
  · exact correction_derivative_bound hv 0 1 O θR ε₁ (1 / 4)
      hθsm hηsm hθcs hηcs hθsupp hηsupp (by norm_num) hε₁le hspace₁
  · exact force_derivative_bound 1 hv 0 1 1 (1 / 4) hvper
      O θR ε₁ hθsm hηsm hθcs hηcs hθsupp hηsupp
      (by norm_num) hε₁le htime₁ hspace₁

end NSFormalization.Section3.T17.Probe

#print axioms NSFormalization.Section3.T17.Probe.field_correction_derivative_bound
#print axioms NSFormalization.Section3.T17.Probe.field_force_derivative_bound
#print axioms NSFormalization.Section3.T17.Probe.nonvacuous_derivative_bounds
