import Contracts.V1.LocalPotential
import Bindings.LocalPotential
import TestSupport.Axioms
noncomputable section
namespace BlowupDensity.Tests
open Set MeasureTheory
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Bindings
open scoped ContDiff Topology
 theorem checkedLocalPotential : Contracts.V1.localPotentialStatement := Bindings.localPotential
run_cmd TestSupport.checkAxioms ``checkedLocalPotential

/-- Independent conformance with `research/T16/Spec.lean:328-336`. -/
example :
    ∀ (v U : SpaceTimeField) (K : Set Space) (x₀ : Space) (r T δ : ℝ),
      0 < r → r < 1 / 2 → 0 < T → 0 < δ → IsCompact K →
      IsPeriodicOn univ v →
      ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ r) →
      (∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
        spatialDivergence v t x = 0) →
      (∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x => U (t, x)) ⊆ K) →
      ∃ D : CutoffData, LocalPotentialAPI v U K x₀ r T δ D :=
  checkedLocalPotential

/-- Independent conformance with the 26-field `LocalPotentialAPI` in
`research/T16/Spec.lean:145-319`. -/
example {v U : SpaceTimeField} {K : Set Space} {x₀ : Space} {r T δ : ℝ}
    (D : CutoffData) :
    LocalPotentialAPI v U K x₀ r T δ D ↔
      ContDiff ℝ ∞ D.θ ∧
      HasCompactSupport D.θ ∧
      (∀ x, D.θ x ∈ Icc (0 : ℝ) 1) ∧
      IsOpen D.plateau ∧
      K ⊆ D.plateau ∧
      EqOn D.θ (fun _ => 1) D.plateau ∧
      0 < D.θRadius ∧
      tsupport D.θ ⊆ Metric.ball (0 : Space) D.θRadius ∧
      ContDiff ℝ ∞ D.η ∧
      HasCompactSupport D.η ∧
      (∀ t, D.η t ∈ Icc (0 : ℝ) 1) ∧
      EqOn D.η (fun _ => 1) (Icc (-1 : ℝ) 1) ∧
      tsupport D.η ⊆ Ioo (-2 : ℝ) 2 ∧
      0 < D.ε₀ ∧
      (∀ ε ∈ Ioc (0 : ℝ) D.ε₀, 2 * ε ^ 2 < min T δ) ∧
      (∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ε * D.θRadius < r) ∧
      ContDiffOn ℝ ∞ D.potential
        (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ r) ∧
      (∀ t x, D.potential (t, x) =
        ∫ ρ in (0 : ℝ)..1,
          ρ • cross (v (t, x₀ + ρ • (x - x₀))) (x - x₀)) ∧
      (∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
        curl (fun y => D.potential (t, y)) x = v (t, x)) ∧
      (∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t,
        ∀ x ∈ Metric.ball x₀ r,
          D.correction ε (t, x) =
            -curl (fun y =>
              (scaledTemporalCutoff D.η T ε t *
                scaledSpatialCutoff D.θ x₀ ε y) • D.potential (t, y)) x) ∧
      (∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
        ContDiff ℝ ∞ (D.correction ε)) ∧
      (∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
        IsPeriodicOn univ (D.correction ε)) ∧
      (∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t x,
        spatialDivergence (D.correction ε) t x = 0) ∧
      (∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
        tsupport (D.correction ε) ⊆
          Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ (univ : Set Space)) ∧
      (∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t,
        tsupport (fun x => D.correction ε (t, x)) ⊆
          periodicSet (Metric.ball x₀ r)) ∧
      (∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
        ∀ t ∈ Ico (T - ε ^ 2) T,
          ∃ O : Set Space, IsOpen O ∧
            tsupport (fun x => periodicScaledPacket U x₀ T ε (t, x)) ⊆ O ∧
            ∀ x ∈ O, correctedBackground v D.correction ε (t, x) = 0) := by
  constructor
  · intro h
    exact ⟨h.theta_smooth, h.theta_compactSupport, h.theta_range,
      h.plateau_open, h.prescribed_subset_plateau, h.theta_one,
      h.theta_radius_pos, h.theta_support, h.eta_smooth,
      h.eta_compactSupport, h.eta_range, h.eta_one, h.eta_support,
      h.eps_pos, h.eps_time, h.eps_space, h.potential_smooth,
      h.potential_formula, h.potential_curl, h.correction_formula,
      h.correction_smooth, h.correction_periodic,
      h.correction_divergence_free, h.correction_support,
      h.correction_support_ball, h.correction_cancels⟩
  · rintro ⟨hθs, hθc, hθr, hpopen, hK, hθone, hθpos, hθsupp,
      hηs, hηc, hηr, hηone, hηsupp, hεpos, hεtime, hεspace, hpsmooth,
      hpformula, hpcurl, hcf, hcsmooth, hcperiodic, hcdiv, hcsupp,
      hcsuppball, hccancels⟩
    exact {
      theta_smooth := hθs
      theta_compactSupport := hθc
      theta_range := hθr
      plateau_open := hpopen
      prescribed_subset_plateau := hK
      theta_one := hθone
      theta_radius_pos := hθpos
      theta_support := hθsupp
      eta_smooth := hηs
      eta_compactSupport := hηc
      eta_range := hηr
      eta_one := hηone
      eta_support := hηsupp
      eps_pos := hεpos
      eps_time := hεtime
      eps_space := hεspace
      potential_smooth := hpsmooth
      potential_formula := hpformula
      potential_curl := hpcurl
      correction_formula := hcf
      correction_smooth := hcsmooth
      correction_periodic := hcperiodic
      correction_divergence_free := hcdiv
      correction_support := hcsupp
      correction_support_ball := hcsuppball
      correction_cancels := hccancels }

/-- The registered binding applies to a genuinely nonzero constant reference
`v = e₀`, with a nonempty chart cylinder and admissible scales. -/
example (x₀ : Space) :
    ∃ D : CutoffData,
      LocalPotentialAPI (fun _ => Contracts.V1.coordinateVector 0) (fun _ => 0)
        ({0} : Set Space) x₀ (1 / 4) 1 1 D := by
  apply Bindings.localPotential
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact isCompact_singleton
  · intro t _ x i; rfl
  · exact contDiffOn_const
  · intro t _ x _
    exact NSFormalization.Section3.T16.spatialDivergence_const_zero _ t x
  · intro t _
    rw [NSFormalization.Section3.T16.tsupport_zero_slice]
    exact empty_subset _

example : (Contracts.V1.coordinateVector 0 : Space) ≠ 0 := by
  intro h
  have hc := congrArg (fun z : Space => z 0) h
  simp [Contracts.V1.coordinateVector] at hc
end BlowupDensity.Tests
