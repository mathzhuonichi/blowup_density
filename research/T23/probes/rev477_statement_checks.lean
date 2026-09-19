import NSFormalization.Section3.T23.StatementRepair
import NSFormalization.Section3.T23.LocalCorrectionBridge

noncomputable section
open Set Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T23
open scoped ContDiff Topology

/- A concrete zero-field instance checks that the local constructor's scale
interval is nonempty; in particular its result is not obtained from an empty
`Ioc (0 : ℝ) D.ε₀`. -/
example : ∃ D : CutoffData,
    LocalCorrectionCore (0 : VelocityField) (0 : VelocityField) ∅ 0 1 1 1 D ∧
      0 < D.ε₀ ∧ D.ε₀ ∈ Ioc (0 : ℝ) D.ε₀ := by
  obtain ⟨D, hD⟩ := exists_localCorrectionCore
    (0 : VelocityField) (0 : VelocityField) ∅ 0 1 1 1
    (by norm_num) (by norm_num) (by norm_num) isCompact_empty
    (contDiff_const.contDiffOn)
    (by
      intro t ht x hx
      have hd : spatialDerivative (0 : VelocityField) t x = 0 := by
        simp only [spatialDerivative]
        simp
      simp [spatialDivergence, hd])
    (by intro t ht; simp)
  exact ⟨D, hD, hD.eps_pos, hD.eps_pos, le_rfl⟩

/- Negative mutation: widening the required cross-transport interval from
`Ico 0 T` to `Icc 0 T` adds the singular endpoint. Reusing the proved field
must fail because `T ∈ Icc 0 T` is not enough to obtain `T < T`. -/
/--
error: Type mismatch
  h.crossTransport_background_advects_packet
has type
  ∀ ε ∈ Ioc 0 D.ε₀,
    ∀ t ∈ Ico 0 T,
      ∀ (x : Space),
        (spatialDerivative (NSFormalization.Section3.T15.scaledVelocity U x₀ T ε) t x)
            (NSFormalization.Section3.T16.correctedBackground v D.correction ε (t, x)) =
          0
but is expected to have type
  ∀ ε ∈ Ioc 0 D.ε₀,
    ∀ t ∈ Icc 0 T,
      ∀ (x : Space),
        (spatialDerivative (NSFormalization.Section3.T15.scaledVelocity U x₀ T ε) t x)
            (NSFormalization.Section3.T16.correctedBackground v D.correction ε (t, x)) =
          0
-/
#guard_msgs in
example (v U : VelocityField) (K : Set Space) (x₀ : Space)
    (r T δ : ℝ) (D : CutoffData) (h : LocalCorrectionCore v U K x₀ r T δ D) :
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
      spatialDerivative (NSFormalization.Section3.T15.scaledVelocity U x₀ T ε) t x
        (NSFormalization.Section3.T16.correctedBackground v D.correction ε (t, x)) = 0 :=
  h.crossTransport_background_advects_packet

-- The repaired G0 declaration required in the canonical module is absent.
/--
error: Unknown identifier `NSFormalization.Section3.T23.boundaryInsertionStatement'`
-/
#guard_msgs in
#check NSFormalization.Section3.T23.boundaryInsertionStatement'
