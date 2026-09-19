import NSFormalization.Section3.T23.Boundary

/-! Pressure normalization for the canonical bounded-domain insertion. -/
noncomputable section
namespace NSFormalization.Section3.T23
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpaceTimeScalar)
open scoped ContDiff

/-- A nonempty bounded open domain has finite, strictly positive real volume. -/
theorem domain_volume_pos {Ω : Set Space} (ho : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) :
    0 < (volume Ω).toReal :=
  ENNReal.toReal_pos (ne_of_gt (ho.measure_pos volume hne)) hb.measure_lt_top.ne

/-- Slab smoothness supplies integrability of every pressure slice. -/
theorem SmoothOnClosedSlab.integrableOn_slice {Ω : Set Space}
    (hb : Bornology.IsBounded Ω) {I : Set ℝ} {p : SpaceTimeScalar}
    (hp : SmoothOnClosedSlab I Ω p) {t : ℝ} (ht : t ∈ I) :
    IntegrableOn (fun x => p (t, x)) Ω := by
  have hc : ContinuousOn (fun x => p (t, x)) (closure Ω) := fun x hx =>
    (hp.contDiffAt_slice ht hx).continuousAt.continuousWithinAt
  exact (hc.integrableOn_compact hb.isCompact_closure).mono_set subset_closure

/-- Subtracting the average really fixes the pressure gauge. -/
theorem domainNormalizePressure_integral {Ω : Set Space} (ho : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hne : Ω.Nonempty) {p : SpaceTimeScalar} {t : ℝ}
    (hp : IntegrableOn (fun x => p (t, x)) Ω) :
    (∫ x in Ω, domainNormalizePressure Ω p (t, x)) = 0 := by
  have : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by simpa using hb.measure_lt_top (μ := volume)⟩
  simp only [domainNormalizePressure]
  rw [integral_sub hp (integrable_const _), integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul, domainPressureMean]
  have hv := (domain_volume_pos ho hb hne).ne'
  field_simp
  ring

/-- No regularity hypothesis is needed for invariance under the spatially constant gauge. -/
theorem pressureGradient_domainNormalizePressure (Ω : Set Space)
    (p : SpaceTimeScalar) (t : ℝ) (x : Space) :
    pressureGradient (domainNormalizePressure Ω p) t x = pressureGradient p t x := by
  unfold pressureGradient domainNormalizePressure
  simp only [fderiv_sub_const]

/-- The physical momentum residual is unchanged by domain normalization. -/
theorem residual_domainNormalizePressure (ν : ℝ) (Ω : Set Space)
    (u : VelocityField) (p : SpaceTimeScalar) (t : ℝ) (x : Space) :
    NavierStokesR3.ProblemStatement.navierStokesResidual ν u
      (domainNormalizePressure Ω p) t x =
    NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x := by
  simp only [NavierStokesR3.ProblemStatement.navierStokesResidual,
    pressureGradient_domainNormalizePressure]
end NSFormalization.Section3.T23
