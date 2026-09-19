import NSFormalization.Section3.T23.Boundary

/-! Local transport for the registered whole-space correction supplier. -/
noncomputable section
namespace NSFormalization.Section3.T23

open Set Filter Metric MeasureTheory
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Paper1.CorrectionProfile
open NSFormalization.Paper1.RadialPotential (timePotential)
open NSFormalization.Source.PhysicalRemoval (temporal_cutoff_support)
open scoped ContDiff Topology

/-- The formula fields identify the supplied correction, without choosing it again. -/
theorem WholeSpaceCorrectionAPI.correction_eq_physical {ν : ℝ} {u : VelocityField}
    {K : Set Space} (C : WholeSpaceCorrectionAPI ν u K) (ε : ℝ) :
    C.correction ε = physicalCorrection C.v C.x₀ C.T C.θ C.η ε := by
  have hp : C.potential = timePotential C.v C.x₀ := by
    funext z
    exact C.potential_formula z.1 z.2
  funext z
  rw [C.correction_formula ε z, hp]
  rfl

/-- Full spatial-slab agreement suffices to match the local correction and force
at every scale supplied by I02. The local potential need not agree globally. -/
theorem WholeSpaceCorrectionAPI.local_match {ν : ℝ} {u v : VelocityField}
    {K : Set Space} (C : WholeSpaceCorrectionAPI ν u K)
    (heq : EqOn v C.v (Ioo (0 : ℝ) (C.T + C.δ) ×ˢ ball C.x₀ C.r))
    {e ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) C.ε₀) :
    let D := localCorrectionData v C.x₀ C.T C.θ C.η C.plateau C.θRadius e
    D.correction ε = C.correction ε ∧
      correctionForce ν v D ε = C.forceCorrection ε := by
  dsimp only
  let D := localCorrectionData v C.x₀ C.T C.θ C.η C.plateau C.θRadius e
  have ht : tsupport (temporalCutoff C.η C.T ε) ⊆ Ioo (0 : ℝ) (C.T + C.δ) := by
    intro t ht
    obtain ⟨s, hs, he⟩ := temporal_cutoff_support hε.1.ne' C.T C.eta_compactSupport ht
    have hi := C.eta_support hs
    have htime := C.eps_time ε hε
    have hT := min_le_left C.T C.δ
    have hδ := min_le_right C.T C.δ
    change C.T + ε ^ 2 * s = t at he
    constructor <;> nlinarith [mul_lt_mul_of_pos_left hi.1 (sq_pos_of_pos hε.1),
      mul_lt_mul_of_pos_left hi.2 (sq_pos_of_pos hε.1)]
  have hs : tsupport (spatialCutoff C.θ C.x₀ ε) ⊆ ball C.x₀ C.r :=
    NSFormalization.Section3.T16.spatialCutoff_tsupport_ball hε.1
      C.theta_compactSupport C.theta_support (C.eps_space ε hε)
  have hw : D.correction ε = C.correction ε :=
    (physicalCorrection_eq_of_cylinder v C.v C.x₀ C.T ε C.r C.θ C.η heq ht hs).trans
      (C.correction_eq_physical ε).symm
  refine ⟨hw, ?_⟩
  have hsupport : tsupport (D.correction ε) ⊆
      Ioo (0 : ℝ) (C.T + C.δ) ×ˢ ball C.x₀ C.r := by
    rw [hw]
    intro z hz
    have h := C.correction_support ε hε hz
    have hb := ball_subset_ball (C.eps_space ε hε).le h.2
    have hh := C.eps_time ε hε
    have hT := min_le_left C.T C.δ
    have hδ := min_le_right C.T C.δ
    exact ⟨⟨by linarith [h.1.1], by linarith [h.1.2]⟩, hb⟩
  change correctionForce ν v D ε = C.forceCorrection ε
  rw [correctionForce_eq_of_open_agreement ν v C.v D ε
    (isOpen_Ioo.prod isOpen_ball) hsupport heq, correctionForce_eq_source, hw]
  funext z
  exact (C.force_formula ε z.1 z.2).symm

/-- The two exact U2 cross-transport fields for the local family chosen with
the supplier cutoffs, including t = 0. -/
theorem WholeSpaceCorrectionAPI.local_crossTransport {ν : ℝ} {u v : VelocityField}
    {K : Set Space} (C : WholeSpaceCorrectionAPI ν u K) (hK : IsCompact K)
    (hv : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (C.T + C.δ) ×ˢ ball C.x₀ C.r))
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) (C.T + C.δ), ∀ x ∈ ball C.x₀ C.r,
      spatialDivergence v t x = 0)
    (hu : ∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x => u (t, x)) ⊆ K)
    {e : ℝ} (he : e ≤ C.ε₀) :
    let D := localCorrectionData v C.x₀ C.T C.θ C.η C.plateau C.θRadius e
    ∀ ε ∈ Ioc (0 : ℝ) e, ∀ t ∈ Ico (0 : ℝ) C.T, ∀ x : Space,
      spatialDerivative (NSFormalization.Section3.T15.scaledVelocity u C.x₀ C.T ε) t x
        (NSFormalization.Section3.T16.correctedBackground v D.correction ε (t, x)) = 0 ∧
      spatialDerivative (NSFormalization.Section3.T16.correctedBackground v D.correction ε) t x
        (NSFormalization.Section3.T15.scaledVelocity u C.x₀ C.T ε (t, x)) = 0 := by
  intro D ε hε t ht x
  have hεC : ε ∈ Ioc (0 : ℝ) C.ε₀ := ⟨hε.1, hε.2.trans he⟩
  exact crossTransport_pair hK hv hdiv hu C.plateau_open C.carrier_subset_plateau
    C.theta_support C.theta_one C.eta_one (C.eps_time ε hεC) (C.eps_space ε hεC)
    hε.1 ht x

/-- The seven-field cutoff required by the repaired boundary statement.
Its potential is the supplier potential, not an unjustified global replacement
by the radial potential of the local reference. -/
def WholeSpaceCorrectionAPI.supplierCutoff {ν : ℝ} {u : VelocityField}
    {K : Set Space} (C : WholeSpaceCorrectionAPI ν u K) : CutoffData :=
  ⟨C.θ, C.η, C.plateau, C.θRadius, C.ε₀, C.potential, C.correction⟩

/-- The literal supplier cutoff has the local force, even when the reference
has uncontrolled exterior values. -/
theorem WholeSpaceCorrectionAPI.supplierCutoff_force {ν : ℝ} {u v : VelocityField}
    {K : Set Space} (C : WholeSpaceCorrectionAPI ν u K)
    (heq : EqOn v C.v (Ioo (0 : ℝ) (C.T + C.δ) ×ˢ ball C.x₀ C.r))
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) C.ε₀) :
    correctionForce ν v C.supplierCutoff ε = C.forceCorrection ε := by
  obtain ⟨hw, hf⟩ := C.local_match (e := C.ε₀) heq hε
  rw [correctionForce_eq_source] at hf ⊢
  change NSFormalization.Source.correctionForce ν v (C.correction ε) = _
  rw [← hw]
  exact hf

/-- The actual domain solution supplies precisely the local hypotheses used
by the construction; no whole-space regularity is inferred. -/
theorem ClassicalSolutionOmega.local_velocity {ν T δ r : ℝ} {Ω : Set Space}
    {a : NSFormalization.Section4.A02.SpatialField} {g : VelocityField}
    (reference : ClassicalSolutionOmega ν Ω a g (T + δ)) (x₀ : Space)
    (hball : ball x₀ r ⊆ Ω) :
    ContDiffOn ℝ ∞ reference.velocity (Ioo (0 : ℝ) (T + δ) ×ˢ ball x₀ r) ∧
      ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ ball x₀ r,
        spatialDivergence reference.velocity t x = 0 := by
  obtain ⟨N, _, hN, hv⟩ := reference.velocity_smooth
  refine ⟨hv.mono (fun z hz => hN ⟨⟨hz.1.1.le, hz.1.2⟩,
    subset_closure (hball hz.2)⟩), ?_⟩
  intro t ht x hx
  exact reference.divergence t ⟨ht.1.le, ht.2⟩ x (hball hx)

end NSFormalization.Section3.T23
