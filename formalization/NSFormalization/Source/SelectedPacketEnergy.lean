import NSFormalization.Source.PacketEndpoint
import NSFormalization.Source.PacketPressure
import NSFormalization.Source.PacketForceExtension
import NavierStokes.R3ActualCandidate

/-!
# Energy and localization of the actual selected compact packet
-/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace NSFormalization.Source.SelectedPacketEnergy
open NavierStokes.ProblemStatement
open NavierStokesR3.CompactEnergy

/-- The library's actual selected compact candidate has uniform physical
kinetic energy and finite full presingular dissipation. -/
theorem selected_energy_packet :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField,
      NavierStokes.R3CompactCandidate.Properties u p f ∧
      NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) u ∧
      IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1) := by
  obtain ⟨u, p, f, h⟩ := NavierStokes.R3CompactCandidate.selected_compact_candidate
  exact ⟨u, p, f, h, PacketEndpoint.compact_properties_uniform_finite_energy h⟩

/-- The exact PDE turns a quiet velocity and pressure interval into a quiet
physical forcing interval. -/
theorem force_zero_early {u f : VelocityField} {p : PressureField}
    (h : NavierStokes.R3CompactCandidate.Properties u p f)
    (hquiet : ∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x, u (t, x) = 0 ∧ p (t, x) = 0) :
    ∀ t ∈ Ioo (0 : ℝ) (3 / 8), ∀ x, f (t, x) = 0 := by
  intro t ht x
  have hu : ∀ s ∈ Ioo (0 : ℝ) (3 / 8), ∀ y, u (s, y) = 0 := by
    intro s hs y
    exact (hquiet s (by rw [abs_of_pos hs.1]; exact hs.2.le) y).1
  have hp : (fun y : Space => p (t, y)) = fun _ => 0 := by
    funext y
    exact (hquiet t (by rw [abs_of_pos ht.1]; exact ht.2.le) y).2
  have heq := h.navier_stokes t ⟨ht.1, by linarith [ht.2]⟩ x
  rw [← NSFormalization.Source.residual_one,
    PacketPressure.residual_eq_pressure_on_quiet_interval ht hu x] at heq
  rw [← heq]
  simp [pressureGradient, hp]

/-- Retaining the original selected sums additionally proves actual initial
vanishing of both velocity and pressure. No new existence hypothesis is used. -/
theorem selected_early_energy_packet :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField,
      NavierStokes.R3CompactCandidate.Properties u p f ∧
      NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) u ∧
      IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1) ∧
      (∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x, u (t, x) = 0 ∧ p (t, x) = 0) ∧
      (∀ t ∈ Ioo (0 : ℝ) (3 / 8), ∀ x, f (t, x) = 0) := by
  obtain ⟨a, _, ea, eb, ep, forcing, hc, _⟩ :=
    NavierStokes.ActualCandidateAssembly.selected_witness
  have h := NavierStokes.R3CompactCandidate.of_localized_fields hc
  refine ⟨_, _, _, h, (PacketEndpoint.compact_properties_uniform_finite_energy h).1,
    (PacketEndpoint.compact_properties_uniform_finite_energy h).2, ?_, ?_⟩
  · intro t ht x
    exact ⟨NavierStokes.TimeLocalization.activatedVelocity_zero_early _ ht x,
      NavierStokes.TimeLocalization.activatedPressure_zero_early _ ht x⟩
  · apply force_zero_early h
    intro t ht x
    exact ⟨NavierStokes.TimeLocalization.activatedVelocity_zero_early _ ht x,
      NavierStokes.TimeLocalization.activatedPressure_zero_early _ ht x⟩

/-- An actual selected compact packet with globally smooth force whose compact
closed spacetime support lies at strictly positive times, uniform physical
energy, finite full presingular dissipation, and early zero velocity/pressure. -/
theorem selected_compact_smooth_energy_packet :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField,
      NavierStokes.R3CompactCandidate.Properties u p f ∧
      ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (∀ z ∈ tsupport f, 0 < z.1) ∧
      NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) u ∧
      IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1) ∧
      (∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x, u (t, x) = 0 ∧ p (t, x) = 0) := by
  obtain ⟨u, p, f, h, he, hd, hquiet, hfquiet⟩ := selected_early_energy_packet
  obtain ⟨K, hK, hs⟩ := h.force_support
  refine ⟨u, p, PacketForceExtension.zeroPast f,
    PacketForceExtension.zeroPast_properties h (by norm_num : (0 : ℝ) < 3 / 8) hfquiet,
    PacketForceExtension.zeroPast_smooth (by norm_num : (0 : ℝ) < 3 / 8) h.force_smooth hfquiet,
    PacketForceExtension.zeroPast_compact hK hs h.force_time_support,
    PacketForceExtension.zeroPast_support_positive (by norm_num : (0 : ℝ) < 3 / 8) hfquiet,
    he, hd, hquiet⟩

/-- The actual selected packet inhabits the existing whole-space candidate
record at viscosity one, with a single compact support for velocity and pressure.
The conclusion additionally retains finite total dissipation and early vanishing. -/
theorem selected_candidate_properties :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
      NavierStokesR3.ProblemStatement.CandidateProperties 1 u p f K ∧
      IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1) ∧
      (∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x, u (t, x) = 0 ∧ p (t, x) = 0) := by
  obtain ⟨u, p, f, h, hf, hcf, hpos, he, hd, hquiet⟩ :=
    selected_compact_smooth_energy_packet
  obtain ⟨Ku, hKu, hsu⟩ := h.velocity_support
  obtain ⟨Kp, hKp, hsp⟩ := h.pressure_support
  refine ⟨u, p, f, Ku ∪ Kp, ?_, hd, hquiet⟩
  refine ⟨h.velocity_smooth, h.pressure_smooth, hKu.union hKp,
    ?_, ?_, hf, ⟨hcf, fun z hz => ⟨hpos z hz, mem_univ _⟩⟩,
    h.zero_initial_velocity, h.divergence_free, ?_, he, h.speed_unbounded⟩
  · intro t ht
    exact (PacketEndpoint.tsupport_subset_of_zero_outside hKu.isClosed (hsu t ht)).trans
      subset_union_left
  · intro t ht
    have hs : tsupport (fun x : Space => p (t, x)) ⊆ Kp := by
      apply closure_minimal _ hKp.isClosed
      intro x hx
      by_contra hn
      exact hx (hsp t ht x hn)
    exact hs.trans subset_union_right
  · intro t ht x
    simpa using h.navier_stokes t ht x

/-- The primary source-defined existence statement at viscosity one. -/
theorem unit_candidateStatement : NavierStokesR3.ProblemStatement.candidateStatement 1 := by
  obtain ⟨u, p, f, K, h, _, _⟩ := selected_candidate_properties
  exact ⟨u, p, f, K, h⟩

end NSFormalization.Source.SelectedPacketEnergy
