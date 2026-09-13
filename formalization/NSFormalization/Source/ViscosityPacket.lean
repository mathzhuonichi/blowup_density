import NSFormalization.Source.ViscosityScaling
import NSFormalization.Source.SelectedPacketEnergy

/-!
# The actual compact packet at every positive viscosity

This transports the selected source witness, including its smooth compact
positive-time force, physical energy, full dissipation, and early vanishing.
The existing source `CandidateProperties` is used without replacing it by an
abstract existence interface.
-/

noncomputable section
namespace NSFormalization.Source
open NavierStokes.ProblemStatement Set MeasureTheory
open scoped ContDiff

def viscosityHomeomorph (a : ℝ) (ha : a ≠ 0) : SpaceTime ≃ₜ SpaceTime :=
  (Homeomorph.refl ℝ).prodCongr (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha))

theorem viscosity_force_compact {a : ℝ} (ha : a ≠ 0) {f : VelocityField}
    (hf : HasCompactSupport f) : HasCompactSupport (viscosityVelocity a f) := by
  have hc := (hf.comp_homeomorph (viscosityHomeomorph a ha)).smul_left (f := fun _ => a)
  convert hc using 1
  funext z
  simp [viscosityVelocity, dilateField, viscosityHomeomorph, Function.comp_def, Prod.map]

theorem viscosity_force_positive {a : ℝ} (ha : a ≠ 0) {f : VelocityField}
    (hf : tsupport f ⊆ NavierStokesR3.ProblemStatement.positiveTimeDomain) :
    tsupport (viscosityVelocity a f) ⊆ NavierStokesR3.ProblemStatement.positiveTimeDomain := by
  have he : viscosityVelocity a f =
      fun z => a • (f ∘ viscosityHomeomorph a ha) z := by
    funext z
    simp [viscosityVelocity, dilateField, viscosityHomeomorph, Function.comp_def, Prod.map]
  rw [he]
  intro z hz
  have hh := (tsupport_smul_subset_right (fun _ : SpaceTime => a)
    (f ∘ viscosityHomeomorph a ha)) hz
  have hh' := tsupport_comp_subset_preimage f (viscosityHomeomorph a ha).continuous hh
  exact ⟨(hf hh').1, mem_univ _⟩

theorem spatial_rescale_tsupport {V : Type*} [Zero V] [SMulZeroClass ℝ V]
    (b : ℝ) {a : ℝ} (ha : a ≠ 0) (f : SpaceTime → V) (t : ℝ)
    {K : Set Space} (hK : IsCompact K) (hf : tsupport (fun x => f (t, x)) ⊆ K) :
    tsupport (fun x => dilateField b 1 a⁻¹ 0 0 f (t, x)) ⊆
      (fun x : Space => a • x) '' K := by
  apply closure_minimal _ (hK.image (by fun_prop)).isClosed
  intro x hx
  have hn : f (t, a⁻¹ • x) ≠ 0 := by
    intro hz
    exact hx (by simp [dilateField, hz])
  exact ⟨a⁻¹ • x, hf (subset_tsupport _ hn), by simp [smul_smul, ha]⟩

theorem viscosity_spatial_energy {a : ℝ} (ha : 0 < a) (u : VelocityField) (t : ℝ) :
    (∫ x : Space, ‖viscosityVelocity a u (t, x)‖ ^ 2) =
      a ^ 5 * (∫ x : Space, ‖u (t, x)‖ ^ 2) := by
  simp only [viscosityVelocity, dilateField, sub_zero, one_mul]
  rw [spatial_energy_dilate (fun x : Space => u (t, x)) a a⁻¹ (inv_pos.mpr ha)]
  simp only [inv_pow, inv_inv]
  ring

theorem viscosity_square_integrable {a : ℝ} (ha : a ≠ 0) {u : VelocityField} {t : ℝ}
    (hu : Integrable (fun x : Space => ‖u (t, x)‖ ^ 2)) :
    Integrable (fun x : Space => ‖viscosityVelocity a u (t, x)‖ ^ 2) := by
  have hi := (hu.comp_smul (inv_ne_zero ha)).const_mul (a ^ 2)
  simpa [viscosityVelocity, dilateField, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs] using hi

theorem viscosity_uniform_energy {a : ℝ} (ha : 0 < a) {u : VelocityField} {I : Set ℝ}
    (hu : NavierStokesR3.ProblemStatement.UniformFiniteEnergy I u) :
    NavierStokesR3.ProblemStatement.UniformFiniteEnergy I (viscosityVelocity a u) := by
  obtain ⟨E, hE, he⟩ := hu
  refine ⟨a ^ 5 * E, mul_nonneg (pow_nonneg ha.le _) hE, ?_⟩
  intro t ht
  obtain ⟨hi, hbound⟩ := he t ht
  refine ⟨viscosity_square_integrable ha.ne' hi, ?_⟩
  unfold NavierStokesR3.ProblemStatement.kineticEnergy at hbound ⊢
  rw [viscosity_spatial_energy ha]
  nlinarith [mul_le_mul_of_nonneg_left hbound (pow_nonneg ha.le 5)]

theorem viscosity_dissipation {a : ℝ} (ha : 0 < a) (u : VelocityField) (t : ℝ) :
    NavierStokesR3.CompactEnergy.dissipation (viscosityVelocity a u) t =
      a ^ 3 * NavierStokesR3.CompactEnergy.dissipation u t := by
  have hder (x : Space) : fderiv ℝ (fun y : Space => a • u (t, a⁻¹ • y)) x =
      fderiv ℝ (fun y : Space => u (t, y)) (a⁻¹ • x) := by
    simpa only [sub_zero, mul_inv_cancel₀ ha.ne', one_smul] using
      fderiv_dilate (fun y : Space => u (t, y)) a a⁻¹ 0 x
  unfold NavierStokesR3.CompactEnergy.dissipation
  simp only [viscosityVelocity, dilateField, sub_zero, one_mul,
    NavierStokes.PeriodicIntegration.spatialPartial, hder]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi := Measure.integral_comp_smul_of_nonneg volume
    (fun x : Space => ‖fderiv ℝ (fun y => u (t, y)) x (coordinateVector i)‖ ^ 2)
    a⁻¹ (hR := (inv_pos.mpr ha).le)
  simpa only [finrank_euclideanSpace, Fintype.card_fin, inv_pow, inv_inv,
    smul_eq_mul] using hi

/-- Transport every field in the concrete source candidate record. -/
theorem viscosity_candidate_properties {a : ℝ} (ha : 0 < a)
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (h : NavierStokesR3.ProblemStatement.CandidateProperties 1 u p f K) :
    NavierStokesR3.ProblemStatement.CandidateProperties (a ^ 2)
      (viscosityVelocity a u) (viscosityPressure a p) (viscosityVelocity a f)
      ((fun x : Space => a • x) '' K) := by
  refine ⟨spatial_rescale_smooth a a h.velocity_smooth,
    spatial_rescale_smooth a (a ^ 2) h.pressure_smooth,
    h.support_compact.image (by fun_prop), ?_, ?_, ?_,
    ⟨viscosity_force_compact ha.ne' h.force_support.1,
      viscosity_force_positive ha.ne' h.force_support.2⟩,
    ?_, ?_, ?_, viscosity_uniform_energy ha h.energy_bounded,
    viscosity_speed_unbounded ha h.speed_unbounded⟩
  · intro t ht
    exact spatial_rescale_tsupport a ha.ne' u t h.support_compact (h.velocity_support t ht)
  · intro t ht
    exact spatial_rescale_tsupport (a ^ 2) ha.ne' p t h.support_compact (h.pressure_support t ht)
  · have hc : ContDiff ℝ ∞ (fun z : SpaceTime => (z.1, a⁻¹ • z.2)) := by fun_prop
    convert (contDiff_const (c := a)).smul (h.force_smooth.comp hc) using 1
    funext z
    simp [viscosityVelocity, dilateField]
  · intro x
    simp [viscosityVelocity, dilateField, h.zero_initial_velocity]
  · intro t ht x
    rw [viscosity_divergence ha.ne', h.divergence_free t ht]
  · intro t ht x
    exact viscosity_equation ha.ne' u p f t x (by simpa using h.navier_stokes t ht _)

/-- The packet used by both manuscripts exists at every fixed positive
viscosity, with finite full dissipation and an actual initial zero interval. -/
theorem selected_packet_every_viscosity {ν : ℝ} (hν : 0 < ν) :
    ∃ u : VelocityField, ∃ p : PressureField, ∃ f : VelocityField, ∃ K : Set Space,
      NavierStokesR3.ProblemStatement.CandidateProperties ν u p f K ∧
      IntegrableOn (NavierStokesR3.CompactEnergy.dissipation u) (Ioo (0 : ℝ) 1) ∧
      (∀ t : ℝ, |t| ≤ 3 / 8 → ∀ x, u (t, x) = 0 ∧ p (t, x) = 0) := by
  obtain ⟨u, p, f, K, h, hd, hquiet⟩ := SelectedPacketEnergy.selected_candidate_properties
  let a := Real.sqrt ν
  have ha : 0 < a := Real.sqrt_pos.mpr hν
  refine ⟨viscosityVelocity a u, viscosityPressure a p, viscosityVelocity a f,
    (fun x : Space => a • x) '' K, ?_, ?_, ?_⟩
  · have hc := viscosity_candidate_properties ha h
    simpa only [a, Real.sq_sqrt hν.le] using hc
  · have he : NavierStokesR3.CompactEnergy.dissipation (viscosityVelocity a u) =
        fun t => a ^ 3 * NavierStokesR3.CompactEnergy.dissipation u t := by
      funext t
      exact viscosity_dissipation ha u t
    rw [he]
    exact hd.const_mul _
  · intro t ht x
    have hq := hquiet t ht (a⁻¹ • x)
    simp [viscosityVelocity, viscosityPressure, dilateField, hq.1, hq.2]

theorem source_core_breakdown : NavierStokesR3.ProblemStatement.coreBreakdownStatement := by
  intro ν hν
  obtain ⟨u, p, f, K, h, _, _⟩ := selected_packet_every_viscosity hν
  exact ⟨u, p, f, K, h⟩

end NSFormalization.Source
