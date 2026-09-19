import NSFormalization.Section3.T18.ForceClass
import NSFormalization.Section3.T10.ForcePaths

/-! T18 U3: smoothness, initial value, quiet history, and periodicity.
Pressure normalization is additive on the integrable slices: the reference
mean is zero, leaving the normalized packet pressure supplied by scaling.
The correction support and the explicit packet zero extension give history. -/

noncomputable section
namespace NSFormalization.Section3.T18
open Set MeasureTheory
open scoped ContDiff
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T15

theorem reference_time (data : InsertionData) {t : ℝ} (ht : t ∈ Ico 0 data.place.T) :
    t ∈ Ico 0 (data.place.T + data.δ) := ⟨ht.1, by linarith [ht.2, data.hδ]⟩

theorem velocity_smooth (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    ContDiffOn ℝ ∞ (velocity data ε) (Ico (0 : ℝ) data.place.T ×ˢ (univ : Set Space)) := by
  intro ε hε
  obtain ⟨S, hv, _⟩ := data.scaling.solution ε (scaling_range data hε)
  exact ((data.reference.velocity_smooth.mono (fun z hz ↦
    ⟨reference_time data hz.1, hz.2⟩)).add
      (data.correction.potential.correction_smooth ε (correction_range data hε)).contDiffOn).add
        (hv ▸ S.velocity_smooth)

theorem pressure_smooth (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    ContDiffOn ℝ ∞ (pressure data ε) (Ico (0 : ℝ) data.place.T ×ˢ (univ : Set Space)) := by
  intro ε hε
  obtain ⟨S, _, hp⟩ := data.scaling.solution ε (scaling_range data hε)
  have hs := (data.reference.pressure_smooth.mono (fun z hz ↦
    ⟨reference_time data hz.1, hz.2⟩)).add (hp ▸ S.pressure_smooth)
  apply hs.congr
  intro z hz
  have hr : ContDiff ℝ ∞ (fun x : Space ↦ data.reference.pressure (z.1, x)) :=
    data.reference.pressure_smooth.comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun x ↦ ⟨reference_time data hz.1, mem_univ x⟩)
  have hi := (NSFormalization.Paper1.memLp_torusLift
    (Complex.continuous_ofReal.comp hr.continuous) 1).re.integrable (by norm_num)
  have hj := data.scaling.pressureSlice_integrable ε (scaling_range data hε) z.1 hz.1
  have hm : pressureMeanT (fun q ↦ data.reference.pressure q +
      periodizedScaledPressure data.packetPressure data.place.x₀ data.place.T ε q) z.1 =
      pressureMeanT data.reference.pressure z.1 +
      pressureMeanT (periodizedScaledPressure data.packetPressure data.place.x₀ data.place.T ε) z.1 := by
    exact integral_add hi hj
  simp only [pressure, normalizedScaledPressure, normalizePressureT, hm,
    data.reference.pressure_gauge z.1 (reference_time data hz.1), zero_add]
  ring

theorem correction_quiet (data : InsertionData) {ε : ℝ} (hε : ε ∈ Ioc 0 (ε₀ data))
    {t : ℝ} (ht : t ≤ data.place.T - 2 * ε ^ 2) (x : Space) :
    data.D.correction ε (t, x) = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  exact (not_lt_of_ge ht)
    (data.correction.potential.correction_support ε (correction_range data hε) h).1.1

theorem packet_quiet (data : InsertionData) {ε t : ℝ}
    (ht : t ≤ data.place.T - 2 * ε ^ 2) (x : Space) :
    periodizedScaledVelocity data.packetVelocity data.place.x₀ data.place.T ε (t, x) = 0 := by
  have hnonpos : (ε⁻¹) ^ 2 * (t - scaledStartTime data.place.T ε) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
    unfold scaledStartTime
    nlinarith [sq_nonneg ε]
  simp only [periodizedScaledVelocity, NSFormalization.Section3.T13.periodize,
    scaledVelocity, NSFormalization.Source.PacketScaling.zeroPastField, scaledSourcePoint]
  simp only [not_lt.mpr hnonpos, ite_false, smul_zero, tsum_zero]

theorem history (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    ∀ t : ℝ, 0 ≤ t → t ≤ data.place.T - 2 * ε ^ 2 → ∀ x : Space,
      velocity data ε (t, x) = data.reference.velocity (t, x) := by
  intro ε hε t _ ht x
  simp only [velocity, correction_quiet data hε ht x, packet_quiet data ht x, add_zero]

theorem initial (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    ∀ x : Space, velocity data ε (0, x) = data.a x := by
  intro ε hε x
  rw [history data ε hε 0 le_rfl (by
    have h := data.place.eps_time ε (scaling_range data hε)
    linarith), data.reference.initial]

theorem velocity_periodic (data : InsertionData) : ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
    IsPeriodicOn (Ico (0 : ℝ) data.place.T) (velocity data ε) := by
  intro ε hε
  obtain ⟨S, hv, _⟩ := data.scaling.solution ε (scaling_range data hε)
  intro t ht x i
  dsimp [velocity]
  rw [data.reference.velocity_periodic t (reference_time data ht) x i,
    data.correction.potential.correction_periodic ε (correction_range data hε) t (mem_univ _) x i,
    ← hv, S.velocity_periodic t ht x i]
end NSFormalization.Section3.T18
