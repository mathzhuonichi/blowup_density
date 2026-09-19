import NSFormalization.Section3.T15.SingleCopy

/-!
# T15 U10 — pressure integrability and mean-zero normalization

The raw rescaled pressure slice is smooth before the target time and has
support strictly inside the fundamental cube.  Its locally finite spatial
periodization is therefore a continuous real-valued field on Euclidean space,
whose canonical measurable torus representative is integrable.  Subtracting
its Haar mean then gives exactly the `PressureGaugeT` field required by
`ClassicalSolutionT`.
-/

noncomputable section

namespace NSFormalization.Section3.T15

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Source.PacketScaling
open NSFormalization.Section4.A02 (SpaceTimeScalar)
open scoped ContDiff Topology

/-! ## Smoothness of the single Euclidean pressure slice -/

/-- The raw packet clause saying that the past-zero pressure is smooth below
time one transports to every spatial slice of the rescaled pressure below the
target time. -/
theorem scaledPressure_slice_contDiff
    {p : PressureField} {x₀ : Space} {T ε t : ℝ}
    (hε : 0 < ε)
    (hp : ContDiffOn ℝ ∞ (zeroPastField p)
      (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (ht : t < T) :
    ContDiff ℝ ∞ (fun x : Space ↦ scaledPressure p x₀ T ε (t, x)) := by
  have hsmooth : ContDiffOn ℝ ∞ (scaledPressure p x₀ T ε)
      (Iio T ×ˢ (univ : Set Space)) := by
    rw [scaledPressure_eq_parabolicPressure]
    have h := dilate_smoothOn (f := zeroPastField p) ((ε⁻¹) ^ 2)
      (inv_pos.mpr hε) (T - ε ^ 2) x₀ hp
    have hwindow : (T - ε ^ 2) + ((ε⁻¹) ^ 2)⁻¹ = T := by
      rw [inv_pow, inv_inv]
      ring
    rwa [hwindow] at h
  rw [contDiff_iff_contDiffAt]
  intro x
  have hopen : IsOpen (Iio T ×ˢ (univ : Set Space)) := isOpen_Iio.prod isOpen_univ
  have hz : ContDiffAt ℝ ∞ (scaledPressure p x₀ T ε) (t, x) :=
    hsmooth.contDiffAt (hopen.mem_nhds ⟨ht, mem_univ x⟩)
  exact hz.comp x (contDiffAt_const.prodMk contDiffAt_id)

/-! ## Integrability of the raw periodized pressure -/

/-- A smooth scaled pressure slice supported strictly inside the fundamental
cube has an integrable locally finite periodization on the torus. -/
theorem periodizedScaledPressure_slice_integrable
    {p : PressureField} {x₀ : Space} {T ε t : ℝ}
    (hsupp : tsupport (fun x : Space ↦ scaledPressure p x₀ T ε (t, x)) ⊆
      interior fundamentalCube)
    (hsmooth : ContDiff ℝ ∞ (fun x : Space ↦
      scaledPressure p x₀ T ε (t, x))) :
    Integrable
      (torusLift (fun x ↦ periodizedScaledPressure p x₀ T ε (t, x)))
      periodicTorusMeasure := by
  have hperiodized : ContDiff ℝ ∞ (fun x : Space ↦
      periodizedScaledPressure p x₀ T ε (t, x)) := by
    have hjoint : ContDiff ℝ ∞
        (NavierStokes.PeriodicLocalization.periodize
          (fun z : SpaceTime ↦ scaledPressure p x₀ T ε (t, z.2))) :=
      NavierStokes.PeriodicLocalization.contDiff_periodize
        (supportedInCube_of_tsupport_subset_interior hsupp)
        (hsmooth.comp contDiff_snd)
    have hslice : ContDiff ℝ ∞ (fun x : Space ↦
        NavierStokes.PeriodicLocalization.periodize
          (fun z : SpaceTime ↦ scaledPressure p x₀ T ε (t, z.2)) ((0 : ℝ), x)) :=
      hjoint.comp (contDiff_const.prodMk contDiff_id)
    simpa only [periodizedScaledPressure,
      NavierStokes.PeriodicLocalization.periodize,
      NavierStokes.PeriodicLocalization.translate,
      latticeVector_eq_lattice] using hslice
  have hc : Continuous (fun x : Space ↦
      ((periodizedScaledPressure p x₀ T ε (t, x) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hperiodized.continuous
  have hi : Integrable
      (torusLift (fun x : Space ↦
        ((periodizedScaledPressure p x₀ T ε (t, x) : ℝ) : ℂ)))
      periodicTorusMeasure :=
    (NSFormalization.Paper1.memLp_torusLift hc 1).integrable le_rfl
  exact hi.re

/-- Every raw periodized pressure slice in the solution interval is honestly
Haar-integrable.  The conclusion is literally the `ScalingAPI` field; the
three premises are precisely the raw packet clauses used in its proof. -/
theorem pressureSlice_integrable
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hcarrier_compact : IsCompact K)
    (hpressure_support : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space ↦ p (t, x)) ⊆ K)
    (hpressure_smooth : ContDiffOn ℝ ∞ (zeroPastField p)
      (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      ∀ t ∈ Ico (0 : ℝ) place.T,
        Integrable
          (torusLift
            (fun x ↦ periodizedScaledPressure p place.x₀ place.T ε (t, x)))
          periodicTorusMeasure := by
  intro ε hε t ht
  have hsupp : tsupport (fun x : Space ↦
      scaledPressure p place.x₀ place.T ε (t, x)) ⊆
      interior fundamentalCube :=
    scaledPressure_slice_subset_cube hε hcarrier_compact hpressure_support
      place.carrier_subset place.eps_space place.chartBall_in_cube ht.2
  have hsmooth : ContDiff ℝ ∞ (fun x : Space ↦
      scaledPressure p place.x₀ place.T ε (t, x)) :=
    scaledPressure_slice_contDiff hε.1 hpressure_smooth ht.2
  exact periodizedScaledPressure_slice_integrable hsupp hsmooth

/-! ## The normalized representative has zero Haar mean -/

/-- Subtracting the Haar mean gives a mean-zero pressure on any time set on
which the raw slices are integrable. -/
theorem normalizePressureT_pressureGauge
    {I : Set ℝ} {q : SpaceTimeScalar}
    (hq : ∀ t ∈ I,
      Integrable (torusLift (fun x ↦ q (t, x))) periodicTorusMeasure) :
    PressureGaugeT I (normalizePressureT q) := by
  intro t ht
  have hi := hq t ht
  change (∫ y : PeriodicTorus,
      torusLift (fun x ↦ q (t, x)) y - pressureMeanT q t
        ∂periodicTorusMeasure) = 0
  rw [integral_sub hi (integrable_const _), integral_const]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  unfold pressureMeanT
  exact sub_self _

/-- At every admissible scale the explicitly normalized pressure satisfies
the exact mean-zero gauge required by `ClassicalSolutionT`. -/
theorem pressure_gauge
    {u f : VelocityField} {p : PressureField} {K : Set Space}
    (hcarrier_compact : IsCompact K)
    (hpressure_support : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space ↦ p (t, x)) ⊆ K)
    (hpressure_smooth : ContDiffOn ℝ ∞ (zeroPastField p)
      (Iio (1 : ℝ) ×ˢ (univ : Set Space)))
    (place : PlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
      PressureGaugeT (Ico (0 : ℝ) place.T)
        (normalizedScaledPressure p place.x₀ place.T ε) := by
  intro ε hε
  exact normalizePressureT_pressureGauge
    (pressureSlice_integrable hcarrier_compact hpressure_support
      hpressure_smooth place ε hε)

end NSFormalization.Section3.T15
