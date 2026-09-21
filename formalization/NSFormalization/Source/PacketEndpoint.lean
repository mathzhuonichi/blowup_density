import NSFormalization.Source.PacketEnergy
import NavierStokes.R3CompactCandidate
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Energy and dissipation up to the open singular endpoint

No velocity value or regular extension at time one is used. The force alone is
smooth on the closed unit slab. Bounded local dissipation integrals imply genuine
integrability on the full open presingular time interval.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace NSFormalization.Source.PacketEndpoint
open NavierStokes.ProblemStatement
open NavierStokes.PeriodicUniqueness (slab spatial_smooth)
open NavierStokesR3.CompactEnergy
open NSFormalization.Source.PacketEnergy

/-- Closed-slab force smoothness and compact spatial support give a uniform
bound for its actual spatial L2 norm, without negative-time assumptions. -/
theorem uniform_force_norm {f : VelocityField} {K : Set Space} (hK : IsCompact K)
    (hf : ContDiffOn ℝ ∞ f (slab 0 1))
    (hs : ∀ t ∈ Icc (0 : ℝ) 1, tsupport (fun x => f (t, x)) ⊆ K) :
    ∃ B : ℝ, 0 < B ∧ ∀ t ∈ Icc (0 : ℝ) 1, Real.sqrt (l2Sq f t) ≤ B := by
  have hc := (l2Sq_continuousOn hK hf hs).sqrt
  obtain ⟨B, hB, hb⟩ := (isCompact_Icc.image_of_continuousOn hc).isBounded.exists_pos_norm_le
  refine ⟨B, hB, ?_⟩
  intro t ht
  have h := hb _ ⟨t, ht, rfl⟩
  simpa [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using h

/-- A nonnegative rate with uniformly bounded integrals on compact initial
slabs is integrable on the entire open unit interval. This endpoint passage uses
an almost-everywhere interval cover; no endpoint value or extension is required. -/
theorem integrable_open_of_bounded_primitives {d : ℝ → ℝ} {C : ℝ}
    (hd : ∀ t, 0 ≤ d t)
    (hi : ∀ t ∈ Ioo (0 : ℝ) 1, IntegrableOn d (Icc 0 t))
    (hb : ∀ t ∈ Ioo (0 : ℝ) 1, (∫ s in (0 : ℝ)..t, d s) ≤ C) :
    IntegrableOn d (Ioo (0 : ℝ) 1) := by
  let b : ℕ → ℝ := fun n => 1 - (1 / 2 : ℝ) * (1 / ((n : ℝ) + 1))
  have hbn (n : ℕ) : b n ∈ Ioo (0 : ℝ) 1 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hp : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hl : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    dsimp [b]
    constructor <;> linarith
  have hbt : Tendsto b atTop (𝓝 1) := by
    have h : Tendsto b atTop (𝓝 ((1 : ℝ) - (1 / 2) * 0)) :=
      tendsto_const_nhds.sub
        (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    simpa [b] using h
  have hclosed : IntegrableOn d (Ioc (0 : ℝ) 1) := by
    apply integrableOn_Ioc_of_intervalIntegral_norm_bounded_right
      (l := atTop) (b := b) (I := C)
      (fun n => (hi (b n) (hbn n)).mono_set Ioc_subset_Icc_self) hbt
    apply Eventually.of_forall
    intro n
    simpa only [Real.norm_of_nonneg (hd _), ← intervalIntegral.integral_of_le (hbn n).1.le]
      using hb (b n) (hbn n)
  exact hclosed.mono_set Ioo_subset_Ioc_self

/-- Actual PDE energy and uniform compact support give one bound for all
strictly presingular times, plus genuine dissipation integrability on `(0,1)`.
The viscosity is arbitrary and strictly positive. -/
theorem presingular_energy_and_dissipation {ν : ℝ} (hν : 0 < ν)
    {u f : VelocityField} {p : PressureField} {K Kf : Set Space}
    (hK : IsCompact K) (hKf : IsCompact Kf)
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    (hp : ContDiffOn ℝ ∞ p preSingularDomain)
    (hf : ContDiffOn ℝ ∞ f (slab 0 1))
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x => u (t, x)) ⊆ K)
    (hfsupp : ∀ t ∈ Icc (0 : ℝ) 1, tsupport (fun x => f (t, x)) ⊆ Kf)
    (hzero : ∀ x, u (0, x) = 0)
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x, spatialDivergence u t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x,
      NSFormalization.Source.residual ν u p t x = f (t, x)) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ico (0 : ℝ) 1,
      Integrable (fun x : Space => ‖u (t, x)‖ ^ 2) ∧ l2Sq u t ≤ B) ∧
    IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1) := by
  obtain ⟨B, hB, hforce⟩ := uniform_force_norm hKf hf hfsupp
  have hlocal (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      IntegrableOn (dissipation u) (Icc 0 t) ∧
      l2Sq u t ≤ B ^ 2 ∧
      (∫ s in (0 : ℝ)..t, dissipation u s) ≤ B ^ 2 / (2 * ν) := by
    have hsub : slab 0 t ⊆ preSingularDomain := fun z hz =>
      ⟨⟨hz.1.1, hz.1.2.trans_lt ht.2⟩, hz.2⟩
    have hsubf : slab 0 t ⊆ slab 0 1 := fun z hz =>
      ⟨⟨hz.1.1, hz.1.2.trans ht.2.le⟩, hz.2⟩
    have hs : ∀ s ∈ Icc 0 t, tsupport (fun x => u (s, x)) ⊆ K :=
      fun s hs => hsupp s ⟨hs.1, hs.2.trans_lt ht.2⟩
    have hfs : ∀ s ∈ Icc 0 t, tsupport (fun x => f (s, x)) ⊆ Kf :=
      fun s hs => hfsupp s ⟨hs.1, hs.2.trans ht.2.le⟩
    have hd := packet_dissipation ht.1 hν hK hKf (hu.mono hsub) (hp.mono hsub)
      (hf.mono hsubf) hs hfs hzero
      (fun s hs => hdiv s ⟨hs.1, hs.2.trans ht.2⟩)
      (fun s hs => hNS s ⟨hs.1, hs.2.trans ht.2⟩)
    have he := packet_energy ht.1 hν.le hK hKf (hu.mono hsub) (hp.mono hsub)
      (hf.mono hsubf) hs hfs hzero
      (fun s hs => hdiv s ⟨hs.1, hs.2.trans ht.2⟩)
      (fun s hs => hNS s ⟨hs.1, hs.2.trans ht.2⟩) t ⟨ht.1.le, le_rfl⟩
    have hbc := (l2Sq_continuousOn hKf (hf.mono hsubf) hfs).sqrt
    have hbint : IntervalIntegrable (fun s => Real.sqrt (l2Sq f s)) volume 0 t := by
      apply IntegrableOn.intervalIntegrable
      rw [uIcc_of_le ht.1.le]
      exact hbc.integrableOn_compact isCompact_Icc
    have hprim : (∫ s in (0 : ℝ)..t, Real.sqrt (l2Sq f s)) ≤ B := by
      have hm := intervalIntegral.integral_mono_on ht.1.le hbint
        (intervalIntegrable_const (a := (0 : ℝ)) (b := t) (c := B))
        (fun s hs => hforce s ⟨hs.1, hs.2.trans ht.2.le⟩)
      have htb : t * B ≤ B := by nlinarith [ht.2]
      simpa using hm.trans (by simpa using htb)
    have hprim0 : 0 ≤ ∫ s in (0 : ℝ)..t, Real.sqrt (l2Sq f s) :=
      intervalIntegral.integral_nonneg_of_forall ht.1.le (fun s => Real.sqrt_nonneg _)
    have hprim2 : (∫ s in (0 : ℝ)..t, Real.sqrt (l2Sq f s)) ^ 2 ≤ B ^ 2 := by
      nlinarith
    have hd0 : 0 ≤ ∫ s in (0 : ℝ)..t, dissipation u s :=
      intervalIntegral.integral_nonneg_of_forall ht.1.le (dissipation_nonneg u)
    refine ⟨hd.1, ?_, (hd.2 t ⟨ht.1.le, le_rfl⟩).trans ?_⟩
    · have := mul_nonneg hν.le hd0
      nlinarith
    · exact div_le_div_of_nonneg_right hprim2 (by positivity)
  constructor
  · refine ⟨B ^ 2, sq_nonneg _, ?_⟩
    intro t ht
    have hsmooth : ContDiff ℝ ∞ (fun x : Space => u (t, x)) := by
      have hsub : slab 0 t ⊆ preSingularDomain := fun z hz =>
        ⟨⟨hz.1.1, hz.1.2.trans_lt ht.2⟩, hz.2⟩
      exact spatial_smooth (hu.mono hsub) ⟨ht.1, le_rfl⟩
    refine ⟨integrable_norm_sq hsmooth.continuous (slice_compact hK (hsupp t ht)), ?_⟩
    rcases eq_or_lt_of_le ht.1 with he | he
    · subst t
      simpa [l2Sq, hzero] using sq_nonneg B
    · exact (hlocal t ⟨he, ht.2⟩).2.1
  · exact integrable_open_of_bounded_primitives (dissipation_nonneg u)
      (fun t ht => (hlocal t ht).1) (fun t ht => (hlocal t ht).2.2)

/-- Convert the source library's pointwise outside-support condition into the
closed support inclusion used by parameter integration. -/
theorem tsupport_subset_of_zero_outside {v : Space → Space} {K : Set Space}
    (hK : IsClosed K) (hv : ∀ x, x ∉ K → v x = 0) : tsupport v ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  exact hx (hv x hn)

/-- The actual source candidate properties imply uniform finite physical L2
energy and finite dissipation on the full open interval, at source viscosity one.
The candidate's speed divergence at time one is compatible with these bounds. -/
theorem compact_properties_endpoint {u f : VelocityField} {p : PressureField}
    (h : NavierStokes.R3CompactCandidate.Properties u p f) :
    (∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ico (0 : ℝ) 1,
      Integrable (fun x : Space => ‖u (t, x)‖ ^ 2) ∧ l2Sq u t ≤ B) ∧
    IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1) := by
  obtain ⟨K, hK, hs⟩ := h.velocity_support
  obtain ⟨Kf, hKf, hfs⟩ := h.force_support
  apply presingular_energy_and_dissipation (ν := 1) zero_lt_one hK hKf
    h.velocity_smooth h.pressure_smooth
    (h.force_smooth.mono (fun z hz => ⟨hz.1.1, hz.2⟩))
    (fun t ht => tsupport_subset_of_zero_outside hK.isClosed (hs t ht))
    (fun t ht => tsupport_subset_of_zero_outside hKf.isClosed (hfs t ht.1))
    h.zero_initial_velocity (fun t ht => h.divergence_free t ⟨ht.1.le, ht.2⟩)
  intro t ht x
  rw [NSFormalization.Source.residual_one]
  exact h.navier_stokes t ht x

/-- Source-compatible physical kinetic-energy condition, together with full
open-interval dissipation integrability. -/
theorem compact_properties_uniform_finite_energy {u f : VelocityField} {p : PressureField}
    (h : NavierStokes.R3CompactCandidate.Properties u p f) :
    NavierStokesR3.ProblemStatement.UniformFiniteEnergy (Ico (0 : ℝ) 1) u ∧
      IntegrableOn (dissipation u) (Ioo (0 : ℝ) 1) := by
  obtain ⟨⟨B, hB, hb⟩, hd⟩ := compact_properties_endpoint h
  refine ⟨⟨B / 2, by positivity, ?_⟩, hd⟩
  intro t ht
  refine ⟨(hb t ht).1, ?_⟩
  have hbound := (hb t ht).2
  change (1 / 2 : ℝ) * l2Sq u t ≤ B / 2
  linarith

end NSFormalization.Source.PacketEndpoint
