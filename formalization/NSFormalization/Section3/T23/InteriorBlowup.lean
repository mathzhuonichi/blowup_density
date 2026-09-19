import NSFormalization.Section3.T23.Boundary

/-! T23 U8: interior packet witnesses and local essential-supremum blow-up. -/

noncomputable section
namespace NSFormalization.Section3.T23
open Set MeasureTheory Filter
open NavierStokes.ProblemStatement
open NSFormalization.Source.PacketScaling
open NSFormalization.Section3.T15 (scaledVelocity scaledVelocity_eq_parabolicVelocity)
open scoped Topology

/-- The I03 rescaling argument, before spatial periodization. -/
theorem scaledPacket_speedUnbounded {U : VelocityField} (hspeed : SpeedUnboundedAtOne U)
    {T ε : ℝ} (hε : 0 < ε) (htime : ε ^ 2 ≤ T) (x₀ : Space) :
    SpeedUnboundedAt T (scaledVelocity U x₀ T ε) := by
  have hinv : (((ε⁻¹ : ℝ) ^ 2)⁻¹) = ε ^ 2 := by rw [inv_pow, inv_inv]
  rw [scaledVelocity_eq_parabolicVelocity, ← hinv]
  exact speed_unbounded_at_target (inv_pos.mpr hε) (by simpa [hinv] using htime)
    x₀ (zeroPastField_speed hspeed)

/-- Positive-level witnesses lie on the packet support, where U2 cancels the
background. U4 supplies the support in the prescribed ball; U3 supplies the
literal velocity formula. These inputs carry no blow-up conclusion. -/
theorem interior_blowup
    {U f v u : VelocityField} {p : PressureField} {K Ω : Set Space}
    (place : DomainPlacementData U p f K) (D : CutoffData)
    (hspeed : SpeedUnboundedAtOne U) {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) place.ε₀)
    (hball : closure (Metric.ball place.chartCenter place.chartRadius) ⊆ Ω)
    (hformula : ∀ z, u z = v z + D.correction ε z +
      scaledVelocity U place.x₀ place.T ε z)
    (hsupport : ∀ t ∈ Ioo (0 : ℝ) place.T,
      tsupport (fun x => scaledVelocity U place.x₀ place.T ε (t, x)) ⊆
        Metric.ball place.chartCenter place.chartRadius)
    (hcancel : ∀ t ∈ Ico (place.T - ε ^ 2) place.T,
      ∀ x ∈ tsupport (fun y => scaledVelocity U place.x₀ place.T ε (t, y)),
        v (t, x) + D.correction ε (t, x) = 0) :
    ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
      ∃ t : ℝ, ∃ x : Space, t ∈ Ioo 0 place.T ∧ place.T - δ < t ∧
        x ∈ Metric.ball place.chartCenter place.chartRadius ∧ x ∈ Ω ∧ M < ‖u (t, x)‖ := by
  have hb := scaledPacket_speedUnbounded hspeed hε.1
    (show ε ^ 2 ≤ place.T by linarith [place.eps_time ε hε, sq_nonneg ε]) place.x₀
  intro M hM δ hδ
  obtain ⟨t, x, ht, hnear, hlarge⟩ := hb M hM δ hδ
  have hne : scaledVelocity U place.x₀ place.T ε (t, x) ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hlarge
    linarith
  have hstart : place.T - ε ^ 2 < t := by
    by_contra hn
    exact hne (congrFun (packet_slice_zero U place.x₀ place.T ε t (not_lt.mp hn)) x)
  have hx := subset_tsupport (fun y => scaledVelocity U place.x₀ place.T ε (t, y)) hne
  have hxball := hsupport t ht hx
  refine ⟨t, x, ht, hnear, hxball, hball (subset_closure hxball), ?_⟩
  rw [hformula, hcancel t ⟨hstart.le, ht.2⟩ x hx, zero_add]
  exact hlarge

/-- Continuity at one witness suffices; no regularity outside the domain is
used. The strict superlevel set is a neighborhood and has positive volume. -/
theorem ofReal_le_eLpNormTop_of_continuousAt {z : Space → Space} {x : Space}
    (hz : ContinuousAt z x) {M : ℝ} (hx : M < ‖z x‖) :
    ENNReal.ofReal M ≤ eLpNorm z ⊤ (volume : Measure Space) := by
  rw [eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm]
  by_contra hcon
  have hae : ∀ᵐ y ∂(volume : Measure Space), ‖z y‖ₑ < ENNReal.ofReal M :=
    ae_lt_of_essSup_lt (not_le.mp hcon)
  have hpos : 0 < volume {y : Space | M < ‖z y‖} :=
    Measure.measure_pos_of_mem_nhds volume (hz.norm.eventually (Ioi_mem_nhds hx))
  have hsub : {y : Space | M < ‖z y‖} ⊆ {y : Space | ¬ ‖z y‖ₑ < ENNReal.ofReal M} := by
    intro y hy
    change ¬ ‖z y‖ₑ < ENNReal.ofReal M
    rw [not_lt]
    exact (ENNReal.ofReal_le_ofReal hy.le).trans_eq (ofReal_norm _)
  exact (not_le.mpr hpos) ((measure_mono hsub).trans (ae_iff.mp hae).le)

/-- Interior witnesses and closed-slab regularity force the whole-space
essential-supremum limsup, regardless of exterior values of the total field. -/
theorem limsupLeft_speedENorm_eq_top_of_interior {T : ℝ} {Ω : Set Space}
    {u : VelocityField}
    (hsmooth : SmoothOnClosedSlab (Ico (0 : ℝ) T) Ω u)
    (hblow : ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
      ∃ t : ℝ, ∃ x : Space, t ∈ Ioo 0 T ∧ T - δ < t ∧ x ∈ Ω ∧ M < ‖u (t, x)‖) :
    NSFormalization.Section4.A02.limsupLeft T
      (fun t => NSFormalization.Section4.A02.speedENorm (fun x => u (t, x))) = ⊤ := by
  by_contra hne
  obtain ⟨b, hb1, hb2⟩ := exists_between (lt_top_iff_ne_top.mpr hne)
  have hfreq : ∃ᶠ t in nhdsWithin T (Iio T),
      b ≤ NSFormalization.Section4.A02.speedENorm (fun x => u (t, x)) := by
    refine (nhdsLT_basis T).frequently_iff.mpr ?_
    intro c hc
    have hb0 : (0 : ℝ) ≤ b.toReal := ENNReal.toReal_nonneg
    obtain ⟨t, x, ht, htc, hx, hMx⟩ :=
      hblow (b.toReal + 1) (by linarith) (T - c) (by linarith)
    refine ⟨t, ⟨by linarith, ht.2⟩, ?_⟩
    have hM := ofReal_le_eLpNormTop_of_continuousAt
      (hsmooth.contDiffAt_slice ⟨ht.1.le, ht.2⟩ (subset_closure hx)).continuousAt hMx
    calc
      b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hb2.ne).symm
      _ ≤ ENNReal.ofReal (b.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ NSFormalization.Section4.A02.speedENorm (fun x => u (t, x)) := hM
  exact (not_le.mpr hb1) (le_limsup_of_frequently_le' hfreq)

namespace U8

variable {U f : VelocityField} {p : PressureField} {K Ω : Set Space}
  (place : DomainPlacementData U p f K) (D : CutoffData)
  {ν δ : ℝ} {a : NSFormalization.Section4.A02.SpatialField} {g : VelocityField}
  (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ))
  {ε₀ : ℝ} {velocity force : ℝ → VelocityField} {pressure : ℝ → PressureField}
  (hspeed : SpeedUnboundedAtOne U) (hscale : ε₀ ≤ place.ε₀)
  (hball : closure (Metric.ball place.chartCenter place.chartRadius) ⊆ Ω)
  (hformula : ∀ ε z, velocity ε z = reference.velocity z + D.correction ε z +
    NSFormalization.Section3.T15.scaledVelocity U place.x₀ place.T ε z)
  (hsupport : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ioo (0 : ℝ) place.T,
    tsupport (fun x => NSFormalization.Section3.T15.scaledVelocity U place.x₀ place.T ε (t, x)) ⊆
      Metric.ball place.chartCenter place.chartRadius)
  (hcancel : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ico (place.T - ε ^ 2) place.T,
    ∀ x ∈ tsupport (fun y => NSFormalization.Section3.T15.scaledVelocity U place.x₀ place.T ε (t, y)),
      reference.velocity (t, x) + D.correction ε (t, x) = 0)
  (hsolution : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∃ w : ClassicalSolutionOmega ν Ω a (force ε) place.T,
      w.velocity = velocity ε ∧ w.pressure = pressure ε)

include hspeed hscale hball hformula hsupport hcancel

/-- The strengthened witness at the exact family threshold. -/
theorem interior : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ M : ℝ, 0 < M → ∀ d : ℝ, 0 < d →
      ∃ t : ℝ, ∃ x : Space, t ∈ Ioo 0 place.T ∧ place.T - d < t ∧
        x ∈ Metric.ball place.chartCenter place.chartRadius ∧ x ∈ Ω ∧
        M < ‖velocity ε (t, x)‖ := by
  intro ε hε
  exact interior_blowup place D hspeed ⟨hε.1, hε.2.trans hscale⟩ hball
    (hformula ε) (hsupport ε hε) (hcancel ε hε)

/-- The exact whole-space pointwise API field, from interior witnesses. -/
theorem blowup : ∀ ε ∈ Ioc (0 : ℝ) ε₀, SpeedUnboundedAt place.T (velocity ε) := by
  intro ε hε M hM d hd
  obtain ⟨t, x, ht, hn, _, _, hl⟩ :=
    interior place D reference hspeed hscale hball hformula hsupport hcancel ε hε M hM d hd
  exact ⟨t, x, ht, hn, hl⟩

include hsolution

/-- The exact essential-supremum API field, using only domain solution smoothness. -/
theorem blowup_limsup : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    NSFormalization.Section4.A02.limsupLeft place.T
      (fun t => NSFormalization.Section4.A02.speedENorm (fun x => velocity ε (t, x))) = ⊤ := by
  intro ε hε
  obtain ⟨w, hw, _⟩ := hsolution ε hε
  apply limsupLeft_speedENorm_eq_top_of_interior (hw ▸ w.velocity_smooth)
  intro M hM d hd
  obtain ⟨t, x, ht, hn, _, hx, hl⟩ :=
    interior place D reference hspeed hscale hball hformula hsupport hcancel ε hε M hM d hd
  exact ⟨t, x, ht, hn, hx, hl⟩

end U8
end NSFormalization.Section3.T23
