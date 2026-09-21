import NSFormalization.Section3.T18.Assembly
import NSFormalization.Section3.T15.SingleCopy

/-!
# Remark 3.13: force amplitudes

`paper/revised/sections/03-torus.tex:403-410`:
"Since the original force is nonzero,
‖g_ε-g‖_{L∞_{t,x}} ≥ ε⁻³‖F‖∞ - Cε⁻² → ∞."
"The force F is nonzero by (packetenergy), since U blows up."

For extended nonnegative amplitudes divergence means convergence to `𝓝 ⊤`.
-/
noncomputable section
namespace NSFormalization.Section3.T18
open Set MeasureTheory Filter Topology
open NavierStokes.ProblemStatement
open NavierStokesR3.CompactEnergy
open NSFormalization.Source.PacketEnergy
open NSFormalization.Section3.T14 NSFormalization.Section3.T15
open scoped ContDiff ENNReal

/-- Zero forcing gives zero kinetic energy, contradicting the packet blowup. -/
theorem packetForce_ne_zero {ν : ℝ} {u f : VelocityField} {p : PressureField}
    {K : Set Space} (hν : 0 < ν) (hK : IsCompact K)
    (hu : ContDiffOn ℝ ∞ u preSingularDomain)
    (hp : ContDiffOn ℝ ∞ p preSingularDomain)
    (hf : ContDiff ℝ ∞ f)
    (hfc : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (hsupp : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => u (t,x)) ⊆ K)
    (hzero : ∀ x : Space, u (0,x) = 0)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space, spatialDivergence u t x = 0)
    (hNS : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = f (t,x))
    (hblow : SpeedUnboundedAtOne u) : f ≠ 0 := by
  intro heq
  obtain ⟨t, x, ht, _, hx⟩ := hblow 1 zero_lt_one 1 zero_lt_one
  have he := energy_le_work_of_packet hν hK hu hp hf hfc hsupp hzero hdiv hNS
    t ⟨ht.1.le, ht.2⟩
  simp [heq, l2Sq, accumulatedForce] at he
  have hd : 0 ≤ ∫ s in Ioo (0 : ℝ) t, dissipation u s :=
    integral_nonneg (fun s => dissipation_nonneg u s)
  have hn : 0 ≤ l2Sq u t := integral_nonneg (fun x => sq_nonneg _)
  have he0 : l2Sq u t = 0 := by
    change l2Sq u t + 2 * ν * (∫ s in Ioo (0 : ℝ) t, dissipation u s) ≤ 0 at he
    nlinarith
  have hc : Continuous (fun x : Space => u (t,x)) :=
    hu.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨⟨ht.1.le, ht.2⟩, mem_univ _⟩)
  have hz := field_eq_zero_of_l2Sq_eq_zero hc (slice_compact hK (hsupp t ⟨ht.1.le, ht.2⟩)) he0 x
  norm_num [hz] at hx

/-- A nonzero force has strictly positive extended supremum norm. -/
theorem packetForce_sup_pos {f : VelocityField} (hf : f ≠ 0) :
    0 < ⨆ z, ‖f z‖ₑ := by
  obtain ⟨z, hz⟩ := Function.ne_iff.mp hf
  exact lt_of_lt_of_le (by simpa using hz) (le_iSup (fun z => ‖f z‖ₑ) z)

/-- Smooth compactly supported forcing has finite amplitude. -/
theorem packetForce_sup_lt_top {f : VelocityField} (hf : Continuous f)
    (hc : HasCompactSupport f) : (⨆ z, ‖f z‖ₑ) < ⊤ := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hf
  apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ ENNReal.ofReal_lt_top
  exact iSup_le (fun z => by simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal (hC z))

end NSFormalization.Section3.T18
