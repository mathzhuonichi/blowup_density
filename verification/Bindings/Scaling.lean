import Contracts.V1.Scaling
import Bindings.Correction
import NSFormalization.Source.PacketScaling
import NSFormalization.Section4.I02.Reference
import NSFormalization.Paper1.CorrectionVectorNorms
import NSFormalization.Section4.I03.Mixed
import NSFormalization.Section4.I03.Energy
import Bindings.ScalingNorms
import Bindings.ScalingEnergy
import NSFormalization.Source.InsertionForceConvergence

/-! The only layer that knows the current implementation's names and paths for
the scaling contract.

`Contracts.V1.Scaling` writes out the two rescaled fields `P_eps`, `F_eps` and
the blow-up predicate `SpeedUnboundedAt` that are not already in
`Contracts.V1.Correction`; this adapter records by `rfl` that each of them is
the upstream notion, and then assembles the whole scaling package.
-/

noncomputable section
namespace BlowupDensity.Bindings

open Set MeasureTheory Filter
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Source NSFormalization.Source.PacketScaling
open NSFormalization.Paper1 NSFormalization.Paper1.CorrectionProfile
open NSFormalization.Section4.I02
open scoped ContDiff ENNReal Topology

section Correspondence

variable (x₀ : Contracts.V1.Space) (T ε : ℝ) (u : Contracts.V1.VelocityField)
  (pr : Contracts.V1.PressureField)

/-- The contract's `P_eps` is the implementation's parabolic rescaling of the
past-zero extension of the packet pressure. -/
theorem scaledPressure_eq :
    Contracts.V1.scaledPressure pr x₀ T ε =
      NSFormalization.Source.parabolicPressure ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField pr) := rfl

/-- The contract's `F_eps` is the implementation's parabolic rescaling of the
packet force. -/
theorem scaledForce_eq :
    Contracts.V1.scaledForce u x₀ T ε =
      NSFormalization.Source.parabolicForce ε⁻¹ (T - ε ^ 2) x₀ u := rfl

/-- The contract's blow-up predicate is the upstream one. -/
theorem speedUnboundedAt_eq :
    Contracts.V1.SpeedUnboundedAt T u = PacketScaling.SpeedUnboundedAt T u := rfl

/-- At the packet's own singular time it is the `I01` predicate. -/
theorem speedUnboundedAt_one :
    Contracts.V1.SpeedUnboundedAt 1 u = Contracts.V1.SpeedUnboundedAtOne u := rfl

/-- The contract's residual is the upstream one, so the transported momentum
equation below is literally the conclusion shape of `parabolic_equation`. -/
theorem navierStokesResidual_eq (ν : ℝ) (t : ℝ) (x : Contracts.V1.Space) :
    Contracts.V1.navierStokesResidual ν u pr t x =
      NSFormalization.Source.residual ν u pr t x := rfl

end Correspondence

section Transport

variable {ν : ℝ} (P : Contracts.V1.PacketAPI ν) {T ε : ℝ} (x₀ : Contracts.V1.Space)

/-- The packet force is its own past-zero extension: `PacketAPI.force_zero_nonpos`. -/
theorem zeroPastField_force : zeroPastField P.force = P.force := by
  funext z
  obtain ⟨t, x⟩ := z
  by_cases ht : 0 < t
  · exact zeroPastField_of_pos P.force ht x
  · rw [zeroPastField_of_nonpos P.force (le_of_not_gt ht) x,
      P.force_zero_nonpos t (le_of_not_gt ht) x]

/-- `eps^{-2}(t - (T - eps^2)) < 1` exactly when `t < T`: the transported
presingular interval of `eq:scaling`. -/
theorem source_time_lt_one (hε : 0 < ε) {t : ℝ} (ht : t < T) :
    ((ε⁻¹ : ℝ)) ^ 2 * (t - (T - ε ^ 2)) < 1 := by
  have hk : (0 : ℝ) < (ε⁻¹) ^ 2 := by positivity
  have hc : ((ε⁻¹ : ℝ)) ^ 2 * ε ^ 2 = 1 := by
    field_simp
  nlinarith [mul_lt_mul_of_pos_left (show t - (T - ε ^ 2) < ε ^ 2 by linarith) hk]

/-- `prop:scaling`, momentum equation: the rescaled fields solve the equation at
the **same** viscosity at every time before `T`, `03-torus.tex:123, 141`. -/
theorem scaled_equation (hε : 0 < ε) {t : ℝ} (ht : t < T) (x : Contracts.V1.Space) :
    Contracts.V1.navierStokesResidual ν
        (Contracts.V1.scaledPacket P.velocity x₀ T ε)
        (Contracts.V1.scaledPressure P.pressure x₀ T ε) t x =
      Contracts.V1.scaledForce P.force x₀ T ε (t, x) := by
  have h := parabolic_equation ν ε⁻¹ (T - ε ^ 2) x₀
    (zeroPastField P.velocity) (zeroPastField P.pressure) (zeroPastField P.force) t x
    (P.extension_navier_stokes _ (source_time_lt_one hε ht) _)
  rw [zeroPastField_force P] at h
  exact h

/-- `prop:scaling`, incompressibility, `03-torus.tex:141`. -/
theorem scaled_divergence_free (hε : 0 < ε) {t : ℝ} (ht : t < T) (x : Contracts.V1.Space) :
    Contracts.V1.spatialDivergence
      (Contracts.V1.scaledPacket P.velocity x₀ T ε) t x = 0 := by
  have hk : (0 : ℝ) < ε⁻¹ := inv_pos.mpr hε
  refine delayed_parabolic_divergence hk (T - ε ^ 2) x₀
    (fun σ hσ y => P.divergence_free σ ⟨hσ.1.le, hσ.2⟩ y) (t := t) ?_ x
  rw [NSFormalization.Section4.I02.inv_sq_inv]
  linarith

/-- `prop:scaling`, unbounded speed at `T`, `03-torus.tex:123, 142-143`. -/
theorem scaled_blowup (hε : 0 < ε) (hT : ε ^ 2 ≤ T) :
    Contracts.V1.SpeedUnboundedAt T (Contracts.V1.scaledPacket P.velocity x₀ T ε) := by
  have hk : (0 : ℝ) < ε⁻¹ := inv_pos.mpr hε
  have hdelay : (((ε⁻¹ : ℝ)) ^ 2)⁻¹ ≤ T := by
    rw [NSFormalization.Section4.I02.inv_sq_inv]; exact hT
  have h := speed_unbounded_at_target hk hdelay x₀
    (zeroPastField_speed P.speed_unbounded)
  rwa [NSFormalization.Section4.I02.inv_sq_inv] at h

end Transport

section Identification

variable {ν : ℝ} {P : Contracts.V1.PacketAPI ν} (C : Contracts.V1.CorrectionAPI ν P)

/-- `CorrectionAPI.potential_formula` pins the vector potential to the
implementation's radial potential: `eq:potential`,
`paper/sections/03-torus.tex:178-180`. -/
theorem potential_eq : C.potential = RadialPotential.timePotential C.v C.x₀ := by
  funext z
  obtain ⟨t, x⟩ := z
  exact C.potential_formula t x

/-- `CorrectionAPI.correction_formula` together with `potential_eq` pins `w_eps`
to the implementation's `physicalCorrection`: `eq:cutoff`,
`paper/sections/03-torus.tex:183-187`.  This is what makes every `Paper1`
estimate for `physicalCorrection` available for an *abstract* `CorrectionAPI`,
without re-running its construction. -/
theorem correction_eq (ε : ℝ) :
    C.correction ε = physicalCorrection C.v C.x₀ C.T C.θ C.η ε := by
  funext z
  rw [C.correction_formula ε z, potential_eq C]
  rfl

/-- `CorrectionAPI.force_formula` pins `H_eps` to the implementation's
`correctionForce` of that correction: `eq:H`,
`paper/sections/03-torus.tex:220-223`. -/
theorem forceCorrection_eq (ε : ℝ) :
    C.forceCorrection ε =
      NSFormalization.Source.correctionForce ν C.v (physicalCorrection C.v C.x₀ C.T C.θ C.η ε) := by
  funext z
  obtain ⟨t, x⟩ := z
  rw [C.force_formula ε t x, correction_eq C ε]
  rfl

/-- The half-width of the regularity window used to replace the slab-regular
reference by a globally smooth one.  `03-torus.tex:164` gives the reference only
on `[0,T+delta]`, while every `Paper1` estimate assumes global smoothness. -/
def window : ℝ := min C.T C.δ / 4

theorem window_pos : 0 < window C := by
  have := lt_min C.time_pos C.margin_pos
  unfold window
  linarith

/-- A globally smooth divergence-free reference agreeing with `C.v` throughout
the cutoff window, from `Paper1.TimeExtension`. -/
theorem exists_window_extension :
    ∃ V : Contracts.V1.VelocityField, ContDiff ℝ ∞ V ∧
      ∀ s : ℝ, |s - C.T| ≤ window C → ∀ y : Contracts.V1.Space, V (s, y) = C.v (s, y) := by
  have hw := window_pos C
  have hsub : Ioo (C.T - 2 * window C) (C.T + 2 * window C) ⊆ Ioo (0 : ℝ) (C.T + C.δ) := by
    intro s hs
    have h1 : window C ≤ C.T / 4 := by
      unfold window
      have := min_le_left C.T C.δ
      linarith
    have h2 : window C ≤ C.δ / 4 := by
      unfold window
      have := min_le_right C.T C.δ
      linarith
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  obtain ⟨V, hVs, _, hVeq, _⟩ := exists_global_reference_extension C.T (window C) hw
    (C.reference_smooth.mono (Set.prod_mono_left hsub))
    (fun s hs x => C.reference_divergence_free s (hsub hs) x)
  refine ⟨V, hVs, fun s hs y => ?_⟩
  rw [abs_le] at hs
  exact hVeq ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, mem_univ y⟩

/-- Outside the window the temporal cutoff already vanishes, so the correction
built from `C.v` and the one built from any window extension agree everywhere.
`03-torus.tex:212`: `eta_eps` is supported in `(T-2eps^2, T+2eps^2)`. -/
theorem temporalCutoff_zero_outside {ε : ℝ} (hε : 0 < ε) (hεw : 2 * ε ^ 2 ≤ window C)
    {s : ℝ} (hs : window C < |s - C.T|) : temporalCutoff C.η C.T ε s = 0 := by
  show C.η ((ε ^ 2)⁻¹ * (s - C.T)) = 0
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
  have hI := C.eta_support hmem
  have hb1 : s - C.T < 2 * ε ^ 2 := by
    have h := mul_lt_mul_of_pos_left hI.2 hε2
    rw [← mul_assoc, mul_inv_cancel₀ hε2.ne', one_mul] at h
    linarith
  have hb2 : -(2 * ε ^ 2) < s - C.T := by
    have h := mul_lt_mul_of_pos_left hI.1 hε2
    rw [← mul_assoc, mul_inv_cancel₀ hε2.ne', one_mul] at h
    linarith
  have habs : |s - C.T| < 2 * ε ^ 2 := abs_lt.mpr ⟨hb2, hb1⟩
  linarith

theorem correction_eq_extension {V : Contracts.V1.VelocityField}
    (hV : ∀ s : ℝ, |s - C.T| ≤ window C → ∀ y : Contracts.V1.Space, V (s, y) = C.v (s, y))
    {ε : ℝ} (hε : 0 < ε) (hεw : 2 * ε ^ 2 ≤ window C) :
    C.correction ε = physicalCorrection V C.x₀ C.T C.θ C.η ε := by
  rw [correction_eq C ε]
  funext z
  obtain ⟨s, y⟩ := z
  by_cases hs : |s - C.T| ≤ window C
  · exact physicalCorrection_congr_slice C.v V C.x₀ C.T C.θ C.η ε (s, y)
      (fun w => (hV s hs w).symm)
  · rw [not_le] at hs
    rw [physicalCorrection, physicalCorrection,
      localCorrection_zero_of_time C.v C.x₀ _ _ s y (temporalCutoff_zero_outside C hε hεw hs),
      localCorrection_zero_of_time V C.x₀ _ _ s y (temporalCutoff_zero_outside C hε hεw hs)]

theorem forceCorrection_eq_extension {V : Contracts.V1.VelocityField}
    (hV : ∀ s : ℝ, |s - C.T| ≤ window C → ∀ y : Contracts.V1.Space, V (s, y) = C.v (s, y))
    {ε : ℝ} (hε : 0 < ε) (hεw : 2 * ε ^ 2 ≤ window C) :
    C.forceCorrection ε =
      NSFormalization.Source.correctionForce ν V (physicalCorrection V C.x₀ C.T C.θ C.η ε) := by
  rw [forceCorrection_eq C ε, ← correction_eq C ε, correction_eq_extension C hV hε hεw]
  funext z
  by_cases hs : |z.1 - C.T| ≤ window C
  · exact correctionForce_congr_slice ν C.v V _ z (fun w => (hV z.1 hs w).symm)
  · rw [not_le] at hs
    have hsupp : tsupport (physicalCorrection V C.x₀ C.T C.θ C.η ε) ⊆
        Ioo (C.T - 2 * ε ^ 2) (C.T + 2 * ε ^ 2) ×ˢ
          Metric.ball C.x₀ (ε * C.θRadius) :=
      PhysicalRemoval.physical_support hε V C.x₀ C.T C.theta_compactSupport
        C.eta_compactSupport C.theta_support C.eta_support
    have hout : z ∉ tsupport (physicalCorrection V C.x₀ C.T C.θ C.η ε) := by
      intro hmem
      obtain ⟨ha, hb⟩ := (hsupp hmem).1
      have : |z.1 - C.T| < 2 * ε ^ 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
      linarith
    rw [NSFormalization.Source.LocalizedInsertion.correctionForce_eq_zero_outside ν C.v _ hout,
      NSFormalization.Source.LocalizedInsertion.correctionForce_eq_zero_outside ν V _ hout]

end Identification

section Monotonicity

/-- Squaring `Source.fourierSobolevNorm_mono_of_compact`: the Bessel weight
`(1+|xi|^2)^s` is monotone in `s`, `paper/sections/04-whole-space.tex:78`. -/
theorem fourierSobolevSq_mono {s r : ℝ} (hsr : s ≤ r) {f : Contracts.V1.Space → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    fourierSobolevSq s f ≤ fourierSobolevSq r f := by
  have h := fourierSobolevNorm_mono_of_compact hsr hf hc
  have hs := fourierSobolevSq_nonneg s f
  have hr := fourierSobolevSq_nonneg r f
  unfold fourierSobolevNorm at h
  nlinarith [Real.sq_sqrt hs, Real.sq_sqrt hr, Real.sqrt_nonneg (fourierSobolevSq s f),
    Real.sqrt_nonneg (fourierSobolevSq r f)]

/-- `‖z‖_{H^s} <= ‖z‖_{H^r}` for `s <= r`, in the Euclidean vector norm of
`01-introduction.tex:103`; the monotonicity step of
`paper/sections/04-whole-space.tex:78`. -/
theorem vectorFourierSobolevNorm_mono {s r : ℝ} (hsr : s ≤ r)
    {F : Contracts.V1.VelocityField} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (t : ℝ) : vectorFourierSobolevNorm s F t ≤ vectorFourierSobolevNorm r F t := by
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum (fun i _ => fourierSobolevSq_mono hsr ?_ ?_)
  · exact (coordinateForce_smooth hF i).comp (contDiff_const.prodMk contDiff_id)
  · exact NSFormalization.Paper3.compact_spatial_slice (coordinateForce_compact hc i) t

/-- Its time-norm form. -/
theorem eLpNorm_vectorFourierSobolevNorm_mono {s r : ℝ} (hsr : s ≤ r) (q : ℝ≥0∞)
    {F : Contracts.V1.VelocityField} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    eLpNorm (vectorFourierSobolevNorm s F) q volume ≤
      eLpNorm (vectorFourierSobolevNorm r F) q volume := by
  refine eLpNorm_mono_real (fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ vectorFourierSobolevNorm s F t from
    Real.sqrt_nonneg _)]
  exact vectorFourierSobolevNorm_mono hsr hF hc t

end Monotonicity

section Mixed

open NSFormalization.Section4.I03

/-- The canonical mixed Lebesgue norm of `Contracts.V1.Data` is *attained*: all
admissible Bochner slice paths of one field agree at every nonnegative time, so
the defining infimum is a single value, namely the `(0,infinity)` time norm of
the spatial norm profile.  This is what lets `eq:packetFscale`
(`paper/sections/03-torus.tex:129-131`) be transported as an **equality**
rather than as a bound. -/
theorem mixedLebesgueENorm_eq {p q : ℝ≥0∞} [Fact (1 ≤ p)]
    {F : Contracts.V1.VelocityField} (hF : Continuous F) (hc : HasCompactSupport F) :
    Contracts.V1.Data.mixedLebesgueENorm q p F = positiveMixedNorm p q F := by
  refine le_antisymm ?_ ?_
  · refine le_trans (iInf_le _ ⟨fun t => (slice_memLp hF hc p t).toLp
      (fun x : Contracts.V1.Space => F (t, x)), fun t _ => MemLp.coeFn_toLp _,
      (continuous_slicePath hF hc).stronglyMeasurable.aestronglyMeasurable⟩) ?_
    exact le_of_eq (eLpNorm_slicePath_eq p hF hc q)
  · refine le_iInf ?_
    rintro ⟨G, hslice, _hmeas⟩
    refine le_of_eq (eLpNorm_congr_enorm_ae ?_).symm
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hG : eLpNorm (G t : Contracts.V1.Space → Contracts.V1.Space) p volume =
        eLpNorm (fun x : Contracts.V1.Space => F (t, x)) p volume :=
      eLpNorm_congr_ae (hslice t (le_of_lt ht))
    rw [Lp.enorm_def, hG, Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal ((slice_memLp hF hc p t).eLpNorm_lt_top.ne)]

/-- `eq:packetFscale` in the canonical Section 4 norm:
`‖F_eps‖_{L^q(0,inf;L^p)} = eps^{alpha(p,q)} ‖F‖_{L^q(0,inf;L^p)}`,
`paper/sections/03-torus.tex:129-131, 148-149`. -/
theorem mixedLebesgueENorm_scaledForce {ν : ℝ} (P : Contracts.V1.PacketAPI ν)
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] {T ε : ℝ} (x₀ : Contracts.V1.Space)
    (hε : 0 < ε) (hT : 0 ≤ T - ε ^ 2) :
    Contracts.V1.Data.mixedLebesgueENorm q p
        (Contracts.V1.scaledForce P.force x₀ T ε) =
      ENNReal.ofReal (ε ^ Contracts.V1.alpha p q) *
        Contracts.V1.Data.mixedLebesgueENorm q p P.force := by
  have hFs : ContDiff ℝ ∞ P.force := P.force_smooth
  have hFc : HasCompactSupport P.force := P.force_support.1
  have hsm : ContDiff ℝ ∞ (parabolicForce ε⁻¹ (T - ε ^ 2) x₀ P.force) :=
    parabolicForce_smooth hFs _ _ _
  have hsc : HasCompactSupport (parabolicForce ε⁻¹ (T - ε ^ 2) x₀ P.force) :=
    parabolicForce_compact _ _ _ hFc
  rw [show Contracts.V1.scaledForce P.force x₀ T ε =
      parabolicForce ε⁻¹ (T - ε ^ 2) x₀ P.force from rfl,
    mixedLebesgueENorm_eq hsm.continuous hsc,
    mixedLebesgueENorm_eq hFs.continuous hFc,
    positiveMixedNorm_parabolicForce hFs hFc
      (fun t ht x => P.force_zero_nonpos t ht x) hε hT x₀ p q]
  rfl

end Mixed

section Threshold

variable {ν : ℝ} {P : Contracts.V1.PacketAPI ν} (C : Contracts.V1.CorrectionAPI ν P)

/-- `I03`'s scale threshold: `I02`'s, shrunk so that the whole cutoff window
`(T - 2eps^2, T + 2eps^2)` fits inside the regularity window on which the
reference has a globally smooth extension.  `eps0 <= eps0(I02)` is the
inequality that `ScalingAPI.eps_le_correction` records. -/
def scalingThreshold : ℝ := min C.ε₀ (Real.sqrt (window C / 2))

theorem scalingThreshold_pos : 0 < scalingThreshold C :=
  lt_min C.eps_pos (Real.sqrt_pos.mpr (by linarith [window_pos C]))

theorem scalingThreshold_le : scalingThreshold C ≤ C.ε₀ := min_le_left _ _

theorem scalingThreshold_le_one : scalingThreshold C ≤ 1 :=
  (scalingThreshold_le C).trans C.eps_le_one

theorem mem_correction_range {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (scalingThreshold C)) :
    ε ∈ Ioc (0 : ℝ) C.ε₀ := ⟨hε.1, hε.2.trans (scalingThreshold_le C)⟩

theorem mem_unit_range {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (scalingThreshold C)) :
    ε ∈ Ioc (0 : ℝ) 1 := ⟨hε.1, hε.2.trans (scalingThreshold_le_one C)⟩

/-- On the shrunken range the cutoff window sits inside the regularity window. -/
theorem window_bound {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (scalingThreshold C)) :
    2 * ε ^ 2 ≤ window C := by
  have h : ε ≤ Real.sqrt (window C / 2) := hε.2.trans (min_le_right _ _)
  have hw : 0 < window C := window_pos C
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ window C / 2 by linarith)
  nlinarith [hε.1.le, Real.sqrt_nonneg (window C / 2)]

/-- `2 eps^2 < min(T, delta)` on the shrunken range, `03-torus.tex:212`. -/
theorem eps_time_bound {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (scalingThreshold C)) :
    2 * ε ^ 2 < min C.T C.δ := C.eps_time ε (mem_correction_range C hε)

/-- `2 eps^2 < T`, the form the energy transport consumes. -/
theorem two_eps_sq_lt_time {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (scalingThreshold C)) :
    2 * ε ^ 2 < C.T :=
  lt_of_lt_of_le (eps_time_bound C hε) (min_le_left _ _)

/-- `eps^2 < T`, the delay hypothesis of `speed_unbounded_at_target`. -/
theorem eps_sq_lt_time {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (scalingThreshold C)) :
    ε ^ 2 < C.T := by
  have h := eps_time_bound C hε
  have := min_le_left C.T C.δ
  nlinarith [sq_nonneg ε]

/-- `K subset ball 0 R_*`: the packet carrier sits inside the cutoff radius,
`03-torus.tex:101-102`.  It is a consequence of `I02`'s plateau data, so `I03`
need not assume it. -/
theorem carrier_subset_ball :
    P.carrier ⊆ Metric.ball (0 : Contracts.V1.Space) C.θRadius := by
  intro x hx
  refine C.theta_support (subset_tsupport _ ?_)
  have hone : C.θ x = 1 := C.theta_one (C.carrier_subset_plateau hx)
  rw [Function.mem_support, hone]
  exact one_ne_zero

end Threshold

section CorrectionBounds

variable {ν : ℝ} {P : Contracts.V1.PacketAPI ν}

/-- `eq:RpositiveScale` line 2 for the *abstract* `I02` correction force, in the
cycles convention: `‖H_eps‖_{L^q_t H^s} <= C eps^{2/q - 1/2 - s}` for
`0 <= s <= 1`, `paper/sections/04-whole-space.tex:67-69`.  The exponent is
literally `beta(q,s) + 1`. -/
theorem correction_cycles_positive (C : Contracts.V1.CorrectionAPI ν P)
    {V : Contracts.V1.VelocityField} (hVs : ContDiff ℝ ∞ V)
    (hV : ∀ s : ℝ, |s - C.T| ≤ window C → ∀ y : Contracts.V1.Space, V (s, y) = C.v (s, y))
    (q : ℝ≥0∞) (hq : 1 ≤ q) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ ε ∈ Ioc (0 : ℝ) (scalingThreshold C),
      eLpNorm (vectorFourierSobolevNorm s (C.forceCorrection ε)) q volume ≤
        ENNReal.ofReal (ε ^ (2 / q.toReal - 1 / 2 - s)) * K := by
  obtain ⟨K, hK, hb⟩ := CorrectionForceNorms.vectorPhysicalForce_uniform_positive_time ν hVs
    C.x₀ C.T C.theta_smooth C.eta_smooth C.theta_compactSupport C.eta_compactSupport hs1 hs0 q hq
  refine ⟨K, hK.ne, fun ε hε => ?_⟩
  rw [forceCorrection_eq_extension C hV hε.1 (window_bound C hε)]
  exact hb ε (mem_unit_range C hε)

/-- `eq:RnegativeScale`, correction half, for the abstract `I02` correction
force, in the cycles convention: `-3/2 < s <= 0`,
`paper/sections/04-whole-space.tex:74-75`. -/
theorem correction_cycles_negative (C : Contracts.V1.CorrectionAPI ν P)
    {V : Contracts.V1.VelocityField} (hVs : ContDiff ℝ ∞ V)
    (hV : ∀ s : ℝ, |s - C.T| ≤ window C → ∀ y : Contracts.V1.Space, V (s, y) = C.v (s, y))
    (q : ℝ≥0∞) (hq : 1 ≤ q) {s : ℝ} (hlo : -3 / 2 < s) (hs0 : s ≤ 0) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ ε ∈ Ioc (0 : ℝ) (scalingThreshold C),
      eLpNorm (vectorFourierSobolevNorm s (C.forceCorrection ε)) q volume ≤
        ENNReal.ofReal (ε ^ (2 / q.toReal - 1 / 2 - s)) * K := by
  obtain ⟨K, hK, hb⟩ := CorrectionForceNorms.vectorPhysicalForce_uniform_negative_time ν hVs
    C.x₀ C.T C.theta_smooth C.eta_smooth C.theta_compactSupport C.eta_compactSupport hlo hs0 q hq
  refine ⟨K, hK.ne, fun ε hε => ?_⟩
  rw [forceCorrection_eq_extension C hV hε.1 (window_bound C hε)]
  exact hb ε (mem_unit_range C hε)

/-- The force difference `g_eps - g = H_eps + F_eps` of
`paper/sections/04-whole-space.tex:48` is exactly the implementation's
insertion-family force, for the *same* `eps`. -/
theorem forceDifference_eq (C : Contracts.V1.CorrectionAPI ν P)
    {V : Contracts.V1.VelocityField}
    (hV : ∀ s : ℝ, |s - C.T| ≤ window C → ∀ y : Contracts.V1.Space, V (s, y) = C.v (s, y))
    {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) (scalingThreshold C)) :
    (fun z => C.forceCorrection ε z +
        Contracts.V1.scaledForce P.force C.x₀ C.T ε z) =
      InsertionFamily.force ν P.force V C.x₀ C.T C.θ C.η ε := by
  rw [forceCorrection_eq_extension C hV hε.1 (window_bound C hε)]
  rfl

end CorrectionBounds

section SobolevFields

variable {ν : ℝ} {P : Contracts.V1.PacketAPI ν}

/-- `eq:RpositiveScale` line 1 in the canonical Section 4 norm, with a constant
family defined for *every* `(q,s)` so that it can be a field of `ScalingAPI`.
`paper/sections/04-whole-space.tex:64-66`. -/
theorem exists_packet_positive_const (P : Contracts.V1.PacketAPI ν)
    (x₀ : Contracts.V1.Space) (T ε₀ : ℝ) (hε₀ : ε₀ ≤ 1) (q : ℝ≥0∞) (s : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ (1 ≤ q → 0 ≤ s → s ≤ 1 → ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      Contracts.V1.Data.forceSobolevENorm q s
          (Contracts.V1.scaledForce P.force x₀ T ε) ≤
        ENNReal.ofReal (c * ε ^ (2 / q.toReal - 3 / 2 - s))) := by
  classical
  by_cases h : 1 ≤ q ∧ 0 ≤ s ∧ s ≤ 1
  · obtain ⟨hq, hs0, hs1⟩ := h
    have hFs : ContDiff ℝ ∞ P.force := P.force_smooth
    have hFc : HasCompactSupport P.force := P.force_support.1
    have hS := profile_positive_finite hFs hFc q hs1
    refine ⟨frequencyUnit ^ |s| *
      (∑ i : Fin 3, eLpNorm (fun t => fourierSobolevNorm s
        (fun x => coordinateForce P.force i (t, x))) q volume).toReal,
      mul_nonneg (Real.rpow_nonneg frequencyUnit_pos.le _) ENNReal.toReal_nonneg,
      fun _ _ _ ε hε => ?_⟩
    exact sobolev_bound_of_cycles s q (parabolicForce_smooth hFs _ _ _)
      (parabolicForce_compact _ _ _ hFc) (Real.rpow_nonneg hε.1.le _) hS
      (cycles_packet_positive hFs hFc q hq hs0 hs1 hε.1 (hε.2.trans hε₀) (T - ε ^ 2) x₀)
  · exact ⟨0, le_rfl, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩

/-- `eq:RnegativeScale`, packet half, in the canonical Section 4 norm,
`paper/sections/04-whole-space.tex:73-75`. -/
theorem exists_packet_negative_const (P : Contracts.V1.PacketAPI ν)
    (x₀ : Contracts.V1.Space) (T ε₀ : ℝ) (q : ℝ≥0∞) (s : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ (1 ≤ q → -3 / 2 < s → s ≤ 0 → ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      Contracts.V1.Data.forceSobolevENorm q s
          (Contracts.V1.scaledForce P.force x₀ T ε) ≤
        ENNReal.ofReal (c * ε ^ (2 / q.toReal - 3 / 2 - s))) := by
  classical
  by_cases h : 1 ≤ q ∧ -3 / 2 < s ∧ s ≤ 0
  · obtain ⟨hq, hlo, hs0⟩ := h
    have hFs : ContDiff ℝ ∞ P.force := P.force_smooth
    have hFc : HasCompactSupport P.force := P.force_support.1
    have hS := profile_homogeneous_finite hFs hFc q hlo hs0
    refine ⟨frequencyUnit ^ |s| *
      (∑ i : Fin 3, eLpNorm (fun t => homogeneousFourierNorm s
        (fun x => coordinateForce P.force i (t, x))) q volume).toReal,
      mul_nonneg (Real.rpow_nonneg frequencyUnit_pos.le _) ENNReal.toReal_nonneg,
      fun _ _ _ ε hε => ?_⟩
    exact sobolev_bound_of_cycles s q (parabolicForce_smooth hFs _ _ _)
      (parabolicForce_compact _ _ _ hFc) (Real.rpow_nonneg hε.1.le _) hS
      (cycles_packet_negative hFs hFc q hq hlo hs0 hε.1 (T - ε ^ 2) x₀)
  · exact ⟨0, le_rfl, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩

/-- `eq:RpositiveScale` line 2 and `eq:RnegativeScale`, correction half, in the
canonical Section 4 norm.  One statement covers both ranges because the exponent
`beta(q,s)+1 = 2/q - 1/2 - s` is the same,
`paper/sections/04-whole-space.tex:67-69, 74-75`. -/
theorem exists_correction_const (C : Contracts.V1.CorrectionAPI ν P)
    {V : Contracts.V1.VelocityField} (hVs : ContDiff ℝ ∞ V)
    (hV : ∀ s : ℝ, |s - C.T| ≤ window C → ∀ y : Contracts.V1.Space, V (s, y) = C.v (s, y))
    (q : ℝ≥0∞) (s : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ (1 ≤ q → (0 ≤ s ∧ s ≤ 1 ∨ -3 / 2 < s ∧ s ≤ 0) →
      ∀ ε ∈ Ioc (0 : ℝ) (scalingThreshold C),
        Contracts.V1.Data.forceSobolevENorm q s (C.forceCorrection ε) ≤
          ENNReal.ofReal (c * ε ^ (2 / q.toReal - 1 / 2 - s))) := by
  classical
  by_cases h : 1 ≤ q ∧ (0 ≤ s ∧ s ≤ 1 ∨ -3 / 2 < s ∧ s ≤ 0)
  · obtain ⟨hq, hrange⟩ := h
    obtain ⟨K, hK, hb⟩ : ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ ε ∈ Ioc (0 : ℝ) (scalingThreshold C),
        eLpNorm (vectorFourierSobolevNorm s (C.forceCorrection ε)) q volume ≤
          ENNReal.ofReal (ε ^ (2 / q.toReal - 1 / 2 - s)) * K := by
      rcases hrange with ⟨hs0, hs1⟩ | ⟨hlo, hs0⟩
      · exact correction_cycles_positive C hVs hV q hq hs0 hs1
      · exact correction_cycles_negative C hVs hV q hq hlo hs0
    refine ⟨frequencyUnit ^ |s| * K.toReal,
      mul_nonneg (Real.rpow_nonneg frequencyUnit_pos.le _) ENNReal.toReal_nonneg,
      fun _ _ ε hε => ?_⟩
    exact sobolev_bound_of_cycles s q (C.force_smooth ε (mem_correction_range C hε))
      (C.force_compactSupport ε (mem_correction_range C hε))
      (Real.rpow_nonneg hε.1.le _) hK (hb ε hε)
  · exact ⟨0, le_rfl, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩

/-- The intermediate-index reduction of `paper/sections/04-whole-space.tex:78`:
below the homogeneous range the order `s` is reached from a valid index
`r in (-3/2, 0]` by inhomogeneous monotonicity, never by a homogeneous claim.
One constant serves both halves. -/
theorem exists_low_order_const (C : Contracts.V1.CorrectionAPI ν P)
    {V : Contracts.V1.VelocityField} (hVs : ContDiff ℝ ∞ V)
    (hV : ∀ s : ℝ, |s - C.T| ≤ window C → ∀ y : Contracts.V1.Space, V (s, y) = C.v (s, y))
    (q : ℝ≥0∞) (s r : ℝ) :
    ∃ c : ℝ, 0 ≤ c ∧ (1 ≤ q → -3 / 2 < r → r ≤ 0 → s ≤ r →
      ∀ ε ∈ Ioc (0 : ℝ) (scalingThreshold C),
        Contracts.V1.Data.forceSobolevENorm q s
              (Contracts.V1.scaledForce P.force C.x₀ C.T ε) ≤
            ENNReal.ofReal (c * ε ^ (2 / q.toReal - 3 / 2 - r)) ∧
          Contracts.V1.Data.forceSobolevENorm q s (C.forceCorrection ε) ≤
            ENNReal.ofReal (c * ε ^ (2 / q.toReal - 1 / 2 - r))) := by
  classical
  by_cases h : 1 ≤ q ∧ -3 / 2 < r ∧ r ≤ 0 ∧ s ≤ r
  · obtain ⟨hq, hlo, hr0, hsr⟩ := h
    have hFs : ContDiff ℝ ∞ P.force := P.force_smooth
    have hFc : HasCompactSupport P.force := P.force_support.1
    have hS := profile_homogeneous_finite hFs hFc q hlo hr0
    obtain ⟨K, hK, hKb⟩ := correction_cycles_negative C hVs hV q hq hlo hr0
    set cP : ℝ := frequencyUnit ^ |s| *
      (∑ i : Fin 3, eLpNorm (fun t => homogeneousFourierNorm r
        (fun x => coordinateForce P.force i (t, x))) q volume).toReal with hcP
    set cH : ℝ := frequencyUnit ^ |s| * K.toReal with hcH
    have hcP0 : 0 ≤ cP :=
      mul_nonneg (Real.rpow_nonneg frequencyUnit_pos.le _) ENNReal.toReal_nonneg
    have hcH0 : 0 ≤ cH :=
      mul_nonneg (Real.rpow_nonneg frequencyUnit_pos.le _) ENNReal.toReal_nonneg
    refine ⟨max cP cH, le_trans hcP0 (le_max_left _ _), fun _ _ _ _ ε hε => ?_⟩
    have hεp : (0 : ℝ) < ε := hε.1
    have hFεs : ContDiff ℝ ∞ (parabolicForce ε⁻¹ (C.T - ε ^ 2) C.x₀ P.force) :=
      parabolicForce_smooth hFs _ _ _
    have hFεc : HasCompactSupport (parabolicForce ε⁻¹ (C.T - ε ^ 2) C.x₀ P.force) :=
      parabolicForce_compact _ _ _ hFc
    have hHs : ContDiff ℝ ∞ (C.forceCorrection ε) :=
      C.force_smooth ε (mem_correction_range C hε)
    have hHc : HasCompactSupport (C.forceCorrection ε) :=
      C.force_compactSupport ε (mem_correction_range C hε)
    constructor
    · have hchain :
          eLpNorm (vectorFourierSobolevNorm s
              (parabolicForce ε⁻¹ (C.T - ε ^ 2) C.x₀ P.force)) q volume ≤
            ENNReal.ofReal (ε ^ (2 / q.toReal - 3 / 2 - r)) *
              ∑ i : Fin 3, eLpNorm (fun t => homogeneousFourierNorm r
                (fun x => coordinateForce P.force i (t, x))) q volume :=
        (eLpNorm_vectorFourierSobolevNorm_mono hsr q hFεs hFεc).trans
          (cycles_packet_negative hFs hFc q hq hlo hr0 hεp (C.T - ε ^ 2) C.x₀)
      refine (sobolev_bound_of_cycles s q hFεs hFεc (Real.rpow_nonneg hεp.le _) hS
        hchain).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hεp.le _)
    · have hchain : eLpNorm (vectorFourierSobolevNorm s (C.forceCorrection ε)) q volume ≤
            ENNReal.ofReal (ε ^ (2 / q.toReal - 1 / 2 - r)) * K :=
        (eLpNorm_vectorFourierSobolevNorm_mono hsr q hHs hHc).trans (hKb ε hε)
      refine (sobolev_bound_of_cycles s q hHs hHc (Real.rpow_nonneg hεp.le _) hK
        hchain).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hεp.le _)
  · exact ⟨0, le_rfl, fun h1 h2 h3 h4 => absurd ⟨h1, h2, h3, h4⟩ h⟩

/-- The force clause of Theorem 4.2, `paper/sections/04-whole-space.tex:42-43`:
`‖g_eps - g‖_{L^q_t H^s_x} -> 0` for `q in {1,2}` and every `s < 2/q - 3/2`, for
the one family. -/
theorem force_convergence (C : Contracts.V1.CorrectionAPI ν P)
    {V : Contracts.V1.VelocityField} (hVs : ContDiff ℝ ∞ V)
    (hV : ∀ s : ℝ, |s - C.T| ≤ window C → ∀ y : Contracts.V1.Space, V (s, y) = C.v (s, y))
    {q : ℝ≥0∞} (hq : q = 1 ∨ q = 2) {s : ℝ} (hs : s < 2 / q.toReal - 3 / 2) :
    Tendsto (fun ε : ℝ => Contracts.V1.Data.forceSobolevENorm q s
        (fun z => C.forceCorrection ε z +
          Contracts.V1.scaledForce P.force C.x₀ C.T ε z))
      (𝓝[>] 0) (𝓝 0) := by
  have hFs : ContDiff ℝ ∞ P.force := P.force_smooth
  have hFc : HasCompactSupport P.force := P.force_support.1
  have hsm : ∀ ε : ℝ, ContDiff ℝ ∞ (InsertionFamily.force ν P.force V C.x₀ C.T C.θ C.η ε) :=
    fun ε => InsertionFamily.force_smooth_all ν hFs hVs C.x₀ C.T ε C.theta_smooth C.eta_smooth
  have hcp : ∀ ε : ℝ, 0 < ε →
      HasCompactSupport (InsertionFamily.force ν P.force V C.x₀ C.T C.θ C.η ε) :=
    fun ε hε => InsertionFamily.force_compact_nonzero ν V hFc C.x₀ C.T ε hε.ne'
      C.theta_compactSupport C.eta_compactSupport
  have hlim : Tendsto (fun ε : ℝ => eLpNorm (vectorFourierSobolevNorm s
      (InsertionFamily.force ν P.force V C.x₀ C.T C.θ C.η ε)) q volume) (𝓝[>] 0) (𝓝 0) := by
    rcases hq with rfl | rfl
    · refine InsertionFamily.force_L1_tendsto_zero ν hFs hFc hVs C.x₀ C.T C.theta_smooth
        C.eta_smooth C.theta_compactSupport C.eta_compactSupport ?_
      have h1 : ((1 : ℝ≥0∞)).toReal = 1 := by norm_num
      rw [h1] at hs
      linarith
    · refine InsertionFamily.force_L2_tendsto_zero ν hFs hFc hVs C.x₀ C.T C.theta_smooth
        C.eta_smooth C.theta_compactSupport C.eta_compactSupport ?_
      have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by norm_num
      rw [h2] at hs
      linarith
  refine (forceSobolevENorm_tendsto_zero s q hsm hcp hlim).congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (scalingThreshold_pos C)).filter_mono nhdsWithin_le_nhds]
    with ε hε hεle
  exact congrArg (Contracts.V1.Data.forceSobolevENorm q s)
    (forceDifference_eq C hV ⟨hε, hεle.le⟩).symm

end SobolevFields

section EnergyFields

variable {ν : ℝ}

/-- Every hypothesis the `eq:packetEscale` transport needs is a field of the
registered `I01` packet contract. -/
theorem packetData (P : Contracts.V1.PacketAPI ν) :
    NSFormalization.Section4.I03.PacketData P.velocity P.carrier
      P.energyBound P.dissipationBound where
  extension_smooth := P.velocity_extension_smooth
  carrier_compact := P.carrier_compact
  support := P.velocity_support
  square_int := P.square_integrable
  zero_initial := P.zero_initial_velocity
  energy_isLUB := P.energy_isLUB
  dissipation_int := P.dissipation_integrable
  dissipation_eq := P.dissipation_eq

/-- `‖U_eps‖_{L^inf(0,T;L^2)} = eps^{1/2} M`, the first identity of
`eq:packetEscale`, `paper/sections/03-torus.tex:125-126`, in the canonical
`E_T` first summand. -/
theorem energyEssSup_scaledPacket (P : Contracts.V1.PacketAPI ν)
    (x₀ : Contracts.V1.Space) {T ε : ℝ} (hε : 0 < ε) (hT : 2 * ε ^ 2 < T) :
    Contracts.V1.Data.energyEssSup T (Contracts.V1.scaledPacket P.velocity x₀ T ε) =
      ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * P.energyBound) := by
  rw [← NSFormalization.Section4.I03.sqrt_mul_eq_rpow_half hε.le P.energyBound]
  exact NSFormalization.Section4.I03.energyEssSup_scaled_eq (packetData P) x₀ hε hT

/-- `‖grad U_eps‖_{L^2(0,T;L^2)} = eps^{1/2} D`, the second identity of
`eq:packetEscale`, `paper/sections/03-torus.tex:127-128`. -/
theorem energyGradient_scaledPacket (P : Contracts.V1.PacketAPI ν)
    (x₀ : Contracts.V1.Space) {T ε : ℝ} (hε : 0 < ε) (hT : 2 * ε ^ 2 < T) :
    Contracts.V1.Data.energyGradient T (Contracts.V1.scaledPacket P.velocity x₀ T ε) =
      ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * P.dissipationBound) := by
  rw [← NSFormalization.Section4.I03.sqrt_mul_eq_rpow_half hε.le P.dissipationBound]
  exact NSFormalization.Section4.I03.energyGradient_scaled_eq (packetData P) x₀ hε hT

end EnergyFields

section Assembly

/-- Bind the whole scaling half of Theorem 4.2's proof (`thm:Rinsert`,
`paper/sections/04-whole-space.tex:31-79`) to the stable version-one contract,
on the **given** `I02` record.

The correction and the correction force are `C`'s own -- the record's
`correction` field is literally `C` -- so "all of these conclusions hold for the
same family of inserted solutions" (`04-whole-space.tex:43`) is structural
rather than an obligation on `R42`.  The one thing this layer changes is the
scale threshold: `scalingThreshold C = min C.eps0 (sqrt (window C / 2))`, small
enough that the whole cutoff window sits inside the interval on which the
slab-regular reference `C.v` has a globally smooth extension `V`, which is what
every `Paper1` estimate assumes.  `ScalingAPI.eps_le_correction` records that
shrinking.

The constants of `eq:RpositiveScale` and `eq:RnegativeScale` are produced by
`choose` from the four `exists_*_const` lemmas above, each of which is total in
`(q,s)` and delivers its bound only inside the manuscript's range; that is what
lets them be plain function fields of the record. -/
def scaling {ν : ℝ} {P : Contracts.V1.PacketAPI ν} (C : Contracts.V1.CorrectionAPI ν P)
    (th : Contracts.V1.ThresholdAPI) :
    Contracts.V1.ScalingAPI ν P := by
  classical
  set V : Contracts.V1.VelocityField := (exists_window_extension C).choose with hVdef
  have hVs : ContDiff ℝ ∞ V := (exists_window_extension C).choose_spec.1
  have hV : ∀ s : ℝ, |s - C.T| ≤ window C → ∀ y : Contracts.V1.Space, V (s, y) = C.v (s, y) :=
    (exists_window_extension C).choose_spec.2
  choose posC hposC0 hposCb using fun (q : ℝ≥0∞) (s : ℝ) =>
    exists_packet_positive_const P C.x₀ C.T (scalingThreshold C) (scalingThreshold_le_one C) q s
  choose negC hnegC0 hnegCb using fun (q : ℝ≥0∞) (s : ℝ) =>
    exists_packet_negative_const P C.x₀ C.T (scalingThreshold C) q s
  choose corC hcorC0 hcorCb using fun (q : ℝ≥0∞) (s : ℝ) =>
    exists_correction_const C hVs hV q s
  choose lowC hlowC0 hlowCb using fun (q : ℝ≥0∞) (s r : ℝ) =>
    exists_low_order_const C hVs hV q s r
  refine
    { correction := C
      thresholds := th
      carrier_subset := carrier_subset_ball C
      ε₀ := scalingThreshold C
      eps_pos := scalingThreshold_pos C
      eps_le_one := scalingThreshold_le_one C
      eps_le_correction := scalingThreshold_le C
      eps_time := fun ε hε => eps_time_bound C hε
      eps_space := fun ε hε => C.eps_space ε (mem_correction_range C hε)
      scaledEquation := fun ε hε t ht x => scaled_equation P C.x₀ hε.1 ht x
      scaledDivergenceFree := fun ε hε t ht x => scaled_divergence_free P C.x₀ hε.1 ht x
      scaledBlowup := fun ε hε => scaled_blowup P C.x₀ hε.1 (eps_sq_lt_time C hε).le
      packetEnergyIdentity := fun ε hε =>
        energyEssSup_scaledPacket P C.x₀ hε.1 (two_eps_sq_lt_time C hε)
      packetDissipationIdentity := fun ε hε =>
        energyGradient_scaledPacket P C.x₀ hε.1 (two_eps_sq_lt_time C hε)
      correctionEnergyConst := max C.energyConst 0
      correctionEnergyConst_nonneg := le_max_right _ _
      correctionEnergyBound := fun ε hε =>
        (C.correction_energy_bound ε (mem_correction_range C hε)).trans
          (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
            (Real.rpow_nonneg hε.1.le _)))
      perturbationEnergyBound := ?_
      packetMixedScaling := fun p q _ _ ε hε =>
        mixedLebesgueENorm_scaledForce P C.x₀ hε.1
          (by nlinarith [two_eps_sq_lt_time C hε, sq_nonneg ε])
      positiveConst := posC
      packetPositiveScaling := ?_
      correctionPositiveConst := corC
      correctionPositiveScaling := ?_
      negativeConst := negC
      packetNegativeScaling := ?_
      correctionNegativeConst := corC
      correctionNegativeScaling := ?_
      lowOrderConst := lowC
      forceLowOrderBound := ?_
      forceConvergence := ?_ }
  -- perturbationEnergyBound, eq:REclose
  · intro ε hε
    have hεc := mem_correction_range C hε
    have hTε := two_eps_sq_lt_time C hε
    have hwsm : ContDiff ℝ ∞ (C.correction ε) := C.correction_smooth ε hεc
    have hwc : HasCompactSupport (C.correction ε) := C.correction_compactSupport ε hεc
    have hUsm : ContDiffOn ℝ ∞ (Contracts.V1.scaledPacket P.velocity C.x₀ C.T ε)
        (Iio C.T ×ˢ (univ : Set Contracts.V1.Space)) :=
      NSFormalization.Section4.I03.scaled_smoothOn (packetData P) C.x₀ hε.1
    have hM : 0 ≤ P.energyBound :=
      NSFormalization.Section4.I03.energyBound_nonneg (packetData P)
    have hD : 0 ≤ P.dissipationBound := by
      rw [P.dissipation_eq]; exact Real.sqrt_nonneg _
    have hCc : (0 : ℝ) ≤ max C.energyConst 0 := le_max_right _ _
    have he1 : (0 : ℝ) ≤ ε ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hε.1.le _
    have he3 : (0 : ℝ) ≤ ε ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hε.1.le _
    have htri := energyENorm_add_le C.T
      (z := C.correction ε) (w := Contracts.V1.scaledPacket P.velocity C.x₀ C.T ε)
      (fun t _ => aestronglyMeasurable_slice_of_contDiff hwsm t)
      (fun t ht => aestronglyMeasurable_slice_of_contDiffOn hUsm ht.2)
      (fun t _ x => differentiableAt_slice_of_contDiff hwsm t x)
      (fun t ht x => differentiableAt_slice_of_contDiffOn hUsm ht.2 x)
      (fun t _ => aestronglyMeasurable_spatialGradient_slice_of_contDiff hwsm t)
      (fun t ht => aestronglyMeasurable_spatialGradient_slice_of_contDiffOn hUsm ht.2)
      (aemeasurable_eLpNorm_spatialGradient_of_contDiff hwsm hwc _)
      (aemeasurable_eLpNorm_spatialGradient_of_contDiffOn hUsm)
    refine htri.trans ?_
    have hU : Contracts.V1.Data.energyENorm C.T
        (Contracts.V1.scaledPacket P.velocity C.x₀ C.T ε) =
          ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * P.energyBound) +
            ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * P.dissipationBound) := by
      rw [Contracts.V1.Data.energyENorm, energyEssSup_scaledPacket P C.x₀ hε.1 hTε,
        energyGradient_scaledPacket P C.x₀ hε.1 hTε]
    have hw : Contracts.V1.Data.energyENorm C.T (C.correction ε) ≤
        ENNReal.ofReal (max C.energyConst 0 * ε ^ ((3 : ℝ) / 2)) :=
      (C.correction_energy_bound ε hεc).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) he3))
    rw [hU]
    refine (add_le_add hw (le_refl _)).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  -- packetPositiveScaling
  · intro q hq s hs0 hs1 ε hε
    refine (hposCb q s hq hs0 hs1 ε hε).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [th.formula, th.formula]
    refine mul_le_mul_of_nonneg_left ?_ (hposC0 q s)
    have := Real.rpow_nonneg hε.1.le (2 / q.toReal - 3 / 2 - 0)
    linarith
  -- correctionPositiveScaling
  · intro q hq s hs0 hs1 ε hε
    refine (hcorCb q s hq (Or.inl ⟨hs0, hs1⟩) ε hε).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [th.formula, th.formula,
      show 2 / q.toReal - 3 / 2 - s + 1 = 2 / q.toReal - 1 / 2 - s by ring]
    refine mul_le_mul_of_nonneg_left ?_ (hcorC0 q s)
    have := Real.rpow_nonneg hε.1.le (2 / q.toReal - 3 / 2 - 0 + 1)
    linarith
  -- packetNegativeScaling
  · intro q hq s hlo hs0 ε hε
    refine (hnegCb q s hq hlo hs0.le ε hε).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [th.formula]
  -- correctionNegativeScaling
  · intro q hq s hlo hs0 ε hε
    refine (hcorCb q s hq (Or.inr ⟨hlo, hs0.le⟩) ε hε).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [th.formula, show 2 / q.toReal - 3 / 2 - s + 1 = 2 / q.toReal - 1 / 2 - s by ring]
  -- forceLowOrderBound
  · intro q hq s hslt hs0
    have hq1 : 1 ≤ q := by rcases hq with rfl | rfl <;> norm_num
    have hqT : th.exponent q.toReal 0 = 2 / q.toReal - 3 / 2 := by rw [th.formula]; ring
    by_cases hlo : -3 / 2 < s
    · refine ⟨s, hlo, hs0, le_rfl, hslt, fun ε hε => ?_⟩
      obtain ⟨h1, h2⟩ := hlowCb q s s hq1 hlo hs0.le le_rfl ε hε
      refine ⟨h1.trans (le_of_eq ?_), h2.trans (le_of_eq ?_)⟩
      · rw [th.formula]
      · rw [th.formula, show 2 / q.toReal - 3 / 2 - s + 1 = 2 / q.toReal - 1 / 2 - s by ring]
    · rw [not_lt] at hlo
      obtain ⟨r, hr1, hr2, hr3⟩ := th.negativeIndex s (by linarith)
      have hrlt : r < th.exponent q.toReal 0 := by
        rw [hqT]
        rcases hq with rfl | rfl
        · rw [show ((1 : ℝ≥0∞)).toReal = 1 by norm_num]; linarith
        · rw [show ((2 : ℝ≥0∞)).toReal = 2 by norm_num]; linarith
      refine ⟨r, hr1, by linarith, hr3.le, hrlt, fun ε hε => ?_⟩
      obtain ⟨h1, h2⟩ := hlowCb q s r hq1 hr1 (by linarith) hr3.le ε hε
      refine ⟨h1.trans (le_of_eq ?_), h2.trans (le_of_eq ?_)⟩
      · rw [th.formula]
      · rw [th.formula, show 2 / q.toReal - 3 / 2 - r + 1 = 2 / q.toReal - 1 / 2 - r by ring]
  -- forceConvergence
  · intro q hq s hs
    refine force_convergence C hVs hV hq ?_
    rw [th.formula] at hs
    linarith

end Assembly

end BlowupDensity.Bindings
