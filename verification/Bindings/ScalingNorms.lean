import Contracts.V1.Packet
import Contracts.V1.Data
import NSFormalization.Section4.I03.Angular
import NSFormalization.Source.CompactForceConvergence

/-!
# Cycles-to-angular transport of the Section 4 Sobolev force norm

`Contracts.V1.Data.forceSobolevENorm q s f` is the manuscript's
`‖f‖_{L^q(0,∞;H^s(R³))}`: an infimum of `eLpNorm G q forceTimeMeasure` over the
*angular* order-`s` datum paths `G` of `f`, in the unitary convention
`ẑ(ξ) = (2π)^{-3/2} ∫ e^{-i x·ξ} z(x) dx` fixed at `01-introduction.tex:91`.

Every scaling estimate available upstream lives instead in Mathlib's
cycles-per-unit-length convention, through
`NSFormalization.Source.vectorFourierSobolevNorm`.  The two conventions are
two-sidedly equivalent with the explicit constant
`Source.frequencyUnit ^ |s| = (2π)^{|s|}`
(`Source/FourierConvention.lean:15`, `Source/AngularForceNorms.lean:19`).

This module is the single place where that constant is paid.  It

* takes the datum infimum against the concrete angular path built in
  `NSFormalization.Section4.I03.Angular` (`forceSobolevENorm_le_cycles`);
* records the cycles-side scaling bounds for the rescaled packet force
  `F_ε = Source.parabolicForce ε⁻¹ t₀ x₀ F` of `04-whole-space.tex:63-78`
  (`cycles_packet_positive`, `cycles_packet_negative`, `cycles_packet_mono`);
* records that the profile constants appearing on their right-hand sides are
  finite (`profile_positive_finite`, `profile_homogeneous_finite`);
* packages the two into the one shape the assembly layer consumes,
  `sobolev_bound_of_cycles`, which turns a cycles-side bound
  `‖·‖ ≤ ofReal b * S` into `forceSobolevENorm q s F ≤ ENNReal.ofReal (C * b)`
  with `C = (2π)^{|s|} * S.toReal`.

The `(2π)^{|s|}` factor is therefore never visible downstream: it is absorbed
into the existential constants of `eq:RpositiveScale` and `eq:RnegativeScale`,
which is legitimate precisely because it does not depend on `ε`.
-/

noncomputable section

namespace BlowupDensity.Bindings

open MeasureTheory Filter Topology
open NSFormalization
open scoped ContDiff ENNReal Topology

/-! ## 1. The datum-infimum step -/

/-- `01-introduction.tex:125` eq:time-norms against `01-introduction.tex:91`.
The contract's angular force norm of a smooth compactly supported field is
bounded by the cycles-convention time norm, with the single convention constant
`(2π)^{|s|}`.

The infimum defining `forceSobolevENorm` is tested against the explicit angular
datum path `Section4.I03.angularPath`, which is admissible: it pairs with every
Schwartz test as the physical field does at *every* time
(`angularPath_pairing`), and it is `MemLp`, hence a.e. strongly measurable, on
`forceTimeMeasure` (`memLp_angularPath`). -/
theorem forceSobolevENorm_le_cycles (s : ℝ) (q : ℝ≥0∞) {F : Contracts.V1.VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    Contracts.V1.Data.forceSobolevENorm q s F ≤
      ENNReal.ofReal (NSFormalization.Source.frequencyUnit ^ |s|) *
        eLpNorm (NSFormalization.Source.vectorFourierSobolevNorm s F) q volume := by
  refine le_trans (iInf_le _ ⟨Section4.I03.angularPath s F hF hc,
    fun t _ i ψ => Section4.I03.angularPath_pairing s F hF hc t i ψ,
    (Section4.I03.memLp_angularPath s F hF hc q).aestronglyMeasurable⟩) ?_
  exact Section4.I03.eLpNorm_angularPath_le s F hF hc q

/-! ## 2. Cycles-convention bounds for the rescaled packet force -/

/-- Strong measurability of each cycles-convention component profile of a smooth
field, the side condition of `Source.eLpNorm_vector_le_sum`. -/
private theorem aestronglyMeasurable_component (s : ℝ) {F : Contracts.V1.VelocityField}
    (hF : ContDiff ℝ ∞ F) (i : Fin 3) :
    AEStronglyMeasurable (fun t => Source.fourierSobolevNorm s
      (fun x => Source.coordinateForce F i (t, x))) volume :=
  (Paper3.stronglyMeasurable_fourierSobolev_time s
    (Source.coordinateForce_smooth hF i).continuous).aestronglyMeasurable

/-- Each component of the parabolically rescaled field is the scalar parabolic
rescaling of the corresponding component of the profile, after the harmless
spatial translation by `x₀`; `Source.coordinate_norm_parabolicForce`. -/
private theorem component_parabolic_rw (s k t₀ : ℝ) (x₀ : Contracts.V1.Space)
    (F : Contracts.V1.VelocityField) (i : Fin 3) :
    (fun t => Source.fourierSobolevNorm s
        (fun x => Source.coordinateForce (Source.parabolicForce k t₀ x₀ F) i (t, x))) =
      fun t => Source.fourierSobolevNorm s
        (Source.parabolicComplexForce k t₀ (fun t x => Source.coordinateForce F i (t, x)) t) :=
  funext fun t => Source.coordinate_norm_parabolicForce s k t₀ x₀ F i t

/-- `04-whole-space.tex:61-66` eq:RpositiveScale, line 1, on the cycles side.
For a nonnegative Sobolev order the rescaled packet force obeys the parabolic
scaling law with exponent `2/q - 3/2 - s`, against the *inhomogeneous* profile
constant of the unrescaled field.

`hs1 : s ≤ 1` is not used by the inequality itself; it is retained because it
is the range in which `profile_positive_finite` makes the right-hand side
finite, and so the range in which the display is meaningful. -/
theorem cycles_packet_positive {F : Contracts.V1.VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (q : ℝ≥0∞) (hq : 1 ≤ q)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (t₀ : ℝ) (x₀ : Contracts.V1.Space) :
    eLpNorm (NSFormalization.Source.vectorFourierSobolevNorm s
        (NSFormalization.Source.parabolicForce ε⁻¹ t₀ x₀ F)) q volume ≤
      ENNReal.ofReal (ε ^ (2 / q.toReal - 3 / 2 - s)) *
        ∑ i : Fin 3, eLpNorm (fun t => NSFormalization.Source.fourierSobolevNorm s
          (fun x => NSFormalization.Source.coordinateForce F i (t, x))) q volume := by
  have _ := hs1
  refine le_trans (Source.eLpNorm_vector_le_sum s _ q hq (fun i =>
    aestronglyMeasurable_component s (Source.parabolicForce_smooth _ _ _ hF) i)) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [component_parabolic_rw s ε⁻¹ t₀ x₀ F i]
  exact Source.force_eLpNorm_positive_epsilon hs0 hε hε1 t₀ q _
    (Paper3.compact_spacetime_fourier_slice_continuous
      (Source.coordinateForce_smooth hF i) (Source.coordinateForce_compact hc i))
    (Paper3.compact_spacetime_bessel_slices s
      (Source.coordinateForce_smooth hF i) (Source.coordinateForce_compact hc i))
    (Paper3.stronglyMeasurable_fourierSobolev_time s
      (Source.coordinateForce_smooth hF i).continuous)

/-- `04-whole-space.tex:72-75` eq:RnegativeScale, packet half, on the cycles side.
For a nonpositive Sobolev order the same parabolic exponent `2/q - 3/2 - s` is
achieved, now against the *homogeneous* profile constant of the unrescaled
field, which is what makes the estimate `ε`-uniform below the critical order.

The lower bound `hlo : -3/2 < s` is the exact range in which the homogeneous
weight `|ξ|^{2s}` is locally integrable on `R³`, i.e. in which the profile
energies on the right are finite at all
(`Paper3.compact_fourier_homogeneous_negative_integrable`); it is a genuine
hypothesis of the underlying scalar estimate, not a convenience. -/
theorem cycles_packet_negative {F : Contracts.V1.VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (q : ℝ≥0∞) (hq : 1 ≤ q)
    {s : ℝ} (hlo : -3 / 2 < s) (hs0 : s ≤ 0) {ε : ℝ} (hε : 0 < ε)
    (t₀ : ℝ) (x₀ : Contracts.V1.Space) :
    eLpNorm (NSFormalization.Source.vectorFourierSobolevNorm s
        (NSFormalization.Source.parabolicForce ε⁻¹ t₀ x₀ F)) q volume ≤
      ENNReal.ofReal (ε ^ (2 / q.toReal - 3 / 2 - s)) *
        ∑ i : Fin 3, eLpNorm (fun t => NSFormalization.Source.homogeneousFourierNorm s
          (fun x => NSFormalization.Source.coordinateForce F i (t, x))) q volume := by
  refine le_trans (Source.eLpNorm_vector_le_sum s _ q hq (fun i =>
    aestronglyMeasurable_component s (Source.parabolicForce_smooth _ _ _ hF) i)) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [component_parabolic_rw s ε⁻¹ t₀ x₀ F i]
  refine Source.force_eLpNorm_negative_epsilon hs0 hε t₀ q _
    (Paper3.compact_spacetime_fourier_slice_continuous
      (Source.coordinateForce_smooth hF i) (Source.coordinateForce_compact hc i))
    (fun t => Paper3.compact_fourier_homogeneous_negative_integrable hlo hs0 _
      ((Source.coordinateForce_smooth hF i).comp (contDiff_const.prodMk contDiff_id))
      (Paper3.compact_spatial_slice (Source.coordinateForce_compact hc i) t))
    (Paper3.stronglyMeasurable_homogeneousFourier_time s
      (Source.coordinateForce_smooth hF i).continuous)

/-- `04-whole-space.tex:78`, on the cycles side: at a *fixed* `ε` the Sobolev
index may be lowered freely, `H^r ⊆ H^s` for `s ≤ r`, so a packet estimate at
the higher index `r` dominates the norm at the lower index `s`.  This is the
step that reaches orders `s ≤ -3/2`, where no direct homogeneous scaling claim
is available. -/
theorem cycles_packet_mono {F : Contracts.V1.VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (q : ℝ≥0∞) (hq : 1 ≤ q)
    {s r : ℝ} (hsr : s ≤ r) {ε : ℝ} (hε : 0 < ε) (t₀ : ℝ) (x₀ : Contracts.V1.Space) :
    eLpNorm (NSFormalization.Source.vectorFourierSobolevNorm s
        (NSFormalization.Source.parabolicForce ε⁻¹ t₀ x₀ F)) q volume ≤
      ∑ i : Fin 3, eLpNorm (fun t => NSFormalization.Source.fourierSobolevNorm r
        (NSFormalization.Source.parabolicComplexForce ε⁻¹ t₀
          (fun t x => NSFormalization.Source.coordinateForce F i (t, x)) t)) q volume := by
  refine le_trans (Source.eLpNorm_vector_le_sum s _ q hq (fun i =>
    aestronglyMeasurable_component s (Source.parabolicForce_smooth _ _ _ hF) i)) ?_
  refine Finset.sum_le_sum fun i _ => ?_
  rw [component_parabolic_rw s ε⁻¹ t₀ x₀ F i]
  exact Source.scalar_force_eLpNorm_mono hsr (inv_ne_zero (ne_of_gt hε)) t₀ q
    (Source.coordinateForce_smooth hF i) (Source.coordinateForce_compact hc i)

/-! ## 3. Finiteness of the profile constants -/

/-- The inhomogeneous profile constant of `eq:RpositiveScale` is finite for every
time exponent, on the whole range `s ≤ 1` of the display: each component profile
is a compactly supported bounded function of time
(`Paper3.memLp_fourierSobolev_le_one_time`). -/
theorem profile_positive_finite {F : Contracts.V1.VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (q : ℝ≥0∞) {s : ℝ} (hs1 : s ≤ 1) :
    (∑ i : Fin 3, eLpNorm (fun t => NSFormalization.Source.fourierSobolevNorm s
      (fun x => NSFormalization.Source.coordinateForce F i (t, x))) q volume) ≠ ⊤ :=
  ENNReal.sum_ne_top.mpr fun i _ =>
    (Paper3.memLp_fourierSobolev_le_one_time hs1 (Source.coordinateForce_smooth hF i)
      (Source.coordinateForce_compact hc i) q).eLpNorm_ne_top

/-- The homogeneous profile constant of `eq:RnegativeScale` is finite exactly on
`-3/2 < s ≤ 0`, the range in which `|ξ|^{2s}` is locally integrable on `R³`
(`Paper3.memLp_homogeneousFourier_time`). -/
theorem profile_homogeneous_finite {F : Contracts.V1.VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (q : ℝ≥0∞) {s : ℝ}
    (hlo : -3 / 2 < s) (hs0 : s ≤ 0) :
    (∑ i : Fin 3, eLpNorm (fun t => NSFormalization.Source.homogeneousFourierNorm s
      (fun x => NSFormalization.Source.coordinateForce F i (t, x))) q volume) ≠ ⊤ :=
  ENNReal.sum_ne_top.mpr fun i _ =>
    (Paper3.memLp_homogeneousFourier_time hlo hs0 (Source.coordinateForce_smooth hF i)
      (Source.coordinateForce_compact hc i) q).eLpNorm_ne_top

/-! ## 4. Collapsing the convention constant into a single real constant -/

/-- The `ℝ≥0∞` arithmetic behind the absorption of `(2π)^{|s|}`: a product of a
nonnegative real constant, a nonnegative real scaling factor and a *finite*
extended-real profile constant is the `ENNReal.ofReal` of the corresponding real
product.  Finiteness of `S` is what makes `S = ENNReal.ofReal S.toReal`. -/
theorem ofReal_rpow_mul_le (A : ℝ) (hA : 0 ≤ A) {b : ℝ} (hb : 0 ≤ b) (S : ℝ≥0∞) (hS : S ≠ ⊤) :
    ENNReal.ofReal A * (ENNReal.ofReal b * S) = ENNReal.ofReal (A * S.toReal * b) := by
  conv_lhs => rw [← ENNReal.ofReal_toReal hS]
  rw [← ENNReal.ofReal_mul hb, ← ENNReal.ofReal_mul hA]
  congr 1
  ring

/-- The one lemma the Section 4 assembly layer calls: any cycles-side bound of
the shape `‖F‖_cycles ≤ ENNReal.ofReal b * S` with `b ≥ 0` and `S` finite
transports to the contract's angular norm as a *single* real bound
`C * b` with `C = (2π)^{|s|} * S.toReal ≥ 0`.

Applied with `b = ε ^ (2/q - 3/2 - s)` and `S` the profile constant, this is
exactly `04-whole-space.tex:63-78` eq:RpositiveScale / eq:RnegativeScale in the
manuscript's own normalization; the convention constant has been absorbed into
`C`, which is legitimate because it is independent of `ε`. -/
theorem sobolev_bound_of_cycles {F : Contracts.V1.VelocityField} (s : ℝ) (q : ℝ≥0∞)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) {b : ℝ} (hb : 0 ≤ b) {S : ℝ≥0∞} (hS : S ≠ ⊤)
    (h : eLpNorm (NSFormalization.Source.vectorFourierSobolevNorm s F) q volume ≤
          ENNReal.ofReal b * S) :
    Contracts.V1.Data.forceSobolevENorm q s F ≤
      ENNReal.ofReal (NSFormalization.Source.frequencyUnit ^ |s| * S.toReal * b) := by
  refine le_trans (forceSobolevENorm_le_cycles s q hF hc) ?_
  refine le_trans (mul_le_mul_right h _) (le_of_eq ?_)
  exact ofReal_rpow_mul_le _ (Real.rpow_nonneg Source.frequencyUnit_pos.le _) hb S hS

/-! ## 5. Transport of convergence -/

/-- `04-whole-space.tex:63-78`, limiting form: a family of smooth compactly
supported forces whose cycles-convention time norms vanish as `ε → 0⁺` also has
vanishing contract force norms.  A squeeze against the constant multiple
`(2π)^{|s|} · ‖·‖_cycles`, the same argument as
`Source.angular_family_tendsto_zero`.

Compact support is only required at positive `ε`, which is all the filter
`𝓝[>] 0` ever sees. -/
theorem forceSobolevENorm_tendsto_zero (s : ℝ) (q : ℝ≥0∞) {F : ℝ → Contracts.V1.VelocityField}
    (hF : ∀ ε, ContDiff ℝ ∞ (F ε)) (hc : ∀ ε, 0 < ε → HasCompactSupport (F ε))
    (hlim : Filter.Tendsto (fun ε : ℝ =>
        eLpNorm (NSFormalization.Source.vectorFourierSobolevNorm s (F ε)) q volume)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Filter.Tendsto (fun ε : ℝ => Contracts.V1.Data.forceSobolevENorm q s (F ε))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hm := ENNReal.Tendsto.const_mul hlim
    (a := ENNReal.ofReal (Source.frequencyUnit ^ |s|)) (Or.inr ENNReal.ofReal_ne_top)
  simp only [mul_zero] at hm
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hm
  · exact Eventually.of_forall fun _ => bot_le
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact forceSobolevENorm_le_cycles s q (hF ε) (hc ε hε)

end BlowupDensity.Bindings
