import NSFormalization.Section4.I02.Mixed
import NSFormalization.Source.MixedForceScaling

/-!
# I03: `eq:packetFscale` as an exact mixed Lebesgue identity

`paper/sections/03-torus.tex:129-132` states, for `1 ≤ p, q ≤ ∞`,
`‖F_ε‖_{L^q(0,∞;L^p)} = ε^{α(p,q)} ‖F‖_{L^q(0,∞;L^p)}` with
`α(p,q) = -3 + 3/p + 2/q`, where `F_ε = Source.parabolicForce ε⁻¹ (T - ε²) x₀ F`.
The proof at `03-torus.tex:148-149` is the change of variables
`y = (x - x₀)/ε`, `σ = (t - t_ε)/ε²`: "the force's spatial norm gains
`ε^{-3+3/p}` and its time norm gains `ε^{2/q}`", the essential-supremum
endpoints included through the convention `1/∞ = 0`.

Everything here is an *equality*, not the inequality of
`Source.compact_force_mixed_bound`: the two change-of-variable identities
`Paper1.CorrectionMixedNorms.eLpNorm_spatial_scale` and
`Source.eLpNorm_parabolic_time` are already exact, and `ENNReal.toReal_mul`
splits the intermediate product unconditionally, so no majorant is needed.

The time norms are over `(0,∞)` on both sides, as the registered Section 4 norm
`Contracts.V1.Data.mixedLebesgueENorm` demands.  That is legitimate exactly as
the manuscript says: `t_ε = T - ε² > 0` and `F` vanishes at nonpositive times,
so every nonpositive-time slice of `F_ε` vanishes too, and restricting the time
measure to `Ioi 0` changes neither side (`positiveMixedNorm_eq_volume`).

`eLpNorm_slicePath_eq` upgrades the `≤` inside `I02.exists_slicePath` to the
equality `verification/Bindings/` needs to turn the infimum defining
`Contracts.V1.Data.mixedLebesgueENorm` into `positiveMixedNorm`.  Nothing below
mentions the contract.
-/

noncomputable section

namespace NSFormalization.Section4.I03

open NavierStokes NavierStokes.ProblemStatement
open Set MeasureTheory
open scoped ContDiff ENNReal

/-- `‖F‖_{L^q(0,∞;L^p)}`: the mixed Lebesgue norm of
`Paper1.CorrectionMixedNorms.mixedNorm` with the time integral restricted to the
positive half line, which is the domain of `eq:packetFscale`. -/
def positiveMixedNorm (p q : ℝ≥0∞) (F : VelocityField) : ℝ≥0∞ :=
  eLpNorm (fun t : ℝ => (eLpNorm (fun x : Space => F (t, x)) p volume).toReal) q
    Paper3.positiveTimeMeasure

/-- For a field whose nonpositive-time slices vanish, the `(0,∞)` time norm and
the time norm over all of `ℝ` agree: the real integrand is supported in `Ioi 0`,
so it is its own indicator there. -/
theorem positiveMixedNorm_eq_volume {F : VelocityField} (p q : ℝ≥0∞)
    (hzero : ∀ t : ℝ, t ≤ 0 → (fun x : Space => F (t, x)) = 0) :
    positiveMixedNorm p q F = Paper1.CorrectionMixedNorms.mixedNorm p q F := by
  have hind : Set.indicator (Set.Ioi (0 : ℝ))
      (fun t : ℝ => (eLpNorm (fun x : Space => F (t, x)) p volume).toReal)
      = fun t : ℝ => (eLpNorm (fun x : Space => F (t, x)) p volume).toReal := by
    funext t
    by_cases ht : (0 : ℝ) < t
    · exact Set.indicator_of_mem ht _
    · have ht' : t ∉ Set.Ioi (0 : ℝ) := ht
      rw [Set.indicator_of_notMem ht', hzero t (not_lt.mp ht)]
      simp
  show eLpNorm (fun t : ℝ => (eLpNorm (fun x : Space => F (t, x)) p volume).toReal) q
      (volume.restrict (Set.Ioi 0)) = _
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict (μ := (volume : Measure ℝ))
    (p := q) measurableSet_Ioi, hind]
  rfl

/-- The exact spatial half of `eq:packetFscale`: a parabolically concentrated
force gains the factor `k^{3 - 3/p}` in its spatial `L^p` norm, the source being
evaluated at the rescaled time.  This is the `ℝ≥0∞` form of
`Source.spatial_force_norm_real`, which loses the `⊤` case through `.toReal`. -/
theorem spatial_slice_norm_parabolicForce {F : VelocityField} (hF : Continuous F)
    (p : ℝ≥0∞) {k : ℝ} (hk : 0 < k) (t₀ : ℝ) (x₀ : Space) (t : ℝ) :
    eLpNorm (fun x : Space => Source.parabolicForce k t₀ x₀ F (t, x)) p volume =
      ENNReal.ofReal (k ^ (3 - 3 / p.toReal)) *
        eLpNorm (fun x : Space => F (k ^ 2 * (t - t₀), x)) p volume := by
  have hsm : StronglyMeasurable (fun x : Space => F (k ^ 2 * (t - t₀), x)) :=
    (hF.comp (continuous_const.prodMk continuous_id)).stronglyMeasurable
  have hrw : (fun x : Space => Source.parabolicForce k t₀ x₀ F (t, x)) =
      k ^ 3 • (fun x : Space => (fun y : Space => F (k ^ 2 * (t - t₀), y)) (k • (x - x₀))) := rfl
  rw [hrw, eLpNorm_const_smul,
    Paper1.CorrectionMixedNorms.eLpNorm_spatial_scale _ hsm p hk x₀, ← mul_assoc]
  congr 1
  rw [Real.enorm_eq_ofReal_abs, abs_of_pos (pow_pos hk 3),
    ← ENNReal.ofReal_mul (pow_nonneg hk.le 3)]
  congr 1
  conv_lhs => arg 1; rw [← Real.rpow_natCast k 3]
  rw [← Real.rpow_add hk]
  congr 1
  push_cast
  ring

set_option linter.unusedVariables false in
/-- `eq:packetFscale` over all of `ℝ` in time: an exact identity, not an
estimate.  The spatial norm contributes `ε^{-3+3/p}` and the parabolic time
change of variables contributes `ε^{2/q}`, for every `p, q`, the
essential-supremum endpoints included via `p.toReal = 0`, `q.toReal = 0`.

`hc` is not consumed by this exact identity -- unlike
`Source.compact_force_mixed_bound`, no majorant is built -- but it is kept in the
signature so that the whole `eq:packetFscale` chain takes the same compactly
supported smooth profile hypotheses. -/
theorem mixedNorm_parabolicForce {F : VelocityField} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) {ε : ℝ} (hε : 0 < ε) (t₀ : ℝ) (x₀ : Space) (p q : ℝ≥0∞) :
    Paper1.CorrectionMixedNorms.mixedNorm p q (Source.parabolicForce ε⁻¹ t₀ x₀ F) =
      ENNReal.ofReal (ε ^ (-3 + 3 / p.toReal + 2 / q.toReal)) *
        Paper1.CorrectionMixedNorms.mixedNorm p q F := by
  have hk : 0 < ε⁻¹ := inv_pos.mpr hε
  have hg : StronglyMeasurable
      (fun t : ℝ => (eLpNorm (fun x : Space => F (t, x)) p volume).toReal) :=
    (Paper1.CorrectionMixedNorms.spatial_norm_measurable hF.continuous p).stronglyMeasurable
  have hslice : (fun t : ℝ => (eLpNorm (fun x : Space =>
        Source.parabolicForce ε⁻¹ t₀ x₀ F (t, x)) p volume).toReal)
      = (ε⁻¹) ^ (3 - 3 / p.toReal) •
        (fun t : ℝ => (eLpNorm (fun x : Space =>
          F ((ε⁻¹) ^ 2 * (t - t₀), x)) p volume).toReal) := by
    funext t
    rw [spatial_slice_norm_parabolicForce hF.continuous p hk t₀ x₀ t, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.rpow_nonneg hk.le _)]
    rfl
  have htime := Source.eLpNorm_parabolic_time
    (fun t : ℝ => (eLpNorm (fun x : Space => F (t, x)) p volume).toReal) hg q hk t₀
  show eLpNorm (fun t : ℝ => (eLpNorm (fun x : Space =>
    Source.parabolicForce ε⁻¹ t₀ x₀ F (t, x)) p volume).toReal) q volume = _
  rw [hslice, eLpNorm_const_smul, htime, ← mul_assoc]
  congr 1
  rw [Real.enorm_eq_ofReal_abs, abs_of_pos (Real.rpow_pos_of_pos hk _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hk.le _), ← Real.rpow_add hk,
    Real.inv_rpow hε.le, ← Real.rpow_neg hε.le,
    show -(3 - 3 / p.toReal + -2 / q.toReal) = -3 + 3 / p.toReal + 2 / q.toReal from by ring]

/-- `eq:packetFscale` in the form the manuscript states it, over `(0,∞)`:
`‖F_ε‖_{L^q(0,∞;L^p)} = ε^{α(p,q)} ‖F‖_{L^q(0,∞;L^p)}` with
`α(p,q) = -3 + 3/p + 2/q`, for `F_ε = Source.parabolicForce ε⁻¹ (T - ε²) x₀ F`.

Restricting to positive time is harmless on both sides: `T - ε² ≥ 0`, so for
`t ≤ 0` the source time `ε⁻²(t - (T - ε²))` is nonpositive and `hzero` kills the
slice of `F_ε` there, exactly the argument of `03-torus.tex:148`. -/
theorem positiveMixedNorm_parabolicForce {F : VelocityField} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hzero : ∀ t : ℝ, t ≤ 0 → ∀ x : Space, F (t, x) = 0)
    {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T - ε ^ 2) (x₀ : Space) (p q : ℝ≥0∞) :
    positiveMixedNorm p q (Source.parabolicForce ε⁻¹ (T - ε ^ 2) x₀ F) =
      ENNReal.ofReal (ε ^ (-3 + 3 / p.toReal + 2 / q.toReal)) * positiveMixedNorm p q F := by
  have hFzero : ∀ t : ℝ, t ≤ 0 → (fun x : Space => F (t, x)) = 0 :=
    fun t ht => funext (hzero t ht)
  have hεzero : ∀ t : ℝ, t ≤ 0 →
      (fun x : Space => Source.parabolicForce ε⁻¹ (T - ε ^ 2) x₀ F (t, x)) = 0 := by
    intro t ht
    have h1 : t - (T - ε ^ 2) ≤ 0 := by linarith
    have h2 : (0 : ℝ) ≤ (ε⁻¹) ^ 2 := sq_nonneg _
    have hs : (ε⁻¹) ^ 2 * (t - (T - ε ^ 2)) ≤ 0 := by nlinarith
    funext x
    show (ε⁻¹) ^ 3 • F ((ε⁻¹) ^ 2 * (t - (T - ε ^ 2)), ε⁻¹ • (x - x₀)) = 0
    rw [hzero _ hs, smul_zero]
  rw [positiveMixedNorm_eq_volume p q hεzero, positiveMixedNorm_eq_volume p q hFzero,
    mixedNorm_parabolicForce hF hc hε (T - ε ^ 2) x₀ p q]

/-- The canonical `L^p`-valued slice path of a continuous compactly supported
field has time norm *equal* to `positiveMixedNorm`, not merely bounded by it.
`I02.exists_slicePath` only needs the inequality; the infimum defining
`Contracts.V1.Data.mixedLebesgueENorm` needs this equality to be transported
in both directions. -/
theorem eLpNorm_slicePath_eq (p : ℝ≥0∞) [Fact (1 ≤ p)] {F : VelocityField}
    (hF : Continuous F) (hc : HasCompactSupport F) (q : ℝ≥0∞) :
    eLpNorm (fun t : ℝ => (I02.slice_memLp hF hc p t).toLp (fun x : Space => F (t, x))) q
        Paper3.positiveTimeMeasure = positiveMixedNorm p q F := by
  refine eLpNorm_congr_enorm_ae (Filter.Eventually.of_forall (fun t => ?_))
  rw [Lp.enorm_toLp, Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (I02.slice_memLp hF hc p t).eLpNorm_lt_top.ne]

end NSFormalization.Section4.I03
