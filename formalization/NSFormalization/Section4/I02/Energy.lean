import NSFormalization.Paper1.InsertionEnergy
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# I02, unit 8: the `E_T` bound in the canonical `ENNReal` energy norm

`paper/sections/03-torus.tex:234` eq:wE asserts `‖w_ε‖_{E_T} ≤ C ε^{3/2}`, with
`E_T = L^∞_t L²_x ∩ L²_t Ḣ¹_x` on `(0,T)` (`01-introduction.tex:143` eq:Enorm).
The tree proves the two *squared halves* separately, in the real-valued
`InsertionEnergy.energyNorm`
(`CorrectionEnergy.physicalCorrection_uniform_energy`,
`InsertionEnergy.correction_gradientSquare_bound`), and never assembles them for
the pure correction.  Section 4's registered norm is instead the
`ENNReal`-valued `Contracts.V1.Data.energyENorm`, whose two summands are
`essSup (fun t => eLpNorm (w t ·) 2 volume)` and
`(∫⁻ t in Ioo 0 T, (eLpNorm (∇w t ·) 2 volume)^2)^{1/2}`.

This module does the transport: it identifies the spatial `eLpNorm` with
`ENNReal.ofReal ∘ Real.sqrt` of the Bochner square integral, identifies the
`PiLp 2` gradient norm with `NavierStokesR3.CompactEnergy.dissipation`, and
concludes the two `ENNReal` bounds from the two real squared bounds.  Nothing
below mentions the contract; the last step is in
`verification/Bindings/Correction.lean`, where `energyENorm` unfolds by `rfl`
to exactly the two expressions bounded here.
-/

noncomputable section

namespace NSFormalization.Section4.I02

open NavierStokes NavierStokes.ProblemStatement NavierStokesR3.CompactEnergy
open Set MeasureTheory Filter
open scoped ContDiff ENNReal Topology

/-- The spatial gradient assembled as a Euclidean three-vector of vectors, so
that its norm is the Frobenius quantity of `01-introduction.tex:145` eq:Enorm.
Written exactly as `Contracts.V1.Data.spatialGradient`, which the binding
identifies with it by `rfl`. -/
def spatialGradient (z : VelocityField) (t : ℝ) (x : Space) : WithLp 2 (Fin 3 → Space) :=
  WithLp.toLp 2 (fun i => spatialDerivative z t x (coordinateVector i))

theorem norm_spatialGradient_sq (z : VelocityField) (t : ℝ) (x : Space) :
    ‖spatialGradient z t x‖ ^ 2 =
      ∑ i : Fin 3, ‖spatialDerivative z t x (coordinateVector i)‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => Space) _

/-- The spatial gradient of a smooth field is continuous in space. -/
theorem continuous_spatialGradient {w : VelocityField} (hw : ContDiff ℝ ∞ w) (t : ℝ) :
    Continuous (fun x : Space => spatialGradient w t x) := by
  have hs : ContDiff ℝ ∞ (fun y : Space => w (t, y)) :=
    hw.comp (contDiff_const.prodMk contDiff_id)
  have hd : Continuous (fun x : Space => fderiv ℝ (fun y : Space => w (t, y)) x) :=
    (hs.fderiv_right (m := ∞) (by simp)).continuous
  have hpi : Continuous
      (fun x : Space => (fun i : Fin 3 => spatialDerivative w t x (coordinateVector i))) :=
    continuous_pi (fun i => hd.clm_apply continuous_const)
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 => Space)).comp hpi

/-- Each spatial slice of a smooth compactly supported spacetime field has
compact support. -/
theorem slice_hasCompactSupport {w : VelocityField} (hc : HasCompactSupport w) (t : ℝ) :
    HasCompactSupport (fun x : Space => w (t, x)) :=
  (hc.isCompact.image continuous_snd).of_isClosed_subset (isClosed_tsupport _)
    (Source.LocalizedInsertion.slice_support_projection hc t)

/-- The spatial gradient of a compactly supported smooth field has compact
support in each slice. -/
theorem hasCompactSupport_spatialGradient {w : VelocityField} (hc : HasCompactSupport w)
    (t : ℝ) : HasCompactSupport (fun x : Space => spatialGradient w t x) := by
  refine HasCompactSupport.intro (slice_hasCompactSupport hc t) (fun x hx => ?_)
  have hz : fderiv ℝ (fun y : Space => w (t, y)) x = 0 := fderiv_of_notMem_tsupport ℝ hx
  simp only [spatialGradient, spatialDerivative, hz]
  rfl

/-- Every spatial gradient slice of a smooth compactly supported field lies in
every `L^p`; in particular the second summand of `E_T` has honest `L²`
slices. -/
theorem spatialGradient_memLp {w : VelocityField} (hw : ContDiff ℝ ∞ w)
    (hc : HasCompactSupport w) (p : ℝ≥0∞) (t : ℝ) :
    MemLp (fun x : Space => spatialGradient w t x) p volume :=
  (continuous_spatialGradient hw t).memLp_of_hasCompactSupport
    (hasCompactSupport_spatialGradient hc t)

/-- The `L²` seminorm of a square-integrable spatial field is the extended real
square root of its Bochner square integral: no totalization gap. -/
theorem eLpNorm_two_eq_ofReal_sqrt {E : Type*} [NormedAddCommGroup E] {f : Space → E}
    (hf : Integrable (fun x : Space => ‖f x‖ ^ 2) volume) :
    eLpNorm f 2 volume = ENNReal.ofReal (Real.sqrt (∫ x : Space, ‖f x‖ ^ 2)) := by
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), h2]
  have hpt : ∀ x : Space, ‖f x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖f x‖ ^ 2) := by
    intro x
    rw [← ofReal_norm,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2), Real.rpow_two]
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hf
      (Filter.Eventually.of_forall (fun x => sq_nonneg (‖f x‖))),
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg (fun x => sq_nonneg (‖f x‖)))
      (by norm_num : (0:ℝ) ≤ 1 / 2), Real.sqrt_eq_rpow]

/-- The `L∞_t L²_x` half of `E_T`, bounded by the uniform squared bound. -/
theorem energyEssSup_le {T A : ℝ} {w : VelocityField}
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hb : ∀ t : ℝ, (∫ x : Space, ‖w (t, x)‖ ^ 2) ≤ A) :
    essSup (fun t => eLpNorm (fun x : Space => w (t, x)) 2 volume)
        (volume.restrict (Ioo (0 : ℝ) T)) ≤ ENNReal.ofReal (Real.sqrt A) := by
  refine essSup_le_of_ae_le _ (Filter.Eventually.of_forall (fun t => ?_))
  have hi : Integrable (fun x : Space => ‖w (t, x)‖ ^ 2) volume :=
    integrable_norm_sq (hw.continuous.comp (continuous_const.prodMk continuous_id))
      (slice_hasCompactSupport hc t)
  show eLpNorm (fun x : Space => w (t, x)) 2 volume ≤ ENNReal.ofReal (Real.sqrt A)
  rw [eLpNorm_two_eq_ofReal_sqrt hi]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (hb t))

/-- The squared spatial gradient `eLpNorm` is exactly the dissipation rate. -/
theorem eLpNorm_spatialGradient_sq {w : VelocityField}
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w) (t : ℝ) :
    (eLpNorm (fun x : Space => spatialGradient w t x) 2 volume) ^ (2 : ℝ) =
      ENNReal.ofReal (dissipation w t) := by
  have hs : ContDiff ℝ ∞ (fun y : Space => w (t, y)) :=
    hw.comp (contDiff_const.prodMk contDiff_id)
  have hcs : HasCompactSupport (fun y : Space => w (t, y)) := slice_hasCompactSupport hc t
  have hcomp : ∀ i : Fin 3,
      Integrable (fun x : Space => ‖spatialDerivative w t x (coordinateVector i)‖ ^ 2) volume :=
    fun i => Paper1.InsertionEnergy.spatial_gradient_square_integrable hs hcs (coordinateVector i)
  have hsum : Integrable (fun x : Space => ‖spatialGradient w t x‖ ^ 2) volume := by
    simp_rw [norm_spatialGradient_sq]
    exact integrable_finsetSum _ (fun i _ => hcomp i)
  have hval : (∫ x : Space, ‖spatialGradient w t x‖ ^ 2) = dissipation w t := by
    simp_rw [norm_spatialGradient_sq]
    rw [integral_finsetSum _ (fun i _ => hcomp i)]
    simp only [dissipation, NavierStokes.PeriodicIntegration.spatialPartial,
      spatialDerivative]
  rw [eLpNorm_two_eq_ofReal_sqrt hsum, hval,
    ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 2),
    Real.rpow_two, Real.sq_sqrt (dissipation_nonneg w t)]

/-- The `L²_t Ḣ¹_x` half of `E_T`, bounded by the squared gradient bound. -/
theorem energyGradient_le {T D : ℝ} {w : VelocityField}
    (hw : ContDiff ℝ ∞ w) (hc : HasCompactSupport w)
    (hi : IntegrableOn (dissipation w) (Ioo (0 : ℝ) T))
    (hD : (∫ t in Ioo (0 : ℝ) T, dissipation w t) ≤ D) :
    (∫⁻ t in Ioo (0 : ℝ) T,
        (eLpNorm (fun x : Space => spatialGradient w t x) 2 volume) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)
      ≤ ENNReal.ofReal (Real.sqrt D) := by
  have hinner : ∀ t : ℝ,
      (eLpNorm (fun x : Space => spatialGradient w t x) 2 volume) ^ (2 : ℝ) =
        ENNReal.ofReal (dissipation w t) := fun t => eLpNorm_spatialGradient_sq hw hc t
  simp_rw [hinner]
  rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun t => dissipation_nonneg w t)),
    ENNReal.ofReal_rpow_of_nonneg
      (setIntegral_nonneg measurableSet_Ioo (fun t _ => dissipation_nonneg w t))
      (by norm_num : (0:ℝ) ≤ (2:ℝ)⁻¹)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [show ((2:ℝ)⁻¹) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  exact Real.sqrt_le_sqrt hD

/-- `√(A ε³) = √A · ε^{3/2}`: the arithmetic that turns the two squared `ε³`
bounds into the manuscript's `ε^{3/2}` rate, `03-torus.tex:275-281`. -/
theorem sqrt_mul_cube {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε) :
    Real.sqrt (A * ε ^ 3) = Real.sqrt A * ε ^ ((3 : ℝ) / 2) := by
  rw [Real.sqrt_mul hA]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ε 3, ← Real.rpow_mul hε]
  norm_num

end NSFormalization.Section4.I02
