import NSFormalization.Section3.T24.AffineBasics
import NSFormalization.Section4.I02.Energy

/-!
# T24a Ua6: finite energy and dissipation of an affine variation

`paper/sections/03-torus.tex:686-687` asserts that every affine variation
`Ũ = U + b` of the packet velocity still has finite energy and dissipation,
`‖Ũ‖_{E_1} < ∞`.

This module proves exactly that, over the **raw** packet field: the only
hypothesis on `U` is the packet clause `‖U‖_{E_1} < ∞` itself, and the variation
`b` ranges over `AffineAdmissible c r τ₀ τ₁` from
`NSFormalization.Section3.T24.AffineBasics` (lane 392), which is imported, not
restated.

## The norm

`E_1` is the registered `BlowupDensity.Contracts.V1.Data.energyENorm 1`
(`verification/Contracts/V1/Data.lean:444-476`),
`‖z‖_{E_T} = ‖z‖_{L^∞(0,T;L²)} + ‖∇z‖_{L²(0,T;L²)}`.  Canonical modules may not
import `Contracts.*`, and no local restatement of the whole-space `E_T` existed
(`Section3.T10.energyENormT` is the *torus* norm), so the three definitions of
`Data.lean:444-476` are restated verbatim in §1 below, on the canonical
`Section4.I02.spatialGradient`, which the contract's `spatialGradient` already
unfolds to.  `research/T24/probes/affine_energy_closes.lean` checks the three
`rfl` bridges against the registered spelling.

## Why no measurability hypothesis on `U`

The textbook route is Minkowski's inequality, `‖U+b‖ ≤ ‖U‖ + ‖b‖`, which in
Lean needs `AEStronglyMeasurable` slices of `U` — a hypothesis the paper clause
does not carry.  Instead every estimate below goes through the elementary
`(x+y)² ≤ 4x² + 4y²` in `ℝ≥0∞` (§2), whose `∫⁻` splitting needs measurability of
the *second* summand only (`lintegral_add_right`); `b` is smooth, so that is
free.  The crude constants are irrelevant: the statement is a finiteness
assertion.

The same care is needed for the gradient: `fderiv` of a sum is the sum of the
`fderiv`s only where both summands are differentiable, so §3 bounds `‖∇(U+b)‖`
by `‖∇U‖ + ‖∇b‖` through a case split, the non-differentiable branch giving
`∇(U+b) = 0` (the `fderiv` junk value) because `b` is smooth.
-/

noncomputable section

namespace NSFormalization.Section3.T24

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.I02 (spatialGradient norm_spatialGradient_sq)
open scoped ContDiff ENNReal BigOperators

/-! ## 1. The whole-space energy norm `E_T`, restated verbatim

Character-for-character `verification/Contracts/V1/Data.lean:444-476`, with the
contract's `spatialGradient` replaced by the canonical
`Section4.I02.spatialGradient` it unfolds to. -/

/-- `01-introduction.tex:145` eq:Enorm, first summand: `‖z‖_{L^∞(0,T;L²(R³))}`.
Verbatim `Contracts.V1.Data.energyEssSup`. -/
def energyEssSup (T : ℝ) (z : VelocityField) : ℝ≥0∞ :=
  essSup (fun t => eLpNorm (fun x => z (t, x)) 2 volume)
    (volume.restrict (Ioo (0 : ℝ) T))

/-- `01-introduction.tex:145` eq:Enorm, second summand:
`‖∇z‖_{L²(0,T;L²(R³))}`.  Verbatim `Contracts.V1.Data.energyGradient`. -/
def energyGradient (T : ℝ) (z : VelocityField) : ℝ≥0∞ :=
  (∫⁻ t in Ioo (0 : ℝ) T,
      (eLpNorm (fun x => spatialGradient z t x) 2 volume) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹)

/-- `01-introduction.tex:143` eq:Enorm:
`‖z‖_{E_T} = ‖z‖_{L^∞(0,T;L²)} + ‖∇z‖_{L²(0,T;L²)}`.
Verbatim `Contracts.V1.Data.energyENorm`. -/
def energyENorm (T : ℝ) (z : VelocityField) : ℝ≥0∞ :=
  energyEssSup T z + energyGradient T z

/-! ## 2. Measurability-free `ℝ≥0∞` plumbing -/

/-- `(x+y)² ≤ 4x² + 4y²` in `ℝ≥0∞`, in the real-exponent form the two `E_T`
summands use.  The constant is deliberately crude: only finiteness is claimed
downstream, and `4` avoids the cross term `2xy`, which has no subtraction-free
proof in `ℝ≥0∞`. -/
theorem add_rpow_two_le (x y : ℝ≥0∞) :
    (x + y) ^ (2 : ℝ) ≤ 4 * x ^ (2 : ℝ) + 4 * y ^ (2 : ℝ) := by
  have hdouble : ∀ w : ℝ≥0∞, ((2 : ℝ≥0∞) * w) ^ (2 : ℝ) = 4 * w ^ (2 : ℝ) := by
    intro w
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    norm_num
  rcases le_total x y with h | h
  · calc (x + y) ^ (2 : ℝ) ≤ ((2 : ℝ≥0∞) * y) ^ (2 : ℝ) := by
          refine ENNReal.rpow_le_rpow ?_ (by norm_num)
          rw [two_mul]
          exact add_le_add h (le_refl y)
      _ = 4 * y ^ (2 : ℝ) := hdouble y
      _ ≤ 4 * x ^ (2 : ℝ) + 4 * y ^ (2 : ℝ) := le_add_self
  · calc (x + y) ^ (2 : ℝ) ≤ ((2 : ℝ≥0∞) * x) ^ (2 : ℝ) := by
          refine ENNReal.rpow_le_rpow ?_ (by norm_num)
          rw [two_mul]
          exact add_le_add (le_refl x) h
      _ = 4 * x ^ (2 : ℝ) := hdouble x
      _ ≤ 4 * x ^ (2 : ℝ) + 4 * y ^ (2 : ℝ) := le_self_add

/-- The squared `L²` seminorm is the plain `∫⁻` of the squared enorm: no
measurability is used, because `eLpNorm` is defined by that integral. -/
theorem rpow_two_eLpNorm_two {E : Type*} [NormedAddCommGroup E] (f : Space → E) :
    (eLpNorm f 2 volume) ^ (2 : ℝ) = ∫⁻ x : Space, ‖f x‖ₑ ^ (2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2, one_div]
  exact ENNReal.rpow_inv_rpow (by norm_num) _

/-- The measurability-free triangle inequality in squared form: if `‖H‖ ≤ ‖F‖ +
‖G‖ pointwise and `G` has a measurable squared enorm, then the squared `L²`
seminorm of `H` is controlled by those of `F` and `G`.  Only `G` needs to be
measurable, because `lintegral_add_right` splits a sum whose *right* summand is
measurable. -/
theorem rpow_two_eLpNorm_add_le {E : Type*} [NormedAddCommGroup E]
    {H F G : Space → E}
    (hpt : ∀ x : Space, ‖H x‖ₑ ≤ ‖F x‖ₑ + ‖G x‖ₑ)
    (hG : Measurable fun x : Space => ‖G x‖ₑ ^ (2 : ℝ)) :
    (eLpNorm H 2 volume) ^ (2 : ℝ) ≤
      4 * (eLpNorm F 2 volume) ^ (2 : ℝ) + 4 * (eLpNorm G 2 volume) ^ (2 : ℝ) := by
  rw [rpow_two_eLpNorm_two, rpow_two_eLpNorm_two, rpow_two_eLpNorm_two]
  calc ∫⁻ x : Space, ‖H x‖ₑ ^ (2 : ℝ)
      ≤ ∫⁻ x : Space, (4 * ‖F x‖ₑ ^ (2 : ℝ) + 4 * ‖G x‖ₑ ^ (2 : ℝ)) := by
        refine lintegral_mono (fun x => ?_)
        exact le_trans (ENNReal.rpow_le_rpow (hpt x) (by norm_num))
          (add_rpow_two_le _ _)
    _ = (∫⁻ x : Space, 4 * ‖F x‖ₑ ^ (2 : ℝ)) + ∫⁻ x : Space, 4 * ‖G x‖ₑ ^ (2 : ℝ) :=
        lintegral_add_right _ (hG.const_mul 4)
    _ = 4 * (∫⁻ x : Space, ‖F x‖ₑ ^ (2 : ℝ)) + 4 * ∫⁻ x : Space, ‖G x‖ₑ ^ (2 : ℝ) := by
        rw [lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]

/-- A field bounded by `√A` in enorm and vanishing off a set `K` has squared `L²`
seminorm at most `A · |K|`.  No measurability of `K` or of the field is used:
`setLIntegral_eq_of_support_subset` restricts the integral by support alone. -/
theorem rpow_two_eLpNorm_le_of_bound {E : Type*} [NormedAddCommGroup E]
    {f : Space → E} {K : Set Space} {A : ℝ}
    (hA : ∀ x : Space, ‖f x‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal A)
    (hz : ∀ x : Space, x ∉ K → f x = 0) :
    (eLpNorm f 2 volume) ^ (2 : ℝ) ≤ ENNReal.ofReal A * volume K := by
  rw [rpow_two_eLpNorm_two]
  have hsupp : Function.support (fun x : Space => ‖f x‖ₑ ^ (2 : ℝ)) ⊆ K := by
    intro x hx
    by_contra hxK
    apply hx
    show ‖f x‖ₑ ^ (2 : ℝ) = 0
    rw [hz x hxK]
    simp [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [← setLIntegral_eq_of_support_subset (μ := volume) hsupp]
  calc (∫⁻ x in K, ‖f x‖ₑ ^ (2 : ℝ))
      ≤ ∫⁻ _x in K, ENNReal.ofReal A := lintegral_mono hA
    _ = ENNReal.ofReal A * volume K := setLIntegral_const _ _

/-! ## 3. Additivity of the spatial gradient, without differentiability of `U` -/

/-- `‖∇(U+b)‖ ≤ ‖∇U‖ + ‖∇b‖` pointwise, for any `U` at all, provided the
variation `b` has differentiable spatial slices.  Where `U` has a spatial
derivative this is the triangle inequality after `fderiv_add`; where it does
not, `U+b` has none either (`b` is differentiable), so `∇(U+b)` is the junk
value `0` and the bound is trivial. -/
theorem enorm_spatialGradient_affineVelocity_le (U b : VelocityField)
    (hb : ∀ t : ℝ, ∀ x : Space, DifferentiableAt ℝ (fun y : Space => b (t, y)) x)
    (t : ℝ) (x : Space) :
    ‖spatialGradient (affineVelocity U b) t x‖ₑ ≤
      ‖spatialGradient U t x‖ₑ + ‖spatialGradient b t x‖ₑ := by
  by_cases hU : DifferentiableAt ℝ (fun y : Space => U (t, y)) x
  · have hsum : spatialGradient (affineVelocity U b) t x =
        spatialGradient U t x + spatialGradient b t x := by
      have hd : fderiv ℝ (fun y : Space => U (t, y) + b (t, y)) x =
          fderiv ℝ (fun y : Space => U (t, y)) x +
            fderiv ℝ (fun y : Space => b (t, y)) x :=
        fderiv_add hU (hb t x)
      have hcoord : (fun i : Fin 3 =>
            spatialDerivative (affineVelocity U b) t x (coordinateVector i)) =
          (fun i : Fin 3 => spatialDerivative U t x (coordinateVector i)) +
            fun i : Fin 3 => spatialDerivative b t x (coordinateVector i) := by
        funext i
        show fderiv ℝ (fun y : Space => affineVelocity U b (t, y)) x (coordinateVector i) = _
        rw [show (fun y : Space => affineVelocity U b (t, y)) =
            fun y : Space => U (t, y) + b (t, y) from rfl, hd]
        rfl
      show WithLp.toLp 2 _ = _
      rw [hcoord]
      rfl
    rw [hsum]
    exact enorm_add_le _ _
  · have hnd : ¬ DifferentiableAt ℝ (fun y : Space => affineVelocity U b (t, y)) x := by
      intro hcon
      have hdsub : DifferentiableAt ℝ
          (fun y : Space => affineVelocity U b (t, y) - b (t, y)) x := hcon.sub (hb t x)
      have hfun : (fun y : Space => affineVelocity U b (t, y) - b (t, y)) =
          fun y : Space => U (t, y) := by
        funext y
        simp [affineVelocity]
      rw [hfun] at hdsub
      exact hU hdsub
    have hzero : spatialGradient (affineVelocity U b) t x = 0 := by
      have hf : fderiv ℝ (fun y : Space => affineVelocity U b (t, y)) x = 0 :=
        fderiv_zero_of_not_differentiableAt hnd
      show WithLp.toLp 2 (fun i : Fin 3 =>
        fderiv ℝ (fun y : Space => affineVelocity U b (t, y)) x (coordinateVector i)) = 0
      rw [hf]
      rfl
    rw [hzero]
    simp

/-! ## 4. Uniform bounds for an admissible variation -/

/-- The spatial derivative of a globally smooth field, read as a function of
spacetime, is continuous: `ContDiff.fderiv` with the base point `(t,x)` and the
fibre variable `y`. -/
theorem continuous_spatialDerivative_uncurry {b : VelocityField} (hb : ContDiff ℝ ∞ b) :
    Continuous fun z : SpaceTime => spatialDerivative b z.1 z.2 := by
  have hpair : ContDiff ℝ ∞ fun p : SpaceTime × Space => ((p.1.1 : ℝ), p.2) :=
    contDiff_fst.fst.prodMk contDiff_snd
  have huncurry : ContDiff ℝ ∞
      (Function.uncurry fun (z : SpaceTime) (y : Space) => b (z.1, y)) := hb.comp hpair
  have hcd : ContDiff ℝ 0 fun z : SpaceTime =>
      fderiv ℝ (fun y : Space => b (z.1, y)) z.2 :=
    ContDiff.fderiv huncurry contDiff_snd (by simp)
  exact hcd.continuous

/-- Outside the spacetime support of a field the spatial derivative vanishes:
the complement of `tsupport` is open and the field is identically zero there,
so each spatial slice is locally zero. -/
theorem spatialDerivative_eq_zero_of_notMem_tsupport {b : VelocityField}
    {z : SpaceTime} (hz : z ∉ tsupport b) : spatialDerivative b z.1 z.2 = 0 := by
  have hopen : IsOpen ((tsupport b)ᶜ) := (isClosed_tsupport b).isOpen_compl
  have hnhds : {y : Space | (z.1, y) ∉ tsupport b} ∈ nhds z.2 :=
    IsOpen.mem_nhds (hopen.preimage (continuous_const.prodMk continuous_id)) hz
  have heq : (fun y : Space => b (z.1, y)) =ᶠ[nhds z.2] fun _ : Space => (0 : Space) := by
    filter_upwards [hnhds] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  show fderiv ℝ (fun y : Space => b (z.1, y)) z.2 = 0
  rw [heq.fderiv_eq, fderiv_const_apply]

/-- A uniform bound for the spatial derivative of a smooth compactly supported
variation: it is continuous with compact spacetime support, hence bounded. -/
theorem exists_bound_spatialDerivative {b : VelocityField}
    (hsmooth : ContDiff ℝ ∞ b) (hcompact : HasCompactSupport b) :
    ∃ C : ℝ, ∀ z : SpaceTime, ‖spatialDerivative b z.1 z.2‖ ≤ C := by
  have hcont : Continuous fun z : SpaceTime => spatialDerivative b z.1 z.2 :=
    continuous_spatialDerivative_uncurry hsmooth
  have hsupp : HasCompactSupport fun z : SpaceTime => spatialDerivative b z.1 z.2 :=
    HasCompactSupport.intro hcompact.isCompact
      (fun z hz => spatialDerivative_eq_zero_of_notMem_tsupport hz)
  exact hcont.bounded_above_of_compact_support hsupp

/-- The squared enorm of the Frobenius gradient is at most `3` times the squared
operator bound of the spatial derivative. -/
theorem enorm_spatialGradient_rpow_two_le {b : VelocityField} {C : ℝ}
    (hC : ∀ z : SpaceTime, ‖spatialDerivative b z.1 z.2‖ ≤ C) (t : ℝ) (x : Space) :
    ‖spatialGradient b t x‖ₑ ^ (2 : ℝ) ≤ ENNReal.ofReal (3 * C ^ 2) := by
  have hcomp : ∀ i : Fin 3, ‖spatialDerivative b t x (coordinateVector i)‖ ≤ C := by
    intro i
    have hunit : ‖coordinateVector i‖ = 1 := by simp [coordinateVector]
    calc ‖spatialDerivative b t x (coordinateVector i)‖
        ≤ ‖spatialDerivative b t x‖ * ‖coordinateVector i‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖spatialDerivative b t x‖ := by rw [hunit, mul_one]
      _ ≤ C := hC (t, x)
  have hsq : ‖spatialGradient b t x‖ ^ 2 ≤ 3 * C ^ 2 := by
    rw [norm_spatialGradient_sq]
    calc ∑ i : Fin 3, ‖spatialDerivative b t x (coordinateVector i)‖ ^ 2
        ≤ ∑ _i : Fin 3, C ^ 2 :=
          Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hcomp i) 2)
      _ = 3 * C ^ 2 := by simp [Finset.sum_const]
  calc ‖spatialGradient b t x‖ₑ ^ (2 : ℝ)
      = ENNReal.ofReal (‖spatialGradient b t x‖ ^ 2) := by
        rw [← ofReal_norm,
          ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2),
          Real.rpow_two]
    _ ≤ ENNReal.ofReal (3 * C ^ 2) := ENNReal.ofReal_le_ofReal hsq

/-- Every spatial slice of a smooth compactly supported variation has squared
`L²` seminorm at most `Cb² · |K|`, uniformly in time, where `K` is the spatial
projection of the (compact) spacetime support. -/
theorem rpow_two_eLpNorm_slice_le {b : VelocityField} {Cb : ℝ}
    (hCb : ∀ z : SpaceTime, ‖b z‖ ≤ Cb) (t : ℝ) :
    (eLpNorm (fun x : Space => b (t, x)) 2 volume) ^ (2 : ℝ) ≤
      ENNReal.ofReal (Cb ^ 2) * volume (Prod.snd '' tsupport b) := by
  refine rpow_two_eLpNorm_le_of_bound (fun x => ?_) (fun x hx => ?_)
  · calc ‖b (t, x)‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖b (t, x)‖ ^ 2) := by
          rw [← ofReal_norm,
            ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2),
            Real.rpow_two]
      _ ≤ ENNReal.ofReal (Cb ^ 2) :=
          ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hCb (t, x)) 2)
  · exact image_eq_zero_of_notMem_tsupport (fun hmem => hx ⟨(t, x), hmem, rfl⟩)

/-- The same for the gradient slices. -/
theorem rpow_two_eLpNorm_gradient_slice_le {b : VelocityField} {Cg : ℝ}
    (hCg : ∀ z : SpaceTime, ‖spatialDerivative b z.1 z.2‖ ≤ Cg) (t : ℝ) :
    (eLpNorm (fun x : Space => spatialGradient b t x) 2 volume) ^ (2 : ℝ) ≤
      ENNReal.ofReal (3 * Cg ^ 2) * volume (Prod.snd '' tsupport b) := by
  refine rpow_two_eLpNorm_le_of_bound
    (fun x => enorm_spatialGradient_rpow_two_le hCg t x) (fun x hx => ?_)
  have hf : fderiv ℝ (fun y : Space => b (t, y)) x = 0 :=
    spatialDerivative_eq_zero_of_notMem_tsupport (z := (t, x))
      (fun hmem => hx ⟨(t, x), hmem, rfl⟩)
  show WithLp.toLp 2 (fun i : Fin 3 =>
    fderiv ℝ (fun y : Space => b (t, y)) x (coordinateVector i)) = 0
  rw [hf]
  rfl

/-! ## 5. The two halves of `E_1` -/

/-- The `L^∞_t L²_x` half of `‖U+b‖_{E_1}` is finite. -/
theorem energyEssSup_affineVelocity_lt_top {U b : VelocityField}
    (hU : energyEssSup 1 U < ⊤) (hsmooth : ContDiff ℝ ∞ b)
    (hcompact : HasCompactSupport b) :
    energyEssSup 1 (affineVelocity U b) < ⊤ := by
  obtain ⟨Cb, hCb⟩ : ∃ C : ℝ, ∀ z : SpaceTime, ‖b z‖ ≤ C :=
    hsmooth.continuous.bounded_above_of_compact_support hcompact
  have hmeas : ∀ t : ℝ, Measurable fun x : Space => ‖b (t, x)‖ₑ ^ (2 : ℝ) := by
    intro t
    have hslice : Continuous fun x : Space => b (t, x) :=
      hsmooth.continuous.comp (continuous_const.prodMk continuous_id)
    exact (hslice.enorm.measurable).pow_const _
  have hDtop : ENNReal.ofReal (Cb ^ 2) * volume (Prod.snd '' tsupport b) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (hcompact.isCompact.image continuous_snd).measure_lt_top.ne
  have hbound : energyEssSup 1 (affineVelocity U b) ≤
      (4 * (energyEssSup 1 U) ^ (2 : ℝ) +
        4 * (ENNReal.ofReal (Cb ^ 2) * volume (Prod.snd '' tsupport b))) ^ ((2 : ℝ)⁻¹) := by
    refine essSup_le_of_ae_le _ ?_
    filter_upwards [ENNReal.ae_le_essSup (μ := volume.restrict (Ioo (0 : ℝ) 1))
      (fun t => eLpNorm (fun x : Space => U (t, x)) 2 volume)] with t ht
    have hstep : (eLpNorm (fun x : Space => affineVelocity U b (t, x)) 2 volume) ^ (2 : ℝ) ≤
        4 * (energyEssSup 1 U) ^ (2 : ℝ) +
          4 * (ENNReal.ofReal (Cb ^ 2) * volume (Prod.snd '' tsupport b)) := by
      refine le_trans (rpow_two_eLpNorm_add_le
        (F := fun x : Space => U (t, x)) (G := fun x : Space => b (t, x))
        (fun x => enorm_add_le _ _) (hmeas t)) ?_
      exact add_le_add (mul_le_mul' (le_refl 4) (ENNReal.rpow_le_rpow ht (by norm_num)))
        (mul_le_mul' (le_refl 4) (rpow_two_eLpNorm_slice_le hCb t))
    calc eLpNorm (fun x : Space => affineVelocity U b (t, x)) 2 volume
        = ((eLpNorm (fun x : Space => affineVelocity U b (t, x)) 2 volume) ^ (2 : ℝ)) ^
            ((2 : ℝ)⁻¹) := (ENNReal.rpow_rpow_inv (by norm_num) _).symm
      _ ≤ _ := ENNReal.rpow_le_rpow hstep (by norm_num)
  refine lt_of_le_of_lt hbound (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_)
  refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) ?_,
    ENNReal.mul_ne_top (by norm_num) hDtop⟩
  exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hU.ne).ne

/-- The `L²_t Ḣ¹_x` half of `‖U+b‖_{E_1}` is finite. -/
theorem energyGradient_affineVelocity_lt_top {U b : VelocityField}
    (hU : energyGradient 1 U < ⊤) (hsmooth : ContDiff ℝ ∞ b)
    (hcompact : HasCompactSupport b) :
    energyGradient 1 (affineVelocity U b) < ⊤ := by
  obtain ⟨Cg, hCg⟩ := exists_bound_spatialDerivative hsmooth hcompact
  have hIU : (∫⁻ t in Ioo (0 : ℝ) 1,
      (eLpNorm (fun x : Space => spatialGradient U t x) 2 volume) ^ (2 : ℝ)) ≠ ⊤ := by
    intro hcon
    rw [energyGradient, hcon, ENNReal.top_rpow_of_pos (by norm_num)] at hU
    exact absurd hU (lt_irrefl _)
  have hdiff : ∀ t : ℝ, ∀ x : Space, DifferentiableAt ℝ (fun y : Space => b (t, y)) x := by
    intro t x
    have hslice : ContDiff ℝ ∞ fun y : Space => b (t, y) :=
      hsmooth.comp (contDiff_const.prodMk contDiff_id)
    exact (hslice.differentiable (by simp)).differentiableAt
  have hmeas : ∀ t : ℝ, Measurable fun x : Space => ‖spatialGradient b t x‖ₑ ^ (2 : ℝ) :=
    fun t => ((NSFormalization.Section4.I02.continuous_spatialGradient
      hsmooth t).enorm.measurable).pow_const _
  have hDtop : ENNReal.ofReal (3 * Cg ^ 2) * volume (Prod.snd '' tsupport b) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (hcompact.isCompact.image continuous_snd).measure_lt_top.ne
  have hkey : (∫⁻ t in Ioo (0 : ℝ) 1,
      (eLpNorm (fun x : Space => spatialGradient (affineVelocity U b) t x) 2 volume) ^
        (2 : ℝ)) ≠ ⊤ := by
    have hstep : (∫⁻ t in Ioo (0 : ℝ) 1,
        (eLpNorm (fun x : Space => spatialGradient (affineVelocity U b) t x) 2 volume) ^
          (2 : ℝ)) ≤
        ∫⁻ t in Ioo (0 : ℝ) 1,
          (4 * (eLpNorm (fun x : Space => spatialGradient U t x) 2 volume) ^ (2 : ℝ) +
            4 * (ENNReal.ofReal (3 * Cg ^ 2) *
              volume (Prod.snd '' tsupport b))) := by
      refine lintegral_mono (fun t => ?_)
      refine le_trans (rpow_two_eLpNorm_add_le
        (F := fun x : Space => spatialGradient U t x)
        (G := fun x : Space => spatialGradient b t x)
        (fun x => enorm_spatialGradient_affineVelocity_le U b hdiff t x) (hmeas t)) ?_
      exact add_le_add (le_refl _)
        (mul_le_mul' (le_refl 4) (rpow_two_eLpNorm_gradient_slice_le hCg t))
    have hsplit : (∫⁻ t in Ioo (0 : ℝ) 1,
        (4 * (eLpNorm (fun x : Space => spatialGradient U t x) 2 volume) ^ (2 : ℝ) +
          4 * (ENNReal.ofReal (3 * Cg ^ 2) * volume (Prod.snd '' tsupport b)))) =
        4 * (∫⁻ t in Ioo (0 : ℝ) 1,
          (eLpNorm (fun x : Space => spatialGradient U t x) 2 volume) ^ (2 : ℝ)) +
          4 * (ENNReal.ofReal (3 * Cg ^ 2) * volume (Prod.snd '' tsupport b)) *
            volume (Ioo (0 : ℝ) 1) := by
      rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by norm_num),
        setLIntegral_const]
    refine ne_top_of_le_ne_top ?_ (le_trans hstep (le_of_eq hsplit))
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num) hIU, ?_⟩
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hDtop) ?_
    simp [Real.volume_Ioo]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hkey

/-! ## 6. The Ua6 statement -/

/-- **T24a Ua6**, `03-torus.tex:686-687`: every affine variation of a
finite-energy velocity has finite energy and dissipation, `‖U+b‖_{E_1} < ∞`.

The conclusion is token-identical to `research/T24/Spec.lean:1076-1077` with the
packet field `P.velocity` replaced by the raw `U`; the only hypothesis on `U` is
the raw packet clause `energyENorm 1 U < ⊤`. -/
theorem energy_finite {U : VelocityField} (c : Space) (r τ₀ τ₁ : ℝ)
    (henergy : energyENorm 1 U < ⊤) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
      energyENorm 1 (affineVelocity U b) < ⊤ := by
  intro b hb
  refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
  · exact energyEssSup_affineVelocity_lt_top
      (lt_of_le_of_lt le_self_add henergy) hb.1 hb.2.1
  · exact energyGradient_affineVelocity_lt_top
      (lt_of_le_of_lt le_add_self henergy) hb.1 hb.2.1

end NSFormalization.Section3.T24
