import NSFormalization.Section4.A05.GradientL6
import NSFormalization.Section4.A02.SolutionClass
import NSFormalization.Section4.I02.Energy
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.Real.Sqrt

/-!
# C01 unit U6: the trilinear Hölder estimate, its absorption form, and `‖Δz‖₂²`

Task `collaboration/tasks/C01.md`, unit `U6` of `research/C01/COMPARISON.md:176`.
This module discharges the three specification fields `trilinearHolder`,
`trilinearAbsorbed` and `laplacianSqENorm` of
`BlowupDensity.C01.Draft.EnergyAbsorptionAPI`
(`research/C01/Spec.lean:410-473`).

## Statements (paper `04-whole-space.tex:107-112`)

* `trilinearHolder`  — `|⟨(z·∇)z, Δz⟩| ≤ ‖z‖₃ · ‖∇z‖₆ · ‖Δz‖₂`, a three-factor
  Hölder inequality with exponents `1/3 + 1/6 + 1/2 = 1`.
* `trilinearAbsorbed` — `|⟨(z·∇)z, Δz⟩| ≤ C₁ ‖z‖₃ ‖Δz‖₂²`, obtained from the
  first by the **registered** gradient-`L⁶` clause with constant
  `C₁ = gradientL6Const` (bound to `A05.gradient_l6`'s `Csix`).
* `laplacianSqENorm` — `‖Δz‖₂ (as eLpNorm)² = ENNReal.ofReal (∫ ‖Δz‖²)`.

## How this file relates to the specification

`Contracts/*` cannot be imported by `formalization/`, so the three fields are
restated here against the **local** declarations the registered contract binds
to (`verification/Bindings/GradientL6.lean:27-46`):

* `Contracts.V1.gradientTensor v = A05.gradTensor v` (`rfl`),
* `Contracts.V1.laplacian v      = A05.lap v`        (`rfl`),
* `Contracts.V1.SmoothSquareIntegrableJets v = A05.SmoothL2 v` (`rfl`).

§0 restates the spec `def`s `lift`, `advectionWork`, `criticalL3`, `laplacianSq`
token-for-token from `research/C01/Spec.lean`, using the A05 objects (which are
definitionally the contract's).  The conformance file
`research/C01/axioms_u6.lean` restates the same `def`s in the contract's own
vocabulary and discharges the three spec-field statements by the theorems below,
with `#print axioms`.

The trilinear Hölder route is `ℝ≥0∞`-valued throughout (no integrability side
condition): the real work integral is injected by `enorm`, dominated pointwise
by `‖z‖·‖∇z‖·‖Δz‖` (Cauchy–Schwarz on the inner product and on the directional
derivative `(z·∇)z = ∇z · z`), then bounded by the generalized Hölder inequality
`ENNReal.lintegral_prod_norm_pow_le`.  No `MemLp z 3` interpolation is needed;
smoothness of `z` supplies only measurability.
-/

noncomputable section

open MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A05 (lap gradTensor SmoothL2 dirDeriv gradientL6Const)
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open scoped ContDiff ENNReal

namespace NSFormalization.Section4.C01

/-! ## 0. The spec `def`s, restated from `research/C01/Spec.lean`

Each is written with the A05 objects `lap`, `gradTensor`, which the binding
records as definitionally the contract's `Contracts.V1.laplacian`,
`Contracts.V1.gradientTensor`; hence each is definitionally the spec's `def`. -/

/-- `Contracts/V1/GradientL6.lean:78` (= the `lift` used by `Spec.lean`'s
`advectionWork`): the time-independent lift of a spatial field. -/
def lift (v : SpatialField) : SpaceTimeField := fun z => v z.2

/-- `research/C01/Spec.lean:191` `laplacianSq`, `‖Δz‖₂²` as a real Bochner
integral of the squared pointwise norm of the componentwise Laplacian. -/
def laplacianSq (z : SpatialField) : ℝ := ∫ x : Space, ‖lap z x‖ ^ 2

/-- `research/C01/Spec.lean:212` `criticalL3`, the critical `L³` norm `‖z‖₃`. -/
def criticalL3 (z : SpatialField) : ℝ≥0∞ := eLpNorm z 3 volume

/-- `research/C01/Spec.lean:202` `advectionWork`, the nonlinear work
`⟨(z·∇)z, Δz⟩` against the Laplacian. -/
def advectionWork (z : SpatialField) : ℝ :=
  ∫ x : Space, (inner ℝ (advection (lift z) 0 x) (lap z x) : ℝ)

/-! ## 1. Pointwise bound on the advection term

`advection (lift z) 0 x = (∇z)(x) · z(x) = ∑ⱼ (z x)ⱼ • ∂ⱼz(x)`, so its norm is
bounded by `‖z x‖ · ‖∇z x‖` by Cauchy–Schwarz on the three coordinate columns. -/

/-- `‖(z·∇)z (x)‖ ≤ ‖z x‖ · ‖∇z x‖` pointwise, with `∇z x` the Frobenius
gradient tensor `gradTensor z x`. -/
theorem advection_norm_le (z : SpatialField) (x : Space) :
    ‖advection (lift z) 0 x‖ ≤ ‖z x‖ * ‖gradTensor z x‖ := by
  have hadv : advection (lift z) 0 x = fderiv ℝ z x (z x) := rfl
  have hbasis : z x = ∑ j : Fin 3, (z x) j • coordinateVector j := by
    ext k
    simp [coordinateVector, Pi.single_apply]
  have hmap : (fderiv ℝ z x) (z x) = ∑ j : Fin 3, (z x) j • dirDeriv j z x := by
    conv_lhs => rw [hbasis]
    rw [map_sum]
    simp only [map_smul, dirDeriv]
  have hnorm_zx : Real.sqrt (∑ j : Fin 3, |(z x) j| ^ 2) = ‖z x‖ := by
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs]
  have hnorm_grad : Real.sqrt (∑ j : Fin 3, ‖dirDeriv j z x‖ ^ 2) = ‖gradTensor z x‖ := by
    rw [PiLp.norm_eq_of_L2]
    rfl
  rw [hadv, hmap]
  calc ‖∑ j : Fin 3, (z x) j • dirDeriv j z x‖
      ≤ ∑ j : Fin 3, ‖(z x) j • dirDeriv j z x‖ := norm_sum_le _ _
    _ = ∑ j : Fin 3, |(z x) j| * ‖dirDeriv j z x‖ := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ Real.sqrt (∑ j : Fin 3, |(z x) j| ^ 2) *
          Real.sqrt (∑ j : Fin 3, ‖dirDeriv j z x‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = ‖z x‖ * ‖gradTensor z x‖ := by rw [hnorm_zx, hnorm_grad]

/-! ## 2. The certified `ℝ≥0∞` bound on the advection work

The core of `trilinearHolder`, hoisted so that its left-hand side is the
lintegral of the enorm of the **integrand** `⟨(z·∇)z, Δz⟩` (not `enorm` of the
already-formed Bochner integral).  A finite right-hand side then certifies that
this integrand is integrable — which `enorm_integral_le_lintegral_enorm` alone
cannot, and which the `ℝ≥0∞` route otherwise leaves unpaid
(`research/C01/REVIEW_U6.md`, Finding 1). -/

/-- `∫⁻ ‖⟨(z·∇)z, Δz⟩‖ₑ ≤ ‖z‖₃ · ‖∇z‖₆ · ‖Δz‖₂`: the integrand is dominated
pointwise by `‖z‖·‖∇z‖·‖Δz‖` (Cauchy–Schwarz on the inner product and on the
directional derivative), then bounded by three-factor Hölder
(`1/3 + 1/6 + 1/2 = 1`) in `ℝ≥0∞`. -/
theorem lintegral_advection_inner_laplacian_le (z : SpatialField) (hz : SmoothL2 z) :
    ∫⁻ x, ‖(inner ℝ (advection (lift z) 0 x) (lap z x) : ℝ)‖ₑ ∂volume ≤
      criticalL3 z * eLpNorm (gradTensor z) 6 volume * eLpNorm (lap z) 2 volume := by
  -- continuity, hence measurability, of the three fields
  have hcz : Continuous z := hz.contDiff.continuous
  have hcg : Continuous (gradTensor z) := by
    show Continuous (fun x =>
      (WithLp.toLp 2 (fun j : Fin 3 => dirDeriv j z x) : WithLp 2 (Fin 3 → Space)))
    exact Continuous.comp (PiLp.continuous_toLp 2 (fun _ : Fin 3 => Space))
      (continuous_pi fun j => (hz.dir j).contDiff.continuous)
  have hcl : Continuous (lap z) :=
    continuous_finsetSum _ (fun i _ => ((hz.dir i).dir i).contDiff.continuous)
  -- pointwise enorm bound on the integrand
  have hpt : ∀ x : Space,
      ‖(inner ℝ (advection (lift z) 0 x) (lap z x) : ℝ)‖ₑ ≤
        ‖z x‖ₑ * ‖gradTensor z x‖ₑ * ‖lap z x‖ₑ := by
    intro x
    have hcs : |(inner ℝ (advection (lift z) 0 x) (lap z x) : ℝ)| ≤
        ‖advection (lift z) 0 x‖ * ‖lap z x‖ := abs_real_inner_le_norm _ _
    have hreal : |(inner ℝ (advection (lift z) 0 x) (lap z x) : ℝ)| ≤
        ‖z x‖ * ‖gradTensor z x‖ * ‖lap z x‖ :=
      hcs.trans (mul_le_mul_of_nonneg_right (advection_norm_le z x) (norm_nonneg _))
    calc ‖(inner ℝ (advection (lift z) 0 x) (lap z x) : ℝ)‖ₑ
        = ENNReal.ofReal |(inner ℝ (advection (lift z) 0 x) (lap z x) : ℝ)| :=
          Real.enorm_eq_ofReal_abs _
      _ ≤ ENNReal.ofReal (‖z x‖ * ‖gradTensor z x‖ * ‖lap z x‖) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ‖z x‖ₑ * ‖gradTensor z x‖ₑ * ‖lap z x‖ₑ := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (norm_nonneg _),
            ofReal_norm, ofReal_norm, ofReal_norm]
  -- three-factor Hölder in `ℝ≥0∞`
  have hpow : ∀ (a : ℝ≥0∞) (k : ℝ), 0 < k → (a ^ k) ^ (1 / k) = a := by
    intro a k hk
    rw [← ENNReal.rpow_mul, mul_one_div, div_self (ne_of_gt hk), ENNReal.rpow_one]
  have hez : (∫⁻ x, ‖z x‖ₑ ^ (3 : ℝ) ∂volume) ^ ((1 : ℝ) / 3) = eLpNorm z 3 volume := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
  have heg : (∫⁻ x, ‖gradTensor z x‖ₑ ^ (6 : ℝ) ∂volume) ^ ((1 : ℝ) / 6)
      = eLpNorm (gradTensor z) 6 volume := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
  have hel : (∫⁻ x, ‖lap z x‖ₑ ^ (2 : ℝ) ∂volume) ^ ((1 : ℝ) / 2)
      = eLpNorm (lap z) 2 volume := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat]
  have hHolder : ∫⁻ x, ‖z x‖ₑ * ‖gradTensor z x‖ₑ * ‖lap z x‖ₑ ∂volume ≤
      eLpNorm z 3 volume * eLpNorm (gradTensor z) 6 volume * eLpNorm (lap z) 2 volume := by
    calc ∫⁻ x, ‖z x‖ₑ * ‖gradTensor z x‖ₑ * ‖lap z x‖ₑ ∂volume
        = ∫⁻ x, ∏ i : Fin 3,
            (![fun x => ‖z x‖ₑ ^ (3 : ℝ), fun x => ‖gradTensor z x‖ₑ ^ (6 : ℝ),
              fun x => ‖lap z x‖ₑ ^ (2 : ℝ)] i x) ^
              (![(1 : ℝ) / 3, 1 / 6, 1 / 2] i) ∂volume := by
          refine lintegral_congr (fun x => ?_)
          rw [Fin.prod_univ_three]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.tail_cons]
          rw [hpow (‖z x‖ₑ) 3 (by norm_num), hpow (‖gradTensor z x‖ₑ) 6 (by norm_num),
            hpow (‖lap z x‖ₑ) 2 (by norm_num)]
      _ ≤ ∏ i : Fin 3,
            (∫⁻ x, (![fun x => ‖z x‖ₑ ^ (3 : ℝ), fun x => ‖gradTensor z x‖ₑ ^ (6 : ℝ),
              fun x => ‖lap z x‖ₑ ^ (2 : ℝ)] i x) ∂volume) ^ (![(1 : ℝ) / 3, 1 / 6, 1 / 2] i) := by
          refine ENNReal.lintegral_prod_norm_pow_le (Finset.univ) ?_ ?_ ?_
          · intro i _
            fin_cases i
            · exact ((continuous_enorm.comp hcz).aemeasurable).pow_const _
            · exact ((continuous_enorm.comp hcg).aemeasurable).pow_const _
            · exact ((continuous_enorm.comp hcl).aemeasurable).pow_const _
          · norm_num [Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
          · intro i _
            fin_cases i <;> norm_num
      _ = eLpNorm z 3 volume * eLpNorm (gradTensor z) 6 volume * eLpNorm (lap z) 2 volume := by
          rw [Fin.prod_univ_three]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.tail_cons]
          rw [hez, heg, hel]
  exact (lintegral_mono hpt).trans hHolder

/-- With the critical norm finite, the advection-work integrand is genuinely
integrable, so `advectionWork z` is the true Bochner integral rather than
Mathlib's junk `0`.  This is the price of the `ℝ≥0∞` route, now paid: the
lintegral bound above bounds the enorm of the *integrand*, so a finite
right-hand side (each factor finite: `criticalL3 z` by hypothesis,
`eLpNorm (∇z) 6` by the registered `L⁶` clause, `eLpNorm (Δz) 2` by `MemLp`)
gives `∫⁻ ‖·‖ₑ < ⊤`.  U7's `enstrophyIdentity`, an equality containing the same
`advectionWork`, needs exactly this. -/
theorem integrable_advection_inner_laplacian (z : SpatialField) (hz : SmoothL2 z)
    (hL3 : criticalL3 z ≠ ⊤) :
    Integrable (fun x => (inner ℝ (advection (lift z) 0 x) (lap z x) : ℝ)) volume := by
  have hcz : Continuous z := hz.contDiff.continuous
  have hcl : Continuous (lap z) :=
    continuous_finsetSum _ (fun i _ => ((hz.dir i).dir i).contDiff.continuous)
  have hcadv : Continuous (fun x => advection (lift z) 0 x) := by
    show Continuous (fun x => (fderiv ℝ z x) (z x))
    exact (hz.contDiff.continuous_fderiv (by simp)).clm_apply hcz
  have hmem : MemLp (lap z) 2 volume :=
    memLp_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => ((hz.dir i).dir i).memLp)
  have hlap : eLpNorm (lap z) 2 volume ≠ ⊤ := hmem.eLpNorm_lt_top.ne
  have hgrad : eLpNorm (gradTensor z) 6 volume ≠ ⊤ :=
    (lt_of_le_of_lt (NSFormalization.Section4.A05.eLpNorm_gradTensor_six_le hz)
      (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hlap))).ne
  refine ⟨(hcadv.inner hcl).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact (lintegral_advection_inner_laplacian_le z hz).trans_lt
    (lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (ENNReal.mul_ne_top hL3 hgrad) hlap))

/-! ## 3. The three spec fields -/

/-- **`trilinearHolder`** (`Spec.lean:410`).  `|⟨(z·∇)z, Δz⟩| ≤ ‖z‖₃‖∇z‖₆‖Δz‖₂`,
in `ℝ≥0∞`.  The real work integral is injected by `enorm`, then bounded by
`lintegral_advection_inner_laplacian_le`. -/
theorem trilinearHolder (z : SpatialField) (hz : SmoothL2 z) :
    ENNReal.ofReal |advectionWork z| ≤
      criticalL3 z * eLpNorm (gradTensor z) 6 volume * eLpNorm (lap z) 2 volume := by
  rw [(Real.enorm_eq_ofReal_abs (advectionWork z)).symm]
  calc ‖advectionWork z‖ₑ
      = ‖∫ x, (inner ℝ (advection (lift z) 0 x) (lap z x) : ℝ)‖ₑ := rfl
    _ ≤ ∫⁻ x, ‖(inner ℝ (advection (lift z) 0 x) (lap z x) : ℝ)‖ₑ ∂volume :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ criticalL3 z * eLpNorm (gradTensor z) 6 volume * eLpNorm (lap z) 2 volume :=
        lintegral_advection_inner_laplacian_le z hz

/-- **`trilinearAbsorbed`** (`Spec.lean:435`).  `|⟨(z·∇)z, Δz⟩| ≤ C₁‖z‖₃‖Δz‖₂²`
with `C₁ = gradientL6Const`, obtained from `trilinearHolder` by the registered
gradient-`L⁶` clause `A05.eLpNorm_gradTensor_six_le`. -/
theorem trilinearAbsorbed (z : SpatialField) (hz : SmoothL2 z) :
    ENNReal.ofReal |advectionWork z| ≤
      ENNReal.ofReal gradientL6Const * criticalL3 z *
        eLpNorm (lap z) 2 volume ^ (2 : ℝ) := by
  have h1 := trilinearHolder z hz
  have h2 := NSFormalization.Section4.A05.eLpNorm_gradTensor_six_le hz
  calc ENNReal.ofReal |advectionWork z|
      ≤ criticalL3 z * eLpNorm (gradTensor z) 6 volume * eLpNorm (lap z) 2 volume := h1
    _ ≤ criticalL3 z * (ENNReal.ofReal gradientL6Const * eLpNorm (lap z) 2 volume) *
          eLpNorm (lap z) 2 volume :=
        mul_le_mul' (mul_le_mul' (le_refl (criticalL3 z)) h2)
          (le_refl (eLpNorm (lap z) 2 volume))
    _ = ENNReal.ofReal gradientL6Const * criticalL3 z * eLpNorm (lap z) 2 volume ^ (2 : ℝ) := by
        rw [ENNReal.rpow_two]; ring

/-- **`laplacianSqENorm`** (`Spec.lean:471`).  `‖Δz‖₂ (as eLpNorm)² = ofReal (∫ ‖Δz‖²)`.
The `L²` case `eLpNorm_two_eq_ofReal_sqrt` is squared. -/
theorem laplacianSqENorm (z : SpatialField) (hz : SmoothL2 z) :
    eLpNorm (lap z) 2 volume ^ (2 : ℝ) = ENNReal.ofReal (laplacianSq z) := by
  have hmem : MemLp (lap z) 2 volume :=
    memLp_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => ((hz.dir i).dir i).memLp)
  have hint : Integrable (fun x => ‖lap z x‖ ^ 2) volume := by
    have h := hmem.integrable_norm_rpow (by norm_num) (by norm_num)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have hval : eLpNorm (lap z) 2 volume ^ (2 : ℝ) = ENNReal.ofReal (∫ x : Space, ‖lap z x‖ ^ 2) := by
    rw [NSFormalization.Section4.I02.eLpNorm_two_eq_ofReal_sqrt hint,
      ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num), Real.rpow_two,
      Real.sq_sqrt (integral_nonneg (fun x => by positivity))]
  exact hval

end NSFormalization.Section4.C01
