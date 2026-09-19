import NSFormalization.Section3.T20.TransportLambda

/-!
# T20 U5 closure probe

This file checks the canonical field type verbatim and instantiates the theorem
on the nonzero mean-free cosine mode
`meanZeroPartT (x ↦ cos (2π x₀) • e₀)`, with its physical `Lambda`
representative supplied by `lambda_exists`.
-/

noncomputable section

namespace NSFormalization.Section3.T20.TransportLambdaProbe

open MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T12
open NSFormalization.Section3.T13
open NSFormalization.Section3.T20
open scoped ContDiff

/-! ## 1. Canonical field-type match -/

/-- `CriticalRegularityTAPI.constantTransportCommutesLambda`, verbatim. -/
def constantTransportCommutesLambdaFieldType : Prop :=
  ∀ (m : Space) (v Lv : SpatialField), SmoothPeriodicT v →
    IsPeriodicLambda v Lv →
      IsPeriodicLambda (constantTransportSpatialT m v)
        (constantTransportSpatialT m Lv)

example (API : CriticalRegularityTAPI) : constantTransportCommutesLambdaFieldType :=
  API.constantTransportCommutesLambda

example : constantTransportCommutesLambdaFieldType := constantTransportCommutesLambda

/-! ## 2. Nonzero smooth mean-zero cosine witness -/

def probeZ : SpatialField :=
  fun x ↦ Real.cos (2 * Real.pi * x 0) • coordinateVector 0

theorem probeZ_contDiff : ContDiff ℝ ∞ probeZ := by
  unfold probeZ
  have hproj : ContDiff ℝ ∞ (fun x : Space ↦ x 0) := contDiff_piLp_apply 2
  exact (Real.contDiff_cos.comp (contDiff_const.mul hproj)).smul contDiff_const

theorem coordinateVector_apply (i j : Fin 3) :
    (coordinateVector i) j = (if j = i then (1 : ℝ) else 0) := by
  simp [coordinateVector, PiLp.single_apply]

theorem probeZ_periodic : IsPeriodicSpatial probeZ := by
  intro x i
  show Real.cos (2 * Real.pi * (x + coordinateVector i) 0) • coordinateVector 0 =
    Real.cos (2 * Real.pi * x 0) • coordinateVector 0
  have hadd : (x + coordinateVector i) 0 =
      x 0 + (if (0 : Fin 3) = i then 1 else 0) := by
    show x 0 + (coordinateVector i) 0 = _
    rw [coordinateVector_apply]
  rcases eq_or_ne (0 : Fin 3) i with hi | hi
  · subst hi
    have hx : (x + coordinateVector (0 : Fin 3)) 0 = x 0 + 1 := by
      rw [hadd]
      norm_num
    have heq : 2 * Real.pi * (x 0 + 1) = 2 * Real.pi * x 0 + 2 * Real.pi := by
      ring
    rw [hx, heq, Real.cos_add_two_pi]
  · have hx : (x + coordinateVector i) 0 = x 0 := by
      rw [hadd]
      simp [hi]
    rw [hx]

theorem probeZ_integrable : Integrable (torusLift probeZ) periodicTorusMeasure :=
  integrable_torusLift_space probeZ_contDiff.continuous

def probeMZ : SpatialField := meanZeroPartT probeZ

theorem probeMZ_smoothPeriodic : SmoothPeriodicT probeMZ := by
  refine ⟨probeZ_contDiff.sub contDiff_const, ?_⟩
  intro x i
  show probeZ (x + coordinateVector i) - meanT probeZ = probeZ x - meanT probeZ
  rw [probeZ_periodic x i]

theorem probeMZ_ne_zero : probeMZ ≠ (0 : SpatialField) := by
  intro h
  let p1 : Space := (2⁻¹ : ℝ) • coordinateVector (0 : Fin 3)
  have hp1coord : p1 0 = (2⁻¹ : ℝ) := by
    show (2⁻¹ : ℝ) • (coordinateVector (0 : Fin 3)) 0 = (2⁻¹ : ℝ)
    rw [coordinateVector_apply]
    simp
  have hzero : probeZ (0 : Space) - probeZ p1 = 0 := by
    have e0 : probeMZ (0 : Space) = 0 := by rw [h]; rfl
    have e1 : probeMZ p1 = 0 := by rw [h]; rfl
    have hd : probeMZ (0 : Space) - probeMZ p1 = probeZ (0 : Space) - probeZ p1 := by
      simp only [probeMZ, meanZeroPartT]
      abel
    rw [e0, e1, sub_zero] at hd
    exact hd.symm
  have hz0 : probeZ (0 : Space) = coordinateVector 0 := by
    simp [probeZ]
  have hz1 : probeZ p1 = (-1 : ℝ) • coordinateVector 0 := by
    show Real.cos (2 * Real.pi * p1 0) • coordinateVector 0 =
      (-1 : ℝ) • coordinateVector 0
    rw [hp1coord]
    have hpi : 2 * Real.pi * (2⁻¹ : ℝ) = Real.pi := by ring
    rw [hpi, Real.cos_pi]
  rw [hz0, hz1, neg_one_smul, sub_neg_eq_add] at hzero
  have hcv : coordinateVector (0 : Fin 3) ≠ 0 := by
    intro hc
    have hca := coordinateVector_apply 0 0
    rw [hc] at hca
    simp at hca
  have hs : (2 : ℝ) • coordinateVector (0 : Fin 3) = 0 := by
    rw [two_smul]
    exact hzero
  exact hcv ((smul_eq_zero.mp hs).resolve_left (by norm_num))

/-- The source is genuinely nonzero, `lambda_exists` supplies an actual graph
witness, and U5 supplies the transported graph at the nonzero direction `e₀`. -/
example : probeMZ ≠ (0 : SpatialField) ∧
    ∃ Lv : SpatialField, IsPeriodicLambda probeMZ Lv ∧
      IsPeriodicLambda
        (constantTransportSpatialT (coordinateVector 0) probeMZ)
        (constantTransportSpatialT (coordinateVector 0) Lv) := by
  obtain ⟨Lv, hLv⟩ := lambda_exists probeMZ probeMZ_smoothPeriodic
  exact ⟨probeMZ_ne_zero, Lv, hLv,
    constantTransportCommutesLambda (coordinateVector 0) probeMZ Lv
      probeMZ_smoothPeriodic hLv⟩

end NSFormalization.Section3.T20.TransportLambdaProbe
