import NSFormalization.Section4.A01.AprioriFamily
import NSFormalization.Section4.A01.ForceBridge

noncomputable section
namespace NSFormalization.Section4.A01.Rev193

open Set MeasureTheory
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.D01 (IsSobolevDatum)
open NSFormalization.Source.ForcedCylinderLocal
open EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
open EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
open EulerSmoothFieldSobolevTime EulerQuadraticSource EulerSobolevHeat EulerVolterraConvolution
open scoped Topology ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/- The exact `constructorInputs_of_bounds` interface at fixed commit `3eaab5c`.
This parameter is used because that sibling module is not present in this checkout. -/
theorem hb_feeds_constructorInputs_192
    (constructorInputs192 : ∀ {q : ℕ} (_hq : 6 ≤ q)
      {f : A02.SpaceTimeField} {S ν : ℝ}
      (hf : D01.MemForceR f) (hν : 0 < ν) (hS : 0 < S)
      (a : SmoothL2Field Space)
      (_ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0) (R : ℕ → ℝ),
      (∀ p (hp : 6 ≤ p), HasAprioriBound hp hν a
        (C01.forcePath (S := S) hf)
        (C01.forcePath_jetLp_continuous (S := S) hf) (R p)) →
      ∃ (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
        (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))),
        U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
        (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
        (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
        ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
          ContDiffOn ℝ 0 G (Icc (0 : ℝ) S) ∧
          ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1))
    {q : ℕ} (hq : 6 ≤ q) {f : A02.SpaceTimeField} {S ν R₆ : ℝ}
    (hf : D01.MemForceR f) (hν : 0 < ν) (hS : 0 < S)
    (a : SmoothL2Field Space)
    (ha : ∀ x, EulerSmoothLimit.divergence a.field x = 0)
    (u₆ : C(Icc (0 : ℝ) S, SobolevSpace 1 7)) (hR : ‖u₆‖ ≤ R₆)
    (h₆ : ∀ t, u₆ t = quadraticDuhamel 1 ν hν hS.le le_rfl
      (coefficients 1 (le_refl 6) (sobolevPath (C01.forcePath (S := S) hf)
        (C01.forcePath_jetLp_continuous (S := S) hf) 6))
      (ordinarySobolev 7 a.toLp a.translation_contDiff) u₆ t)
    (E C : ℕ → ℝ) (hE : ∀ p, 0 ≤ E p) (hC : ∀ p, 0 ≤ C p)
    (hMG : ∀ p (hp : 6 ≤ p), MildGronwall hp hν a (C01.forcePath (S := S) hf)
      (C01.forcePath_jetLp_continuous (S := S) hf) (E p) (C p)) :
    ∃ (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
      (u : C(Icc (0 : ℝ) S, SobolevSpace 1 (q + 1))),
      U ⟨0, le_rfl, hS.le⟩ = a.toLp ∧
      (∀ t, ordinaryLift (U t) = value 1 (u t)) ∧
      (∀ t, value 1 (u t) ∈ divergenceFreeSpace 1 1 0) ∧
      ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
        ContDiffOn ℝ 0 G (Icc (0 : ℝ) S) ∧
        ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1) := by
  apply constructorInputs192 hq hf hν hS a ha
    (aprioriRadius a _ _ R₆ E C)
  exact hb_of_base hν hS.le a _ _ u₆ hR h₆ E C hE hC hMG

private theorem zero_value :
    (SmoothL2Field.zeroField : SmoothL2Field Space).toLp = 0 := by
  apply Lp.ext
  filter_upwards [(SmoothL2Field.zeroField : SmoothL2Field Space).toLp_ae,
    Lp.coeFn_zero Space 2 volume] with x hx hz
  exact hx.trans hz.symm

private theorem zero_sob (p : ℕ) : ordinarySobolev p
    (SmoothL2Field.zeroField : SmoothL2Field Space).toLp
    (SmoothL2Field.zeroField : SmoothL2Field Space).translation_contDiff = 0 := by
  apply value_injective 1
  simp only [ordinarySobolev_value, zero_value, map_zero]
  rfl

private theorem zero_mild (p : ℕ) (hp : 6 ≤ p) {T : ℝ} (hT : 0 ≤ T)
    (hTS : T ≤ 1) : ∀ t,
    (0 : C(Icc (0 : ℝ) T, SobolevSpace 1 (p+1))) t =
      quadraticDuhamel 1 1 (by norm_num) hT hTS
        (coefficients 1 hp (sobolevPath
          (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
          (fun _ => continuous_const) p))
        (ordinarySobolev (p+1) (SmoothL2Field.zeroField : SmoothL2Field Space).toLp
          (SmoothL2Field.zeroField : SmoothL2Field Space).translation_contDiff) 0 t := by
  intro t
  simp only [quadraticDuhamel, source_eq, ContinuousMap.zero_apply, zero_sob,
    map_zero, sobolevPath, ContinuousMap.coe_mk, sub_zero,
    intervalIntegral.integral_zero, add_zero]

private theorem zero_mildGronwall (p : ℕ) (hp : 6 ≤ p) :
    MildGronwall hp (by norm_num : (0 : ℝ) < 1)
      (SmoothL2Field.zeroField : SmoothL2Field Space)
      (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
      (fun _ => continuous_const) 1 1 := by
  intro T hT hTS u hu
  have he := quadratic_mild_unique_window (by norm_num : (0 : ℝ) < 1) hT hTS _ _ u 0
    hu (zero_mild p hp hT hTS)
  subst u
  refine ⟨0, ?_, ?_, ?_⟩
  · intro t
    simp
  · simp only [ContinuousMap.zero_apply, zero_sob, norm_zero, mul_zero, le_rfl]
  · intro t
    have hf : sobolevPath (fun _ : Icc (0 : ℝ) 1 =>
        (SmoothL2Field.zeroField : SmoothL2Field Space))
        (fun _ => continuous_const) (p+1) = 0 := by
      apply ContinuousMap.ext
      intro s
      exact zero_sob (p+1)
    simp only [ContinuousMap.zero_apply, extendPath, map_zero, norm_zero, zero_pow,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_zero, add_zero, hf,
      intervalIntegral.integral_zero, le_rfl]

/- The vendor radius for zero initial data is `‖u₀‖ + 1 = 1`; no bound hypothesis
or `MildGronwall` premise is assumed in this concrete instance. -/
example : HasAprioriBound (le_refl 6) (by norm_num : (0 : ℝ) < 1)
    (SmoothL2Field.zeroField : SmoothL2Field Space)
    (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
    (fun _ => continuous_const) 1 := by
  exact hasAprioriBound_base (by norm_num) (by norm_num) _ _ _ 0 (by norm_num)
    (zero_mild 6 le_rfl (by norm_num) le_rfl)

example : ∀ p (hp : 6 ≤ p), HasAprioriBound hp (by norm_num : (0 : ℝ) < 1)
    (SmoothL2Field.zeroField : SmoothL2Field Space)
    (fun _ : Icc (0 : ℝ) 1 => (SmoothL2Field.zeroField : SmoothL2Field Space))
    (fun _ => continuous_const)
    (aprioriRadius (S := 1) SmoothL2Field.zeroField (fun _ => SmoothL2Field.zeroField)
      (fun _ => continuous_const) 1 (fun _ => 1) (fun _ => 1) p) := by
  apply hb_of_base (by norm_num) (by norm_num) _ _ _ 0 (by norm_num)
    (zero_mild 6 le_rfl (by norm_num) le_rfl) (fun _ => 1) (fun _ => 1)
    (fun _ => by norm_num) (fun _ => by norm_num)
  exact zero_mildGronwall

end NSFormalization.Section4.A01.Rev193
