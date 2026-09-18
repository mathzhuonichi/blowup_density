import NSFormalization.Section3.T12.HaarCube
import NSFormalization.Section3.T12.FourierEmbeddings
import NSFormalization.Section3.T12.CutoffGagliardo
import NSFormalization.Section3.T12.DirDeriv

/-!
# T12 U5 — `‖∇v‖_{L⁶(T³)} ≤ C₆ ‖Δv‖_{L²(T³)}` for smooth mean-zero periodic fields

`paper/sections/appendix-b-embeddings.tex:26-32`, used at `03-torus.tex:467-477`:
the third displayed critical embedding of Lemma B.1 in its torus form.  This is
the `gradientLSix` field of the reconciled `MeanZeroSobolevCalculusAPI`
(`research/T12/probes/api_on_canonical.lean:184-187`), proved verbatim as

`∀ v, SmoothPeriodicT v → IsMeanZeroT v →
  periodicLpENorm 6 (gradientTensor v) ≤ ENNReal.ofReal Csix * periodicLpENorm 2 (laplacian v)`.

## Route (`research/T12/T12_SPLIT.md` U5, route (c): integer order, no fractional Gagliardo)

1. **Haar → cube.**  `HaarCube.periodicLpENorm_eq_restrict_gradientTensor` turns the
   left side into `eLpNorm (∇v) 6 (volume.restrict fundamentalCube)`.
2. **Localize.**  The lane-365 cutoff `χ = cutoff` is `1` on the ball of radius `5/2`,
   which contains `[0,1]³`, so `∇(χv) = ∇v` on the cube; the cube-restricted norm is
   at most the whole-space norm of `∇(χv)` (`Measure.restrict_le_self`).
3. **Registered whole-space embedding.**  `χv` is smooth with compact support, hence
   `SmoothL2`, so `A05.eLpNorm_gradTensor_six_le` (the estimate registered as
   `Contracts.V1.GradientL6API.gradientLSix`) gives
   `‖∇(χv)‖₆ ≤ gradientL6Const · ‖Δ(χv)‖₂` over `volume`.
4. **Leibniz.**  `Δ(χv) = χ·Δv + 2∑ᵢ (∂ᵢχ)(∂ᵢv) + (Δχ)·v` (`lap_cutoffMul_eq`), giving the
   pointwise majorant `‖Δ(χv) x‖ ≤ leibnizConst · (‖Δv x‖ + ‖∇v x‖ + ‖v x‖)`, supported in
   `closedBall 0 3 = tsupport χ`.
5. **Lattice tiling.**  The majorant is periodic, so `T13.lintegral_eq_tsum_halfOpenCube`
   plus the lane-377 count `CutoffGagliardo.lattice_count_le` (at most `7³ = 343` lattice
   translates meet `closedBall 0 3`) folds the whole-space `L²` norm back onto one cube:
   `‖Δ(χv)‖_{L²(ℝ³)} ≤ 343 · ‖majorant‖_{L²(Q)}`.
6. **Lower-order terms.**  On the torus, `‖v‖_{L²}` and `‖∇v‖_{L²}` are both bounded by
   `hTwoConst · ‖Δv‖_{L²}`: the first by reweighting the order-2 datum by `1/(1+4π²|k|²)`
   and Parseval, the second because `‖∇v‖_{L²(T³)} = ‖v‖_{Ḣ¹(T³)}` (T10's
   `gradient_eq_homogeneousENorm`) and `|2πk| ≤ 1 + 4π²|k|²`; both then use the
   registered `FourierEmbeddings.hTwo_le_laplacian`.

No `sorry`, no `axiom`, no `native_decide`, no named goal input; every declaration
reduces to `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section
namespace NSFormalization.Section3.T12
open Set MeasureTheory Metric
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section4.A05 (dirDeriv lap gradTensor SmoothL2)
open scoped ContDiff ENNReal BigOperators Topology

/-! ## §1  Bounded Fourier multipliers and the two torus lower-order bounds -/


/-- `1/(1+4π²|k|²) ≤ 1`. -/
theorem inverseWeight_abs_le_one (k : PeriodicFrequency) :
    |(periodicFrequencyWeight k)⁻¹| ≤ 1 := by
  have h1 := one_le_fourierWeight k
  rw [abs_of_nonneg (by positivity)]
  rw [inv_le_one₀ (by linarith)]
  exact h1

theorem inverseWeight_even (k : PeriodicFrequency) :
    (periodicFrequencyWeight (-k))⁻¹ = (periodicFrequencyWeight k)⁻¹ := by
  rw [fourierWeight_neg]

/-- `2π|k| ≤ 1 + 4π²|k|²`. -/
theorem homogeneousRatio_one_abs_le_one (k : PeriodicFrequency) :
    |homogeneousDatumWeight 1 k / periodicFrequencyWeight k| ≤ 1 := by
  have hw := fourierWeight_pos k
  have hang : 0 ≤ periodicAngularFrequencySq k := by
    unfold periodicAngularFrequencySq; positivity
  have hnn : 0 ≤ homogeneousDatumWeight 1 k := by
    unfold homogeneousDatumWeight
    split
    · exact le_rfl
    · exact Real.rpow_nonneg hang _
  rw [abs_of_nonneg (div_nonneg hnn hw.le), div_le_one hw]
  by_cases hk : k = 0
  · simp only [homogeneousDatumWeight, hk, ↓reduceIte]
    exact (fourierWeight_pos 0).le
  · have hsq := sqrt_angularFrequencySq_le_weight k
    have heq : homogeneousDatumWeight 1 k = Real.sqrt (periodicAngularFrequencySq k) := by
      simp only [homogeneousDatumWeight, hk, ↓reduceIte, Real.sqrt_eq_rpow]
      rfl
    rw [heq]
    exact hsq

theorem homogeneousDatumWeight_one_even (k : PeriodicFrequency) :
    homogeneousDatumWeight 1 (-k) / periodicFrequencyWeight (-k) =
      homogeneousDatumWeight 1 k / periodicFrequencyWeight k := by
  rw [fourierWeight_neg]
  congr 1
  unfold homogeneousDatumWeight
  simp [neg_eq_zero, angularFrequencySq_neg]

/-! ## Torus lower-order bounds -/

theorem periodicLpENorm_two_le_laplacian {v : SpatialField} (hv : SmoothPeriodicT v)
    (hm : IsMeanZeroT v) :
    periodicLpENorm 2 v ≤ ENNReal.ofReal hTwoConst * periodicLpENorm 2 (laplacian v) := by
  obtain ⟨hs, hp⟩ := hv
  obtain ⟨A, hA⟩ := smooth_periodic_datum (2 : ℝ) hs hp
  have hint : Integrable (torusLift v) periodicTorusMeasure :=
    (memLp_torusLift_vector hs.continuous 1).integrable le_rfl
  let A0 : PeriodicSobolev 0 :=
    ⟨reweightDatum (fun k => (periodicFrequencyWeight k)⁻¹) 1 zero_le_one
        inverseWeight_abs_le_one A.1,
      reweightDatum_real (fun k => (periodicFrequencyWeight k)⁻¹) 1 zero_le_one
        inverseWeight_abs_le_one inverseWeight_even A⟩
  have hA0 : IsPeriodicDatum 0 v A0 := by
    refine ⟨hp, hint, ?_⟩
    intro i k
    have hwne : (periodicFrequencyWeight k : ℂ) ≠ 0 := by
      exact_mod_cast (fourierWeight_pos k).ne'
    change reweightDatum (fun k => (periodicFrequencyWeight k)⁻¹) 1 zero_le_one
      inverseWeight_abs_le_one A.1 i k = _
    rw [reweightDatum_apply, hA.2.2 i k]
    simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_inv,
      show ((2 : ℝ) / 2) = 1 by norm_num, show ((0 : ℝ) / 2) = (0 : ℝ) by norm_num,
      Real.rpow_one, Real.rpow_zero, Complex.ofReal_one, one_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hwne, one_mul]
  calc periodicLpENorm 2 v = ‖A0.1‖ₑ :=
        (parseval_forward v A0 hA0 (memLp_torusLift_vector hs.continuous 2)).symm
    _ ≤ ENNReal.ofReal 1 * ‖A.1‖ₑ :=
        reweightDatum_enorm_le' (fun k => (periodicFrequencyWeight k)⁻¹) 1 zero_le_one
          inverseWeight_abs_le_one A.1
    _ = periodicSobolevENorm 2 v := by
        rw [periodicSobolevENorm_eq hA, ENNReal.ofReal_one, one_mul]
        rfl
    _ ≤ ENNReal.ofReal hTwoConst * periodicLpENorm 2 (laplacian v) :=
        hTwo_le_laplacian v ⟨hs, hp⟩ hm

theorem periodicHomogeneousENorm_one_le_sobolev_two {v : SpatialField}
    (hv : SmoothPeriodicT v) (hm : IsMeanZeroT v) :
    periodicHomogeneousENorm 1 v ≤ periodicSobolevENorm 2 v := by
  obtain ⟨hs, hp⟩ := hv
  obtain ⟨A, hA⟩ := smooth_periodic_datum (2 : ℝ) hs hp
  have hint : Integrable (torusLift v) periodicTorusMeasure :=
    (memLp_torusLift_vector hs.continuous 1).integrable le_rfl
  let A1 : PeriodicSobolev 1 :=
    ⟨reweightDatum (fun k => homogeneousDatumWeight 1 k / periodicFrequencyWeight k) 1
        zero_le_one homogeneousRatio_one_abs_le_one A.1,
      reweightDatum_real (fun k => homogeneousDatumWeight 1 k / periodicFrequencyWeight k) 1
        zero_le_one homogeneousRatio_one_abs_le_one homogeneousDatumWeight_one_even A⟩
  have hA1 : IsPeriodicHomogeneousDatum 1 v A1 := by
    refine ⟨hp, hint, hm, ?_⟩
    intro i k
    have hwne : (periodicFrequencyWeight k : ℂ) ≠ 0 := by
      exact_mod_cast (fourierWeight_pos k).ne'
    change reweightDatum (fun k => homogeneousDatumWeight 1 k / periodicFrequencyWeight k) 1
      zero_le_one homogeneousRatio_one_abs_le_one A.1 i k = _
    rw [reweightDatum_apply, hA.2.2 i k]
    simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_div,
      show ((2 : ℝ) / 2) = 1 by norm_num, Real.rpow_one]
    rw [← mul_assoc, div_mul_cancel₀ _ hwne]
  calc periodicHomogeneousENorm 1 v ≤ ‖A1.1‖ₑ := iInf_le_of_le ⟨A1, hA1⟩ le_rfl
    _ ≤ ENNReal.ofReal 1 * ‖A.1‖ₑ :=
        reweightDatum_enorm_le' (fun k => homogeneousDatumWeight 1 k / periodicFrequencyWeight k)
          1 zero_le_one homogeneousRatio_one_abs_le_one A.1
    _ = periodicSobolevENorm 2 v := by
        rw [periodicSobolevENorm_eq hA, ENNReal.ofReal_one, one_mul]
        rfl

theorem periodicLpENorm_gradientTensor_le_laplacian {v : SpatialField}
    (hv : SmoothPeriodicT v) (hm : IsMeanZeroT v) :
    periodicLpENorm 2 (gradientTensor v) ≤
      ENNReal.ofReal hTwoConst * periodicLpENorm 2 (laplacian v) := by
  calc periodicLpENorm 2 (gradientTensor v)
      = periodicHomogeneousENorm 1 (meanZeroPartT v) :=
        NSFormalization.Section3.T10.gradient_eq_homogeneousENorm hv.1 hv.2
    _ = periodicHomogeneousENorm 1 v := by rw [meanZeroPartT_eq_self hm]
    _ ≤ periodicSobolevENorm 2 v := periodicHomogeneousENorm_one_le_sobolev_two hv hm
    _ ≤ ENNReal.ofReal hTwoConst * periodicLpENorm 2 (laplacian v) :=
        hTwo_le_laplacian v hv hm

/-! ## §2  Calculus helpers for the cutoff product -/


variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

-- `contDiff_dirDeriv` moved verbatim to `NSFormalization.Section3.T12.DirDeriv`
-- (lane 427 dedupe with `GradientLambdaL3.lean`); it is imported above.

theorem hasCompactSupport_dirDeriv {w : Space → F} (hw : HasCompactSupport w)
    (i : Fin 3) : HasCompactSupport (dirDeriv i w) := by
  have h : HasCompactSupport (fderiv ℝ w) := hw.fderiv ℝ
  exact h.comp_left (g := fun T : Space →L[ℝ] F => T (coordinateVector i)) (by simp)

theorem dirDeriv_smul_eq {c : Space → ℝ} {w : Space → F} (hc : ContDiff ℝ ∞ c)
    (hw : ContDiff ℝ ∞ w) (i : Fin 3) :
    dirDeriv i (fun x => c x • w x)
      = fun x => c x • dirDeriv i w x + (dirDeriv i c x) • w x := by
  funext x
  show fderiv ℝ (c • w) x (coordinateVector i) = _
  rw [fderiv_smul (hc.differentiable (by simp) x) (hw.differentiable (by simp) x)]
  simp [dirDeriv]

theorem dirDeriv_add_eq {f g : Space → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (i : Fin 3) :
    dirDeriv i (fun x => f x + g x) = fun x => dirDeriv i f x + dirDeriv i g x := by
  funext x
  show fderiv ℝ (f + g) x (coordinateVector i) = _
  rw [fderiv_add (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)]
  rfl

/-! ## Leibniz for the cutoff product -/

theorem dirDeriv_cutoffMul_eq {v : SpatialField} (hv : ContDiff ℝ ∞ v) (i : Fin 3) :
    dirDeriv i (cutoffMul v)
      = fun x => cutoff x • dirDeriv i v x + (dirDeriv i cutoff x) • v x :=
  dirDeriv_smul_eq cutoff_contDiff hv i

theorem dirDeriv_two_cutoffMul {v : SpatialField} (hv : ContDiff ℝ ∞ v) (i : Fin 3)
    (x : Space) :
    dirDeriv i (dirDeriv i (cutoffMul v)) x
      = cutoff x • dirDeriv i (dirDeriv i v) x
        + ((dirDeriv i cutoff x) • dirDeriv i v x + (dirDeriv i cutoff x) • dirDeriv i v x)
        + (dirDeriv i (dirDeriv i cutoff) x) • v x := by
  have hf : ContDiff ℝ ∞ (fun y => cutoff y • dirDeriv i v y) :=
    cutoff_contDiff.smul (contDiff_dirDeriv hv i)
  have hg : ContDiff ℝ ∞ (fun y => (dirDeriv i cutoff y) • v y) :=
    (contDiff_dirDeriv cutoff_contDiff i).smul hv
  rw [dirDeriv_cutoffMul_eq hv i, dirDeriv_add_eq hf hg i,
    dirDeriv_smul_eq cutoff_contDiff (contDiff_dirDeriv hv i) i,
    dirDeriv_smul_eq (contDiff_dirDeriv cutoff_contDiff i) hv i]
  simp only [add_assoc]

theorem lap_cutoffMul_eq {v : SpatialField} (hv : ContDiff ℝ ∞ v) (x : Space) :
    lap (cutoffMul v) x
      = cutoff x • lap v x
        + (∑ i : Fin 3, ((dirDeriv i cutoff x) • dirDeriv i v x
            + (dirDeriv i cutoff x) • dirDeriv i v x))
        + (lap cutoff x) • v x := by
  show ∑ i : Fin 3, dirDeriv i (dirDeriv i (cutoffMul v)) x = _
  simp_rw [dirDeriv_two_cutoffMul hv]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  · congr 1
    show ∑ i : Fin 3, cutoff x • dirDeriv i (dirDeriv i v) x = cutoff x • lap v x
    rw [← Finset.smul_sum]
    rfl
  · show ∑ i : Fin 3, (dirDeriv i (dirDeriv i cutoff) x) • v x = (lap cutoff x) • v x
    rw [← Finset.sum_smul]
    rfl

/-! ## Constants from the cutoff -/

theorem contDiff_lap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {w : Space → E} (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (lap w) := by
  show ContDiff ℝ ∞ fun x => ∑ i : Fin 3, dirDeriv i (dirDeriv i w) x
  exact ContDiff.sum fun i _ => contDiff_dirDeriv (contDiff_dirDeriv hw i) i

theorem hasCompactSupport_lap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {w : Space → E} (hw : HasCompactSupport w) : HasCompactSupport (lap w) := by
  have h : ∀ i : Fin 3, HasCompactSupport (dirDeriv i (dirDeriv i w)) := fun i =>
    hasCompactSupport_dirDeriv (hasCompactSupport_dirDeriv hw i) i
  show HasCompactSupport fun x => ∑ i : Fin 3, dirDeriv i (dirDeriv i w) x
  have he : (fun x => ∑ i : Fin 3, dirDeriv i (dirDeriv i w) x)
      = dirDeriv 0 (dirDeriv 0 w) + dirDeriv 1 (dirDeriv 1 w) + dirDeriv 2 (dirDeriv 2 w) := by
    funext x
    simp [Fin.sum_univ_three]
  rw [he]
  exact ((h 0).add (h 1)).add (h 2)

theorem exists_cutoff_lap_bound : ∃ M : ℝ, ∀ x : Space, ‖lap cutoff x‖ ≤ M :=
  (contDiff_lap cutoff_contDiff).continuous.bounded_above_of_compact_support
    (hasCompactSupport_lap hasCompactSupport_cutoff)

theorem smoothL2_cutoffMul {v : SpatialField} (hv : ContDiff ℝ ∞ v) :
    SmoothL2 (cutoffMul v) := by
  refine ⟨contDiff_cutoffMul hv, fun n => ?_⟩
  exact Continuous.memLp_of_hasCompactSupport
    ((contDiff_cutoffMul hv).continuous_iteratedFDeriv (by norm_num))
    ((hasCompactSupport_cutoffMul v).iteratedFDeriv n)

theorem norm_coordinateVector (i : Fin 3) : ‖coordinateVector i‖ = 1 := by
  simp [coordinateVector]

theorem norm_dirDeriv_le_norm_gradTensor (v : SpatialField) (i : Fin 3) (x : Space) :
    ‖dirDeriv i v x‖ ≤ ‖gradTensor v x‖ :=
  PiLp.norm_apply_le (gradTensor v x) i

/-! ## The explicit cutoff constants -/

def cutoffGradBound : ℝ := Classical.choose exists_cutoff_fderiv_bound

theorem cutoffGradBound_spec (x : Space) : ‖fderiv ℝ cutoff x‖ ≤ cutoffGradBound :=
  Classical.choose_spec exists_cutoff_fderiv_bound x

theorem cutoffGradBound_nonneg : 0 ≤ cutoffGradBound :=
  le_trans (norm_nonneg _) (cutoffGradBound_spec 0)

theorem norm_dirDeriv_cutoff_le (i : Fin 3) (x : Space) :
    ‖dirDeriv i cutoff x‖ ≤ cutoffGradBound := by
  have h : ‖fderiv ℝ cutoff x (coordinateVector i)‖
      ≤ ‖fderiv ℝ cutoff x‖ * ‖coordinateVector i‖ := ContinuousLinearMap.le_opNorm _ _
  rw [norm_coordinateVector, mul_one] at h
  exact h.trans (cutoffGradBound_spec x)

def cutoffLapBound : ℝ := Classical.choose exists_cutoff_lap_bound

theorem cutoffLapBound_spec (x : Space) : ‖lap cutoff x‖ ≤ cutoffLapBound :=
  Classical.choose_spec exists_cutoff_lap_bound x

theorem cutoffLapBound_nonneg : 0 ≤ cutoffLapBound :=
  le_trans (norm_nonneg _) (cutoffLapBound_spec 0)

def leibnizConst : ℝ := 1 + 6 * cutoffGradBound + cutoffLapBound

theorem leibnizConst_pos : 0 < leibnizConst := by
  have h1 := cutoffGradBound_nonneg
  have h2 := cutoffLapBound_nonneg
  unfold leibnizConst
  linarith

theorem norm_lap_cutoffMul_le {v : SpatialField} (hv : ContDiff ℝ ∞ v) (x : Space) :
    ‖lap (cutoffMul v) x‖
      ≤ leibnizConst * (‖lap v x‖ + ‖gradTensor v x‖ + ‖v x‖) := by
  have hM1 := cutoffGradBound_nonneg
  have hM2 := cutoffLapBound_nonneg
  have hL := norm_nonneg (lap v x)
  have hG := norm_nonneg (gradTensor v x)
  have hV := norm_nonneg (v x)
  have hchi : |cutoff x| ≤ 1 := by
    have h := cutoff_range x
    rw [abs_le]
    exact ⟨by linarith [h.1], h.2⟩
  have hA : ‖cutoff x • lap v x‖ ≤ ‖lap v x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    nlinarith
  have hS : ‖∑ i : Fin 3, ((dirDeriv i cutoff x) • dirDeriv i v x
        + (dirDeriv i cutoff x) • dirDeriv i v x)‖
      ≤ 6 * cutoffGradBound * ‖gradTensor v x‖ := by
    calc ‖∑ i : Fin 3, ((dirDeriv i cutoff x) • dirDeriv i v x
            + (dirDeriv i cutoff x) • dirDeriv i v x)‖
        ≤ ∑ i : Fin 3, ‖(dirDeriv i cutoff x) • dirDeriv i v x
            + (dirDeriv i cutoff x) • dirDeriv i v x‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 3, 2 * (cutoffGradBound * ‖gradTensor v x‖) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hchi' := norm_dirDeriv_cutoff_le i x
          have hgrad := norm_dirDeriv_le_norm_gradTensor v i x
          have hpt : ‖(dirDeriv i cutoff x) • dirDeriv i v x‖
              ≤ cutoffGradBound * ‖gradTensor v x‖ := by
            rw [norm_smul]
            exact mul_le_mul hchi' hgrad (norm_nonneg _) hM1
          calc ‖(dirDeriv i cutoff x) • dirDeriv i v x
                + (dirDeriv i cutoff x) • dirDeriv i v x‖
              ≤ ‖(dirDeriv i cutoff x) • dirDeriv i v x‖
                + ‖(dirDeriv i cutoff x) • dirDeriv i v x‖ := norm_add_le _ _
            _ ≤ 2 * (cutoffGradBound * ‖gradTensor v x‖) := by linarith
      _ = 6 * cutoffGradBound * ‖gradTensor v x‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hC : ‖(lap cutoff x) • v x‖ ≤ cutoffLapBound * ‖v x‖ := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (cutoffLapBound_spec x) (norm_nonneg _)
  rw [lap_cutoffMul_eq hv x]
  calc ‖cutoff x • lap v x
        + (∑ i : Fin 3, ((dirDeriv i cutoff x) • dirDeriv i v x
            + (dirDeriv i cutoff x) • dirDeriv i v x))
        + (lap cutoff x) • v x‖
      ≤ ‖cutoff x • lap v x
          + (∑ i : Fin 3, ((dirDeriv i cutoff x) • dirDeriv i v x
              + (dirDeriv i cutoff x) • dirDeriv i v x))‖
        + ‖(lap cutoff x) • v x‖ := norm_add_le _ _
    _ ≤ (‖cutoff x • lap v x‖
          + ‖∑ i : Fin 3, ((dirDeriv i cutoff x) • dirDeriv i v x
              + (dirDeriv i cutoff x) • dirDeriv i v x)‖)
        + ‖(lap cutoff x) • v x‖ := by
          gcongr
          exact norm_add_le _ _
    _ ≤ (‖lap v x‖ + 6 * cutoffGradBound * ‖gradTensor v x‖)
        + cutoffLapBound * ‖v x‖ := by gcongr
    _ ≤ leibnizConst * (‖lap v x‖ + ‖gradTensor v x‖ + ‖v x‖) := by
          unfold leibnizConst
          nlinarith [mul_nonneg hM1 hL, mul_nonneg hM1 hV, mul_nonneg hM2 hL,
            mul_nonneg hM2 hG]

/-! ## Support of the localized field -/

theorem tsupport_cutoff_eq : tsupport cutoff = closedBall (0 : Space) 3 := by
  change tsupport (cutoffBump : Space → ℝ) = _
  rw [cutoffBump.tsupport_eq]
  norm_num [cutoffBump]

theorem support_cutoffMul_subset (v : SpatialField) :
    Function.support (cutoffMul v) ⊆ closedBall (0 : Space) 3 := by
  intro x hx
  rw [← tsupport_cutoff_eq]
  apply subset_tsupport
  intro h
  exact hx (by simp [cutoffMul, h])

theorem eqOn_zero_dirDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w : Space → E} {U : Set Space} (hU : IsOpen U) (hw : EqOn w 0 U) (i : Fin 3) :
    EqOn (dirDeriv i w) 0 U := by
  intro y hy
  have hev : w =ᶠ[𝓝 y] (fun _ => (0 : E)) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hy) (fun z hz => hw hz)
  show fderiv ℝ w y (coordinateVector i) = 0
  rw [hev.fderiv_eq]
  simp

theorem eqOn_zero_lap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {w : Space → E} {U : Set Space} (hU : IsOpen U) (hw : EqOn w 0 U) :
    EqOn (lap w) 0 U := by
  intro y hy
  show ∑ i : Fin 3, dirDeriv i (dirDeriv i w) y = 0
  refine Finset.sum_eq_zero fun i _ => ?_
  exact eqOn_zero_dirDeriv hU (eqOn_zero_dirDeriv hU hw i) i hy

theorem lap_cutoffMul_eq_zero (v : SpatialField) {x : Space}
    (hx : x ∉ closedBall (0 : Space) 3) : lap (cutoffMul v) x = 0 := by
  have hU : IsOpen ((closedBall (0 : Space) 3)ᶜ) := isClosed_closedBall.isOpen_compl
  have hw : EqOn (cutoffMul v) 0 ((closedBall (0 : Space) 3)ᶜ) := by
    intro y hy
    by_contra h
    exact hy (support_cutoffMul_subset v h)
  exact eqOn_zero_lap hU hw hx

/-! ## The periodic majorant and the lattice count -/

def leibnizMajorant (v : SpatialField) : Space → ℝ :=
  fun x => leibnizConst * (‖lap v x‖ + ‖gradTensor v x‖ + ‖v x‖)

theorem leibnizMajorant_nonneg (v : SpatialField) (x : Space) : 0 ≤ leibnizMajorant v x := by
  have h := leibnizConst_pos
  have := norm_nonneg (lap v x)
  have := norm_nonneg (gradTensor v x)
  have := norm_nonneg (v x)
  unfold leibnizMajorant
  positivity

theorem norm_gradTensor_eq (v : SpatialField) (x : Space) :
    ‖gradTensor v x‖ = Real.sqrt (∑ j : Fin 3, ‖dirDeriv j v x‖ ^ 2) := by
  rw [PiLp.norm_eq_of_L2]
  rfl

theorem continuous_norm_gradTensor {v : SpatialField} (hv : ContDiff ℝ ∞ v) :
    Continuous (fun x => ‖gradTensor v x‖) := by
  have he : (fun x => ‖gradTensor v x‖)
      = fun x => Real.sqrt (∑ j : Fin 3, ‖dirDeriv j v x‖ ^ 2) := by
    funext x
    exact norm_gradTensor_eq v x
  rw [he]
  exact Real.continuous_sqrt.comp
    (continuous_finsetSum _ fun j _ => ((contDiff_dirDeriv hv j).continuous.norm.pow 2))

theorem continuous_leibnizMajorant {v : SpatialField} (hv : ContDiff ℝ ∞ v) :
    Continuous (leibnizMajorant v) :=
  continuous_const.mul
    ((((contDiff_lap hv).continuous.norm).add (continuous_norm_gradTensor hv)).add
      hv.continuous.norm)

theorem isPeriodicSpatial_gradientTensor {v : SpatialField} (hp : IsPeriodicSpatial v) :
    IsPeriodicSpatial (gradTensor v) := by
  intro x j
  show (WithLp.toLp 2 (fun i => dirDeriv i v (x + coordinateVector j)))
      = WithLp.toLp 2 (fun i => dirDeriv i v x)
  congr 1
  funext i
  exact NavierStokes.PeriodicUniqueness.spatial_partial_periodic (fun y l => hp y l) i x j

theorem isPeriodicSpatial_leibnizMajorant {v : SpatialField} (hp : IsPeriodicSpatial v) :
    IsPeriodicSpatial (leibnizMajorant v) := by
  intro x j
  show leibnizConst * (‖lap v (x + coordinateVector j)‖
      + ‖gradTensor v (x + coordinateVector j)‖ + ‖v (x + coordinateVector j)‖)
    = leibnizConst * (‖lap v x‖ + ‖gradTensor v x‖ + ‖v x‖)
  have hlap : lap v (x + coordinateVector j) = lap v x := isPeriodicSpatial_laplacian hp x j
  rw [hlap, isPeriodicSpatial_gradientTensor hp x j, hp x j]

theorem enorm_lap_cutoffMul_le {v : SpatialField} (hv : ContDiff ℝ ∞ v) (z : Space) :
    ‖lap (cutoffMul v) z‖ₑ ^ (2 : ℝ)
      ≤ (closedBall (0 : Space) 3).indicator (fun _ => (1 : ℝ≥0∞)) z
          * ‖leibnizMajorant v z‖ₑ ^ (2 : ℝ) := by
  by_cases hz : z ∈ closedBall (0 : Space) 3
  · rw [Set.indicator_of_mem hz, one_mul]
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    rw [← ofReal_norm, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (leibnizMajorant_nonneg v z)]
    exact norm_lap_cutoffMul_le hv z
  · rw [Set.indicator_of_notMem hz, lap_cutoffMul_eq_zero v hz, zero_mul, enorm_zero,
      ENNReal.zero_rpow_of_pos (by norm_num)]

/-! ## The lattice tiling estimate -/

theorem measurable_enn_sq : Measurable (fun x : ℝ≥0∞ => x ^ (2 : ℝ)) := by fun_prop

theorem lintegral_lap_cutoffMul_le {v : SpatialField} (hv : SmoothPeriodicT v) :
    ∫⁻ x : Space, ‖lap (cutoffMul v) x‖ₑ ^ (2 : ℝ)
      ≤ 343 * ∫⁻ y in halfOpenCube, ‖leibnizMajorant v y‖ₑ ^ (2 : ℝ) := by
  have hmajM : Measurable (fun y : Space => ‖leibnizMajorant v y‖ₑ ^ (2 : ℝ)) :=
    measurable_enn_sq.comp (continuous_leibnizMajorant hv.1).measurable.enorm
  have hmeasLHS : Measurable (fun x : Space => ‖lap (cutoffMul v) x‖ₑ ^ (2 : ℝ)) :=
    measurable_enn_sq.comp
      (contDiff_lap (contDiff_cutoffMul hv.1)).continuous.measurable.enorm
  have hind : Measurable ((closedBall (0 : Space) 3).indicator (fun _ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator measurableSet_closedBall
  have hterm : ∀ n : PeriodicFrequency, Measurable (fun y : Space =>
      (closedBall (0 : Space) 3).indicator (fun _ => (1 : ℝ≥0∞)) (y + latticeVector n)
        * ‖leibnizMajorant v y‖ₑ ^ (2 : ℝ)) := fun n =>
    (hind.comp (measurable_id.add_const (latticeVector n))).mul hmajM
  rw [lintegral_eq_tsum_halfOpenCube hmeasLHS]
  calc ∑' n : PeriodicFrequency, ∫⁻ y in halfOpenCube,
          ‖lap (cutoffMul v) (y + latticeVector n)‖ₑ ^ (2 : ℝ)
      ≤ ∑' n : PeriodicFrequency, ∫⁻ y in halfOpenCube,
          (closedBall (0 : Space) 3).indicator (fun _ => (1 : ℝ≥0∞)) (y + latticeVector n)
            * ‖leibnizMajorant v y‖ₑ ^ (2 : ℝ) := by
        refine ENNReal.tsum_le_tsum fun n => lintegral_mono fun y => ?_
        have h := enorm_lap_cutoffMul_le hv.1 (y + latticeVector n)
        rwa [periodic_latticeVector (isPeriodicSpatial_leibnizMajorant hv.2) y n] at h
    _ = ∫⁻ y in halfOpenCube, ∑' n : PeriodicFrequency,
          (closedBall (0 : Space) 3).indicator (fun _ => (1 : ℝ≥0∞)) (y + latticeVector n)
            * ‖leibnizMajorant v y‖ₑ ^ (2 : ℝ) :=
        (lintegral_tsum fun n => (hterm n).aemeasurable).symm
    _ = ∫⁻ y in halfOpenCube, (∑' n : PeriodicFrequency,
          (closedBall (0 : Space) 3).indicator (fun _ => (1 : ℝ≥0∞)) (y + latticeVector n))
            * ‖leibnizMajorant v y‖ₑ ^ (2 : ℝ) := by
        refine lintegral_congr fun y => ?_
        rw [ENNReal.tsum_mul_right]
    _ ≤ ∫⁻ y in halfOpenCube, (343 : ℝ≥0∞) * ‖leibnizMajorant v y‖ₑ ^ (2 : ℝ) :=
        lintegral_mono fun y => mul_le_mul' (lattice_count_le y) le_rfl
    _ = 343 * ∫⁻ y in halfOpenCube, ‖leibnizMajorant v y‖ₑ ^ (2 : ℝ) :=
        lintegral_const_mul _ hmajM

theorem eLpNorm_lap_cutoffMul_le {v : SpatialField} (hv : SmoothPeriodicT v) :
    eLpNorm (lap (cutoffMul v)) 2 volume
      ≤ 343 * eLpNorm (leibnizMajorant v) 2 (volume.restrict fundamentalCube) := by
  have hQ : (volume : Measure Space).restrict fundamentalCube
      = (volume : Measure Space).restrict halfOpenCube :=
    Measure.restrict_congr_set fundamentalCube_ae_eq_halfOpenCube
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), hQ,
    show (2 : ℝ≥0∞).toReal = 2 by norm_num]
  calc (∫⁻ x : Space, ‖lap (cutoffMul v) x‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
      ≤ (343 * ∫⁻ y in halfOpenCube, ‖leibnizMajorant v y‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.rpow_le_rpow (lintegral_lap_cutoffMul_le hv) (by norm_num)
    _ = (343 : ℝ≥0∞) ^ (1 / (2 : ℝ))
        * (∫⁻ y in halfOpenCube, ‖leibnizMajorant v y‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
    _ ≤ 343 * (∫⁻ y in halfOpenCube, ‖leibnizMajorant v y‖ₑ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
        gcongr
        calc (343 : ℝ≥0∞) ^ (1 / (2 : ℝ)) ≤ (343 : ℝ≥0∞) ^ (1 : ℝ) :=
              ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 343 := ENNReal.rpow_one _

/-! ## §4  The cube comparison, the constant, and the API field -/

/-- On the fundamental cube the cutoff is identically one on a neighbourhood, so the
gradient tensors of `v` and of the localization `χv` agree there. -/
theorem gradTensor_cutoffMul_eqOn (v : SpatialField) :
    EqOn (gradTensor (cutoffMul v)) (gradTensor v) fundamentalCube := by
  intro x hx
  have hball : ball (0 : Space) (5 / 2) ∈ 𝓝 x := by
    refine Metric.isOpen_ball.mem_nhds ?_
    rw [mem_ball, dist_zero_right]
    exact (norm_le_two_of_mem_fundamentalCube hx).trans_lt (by norm_num)
  have hev : cutoffMul v =ᶠ[𝓝 x] v :=
    Filter.eventuallyEq_of_mem hball fun y hy => by
      simp [cutoffMul, cutoff_eq_one_on_ball hy]
  show WithLp.toLp 2 (fun i => dirDeriv i (cutoffMul v) x)
    = WithLp.toLp 2 (fun i => dirDeriv i v x)
  congr 1
  funext i
  show fderiv ℝ (cutoffMul v) x (coordinateVector i) = fderiv ℝ v x (coordinateVector i)
  rw [hev.fderiv_eq]

theorem eLpNorm_leibnizMajorant_le {v : SpatialField} (hv : ContDiff ℝ ∞ v)
    (μ : Measure Space) :
    eLpNorm (leibnizMajorant v) 2 μ
      ≤ ENNReal.ofReal leibnizConst
          * (eLpNorm (lap v) 2 μ + eLpNorm (gradTensor v) 2 μ + eLpNorm v 2 μ) := by
  have hm1 : AEStronglyMeasurable (fun x => ‖lap v x‖) μ :=
    (contDiff_lap hv).continuous.norm.aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun x => ‖gradTensor v x‖) μ :=
    (continuous_norm_gradTensor hv).aestronglyMeasurable
  have hm3 : AEStronglyMeasurable (fun x => ‖v x‖) μ :=
    hv.continuous.norm.aestronglyMeasurable
  have hc : ‖leibnizConst‖ₑ = ENNReal.ofReal leibnizConst := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg leibnizConst_pos.le]
  have hsmul : leibnizMajorant v
      = leibnizConst • (fun x => ‖lap v x‖ + ‖gradTensor v x‖ + ‖v x‖) := rfl
  calc eLpNorm (leibnizMajorant v) 2 μ
      = eLpNorm (leibnizConst • (fun x => ‖lap v x‖ + ‖gradTensor v x‖ + ‖v x‖)) 2 μ := by
        rw [hsmul]
    _ ≤ ‖leibnizConst‖ₑ
          * eLpNorm (fun x => ‖lap v x‖ + ‖gradTensor v x‖ + ‖v x‖) 2 μ :=
        eLpNorm_const_smul_le
    _ = ENNReal.ofReal leibnizConst
          * eLpNorm (fun x => ‖lap v x‖ + ‖gradTensor v x‖ + ‖v x‖) 2 μ := by rw [hc]
    _ ≤ ENNReal.ofReal leibnizConst
          * (eLpNorm (lap v) 2 μ + eLpNorm (gradTensor v) 2 μ + eLpNorm v 2 μ) := by
        gcongr
        calc eLpNorm (fun x => ‖lap v x‖ + ‖gradTensor v x‖ + ‖v x‖) 2 μ
            ≤ eLpNorm (fun x => ‖lap v x‖ + ‖gradTensor v x‖) 2 μ
              + eLpNorm (fun x => ‖v x‖) 2 μ := eLpNorm_add_le (hm1.add hm2) hm3 (by norm_num)
          _ ≤ (eLpNorm (fun x => ‖lap v x‖) 2 μ + eLpNorm (fun x => ‖gradTensor v x‖) 2 μ)
              + eLpNorm (fun x => ‖v x‖) 2 μ := by
                gcongr
                exact eLpNorm_add_le hm1 hm2 (by norm_num)
          _ = eLpNorm (lap v) 2 μ + eLpNorm (gradTensor v) 2 μ + eLpNorm v 2 μ := by
                rw [eLpNorm_norm, eLpNorm_norm, eLpNorm_norm]

/-- The explicit constant of the torus `L⁶` gradient embedding: the registered
whole-space constant `A05.gradientL6Const`, the lattice count `7³ = 343`, the Leibniz
constant of the cutoff, and the mean-zero `H²`/Laplacian comparison `hTwoConst`. -/
def Csix : ℝ :=
  343 * NSFormalization.Section4.A05.gradientL6Const * leibnizConst * (1 + 2 * hTwoConst)

theorem Csix_pos : 0 < Csix := by
  have h1 := NSFormalization.Section4.A05.gradientL6Const_pos
  have h2 := leibnizConst_pos
  have h3 := hTwoConst_pos
  have h4 : (0 : ℝ) < 343 * NSFormalization.Section4.A05.gradientL6Const := by linarith
  have h5 : (0 : ℝ) < 1 + 2 * hTwoConst := by linarith
  exact mul_pos (mul_pos h4 h2) h5

theorem ofReal_Csix :
    ENNReal.ofReal Csix
      = (343 : ℝ≥0∞) * ENNReal.ofReal NSFormalization.Section4.A05.gradientL6Const
          * ENNReal.ofReal leibnizConst * ENNReal.ofReal (1 + 2 * hTwoConst) := by
  have h1 := NSFormalization.Section4.A05.gradientL6Const_pos
  have h2 := leibnizConst_pos
  have h3 := hTwoConst_pos
  have hA : (0 : ℝ) ≤ 343 * NSFormalization.Section4.A05.gradientL6Const := by linarith
  have hB : (0 : ℝ) ≤ 343 * NSFormalization.Section4.A05.gradientL6Const * leibnizConst :=
    mul_nonneg hA h2.le
  unfold Csix
  rw [ENNReal.ofReal_mul hB, ENNReal.ofReal_mul hA,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 343), ENNReal.ofReal_ofNat]

/-- `appendix-b-embeddings.tex:26-32`, used at `03-torus.tex:467-477`: the
`gradientLSix` field of `MeanZeroSobolevCalculusAPI`, verbatim, with `Csix`. -/
theorem gradientLSix :
    ∀ v : SpatialField, SmoothPeriodicT v → IsMeanZeroT v →
      periodicLpENorm 6 (gradientTensor v) ≤
        ENNReal.ofReal Csix * periodicLpENorm 2 (laplacian v) := by
  intro v hv hm
  have hTwo := hTwoConst_pos
  have hLQ : eLpNorm (lap v) 2 (volume.restrict fundamentalCube)
      = periodicLpENorm 2 (laplacian v) :=
    (periodicLpENorm_eq_restrict (laplacian v) (isPeriodicSpatial_laplacian hv.2) 2).symm
  have hVQ : eLpNorm v 2 (volume.restrict fundamentalCube) = periodicLpENorm 2 v :=
    (periodicLpENorm_eq_restrict v hv.2 2).symm
  have hGQ : eLpNorm (gradTensor v) 2 (volume.restrict fundamentalCube)
      = periodicLpENorm 2 (gradientTensor v) :=
    (periodicLpENorm_eq_restrict_gradientTensor v
      (isPeriodicSpatial_gradientTensor hv.2) 2).symm
  have hcoef : periodicLpENorm 2 (laplacian v)
        + ENNReal.ofReal hTwoConst * periodicLpENorm 2 (laplacian v)
        + ENNReal.ofReal hTwoConst * periodicLpENorm 2 (laplacian v)
      = ENNReal.ofReal (1 + 2 * hTwoConst) * periodicLpENorm 2 (laplacian v) := by
    rw [ENNReal.ofReal_add (by norm_num) (by linarith),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat]
    ring
  calc periodicLpENorm 6 (gradientTensor v)
      = eLpNorm (gradTensor v) 6 (volume.restrict fundamentalCube) :=
        periodicLpENorm_eq_restrict_gradientTensor v
          (isPeriodicSpatial_gradientTensor hv.2) 6
    _ = eLpNorm (gradTensor (cutoffMul v)) 6 (volume.restrict fundamentalCube) :=
        (eLpNorm_congr_ae (ae_restrict_of_forall_mem measurableSet_fundamentalCube
          fun x hx => gradTensor_cutoffMul_eqOn v hx)).symm
    _ ≤ eLpNorm (gradTensor (cutoffMul v)) 6 volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
    _ ≤ ENNReal.ofReal NSFormalization.Section4.A05.gradientL6Const
          * eLpNorm (lap (cutoffMul v)) 2 volume :=
        NSFormalization.Section4.A05.eLpNorm_gradTensor_six_le (smoothL2_cutoffMul hv.1)
    _ ≤ ENNReal.ofReal NSFormalization.Section4.A05.gradientL6Const
          * (343 * eLpNorm (leibnizMajorant v) 2 (volume.restrict fundamentalCube)) := by
        gcongr
        exact eLpNorm_lap_cutoffMul_le hv
    _ ≤ ENNReal.ofReal NSFormalization.Section4.A05.gradientL6Const
          * (343 * (ENNReal.ofReal leibnizConst
            * (periodicLpENorm 2 (laplacian v) + periodicLpENorm 2 (gradientTensor v)
              + periodicLpENorm 2 v))) := by
        gcongr
        have h := eLpNorm_leibnizMajorant_le hv.1 (volume.restrict fundamentalCube)
        rwa [hLQ, hGQ, hVQ] at h
    _ ≤ ENNReal.ofReal NSFormalization.Section4.A05.gradientL6Const
          * (343 * (ENNReal.ofReal leibnizConst
            * (periodicLpENorm 2 (laplacian v)
              + ENNReal.ofReal hTwoConst * periodicLpENorm 2 (laplacian v)
              + ENNReal.ofReal hTwoConst * periodicLpENorm 2 (laplacian v)))) := by
        gcongr
        · exact periodicLpENorm_gradientTensor_le_laplacian hv hm
        · exact periodicLpENorm_two_le_laplacian hv hm
    _ = ENNReal.ofReal Csix * periodicLpENorm 2 (laplacian v) := by
        rw [hcoef, ofReal_Csix]
        ring

end NSFormalization.Section3.T12
