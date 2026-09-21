import NSFormalization.Section4.R43.Endpoint

/-! Theorem 4.1(ii), the non-density direction for q = 1.
The threshold 1/2 is `Thresholds.lean`'s `ThresholdAPI.l1` at s = 0,
or the first equality of `ThresholdAPI.energy`. -/
noncomputable section
open Set MeasureTheory
open NSFormalization.Paper3 NSFormalization.Source.RealSobolev
open scoped ENNReal

namespace NSFormalization.Section4.R41
open A02 (SpaceTimeField SpatialField maximalLifespanR)
open D01

/-- Angular order lowering is contractive, by its unitary multiplier model. -/
theorem angularOrderLowering_norm_le (s r : ℝ) (hrs : r ≤ s) (v : FourierData) :
    ‖angularOrderLowering s r hrs v‖ ≤ ‖v‖ := by
  rw [angularOrderLowering_eq_dilation_mid, angularFrequencyDilation.norm_map]
  calc
    _ ≤ ‖angularFrequencyDilation.symm v‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [angularOrderLoweringMid_coeFn s r hrs
        (angularFrequencyDilation.symm v)] with ξ hξ
      rw [hξ, lowering_mid_symbol_eq, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (sobolevBesselWeight_norm_le_one (sub_nonpos.mpr hrs) _)
    _ = ‖v‖ := angularFrequencyDilation.symm.norm_map v

/-- The componentwise lowering map has operator bound one. -/
theorem lowerVectorL_norm_le (s r : ℝ) (hrs : r ≤ s) (v : RealVectorSobolev s) :
    ‖lowerVectorL s r hrs v‖ ≤ ‖v‖ := by
  have hsq : ‖lowerVectorL s r hrs v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_le_sum
    intro i _
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    exact angularOrderLowering_norm_le s r hrs (v i : FourierData)
  nlinarith [norm_nonneg (lowerVectorL s r hrs v), norm_nonneg v]

/-- Monotonicity holds for every time exponent and every physical force,
including when there is no admissible datum path. -/
theorem forceSobolevENorm_mono_order (q : ℝ≥0∞) (s s' : ℝ) (hss : s ≤ s')
    (f : SpaceTimeField) : forceSobolevENorm q s f ≤ forceSobolevENorm q s' f := by
  refine le_iInf fun G => ?_
  let L := lowerVectorL s' s hss
  have hpath := isSobolevPath_lower hss G.2.1
  have hmeas : AEStronglyMeasurable (fun t => L (G.1 t)) forceTimeMeasure :=
    L.continuous.comp_aestronglyMeasurable G.2.2
  calc
    forceSobolevENorm q s f ≤ Homogeneous.bochnerDatumENorm q s (fun t => L (G.1 t)) :=
      iInf_le (fun H : {H : ℝ → RealVectorSobolev s //
        IsSobolevPath s f H ∧ AEStronglyMeasurable H forceTimeMeasure} =>
          Homogeneous.bochnerDatumENorm q s H.1) ⟨_, hpath, hmeas⟩
    _ ≤ Homogeneous.bochnerDatumENorm q s' G.1 :=
      eLpNorm_mono (fun t => lowerVectorL_norm_le s' s hss (G.1 t))

/-- Verbatim local restatement of Data.lean:553. -/
def forceClassR : Set SpaceTimeField := {f | MemForceR f}

/-- Verbatim local restatement of Data.lean:672–674. -/
def breakdownSetIn (Y : Set SpaceTimeField) (ν : ℝ) (a : SpatialField) (T : ℝ) :
    Set SpaceTimeField :=
  {f | f ∈ Y ∧ maximalLifespanR ν a f ≤ ENNReal.ofReal T}

/-- Verbatim local restatement of Data.lean:678–679. -/
def breakdownSetR (ν : ℝ) (a : SpatialField) (T : ℝ) : Set SpaceTimeField :=
  breakdownSetIn forceClassR ν a T

/-- Verbatim local restatement of Data.lean:686–687. -/
def breakdownSetRZero (ν T : ℝ) : Set SpaceTimeField :=
  breakdownSetR ν (fun _ => 0) T

/-- Verbatim local restatement of Data.lean:702–703. -/
def RelativelyDense (q : ℝ≥0∞) (s : ℝ) (Y S : Set SpaceTimeField) : Prop :=
  ∀ g ∈ Y, ∀ r : ℝ≥0∞, 0 < r → ∃ f ∈ S, forceSobolevENorm q s (f - g) < r

/-- Verbatim local restatement of Data.lean:707–708. -/
def BreakdownDenseR (ν : ℝ) (a : SpatialField) (T : ℝ) (q : ℝ≥0∞) (s : ℝ) : Prop :=
  RelativelyDense q s forceClassR (breakdownSetR ν a T)

/-- The explicit radius is independent of the order and the terminal time. -/
theorem criticalRadius_le_forceSobolevENorm {ν T s : ℝ} (hν : 0 < ν)
    (hs : 1 / 2 ≤ s) {f : SpaceTimeField} (hf : f ∈ breakdownSetRZero ν T) :
    ENNReal.ofReal (R43.criticalConst * ν) ≤ forceSobolevENorm 1 s f := by
  have hhalf : ENNReal.ofReal (R43.criticalConst * ν) ≤ forceSobolevENormL1 (1 / 2) f := by
    apply le_of_not_gt
    intro hsmall
    have htop := R43.inhomogeneousAtZero_of_memForceR ν hν f hf.1 hsmall
    exact ENNReal.ofReal_ne_top (top_le_iff.mp (htop ▸ hf.2))
  exact hhalf.trans (forceSobolevENorm_mono_order 1 (1 / 2) s hs f)

/-- RMainAPI.nonDensityZero at q = 1, with radius criticalConst * ν. -/
theorem nonDensityZero_L1 : ∀ ν T : ℝ, 0 < ν → 0 < T → ∀ s : ℝ, 1 / 2 ≤ s →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ f ∈ breakdownSetRZero ν T,
      ENNReal.ofReal ρ ≤ forceSobolevENorm 1 s f := by
  intro ν T hν _ s hs
  exact ⟨R43.criticalConst * ν, mul_pos R43.criticalConst_pos hν,
    fun _ hf => criticalRadius_le_forceSobolevENorm hν hs hf⟩

/-- The centre of the excluded relative ball is in the ambient force class. -/
theorem zero_mem_forceClassR : (0 : SpaceTimeField) ∈ forceClassR :=
  A04.memForceR_zero

/-- Theorem 4.1(ii), failure of relative density at and above the L¹ threshold. -/
theorem not_breakdownDenseR_zero_L1 : ∀ ν T : ℝ, 0 < ν → 0 < T → ∀ s : ℝ,
    1 / 2 ≤ s → ¬ BreakdownDenseR ν (fun _ => 0) T 1 s := by
  intro ν T hν hT s hs hdense
  obtain ⟨ρ, hρ, hbound⟩ := nonDensityZero_L1 ν T hν hT s hs
  obtain ⟨f, hf, hdist⟩ := hdense 0 zero_mem_forceClassR (ENNReal.ofReal ρ)
    (ENNReal.ofReal_pos.mpr hρ)
  simp only [sub_zero] at hdist
  exact (not_lt_of_ge (hbound f hf)) hdist

example : (0 : SpaceTimeField) ∈ forceClassR := zero_mem_forceClassR

example : ¬ BreakdownDenseR 1 (fun _ => 0) 1 1 (1 / 2) :=
  not_breakdownDenseR_zero_L1 1 1 (by norm_num) (by norm_num) (1 / 2) le_rfl

end NSFormalization.Section4.R41
