import NSFormalization.Paper3.AngularRealSobolev
import NSFormalization.Paper3.RealVectorPositiveDensity

/-! Euclidean real-vector and Bochner transport of the checked angular equivalence.
Mathlib supplies finite-product equivalences and bounded maps on Bochner Lp.
The physical approximation is reused from RealVectorPositiveDensity. -/
noncomputable section
set_option maxHeartbeats 800000
namespace NSFormalization.Paper3
open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Source RealSobolev
open scoped ENNReal ContDiff SchwartzMap

/-- Coordinate transport, with the actual Euclidean PiLp2 norm on both sides. -/
def cyclesToAngularRealVector (s : ℝ) : RealVectorSobolev s ≃L[ℝ] RealVectorSobolev s :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => RealSobolevHilbert s)).trans
    ((ContinuousLinearEquiv.piCongrRight (fun _ : Fin 3 => cyclesToAngularReal s)).trans
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => RealSobolevHilbert s)).symm)

@[simp] theorem cyclesToAngularRealVector_apply (s : ℝ) (v : RealVectorSobolev s) (i : Fin 3) :
    cyclesToAngularRealVector s v i = cyclesToAngularReal s (v i) := rfl

/-- The scalar norm comparison retains its constant in the Euclidean vector norm. -/
theorem cyclesToAngularRealVector_norm_le (s : ℝ) (v : RealVectorSobolev s) :
    ‖cyclesToAngularRealVector s v‖ ≤ frequencyUnit ^ |s| * ‖v‖ := by
  have hC : 0 ≤ frequencyUnit ^ |s| := Real.rpow_nonneg frequencyUnit_pos.le _
  have hs : ‖cyclesToAngularRealVector s v‖ ^ 2 ≤
      (frequencyUnit ^ |s| * ‖v‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi := cyclesToAngularReal_norm_le s (v i)
    have hp := mul_nonneg hC (norm_nonneg (v i))
    change ‖cyclesToAngularReal s (v i)‖ ^ 2 ≤ _
    nlinarith [norm_nonneg (cyclesToAngularReal s (v i))]
  nlinarith [norm_nonneg (cyclesToAngularRealVector s v),
    mul_nonneg hC (norm_nonneg v)]

/-- Every physical component is preserved, including arbitrary non-L1 data. -/
theorem angularRealization_cyclesToAngularRealVector (s : ℝ) (v : RealVectorSobolev s)
    (i : Fin 3) :
    angularRealization s (cyclesToAngularRealVector s v i : FourierData) =
      sobolevRealization s (v i : FourierData) :=
  angularRealization_cyclesToAngularReal s (v i)

/-- The normalized angular data path of the same physical compact force. -/
def angularRealVectorSlice (s : ℝ) (F : Fin 3 → ℝ × Space → ℝ)
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) (hc : ∀ i, HasCompactSupport (F i)) :
    ℝ → RealVectorSobolev s :=
  fun t => cyclesToAngularRealVector s (realVectorSlice s F hF hc t)

/-- The angular data of each slice pair with every Schwartz test as the
literal original real physical component. -/
theorem angularRealVectorSlice_pairing (s : ℝ) (F : Fin 3 → ℝ × Space → ℝ)
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) (hc : ∀ i, HasCompactSupport (F i))
    (t : ℝ) (i : Fin 3) (ψ : SchwartzMap Space ℂ) :
    angularRealization s (angularRealVectorSlice s F hF hc t i : FourierData) ψ =
      ∫ x : Space, ψ x * (F i (t, x) : ℂ) := by
  change angularRealization s
    (cyclesToAngularReal s (realCompactSobolevTimeSlice s (F i) (hF i) (hc i) t) : FourierData) ψ = _
  rw [angularRealization_cyclesToAngularReal, coe_realCompactSobolevTimeSlice]
  exact sobolevRealization_compactFourierLp_apply s _ _ _ ψ

theorem memLp_angularRealVectorSlice (s : ℝ) (F : Fin 3 → ℝ × Space → ℝ)
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) (hc : ∀ i, HasCompactSupport (F i)) (q : ℝ≥0∞) :
    MemLp (angularRealVectorSlice s F hF hc) q positiveTimeMeasure :=
  (cyclesToAngularRealVector s).toContinuousLinearMap.comp_memLp'
    (memLp_realVectorSlice s F hF hc q)

variable (s : ℝ) (q : ℝ≥0∞) [Fact (1 ≤ q)]

/-- Bochner transport uses Mathlib's existing bounded composition operator. -/
def cyclesToAngularRealVectorBochner :
    Lp (RealVectorSobolev s) q positiveTimeMeasure →L[ℝ]
      Lp (RealVectorSobolev s) q positiveTimeMeasure :=
  (cyclesToAngularRealVector s).toContinuousLinearMap.compLpL q positiveTimeMeasure

def angularToCyclesRealVectorBochner :
    Lp (RealVectorSobolev s) q positiveTimeMeasure →L[ℝ]
      Lp (RealVectorSobolev s) q positiveTimeMeasure :=
  (cyclesToAngularRealVector s).symm.toContinuousLinearMap.compLpL q positiveTimeMeasure

@[simp] theorem cyclesToAngularRealVectorBochner_inverse
    (b : Lp (RealVectorSobolev s) q positiveTimeMeasure) :
    cyclesToAngularRealVectorBochner s q (angularToCyclesRealVectorBochner s q b) = b := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
      (cyclesToAngularRealVector s).toContinuousLinearMap (angularToCyclesRealVectorBochner s q b),
    ContinuousLinearMap.coeFn_compLpL (cyclesToAngularRealVector s).symm.toContinuousLinearMap b]
    with t ht hi
  exact ht.trans ((congrArg (cyclesToAngularRealVector s) hi).trans
    ((cyclesToAngularRealVector s).apply_symm_apply (b t)))

@[simp] theorem angularToCyclesRealVectorBochner_inverse
    (b : Lp (RealVectorSobolev s) q positiveTimeMeasure) :
    angularToCyclesRealVectorBochner s q (cyclesToAngularRealVectorBochner s q b) = b := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
      (cyclesToAngularRealVector s).symm.toContinuousLinearMap (cyclesToAngularRealVectorBochner s q b),
    ContinuousLinearMap.coeFn_compLpL (cyclesToAngularRealVector s).toContinuousLinearMap b]
    with t ht hi
  exact ht.trans ((congrArg (cyclesToAngularRealVector s).symm hi).trans
    ((cyclesToAngularRealVector s).symm_apply_apply (b t)))

theorem cyclesToAngularRealVectorBochner_slice (F : Fin 3 → ℝ × Space → ℝ)
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) (hc : ∀ i, HasCompactSupport (F i)) :
    cyclesToAngularRealVectorBochner s q
      ((memLp_realVectorSlice s F hF hc q).toLp (realVectorSlice s F hF hc)) =
      (memLp_angularRealVectorSlice s F hF hc q).toLp (angularRealVectorSlice s F hF hc) := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
      (cyclesToAngularRealVector s).toContinuousLinearMap
      ((memLp_realVectorSlice s F hF hc q).toLp (realVectorSlice s F hF hc)),
    (memLp_realVectorSlice s F hF hc q).coeFn_toLp,
    (memLp_angularRealVectorSlice s F hF hc q).coeFn_toLp] with t ht hr ha
  exact ht.trans ((congrArg (cyclesToAngularRealVector s) hr).trans ha.symm)

/-- Real compact smooth physical forces supported strictly in positive time
are dense in the normalized angular Euclidean-vector Bochner model. -/
theorem exists_angular_real_vector_positive_physical_approx (hq : q ≠ ⊤)
    (b : Lp (RealVectorSobolev s) q positiveTimeMeasure) {ε : ℝ} (hε : 0 < ε) :
    ∃ (F : ℝ × Space → Space), ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      tsupport F ⊆ {z | 0 < z.1} ∧
      ∃ (f : Fin 3 → ℝ × Space → ℝ)
        (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hc : ∀ i, HasCompactSupport (f i)),
        (∀ z i, F z i = f i z) ∧
        ‖b - (memLp_angularRealVectorSlice s f hf hc q).toLp
          (angularRealVectorSlice s f hf hc)‖ < ε := by
  let A := cyclesToAngularRealVectorBochner s q
  have hC : 0 < ‖A‖ + 1 := by positivity
  obtain ⟨F, hF, hFc, hFs, f, hf, hc, hFi, he⟩ :=
    exists_real_vector_positive_physical_approx s q hq
      (angularToCyclesRealVectorBochner s q b) (div_pos hε hC)
  refine ⟨F, hF, hFc, hFs, f, hf, hc, hFi, ?_⟩
  rw [← cyclesToAngularRealVectorBochner_slice,
    ← cyclesToAngularRealVectorBochner_inverse s q b, ← map_sub]
  change ‖A _‖ < ε
  apply (A.le_opNorm _).trans_lt
  have he' := (mul_lt_mul_of_pos_left he hC).trans_eq (mul_div_cancel₀ ε hC.ne')
  nlinarith [norm_nonneg (angularToCyclesRealVectorBochner s q b -
    (memLp_realVectorSlice s f hf hc q).toLp (realVectorSlice s f hf hc))]

end NSFormalization.Paper3
