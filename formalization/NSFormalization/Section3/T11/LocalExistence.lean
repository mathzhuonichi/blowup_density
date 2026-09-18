import NSFormalization.Section3.T11.LocalExistenceProbe

/-! # Periodic quantitative local existence: the coefficient construction

The order-wise input below is the amended H¹ target. Coefficient fixed-point
results use the exact H³/H² contract and do not assert the H¹ target.
-/
noncomputable section
namespace NSFormalization.Section3.T11

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open MNS2 MNS2.EndpointSafeTwoSpaceDuhamelContract
open scoped ContDiff ENNReal NNReal BigOperators Topology

local instance torusExistenceNormedGroup : NormedAddCommGroup (PeriodicSobolev 3) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance torusExistenceNormedSpace : NormedSpace ℝ (PeriodicSobolev 3) :=
  realPeriodicSubmodule.normedSpace

/-- Amendment 1, verbatim; this is a target, not a proved existence assertion. -/
def PeriodicQuantitativeLocalInput' : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∀ M : ℕ → ℝ≥0∞, (∀ m, M m ≠ ⊤) → ∃ δ : ℝ, 0 < δ ∧
    ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 1 a ≤ K →
      ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g →
        (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ M m) →
          ∃ w : ClassicalSolutionT ν a g δ, PeriodicLocalRegularity ν a g δ w

theorem quantitative_lifespan_lower_bound' (H : PeriodicQuantitativeLocalInput') :
    ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ →
      ∀ M : ℕ → ℝ≥0∞, (∀ m, M m ≠ ⊤) → ∃ δ : ℝ, 0 < δ ∧
      ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 1 a ≤ K →
        ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g →
          (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ M m) →
            ENNReal.ofReal δ ≤ maximalLifespanT ν a g := by
  intro ν hν K hK M hM
  obtain ⟨δ, hδ, hlocal⟩ := H ν hν K hK M hM
  refine ⟨δ, hδ, ?_⟩
  intro a ha hKa g hg hp hMg
  obtain ⟨w, _⟩ := hlocal a ha hKa g hg hp hMg
  exact le_iSup_of_le δ (le_iSup_of_le
    (show Nonempty (ClassicalSolutionT ν a g δ) from ⟨w⟩) le_rfl)

/-- Conjugate reflection is a closed condition on the genuine vector ℓ² carrier. -/
theorem torus_realSubmodule_closed :
    IsClosed (realPeriodicSubmodule : Set PeriodicVectorData) := by
  change IsClosed {A : PeriodicVectorData | ∀ i k, A i (-k) = star (A i k)}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro k
  exact isClosed_eq ((lp.evalCLM ℂ _ 2 (-k)).continuous.comp (PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ PeriodicScalarData) i))
    (((lp.evalCLM ℂ _ 2 k).continuous.comp (PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ PeriodicScalarData) i)).star)

/-- All Sobolev orders use the same complete real carrier; weights are in symbols. -/
instance torusExistenceCompleteSpace : CompleteSpace (PeriodicSobolev 3) :=
  completeSpace_coe_iff_isComplete.mpr torus_realSubmodule_closed.isComplete

/-- The bounded even multiplier as a real continuous linear map. -/
def torusMultiplierCLM (s r : ℝ) (m : PeriodicFrequency → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hm : ∀ k, |m k| ≤ B) (he : ∀ k, m (-k) = m k) :
    PeriodicSobolev s →L[ℝ] PeriodicSobolev r :=
  LinearMap.mkContinuous
    { toFun := torusMultiplier s r m B hB hm he
      map_add' := by
        intro A D
        apply Subtype.ext
        apply WithLp.ofLp_injective 2
        funext i
        ext k
        change (m k : ℂ) * (A.1 i k + D.1 i k) = _
        exact mul_add _ _ _
      map_smul' := by
        intro c A
        apply Subtype.ext
        apply WithLp.ofLp_injective 2
        funext i
        ext k
        change (m k : ℂ) * ((c : ℂ) * A.1 i k) = (c : ℂ) * ((m k : ℂ) * A.1 i k)
        ring }
    B (torusMultiplier_norm_le s r m B hB hm he)

/-- Canonical heat CLM. -/
def torusHeatCLM {ν : ℝ} (hν : 0 ≤ ν) (t : ℝ≥0) :
    PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 3 :=
  torusMultiplierCLM 3 3 (torusHeatSymbol ν t) 1 zero_le_one
    (fun k ↦ by
      unfold torusHeatSymbol
      rw [abs_of_nonneg (NSFormalization.Paper1.PeriodicHeatMultiplier.heatSymbol_nonneg ν t k)]
      exact NSFormalization.Paper1.PeriodicHeatMultiplier.heatSymbol_le_one hν t.2 k)
    (torusHeatSymbol_neg ν t)

/-- Canonical H²→H³ smoothing CLM with explicit reweighting. -/
def torusSmoothingCLM {ν : ℝ} (hν : 0 < ν) (t : ℝ) (ht : 0 < t) :
    PeriodicSobolev 2 →L[ℝ] PeriodicSobolev 3 :=
  torusMultiplierCLM 2 3
    (fun k ↦ Real.sqrt (periodicFrequencyWeight k) * torusHeatSymbol ν t k)
    (torusSmoothingKernel ν t) (Real.sqrt_nonneg _)
    (fun k ↦ by
      unfold torusHeatSymbol
      rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _)
        (NSFormalization.Paper1.PeriodicHeatMultiplier.heatSymbol_nonneg ν t k)), torus_weight_eq]
      exact NSFormalization.Paper1.PeriodicHeatMultiplier.sqrt_weight_mul_heatSymbol_le hν ht k)
    (fun k ↦ by rw [torus_weight_neg, torusHeatSymbol_neg])

/-- Strong continuity on the scalar ℓ² carrier, by a summable square majorant. -/
theorem torus_scalarHeat_continuous {ν : ℝ} (hν : 0 ≤ ν) (A : PeriodicScalarData) :
    Continuous (fun t : ℝ≥0 ↦ NSFormalization.Paper1.PeriodicHeatMultiplier.heat hν t.2 A) := by
  let H := fun t : ℝ≥0 ↦ NSFormalization.Paper1.PeriodicHeatMultiplier.heat hν t.2 A
  apply continuous_iff_continuousAt.mpr
  intro t₀
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hc (k : PeriodicFrequency) : Continuous (fun t : ℝ≥0 ↦ ‖(H t - H t₀) k‖ ^ 2) := by
    change Continuous (fun t : ℝ≥0 ↦ ‖(torusHeatSymbol ν t k : ℂ) * A k -
      (torusHeatSymbol ν t₀ k : ℂ) * A k‖ ^ 2)
    unfold torusHeatSymbol NSFormalization.Paper1.PeriodicHeatMultiplier.heatSymbol
    fun_prop
  have hb (k : PeriodicFrequency) (t : ℝ≥0) :
      ‖‖(H t - H t₀) k‖ ^ 2‖ ≤ 4 * ‖A k‖ ^ 2 := by
    have hh (s : ℝ≥0) : ‖H s k‖ ≤ ‖A k‖ := by
      change ‖(torusHeatSymbol ν s k : ℂ) * A k‖ ≤ ‖A k‖
      unfold torusHeatSymbol
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (NSFormalization.Paper1.PeriodicHeatMultiplier.heatSymbol_nonneg ν s k)]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (NSFormalization.Paper1.PeriodicHeatMultiplier.heatSymbol_le_one hν s.2 k)
    have hn : ‖(H t - H t₀) k‖ ≤ 2 * ‖A k‖ := by
      exact (norm_sub_le _ _).trans (by linarith [hh t, hh t₀])
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg ((H t - H t₀) k)]
  have hs : Summable (fun k ↦ 4 * ‖A k‖ ^ 2) := by
    simpa using (((lp.memℓp A).summable (by norm_num)).mul_left 4)
  have hcSum := continuous_tsum hc hs hb
  have hnorm : Continuous (fun t : ℝ≥0 ↦ ‖H t - H t₀‖) := by
    have he (t : ℝ≥0) : ‖H t - H t₀‖ = Real.sqrt (∑' k, ‖(H t - H t₀) k‖ ^ 2) := by
      rw [lp.norm_eq_tsum_rpow (by norm_num), Real.sqrt_eq_rpow]
      norm_num
    simp_rw [he]
    exact hcSum.sqrt
  have ht := (hnorm.continuousAt (x := t₀)).tendsto
  rw [sub_self, norm_zero] at ht
  exact ht

/-- Joint heat continuity, including time zero and varying complete-carrier data. -/
theorem torusHeatCLM_continuous {ν : ℝ} (hν : 0 ≤ ν) :
    Continuous (fun p : ℝ≥0 × PeriodicSobolev 3 ↦ torusHeatCLM hν p.1 p.2) := by
  apply continuous_prod_of_continuous_lipschitzWith' _ 1
  · intro t
    apply LipschitzWith.of_dist_le_mul
    intro A B
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    change ‖torusHeat 3 hν t.2 (A-B)‖ ≤ (1 : ℝ) * ‖A-B‖
    rw [one_mul]
    exact torusHeat_norm_le 3 hν t.2 (A-B)
  · intro A
    apply continuous_induced_rng.mpr
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro i
    exact torus_scalarHeat_continuous hν (A.1 i)


/-- An integrable explicit majorant for the endpoint singularity. -/
theorem torusSmoothingKernel_le {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) :
    torusSmoothingKernel ν t ≤ 1 + (Real.sqrt ν)⁻¹ * t ^ (-(1 / 2 : ℝ)) := by
  have hx : 0 ≤ 1 / (ν*t) := by positivity
  have hsq := Real.sq_sqrt hx
  have hroot := Real.sqrt_nonneg (1 / (ν*t))
  have hb : Real.sqrt (1 + 1 / (ν*t)) ≤ 1 + Real.sqrt (1 / (ν*t)) := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    nlinarith
  have he : Real.sqrt (1 / (ν*t)) = (Real.sqrt ν)⁻¹ * t ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_mul hν.le,
      Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
    simp [one_div, mul_inv_rev, mul_comm]
  exact hb.trans_eq (congrArg (1 + ·) he)

/-- Local integrability of the exact kernel; no endpoint modification of its formula. -/
theorem torusSmoothingKernel_integrable {ν : ℝ} (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (torusSmoothingKernel ν) volume 0 T := by
  have hi : IntervalIntegrable (fun t : ℝ ↦ 1 + (Real.sqrt ν)⁻¹ * t ^ (-(1 / 2 : ℝ))) volume 0 T :=
    intervalIntegrable_const.add
      ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _)
  apply hi.mono_fun'
  · apply MNS2.aestronglyMeasurable_interval_of_continuousOn_Ioo hT
    apply ContinuousOn.sqrt
    apply continuousOn_const.add
    apply continuousOn_const.div (continuousOn_const.mul continuousOn_id)
    intro t ht
    exact ne_of_gt (mul_pos hν ht.1)
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [uIoc_of_le hT] at ht
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ torusSmoothingKernel ν t from Real.sqrt_nonneg _)]
    exact torusSmoothingKernel_le hν ht.1

/-- Every convolution in the stated symbol is absolutely convergent on arbitrary
complete-carrier data. Boundedness into H² is the separate residual input. -/
theorem torusConvolution_summable (A B : PeriodicSobolev 3) (i j : Fin 3)
    (k : PeriodicFrequency) :
    Summable (fun l : PeriodicFrequency ↦
      ‖(((periodicFrequencyWeight l) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * A.1 j l *
        (((periodicFrequencyWeight (k-l)) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * B.1 i (k-l)‖) := by
  have hw (l : PeriodicFrequency) : 1 ≤ periodicFrequencyWeight l := by
    unfold periodicFrequencyWeight
    exact le_add_of_nonneg_right (by positivity)
  have hw0 (l : PeriodicFrequency) : 0 ≤ periodicFrequencyWeight l := (zero_le_one.trans (hw l))
  have hb (l : PeriodicFrequency) : ‖((periodicFrequencyWeight l ^ (-(3 : ℝ) / 2) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hw0 l) _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (hw l) (by norm_num)
  have hA : Summable (fun l ↦ ‖A.1 j l‖ ^ 2) := by
    simpa using (lp.memℓp (A.1 j)).summable (by norm_num)
  have hB : Summable (fun l ↦ ‖B.1 i (k-l)‖ ^ 2) := by
    have h : Summable (fun l ↦ ‖B.1 i l‖ ^ 2) := by
      simpa using (lp.memℓp (B.1 i)).summable (by norm_num)
    exact h.comp_injective (sub_right_injective)
  apply (hA.add hB).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro l
  have hprod : ‖(((periodicFrequencyWeight l) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * A.1 j l *
      (((periodicFrequencyWeight (k-l)) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * B.1 i (k-l)‖ ≤
        ‖A.1 j l‖ * ‖B.1 i (k-l)‖ := by
    simp only [norm_mul]
    calc
      _ ≤ (1 * ‖A.1 j l‖) * 1 * ‖B.1 i (k-l)‖ := by gcongr <;> apply hb
      _ = _ := by ring
  exact hprod.trans (by nlinarith [sq_nonneg (‖A.1 j l‖ - ‖B.1 i (k-l)‖)])

/-- The single analytic residue: the projected convolution has a bounded real
bilinear realization with the exact H³×H³→H² coefficients. This is neither a
local existence assertion nor a restatement of the two-space contract. -/
def TorusConvolutionInput : Prop :=
  ∃ Q : PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 2,
    ∀ A B i k, (Q A B).1 i k = torusProjectedConvectionSymbol A B i k

/-- All the two-space obligations other than projected convolution are discharged. -/
theorem torusTwoSpaceContract_nonempty (H : TorusConvolutionInput) (ν : ℝ) (hν : 0 < ν) :
    Nonempty (TorusTwoSpaceContract ν) := by
  obtain ⟨Q, hQ⟩ := H
  let C : MNS2.EndpointSafeTwoSpaceDuhamelContract ℝ (PeriodicSobolev 3) (PeriodicSobolev 2) :=
    { linearEvolution := torusHeatCLM hν.le
      linear_zero := by
        apply ContinuousLinearMap.ext
        intro A
        exact torusHeat_zero 3 hν.le A
      linear_add := by
        intro a b
        apply ContinuousLinearMap.ext
        intro A
        exact torusHeat_add 3 hν.le a.2 b.2 A
      continuous_linear_action := torusHeatCLM_continuous hν.le
      positiveSmoothing := torusSmoothingCLM hν
      bilinear := Q
      smoothingKernel := torusSmoothingKernel ν
      smoothingKernel_nonneg := fun t _ ↦ Real.sqrt_nonneg _
      norm_positiveSmoothing_apply_le := by
        intro t ht A
        exact torusHeatSmoothing_norm_le 2 hν ht A
      intervalIntegrable_smoothingKernel := torusSmoothingKernel_integrable hν
      smoothing_coherent := by
        intro a ha b
        apply ContinuousLinearMap.ext
        intro A
        exact torusHeatSmoothing_coherent 2 hν ha b.2 A }
  exact ⟨⟨C, fun _ _ _ _ ↦ rfl, fun _ _ _ _ _ ↦ rfl, hQ, rfl⟩⟩


/-- Affine Picard map with an arbitrary continuous forced linear path. -/
def torusAffinePicard {ν T : ℝ} (C : TorusTwoSpaceContract ν) (hT : 0 ≤ T)
    (L f : C(Icc (0 : ℝ) T, PeriodicSobolev 3)) :
    C(Icc (0 : ℝ) T, PeriodicSobolev 3) :=
  L + C.analytic.picardMap hT 0 f

theorem torusAffinePicard_apply {ν T : ℝ} (C : TorusTwoSpaceContract ν) (hT : 0 ≤ T)
    (L f : C(Icc (0 : ℝ) T, PeriodicSobolev 3)) (t : Icc (0 : ℝ) T) :
    torusAffinePicard C hT L f t =
      L t - C.analytic.duhamelIntegral (IccExtend hT f) t := by
  simp [torusAffinePicard, picardMap_apply, sub_eq_add_neg]

theorem torusAffinePicard_norm_le {ν T R b : ℝ} (C : TorusTwoSpaceContract ν)
    (hT : 0 ≤ T) (hb : 0 ≤ b)
    (L f : C(Icc (0 : ℝ) T, PeriodicSobolev 3))
    (hL : ∀ t, ‖L t‖ ≤ b) (hf : ‖f‖ ≤ R) :
    ‖torusAffinePicard C hT L f‖ ≤
      b + ‖C.analytic.bilinear‖ * C.analytic.kernelPrimitive T * R ^ 2 := by
  have hK := C.analytic.kernelPrimitive_nonneg hT
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro t
  rw [torusAffinePicard_apply]
  have hI := C.analytic.norm_duhamelIntegral_le hT t.2
    (fun s _ ↦ (norm_IccExtend_le hT f s).trans hf)
  have hmono := C.analytic.kernelPrimitive_mono hT t.2 (right_mem_Icc.mpr hT) t.2.2
  calc
    _ ≤ ‖L t‖ + ‖C.analytic.duhamelIntegral (IccExtend hT f) t‖ := norm_sub_le _ _
    _ ≤ b + ‖C.analytic.bilinear‖ * R ^ 2 * C.analytic.kernelPrimitive t := add_le_add (hL t) hI
    _ ≤ b + ‖C.analytic.bilinear‖ * R ^ 2 * C.analytic.kernelPrimitive T :=
      add_le_add (le_refl b) (mul_le_mul_of_nonneg_left hmono (by positivity))
    _ = _ := by ring

theorem torusAffinePicard_dist_le {ν T R : ℝ} (C : TorusTwoSpaceContract ν)
    (hT : 0 ≤ T) (hR : 0 ≤ R)
    (L f g : C(Icc (0 : ℝ) T, PeriodicSobolev 3)) (hf : ‖f‖ ≤ R) (hg : ‖g‖ ≤ R) :
    dist (torusAffinePicard C hT L f) (torusAffinePicard C hT L g) ≤
      (2 * ‖C.analytic.bilinear‖ * C.analytic.kernelPrimitive T * R) * dist f g := by
  simpa only [torusAffinePicard, dist_add_left, mul_assoc, mul_comm, mul_left_comm] using
    C.analytic.dist_picardMap_le hT (0 : PeriodicSobolev 3) hR hf hg


/-- Banach construction with the exact prescribed-window numeric certificate.
The linear path may include an actual force integral. -/
theorem torusAffinePicard_exists_unique {ν T R b : ℝ} (C : TorusTwoSpaceContract ν)
    (P : TorusPicardConstants C T R b)
    (L : C(Icc (0 : ℝ) T, PeriodicSobolev 3)) (hL : ∀ t, ‖L t‖ ≤ b) :
    ∃ f : C(Icc (0 : ℝ) T, PeriodicSobolev 3),
      ‖f‖ ≤ R ∧ torusAffinePicard C P.time_pos.le L f = f ∧
      ∀ g : C(Icc (0 : ℝ) T, PeriodicSobolev 3), ‖g‖ ≤ R →
        torusAffinePicard C P.time_pos.le L g = g → g = f := by
  let S : Set C(Icc (0 : ℝ) T, PeriodicSobolev 3) := Metric.closedBall 0 R
  have hmem (f : C(Icc (0 : ℝ) T, PeriodicSobolev 3)) : f ∈ S ↔ ‖f‖ ≤ R := by
    simp [S, Metric.mem_closedBall, dist_zero_right]
  let torusBallComplete : CompleteSpace S :=
    completeSpace_coe_iff_isComplete.mpr Metric.isClosed_closedBall.isComplete
  have torusBallNonempty : Nonempty S := ⟨⟨0, (hmem 0).mpr (by simpa using P.radius_pos.le)⟩⟩
  have hmaps (f : S) : torusAffinePicard C P.time_pos.le L f.1 ∈ S :=
    (hmem _).mpr ((torusAffinePicard_norm_le C P.time_pos.le P.linear_nonneg L f.1 hL
      ((hmem _).mp f.2)).trans P.self_map_bound)
  let Φ : S → S := fun f ↦ ⟨torusAffinePicard C P.time_pos.le L f.1, hmaps f⟩
  let θ : ℝ := 2 * ‖C.analytic.bilinear‖ * C.analytic.kernelPrimitive T * R
  have hθ : 0 ≤ θ := mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))
      (C.analytic.kernelPrimitive_nonneg P.time_pos.le)) P.radius_pos.le
  have hc : ContractingWith θ.toNNReal Φ := by
    refine ⟨Real.toNNReal_lt_one.mpr P.contraction_bound, LipschitzWith.of_dist_le_mul ?_⟩
    intro f g
    rw [Real.coe_toNNReal _ hθ]
    exact torusAffinePicard_dist_le C P.time_pos.le P.radius_pos.le L f.1 g.1
      ((hmem _).mp f.2) ((hmem _).mp g.2)
  let f := hc.fixedPoint
  have hfix : torusAffinePicard C P.time_pos.le L f.1 = f.1 :=
    congrArg Subtype.val hc.fixedPoint_isFixedPt
  refine ⟨f.1, (hmem _).mp f.2, hfix, ?_⟩
  intro g hg hgf
  have hgfix : Function.IsFixedPt Φ ⟨g, (hmem g).mpr hg⟩ := Subtype.ext hgf
  exact congrArg Subtype.val (hc.fixedPoint_unique hgfix)

/-- Continuity of the actual force integral, including both endpoints. -/
theorem torus_forceIntegral_continuousOn {ν T : ℝ} (C : TorusTwoSpaceContract ν)
    (hT : 0 ≤ T) (F : ℝ → PeriodicSobolev 3) (hF : ContinuousOn F (Icc 0 T)) :
    ContinuousOn (fun t ↦ ∫ s in (0 : ℝ)..t,
      C.analytic.linearEvolution (Real.toNNReal (t-s)) (F s)) (Icc 0 T) := by
  let Fc : C(Icc (0 : ℝ) T, PeriodicSobolev 3) :=
    ⟨fun t ↦ F t, continuousOn_iff_continuous_domRestrict.mp hF⟩
  have hFc : Continuous (IccExtend hT Fc) := Fc.continuous.Icc_extend'
  have hj : Continuous (fun p : ℝ × ℝ ↦
      C.analytic.linearEvolution (Real.toNNReal (p.1-p.2)) (IccExtend hT Fc p.2)) :=
    C.analytic.continuous_linear_action.comp
      ((continuous_real_toNNReal.comp (continuous_fst.sub continuous_snd)).prodMk
        (hFc.comp continuous_snd))
  have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun t s ↦ C.analytic.linearEvolution (Real.toNNReal (t-s)) (IccExtend hT Fc s))
    (μ := volume) (a₀ := 0) hj continuous_id
  apply hi.continuousOn.congr
  intro t ht
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  dsimp only
  rw [IccExtend_of_mem hT Fc ⟨hs.1, hs.2.trans ht.2⟩]
  rfl

/-- The force integral is a Bochner integral on each causal subwindow. -/
theorem torus_forceIntegrable {ν T t : ℝ} (C : TorusTwoSpaceContract ν)
    (F : ℝ → PeriodicSobolev 3) (hF : ContinuousOn F (Icc 0 T))
    (ht : t ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable (fun s ↦ C.analytic.linearEvolution (Real.toNNReal (t-s)) (F s))
      volume 0 t := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le ht.1]
  exact C.analytic.continuous_linear_action.comp_continuousOn
    (((continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).continuousOn).prodMk
      (hF.mono (Icc_subset_Icc_right ht.2)))

/-- Forced prescribed-window existence, with exactly the route's force and ball premises. -/
theorem torusForcedPicard_exists {ν : ℝ} (C : TorusTwoSpaceContract ν)
    (A : PeriodicSobolev 3) (F : ℝ → PeriodicSobolev 3) (T R b : ℝ)
    (P : TorusPicardConstants C T R b) (hF : ContinuousOn F (Icc 0 T))
    (hb : ∀ t, ∀ ht : t ∈ Icc (0 : ℝ) T,
      ‖C.analytic.linearEvolution ⟨t, ht.1⟩ A +
        ∫ s in (0 : ℝ)..t,
          C.analytic.linearEvolution (Real.toNNReal (t-s)) (F s)‖ ≤ b) :
    ∃ u : ℝ → PeriodicSobolev 3,
      TorusForcedMildOn C A F T u ∧ ∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ R := by
  let L : C(Icc (0 : ℝ) T, PeriodicSobolev 3) :=
    ⟨fun t ↦ C.analytic.linearEvolution (Real.toNNReal t.1) A +
      ∫ s in (0 : ℝ)..t.1, C.analytic.linearEvolution (Real.toNNReal (t.1-s)) (F s),
      (C.analytic.continuous_linear_action.comp
        ((continuous_real_toNNReal.comp continuous_subtype_val).prodMk continuous_const)).add
        (continuousOn_iff_continuous_domRestrict.mp
          (torus_forceIntegral_continuousOn C P.time_pos.le F hF))⟩
  have hL (t : Icc (0 : ℝ) T) : ‖L t‖ ≤ b := by
    change ‖C.analytic.linearEvolution (Real.toNNReal t.1) A + _‖ ≤ b
    rw [Real.toNNReal_of_nonneg t.2.1]
    exact hb t t.2
  obtain ⟨f, hfn, hfix, _⟩ := torusAffinePicard_exists_unique C P L hL
  let u := IccExtend P.time_pos.le f
  have huc : Continuous u := f.continuous.Icc_extend'
  have heq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      u t = torusForcedPicard C A F u ⟨t, ht.1⟩ := by
    have h := congrArg (fun v : C(Icc (0 : ℝ) T, PeriodicSobolev 3) ↦ v ⟨t, ht⟩) hfix
    rw [torusAffinePicard_apply] at h
    rw [show u t = f ⟨t, ht⟩ from IccExtend_of_mem P.time_pos.le f ht, ← h]
    simp only [L, ContinuousMap.coe_mk, torusForcedPicard,
      Real.toNNReal_of_nonneg ht.1, duhamelIntegral, u]
    rfl
  refine ⟨u, ⟨P.time_pos.le, huc.continuousOn, ?_, ?_, ?_, heq⟩, ?_⟩
  · have h := heq 0 (left_mem_Icc.mpr P.time_pos.le)
    change u 0 = C.analytic.linearEvolution 0 A +
      (∫ s in (0 : ℝ)..0, C.analytic.linearEvolution (Real.toNNReal (0-s)) (F s)) -
      ∫ s in (0 : ℝ)..0, C.analytic.duhamelIntegrand 0 u s at h
    simpa [C.analytic.linear_zero] using h
  · intro t ht
    exact torus_forceIntegrable C F hF ht
  · intro t ht
    exact C.analytic.intervalIntegrable_duhamelIntegrand_of_continuousOn ht.1
      (huc.continuousOn)
  · intro t ht
    exact (norm_IccExtend_le P.time_pos.le f t).trans hfn


/-- Restriction preserves the actual integrability certificates and forced equation. -/
theorem TorusForcedMildOn.restrict {ν T S : ℝ} {C : TorusTwoSpaceContract ν}
    {A : PeriodicSobolev 3} {F u : ℝ → PeriodicSobolev 3}
    (hu : TorusForcedMildOn C A F T u) (hS : 0 ≤ S) (hST : S ≤ T) :
    TorusForcedMildOn C A F S u := by
  have hsub : Icc (0 : ℝ) S ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right hST
  exact ⟨hS, hu.continuous_path.mono hsub, hu.initial,
    fun t ht ↦ hu.force_integrable t (hsub ht),
    fun t ht ↦ hu.nonlinear_integrable t (hsub ht),
    fun t ht ↦ hu.equation t (hsub ht)⟩

/-- Uniqueness on a certified causal window, without assumptions outside it. -/
theorem torusForcedMildOn_unique {ν T R b : ℝ} (C : TorusTwoSpaceContract ν)
    (P : TorusPicardConstants C T R b) {A : PeriodicSobolev 3}
    {F u v : ℝ → PeriodicSobolev 3}
    (hu : TorusForcedMildOn C A F T u) (hv : TorusForcedMildOn C A F T v)
    (hub : ∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ R)
    (hvb : ∀ t ∈ Icc (0 : ℝ) T, ‖v t‖ ≤ R) :
    ∀ t ∈ Icc (0 : ℝ) T, u t = v t := by
  let fu : C(Icc (0 : ℝ) T, PeriodicSobolev 3) :=
    ⟨fun t ↦ u t, continuousOn_iff_continuous_domRestrict.mp hu.continuous_path⟩
  let fv : C(Icc (0 : ℝ) T, PeriodicSobolev 3) :=
    ⟨fun t ↦ v t, continuousOn_iff_continuous_domRestrict.mp hv.continuous_path⟩
  let θ := 2 * ‖C.analytic.bilinear‖ * C.analytic.kernelPrimitive T * R
  have hK := C.analytic.kernelPrimitive_nonneg P.time_pos.le
  have hd : dist fu fv ≤ θ * dist fu fv := by
    have hR := P.radius_pos.le
    rw [ContinuousMap.dist_le (by dsimp [θ]; positivity)]
    intro t
    have hdiff : ∀ s ∈ Icc (0 : ℝ) T, ‖u s - v s‖ ≤ dist fu fv := by
      intro s hs
      rw [← dist_eq_norm]
      exact ContinuousMap.dist_apply_le_dist (f := fu) (g := fv) ⟨s, hs⟩
    have hi := C.analytic.norm_duhamelIntegral_sub_le P.time_pos.le t.2
      hu.continuous_path hv.continuous_path P.radius_pos.le hub hvb hdiff
    have hm := C.analytic.kernelPrimitive_mono P.time_pos.le t.2
      (right_mem_Icc.mpr P.time_pos.le) t.2.2
    change dist (u t.1) (v t.1) ≤ _
    rw [hu.equation t t.2, hv.equation t t.2]
    simp only [torusForcedPicard]
    rw [dist_eq_norm]
    have he : ∀ x y z : PeriodicSobolev 3, (x-y)-(x-z) = -(y-z) := by intros; abel
    rw [he, norm_neg]
    change ‖C.analytic.duhamelIntegral u t - C.analytic.duhamelIntegral v t‖ ≤ _
    calc
      _ ≤ ‖C.analytic.bilinear‖ * (2 * R) * dist fu fv * C.analytic.kernelPrimitive t := hi
      _ ≤ ‖C.analytic.bilinear‖ * (2 * R) * dist fu fv * C.analytic.kernelPrimitive T :=
        mul_le_mul_of_nonneg_left hm (by positivity)
      _ = θ * dist fu fv := by dsimp [θ]; ring
  have hz : dist fu fv = 0 := by nlinarith [dist_nonneg (x := fu) (y := fv), P.contraction_bound]
  have heq := dist_eq_zero.mp hz
  intro t ht
  exact congrArg (fun f : C(Icc (0 : ℝ) T, PeriodicSobolev 3) ↦ f ⟨t, ht⟩) heq

/-- A short subwindow inherits the same radius and linear bound certificate. -/
theorem TorusPicardConstants.restrict {ν T S R b : ℝ} {C : TorusTwoSpaceContract ν}
    (P : TorusPicardConstants C T R b) (hS : 0 < S) (hST : S ≤ T) :
    TorusPicardConstants C S R b := by
  have hm := C.analytic.kernelPrimitive_mono P.time_pos.le ⟨hS.le, hST⟩
    (right_mem_Icc.mpr P.time_pos.le) hST
  refine ⟨hS, P.radius_pos, P.linear_nonneg, ?_, ?_⟩
  · exact (add_le_add (le_refl b)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (norm_nonneg _))
        (sq_nonneg R))).trans P.self_map_bound
  · exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hm (by positivity)) P.radius_pos.le).trans_lt P.contraction_bound


/-- Explicit cumulative smoothing bound for any exact contract. -/
theorem torus_kernelPrimitive_le {ν : ℝ} (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    {T : ℝ} (hT : 0 ≤ T) :
    C.analytic.kernelPrimitive T ≤ T + 2 * (Real.sqrt ν)⁻¹ * Real.sqrt T := by
  have hi : IntervalIntegrable (fun t : ℝ ↦ 1 + (Real.sqrt ν)⁻¹ * t ^ (-(1 / 2 : ℝ))) volume 0 T :=
    intervalIntegrable_const.add
      ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _)
  have hb := intervalIntegral.integral_mono_on_of_le_Ioo hT
    (C.analytic.intervalIntegrable_safeKernel hT) hi (fun t ht ↦ by
      rw [safeKernel, endpointSafePositiveMajorant_of_pos _ ht.1, C.kernel_eq]
      exact torusSmoothingKernel_le hν ht.1)
  unfold kernelPrimitive
  refine hb.trans_eq ?_
  rw [intervalIntegral.integral_add intervalIntegrable_const
    ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _),
    intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
  norm_num [← Real.sqrt_eq_rpow]
  ring

/-- The actual same-order force contribution is bounded by its interval sup norm. -/
theorem torus_forcedLinear_bound {ν T : ℝ} (hν : 0 ≤ ν) (C : TorusTwoSpaceContract ν)
    (A : PeriodicSobolev 3) (F : ℝ → PeriodicSobolev 3) {B : ℝ}
    (hB : ∀ t ∈ Icc (0 : ℝ) T, ‖F t‖ ≤ B) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
    ‖C.analytic.linearEvolution ⟨t, ht.1⟩ A +
      ∫ s in (0 : ℝ)..t, C.analytic.linearEvolution (Real.toNNReal (t-s)) (F s)‖ ≤ ‖A‖ + B * t := by
  have hh (s : ℝ≥0) (D : PeriodicSobolev 3) : ‖C.analytic.linearEvolution s D‖ ≤ ‖D‖ := by
    have he : C.analytic.linearEvolution s D = torusHeat 3 hν s.2 D := by
      apply Subtype.ext
      apply WithLp.ofLp_injective 2
      funext i
      ext k
      exact C.linear_symbol s D i k
    rw [he]
    exact torusHeat_norm_le 3 hν s.2 D
  have hi : ‖∫ s in (0 : ℝ)..t, C.analytic.linearEvolution (Real.toNNReal (t-s)) (F s)‖ ≤ B*t := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := B)
      (f := fun s ↦ C.analytic.linearEvolution (Real.toNNReal (t-s)) (F s)) (fun s hs ↦ by
      rw [uIoc_of_le ht.1] at hs
      exact (hh _ _).trans (hB s ⟨hs.1.le, hs.2.trans ht.2⟩))
    simpa only [sub_zero, abs_of_nonneg ht.1] using h
  exact (norm_add_le _ _).trans (add_le_add (hh _ _) hi)


/-- Explicit positive horizon: `η` is a desired upper bound for the kernel mass. -/
def torusKernelTime (ν η : ℝ) : ℝ :=
  min 1 ((η / (1 + 2 * (Real.sqrt ν)⁻¹)) ^ 2)

theorem torusKernelTime_pos {ν η : ℝ} (hη : 0 < η) : 0 < torusKernelTime ν η := by
  unfold torusKernelTime
  exact lt_min zero_lt_one (sq_pos_of_pos (div_pos hη (by positivity)))

theorem torusKernelTime_le_one (ν η : ℝ) : torusKernelTime ν η ≤ 1 := min_le_left _ _

/-- The explicit horizon controls the exact contract's cumulative smoothing mass. -/
theorem torusKernelTime_mass {ν η : ℝ} (hν : 0 < ν) (hη : 0 < η)
    (C : TorusTwoSpaceContract ν) : C.analytic.kernelPrimitive (torusKernelTime ν η) ≤ η := by
  let T := torusKernelTime ν η
  have hT : 0 ≤ T := (torusKernelTime_pos hη).le
  have hT1 : T ≤ 1 := torusKernelTime_le_one ν η
  have hs : T ≤ Real.sqrt T := by
    have hsq := Real.sq_sqrt hT
    have hn := Real.sqrt_nonneg T
    nlinarith
  have hc : 0 < 1 + 2 * (Real.sqrt ν)⁻¹ := by positivity
  have hsbound : Real.sqrt T ≤ η / (1 + 2 * (Real.sqrt ν)⁻¹) := by
    apply (Real.sqrt_le_left (div_pos hη hc).le).mpr
    exact min_le_right _ _
  calc
    C.analytic.kernelPrimitive T ≤ T + 2 * (Real.sqrt ν)⁻¹ * Real.sqrt T := torus_kernelPrimitive_le hν C hT
    _ ≤ (1 + 2 * (Real.sqrt ν)⁻¹) * Real.sqrt T := by nlinarith
    _ ≤ (1 + 2 * (Real.sqrt ν)⁻¹) * (η / (1 + 2 * (Real.sqrt ν)⁻¹)) :=
      mul_le_mul_of_nonneg_left hsbound hc.le
    _ = η := mul_div_cancel₀ η hc.ne'

/-- A uniform positive kernel threshold for radius `b+1`. -/
def torusPicardThreshold (q b : ℝ) : ℝ :=
  min (1 / (q * (b+1)^2 + 1)) (1 / (2 * (q * (2*(b+1)) + 1)))

/-- Datum/force-size quantitative H³ certificate, with no H¹ relabelling. -/
theorem torusPicardConstants_explicit {ν b : ℝ} (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    (hb : 0 ≤ b) :
    TorusPicardConstants C (torusKernelTime ν (torusPicardThreshold ‖C.analytic.bilinear‖ b)) (b+1) b := by
  let q := ‖C.analytic.bilinear‖
  let η := torusPicardThreshold q b
  have hq : 0 ≤ q := norm_nonneg _
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hK := torusKernelTime_mass hν hη C
  have hK1 : C.analytic.kernelPrimitive (torusKernelTime ν η) ≤ 1 / (q * (b+1)^2 + 1) :=
    hK.trans (min_le_left _ _)
  have hK2 : C.analytic.kernelPrimitive (torusKernelTime ν η) ≤ 1 / (2 * (q * (2*(b+1)) + 1)) :=
    hK.trans (min_le_right _ _)
  refine ⟨torusKernelTime_pos hη, by positivity, hb, ?_, ?_⟩
  · have hstep := mul_le_mul_of_nonneg_left hK1 (show 0 ≤ q * (b+1)^2 by positivity)
    have hfrac : q * (b+1)^2 * (1 / (q * (b+1)^2+1)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]
      linarith
    change b + q * C.analytic.kernelPrimitive (torusKernelTime ν η) * (b+1)^2 ≤ b+1
    nlinarith
  · have hstep := mul_le_mul_of_nonneg_left hK2 (show 0 ≤ q * (2*(b+1)) by positivity)
    have hfrac : q * (2*(b+1)) * (1 / (2*(q*(2*(b+1))+1))) < 1 := by
      rw [mul_one_div, div_lt_one (by positivity)]
      nlinarith
    change 2 * q * C.analytic.kernelPrimitive (torusKernelTime ν η) * (b+1) < 1
    nlinarith

/-- Explicit lifespan on the H³ carrier, in terms of the datum norm and a force
supremum on `[0,1]`. All integral, continuity and uniqueness obligations are proved. -/
theorem torusForcedPicard_quantitative {ν : ℝ} (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    (A : PeriodicSobolev 3) (F : ℝ → PeriodicSobolev 3) (B : ℝ) (hB : 0 ≤ B)
    (hF : ContinuousOn F (Icc 0 1)) (hFB : ∀ t ∈ Icc (0 : ℝ) 1, ‖F t‖ ≤ B) :
    let b := ‖A‖ + B
    let T := torusKernelTime ν (torusPicardThreshold ‖C.analytic.bilinear‖ b)
    0 < T ∧ T ≤ 1 ∧ ∃ u : ℝ → PeriodicSobolev 3,
      TorusForcedMildOn C A F T u ∧ (∀ t ∈ Icc (0 : ℝ) T, ‖u t‖ ≤ b+1) ∧
      ∀ v : ℝ → PeriodicSobolev 3, TorusForcedMildOn C A F T v →
        (∀ t ∈ Icc (0 : ℝ) T, ‖v t‖ ≤ b+1) → ∀ t ∈ Icc (0 : ℝ) T, v t = u t := by
  dsimp only
  let b := ‖A‖ + B
  let T := torusKernelTime ν (torusPicardThreshold ‖C.analytic.bilinear‖ b)
  have hb : 0 ≤ b := add_nonneg (norm_nonneg _) hB
  have P := torusPicardConstants_explicit hν C hb
  have hT1 : T ≤ 1 := torusKernelTime_le_one _ _
  have hsub : Icc (0 : ℝ) T ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc_right hT1
  have hl (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ‖C.analytic.linearEvolution ⟨t, ht.1⟩ A +
        ∫ s in (0 : ℝ)..t, C.analytic.linearEvolution (Real.toNNReal (t-s)) (F s)‖ ≤ b := by
    exact (torus_forcedLinear_bound hν.le C A F (fun s hs ↦ hFB s (hsub hs)) t ht).trans
      (add_le_add (le_refl _) (by nlinarith [ht.2]))
  obtain ⟨u, hu, hub⟩ := torusForcedPicard_exists C A F T (b+1) b P (hF.mono hsub) hl
  exact ⟨P.time_pos, hT1, u, hu, hub, fun v hv hvb ↦ torusForcedMildOn_unique C P hv hu hvb hub⟩


/-- The zero Fourier mode is non-vacuous and its convection vanishes exactly. -/
theorem torusConvectionSymbol_constants (c d : Space) (i : Fin 3) (k : PeriodicFrequency) :
    torusConvectionSymbol (torusConstantDatum 3 c) (torusConstantDatum 3 d) i k = 0 := by
  by_cases hk : k = 0
  · subst k
    simp [torusConvectionSymbol, periodicDerivativeSymbol]
  · have hz (j : Fin 3) (l : PeriodicFrequency) :
        (((periodicFrequencyWeight l) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) *
          (torusConstantDatum 3 c).1 j l *
          (((periodicFrequencyWeight (k-l)) ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) *
          (torusConstantDatum 3 d).1 i (k-l) = 0 := by
      by_cases hl : l = 0
      · subst l
        simp [torusConstantDatum, lp.single_apply, hk]
      · simp [torusConstantDatum, lp.single_apply, hl]
    simp [torusConvectionSymbol, hz]

/-- Both nonzero constant modes test the actual projected symbol. -/
theorem torusProjectedConvectionSymbol_constants (c d : Space) (i : Fin 3) (k : PeriodicFrequency) :
    torusProjectedConvectionSymbol (torusConstantDatum 3 c) (torusConstantDatum 3 d) i k = 0 := by
  simp [torusProjectedConvectionSymbol, torusConvectionSymbol_constants]

/-- Amendment 1 has nonzero datum, force and solution witnesses on one common horizon. -/
theorem nonzero_forced_witness' :
    ∃ (K : ℝ≥0∞) (M : ℕ → ℝ≥0∞) (a : SpatialField) (g : SpaceTimeField),
      K ≠ ⊤ ∧ (∀ m, M m ≠ ⊤) ∧ a ∈ initialClassT ∧ periodicSobolevENorm 1 a ≤ K ∧
      ContDiff ℝ ∞ g ∧ IsPeriodicOn univ g ∧
      (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ M m) ∧
      ∃ w : ClassicalSolutionT 1 a g 1,
        PeriodicLocalRegularity 1 a g 1 w ∧
        w.velocity (0, 0) ≠ 0 ∧ g (0, 0) ≠ 0 := by
  obtain ⟨K, a, g, hK, ha, hKa, hg, hp, hKg, hw⟩ := nonzero_forced_witness
  exact ⟨K, fun _ ↦ K, a, g, hK, fun _ ↦ hK, ha, hKa, hg, hp, hKg, hw⟩

end NSFormalization.Section3.T11
