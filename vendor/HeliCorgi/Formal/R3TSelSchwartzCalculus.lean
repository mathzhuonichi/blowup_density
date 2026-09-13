import Formal.R3TSelClassicalComparability

/-!
# Schwartz-core calculus for the T-SEL commutator (SEL-4 infrastructure)

Pointwise product/derivative calculus on the Schwartz core, consumed by the BKM
commutator estimate (`Formal/R3TSelLeibnizCommutator.lean`):

* `r3SchwartzSMul` — the pointwise scalar–vector product `x ↦ a x • w x` as a Schwartz
  velocity, with the exact product rule `lineDerivOp_r3SchwartzSMul` for `∂_{m}`;
* commutation of line derivatives on Schwartz maps (`lineDerivOp_comm`), from the
  `C²` symmetry of the second Fréchet derivative — no analyticity is used — and its
  iterated form `iteratedLineDerivOp_lineDerivOp_comm`;
* commutation of `∂` with the coordinate projection (`lineDerivOp_r3SchwartzCoordinate`);
* sup bounds: the operator norm of a `R3 →L[ℝ] R3C` map by its standard-basis values,
  boundedness of `x ↦ ‖fderiv φ x‖`, the resulting pointwise bounds of first derivatives
  by `r3SchwartzGradSup`;
* the single-tuple `L²` bound `norm_toLp_tuple_le`: every derivative tuple of length
  `≤ 3` has `L²` norm at most `(2π)³ ‖J³φ‖`, from the proved SEL-1 comparability
  machinery.

No claim beyond the Schwartz core; nothing here mentions solutions of any PDE.
-/

namespace MNS2

open MeasureTheory SchwartzMap LineDeriv Real
open scoped FourierTransform SchwartzMap ENNReal NNReal ContDiff

noncomputable section

/-! ## The pointwise scalar–vector product -/

/-- Pointwise scalar–vector product of Schwartz maps: `x ↦ a x • w x`. -/
def r3SchwartzSMul (a : R3SchwartzScalar) (w : R3SchwartzVelocity) : R3SchwartzVelocity :=
  SchwartzMap.pairing
    (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] R3C →L[ℂ] R3C) a w

@[simp]
theorem r3SchwartzSMul_apply (a : R3SchwartzScalar) (w : R3SchwartzVelocity) (x : R3) :
    r3SchwartzSMul a w x = a x • w x := rfl

/-- The convection is the sum of the coordinate–derivative products. -/
theorem r3SchwartzConvection_eq_sum_smul (u v : R3SchwartzVelocity) :
    r3SchwartzConvection u v =
      ∑ i : Fin 3, r3SchwartzSMul (r3SchwartzCoordinate i u)
        (r3SchwartzCoordinateDerivative i v) := by
  refine SchwartzMap.ext fun x => ?_
  rw [r3SchwartzConvection_apply]
  rw [show (∑ i : Fin 3, r3SchwartzSMul (r3SchwartzCoordinate i u)
      (r3SchwartzCoordinateDerivative i v)) x =
      ∑ i : Fin 3, (r3SchwartzSMul (r3SchwartzCoordinate i u)
        (r3SchwartzCoordinateDerivative i v)) x from by
    simp [SchwartzMap.sum_apply]]
  exact Finset.sum_congr rfl fun i _ => by simp

/-- Exact product rule for the line derivative of a scalar–vector product. -/
theorem lineDerivOp_r3SchwartzSMul (m : R3) (a : R3SchwartzScalar)
    (w : R3SchwartzVelocity) :
    ∂_{m} (r3SchwartzSMul a w) =
      r3SchwartzSMul (∂_{m} a) w + r3SchwartzSMul a (∂_{m} w) := by
  refine SchwartzMap.ext fun x => ?_
  have hcoe : ⇑(r3SchwartzSMul a w) = ⇑a • ⇑w := funext fun y => rfl
  have hder := (a.hasFDerivAt x).smul (w.hasFDerivAt x)
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hcoe, hder.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, SchwartzMap.add_apply, r3SchwartzSMul_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [add_comm]

/-! ## Commutation of line derivatives -/

section comm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Second-derivative symmetry on the Schwartz core: line derivatives commute. -/
theorem lineDerivOp_comm (m m' : R3) (ψ : 𝓢(R3, F)) :
    ∂_{m} (∂_{m'} ψ) = ∂_{m'} (∂_{m} ψ) := by
  refine SchwartzMap.ext fun x => ?_
  have hsym : IsSymmSndFDerivAt ℝ (⇑ψ) x := by
    refine ContDiffAt.isSymmSndFDerivAt ((ψ.smooth ⊤).contDiffAt) ?_
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out
  have key : ∀ p q : R3, (∂_{p} (∂_{q} ψ)) x = fderiv ℝ (fderiv ℝ (⇑ψ)) x p q := by
    intro p q
    have hcoe : ((∂_{q} ψ : 𝓢(R3, F)) : R3 → F) = fun y => fderiv ℝ (⇑ψ) y q := by
      funext y
      exact SchwartzMap.lineDerivOp_apply_eq_fderiv q ψ y
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hcoe]
    have hd : DifferentiableAt ℝ (fderiv ℝ (⇑ψ)) x := by
      have h1 : ContDiff ℝ (1 : ℕ) (fderiv ℝ (⇑ψ)) := by
        refine (ψ.smooth ⊤).fderiv_right ?_
        first
        | exact ENat.LEInfty.out
        | (norm_num; exact ENat.LEInfty.out)
        | norm_num
      exact (h1.differentiable (by first | norm_num | simp)).differentiableAt
    rw [fderiv_clm_apply hd (differentiableAt_const q)]
    simp
  rw [key m m', key m' m, hsym m m']

/-- A single line derivative moves through an iterated line-derivative tuple. -/
theorem iteratedLineDerivOp_lineDerivOp_comm {n : ℕ} (m : Fin n → R3) (e : R3)
    (ψ : 𝓢(R3, F)) :
    ∂^{m} (∂_{e} ψ) = ∂_{e} (∂^{m} ψ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedLineDerivOp_succ_left, iteratedLineDerivOp_succ_left,
      ih (Fin.tail m), lineDerivOp_comm (m 0) e]

end comm

/-- The coordinate projection commutes with line derivatives. -/
theorem lineDerivOp_r3SchwartzCoordinate (m : R3) (i : Fin 3)
    (ψ : R3SchwartzVelocity) :
    ∂_{m} (r3SchwartzCoordinate i ψ) = r3SchwartzCoordinate i (∂_{m} ψ) := by
  refine SchwartzMap.ext fun x => ?_
  have hcoe : ⇑(r3SchwartzCoordinate i ψ) =
      fun y => (r3CoordinateFiberAux i) (ψ y) := by
    funext y
    rfl
  have hder := (((r3CoordinateFiberAux i).restrictScalars ℝ).hasFDerivAt).comp x
    (ψ.hasFDerivAt x)
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, hcoe,
    show (fun y => (r3CoordinateFiberAux i) (ψ y)) =
      ⇑((r3CoordinateFiberAux i).restrictScalars ℝ) ∘ ⇑ψ from rfl,
    hder.fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars']
  rfl

/-! ## Sup bounds by the gradient-sup -/

/-- Operator-norm bound of a continuous linear map on `R3` by its standard-basis
values. -/
theorem clm_norm_le_sum_stdBasis {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (L : R3 →L[ℝ] F) :
    ‖L‖ ≤ ∑ c : Fin 3, ‖L (r3StdBasis c)‖ := by
  refine L.opNorm_le_bound (Finset.sum_nonneg fun c _ => norm_nonneg _) fun y => ?_
  conv_lhs => rw [show y = ∑ c : Fin 3, y c • r3StdBasis c from r3_eq_sum_stdBasis y]
  rw [map_sum]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [map_smul, norm_smul]
  have h1 : ‖y c‖ ≤ ‖y‖ := PiLp.norm_apply_le y c
  calc ‖y c‖ * ‖L (r3StdBasis c)‖ ≤ ‖y‖ * ‖L (r3StdBasis c)‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖L (r3StdBasis c)‖ * ‖y‖ := by ring

/-- Boundedness of the pointwise Fréchet-derivative norm of a Schwartz map on `R3`. -/
theorem bddAbove_range_norm_fderiv_schwartz {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (φ : 𝓢(R3, F)) :
    BddAbove (Set.range fun x : R3 => ‖fderiv ℝ (⇑φ) x‖) := by
  have hbound : ∀ c : Fin 3, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : R3, ‖(∂_{r3StdBasis c} φ) x‖ ≤ C := by
    intro c
    obtain ⟨C, hC0, hC⟩ := (∂_{r3StdBasis c} φ).decay 0 0
    exact ⟨C, hC0.le, fun x => by simpa using hC x⟩
  choose Cf hCf0 hCf using hbound
  refine ⟨∑ c : Fin 3, Cf c, ?_⟩
  rintro r ⟨x, rfl⟩
  refine (clm_norm_le_sum_stdBasis (fderiv ℝ (⇑φ) x)).trans ?_
  refine Finset.sum_le_sum fun c _ => ?_
  have h1 : fderiv ℝ (⇑φ) x (r3StdBasis c) = (∂_{r3StdBasis c} φ) x :=
    (SchwartzMap.lineDerivOp_apply_eq_fderiv (r3StdBasis c) φ x).symm
  rw [h1]
  exact hCf c x

/-- The pointwise Fréchet-derivative norm is bounded by the gradient-sup. -/
theorem norm_fderiv_le_r3SchwartzGradSup (φ : R3SchwartzVelocity) (x : R3) :
    ‖fderiv ℝ (⇑φ) x‖ ≤ r3SchwartzGradSup φ :=
  le_ciSup (bddAbove_range_norm_fderiv_schwartz φ) x

theorem r3SchwartzGradSup_nonneg (φ : R3SchwartzVelocity) :
    0 ≤ r3SchwartzGradSup φ :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/-- First derivatives of a Schwartz velocity are pointwise bounded by the
gradient-sup. -/
theorem norm_lineDerivOp_stdBasis_le_gradSup (c : Fin 3) (φ : R3SchwartzVelocity)
    (x : R3) : ‖(∂_{r3StdBasis c} φ) x‖ ≤ r3SchwartzGradSup φ := by
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  calc ‖fderiv ℝ (⇑φ) x (r3StdBasis c)‖
      ≤ ‖fderiv ℝ (⇑φ) x‖ * ‖r3StdBasis c‖ :=
        (fderiv ℝ (⇑φ) x).le_opNorm _
    _ = ‖fderiv ℝ (⇑φ) x‖ := by
        rw [show ‖r3StdBasis c‖ = 1 from by
          unfold r3StdBasis
          simp [PiLp.norm_single], mul_one]
    _ ≤ r3SchwartzGradSup φ := norm_fderiv_le_r3SchwartzGradSup φ x

/-- First derivatives of a scalar coordinate are pointwise bounded by the
gradient-sup. -/
theorem norm_lineDerivOp_coordinate_le_gradSup (c i : Fin 3) (φ : R3SchwartzVelocity)
    (x : R3) :
    ‖(∂_{r3StdBasis c} (r3SchwartzCoordinate i φ)) x‖ ≤ r3SchwartzGradSup φ := by
  rw [lineDerivOp_r3SchwartzCoordinate]
  rw [show (r3SchwartzCoordinate i (∂_{r3StdBasis c} φ)) x =
      (∂_{r3StdBasis c} φ) x i from rfl]
  exact (norm_coord_le_norm_r3C _ i).trans
    (norm_lineDerivOp_stdBasis_le_gradSup c φ x)

/-! ## Single-tuple `L²` bounds from the SEL-1 machinery -/

/-- The `L²` norm of a Schwartz velocity as an integral. -/
theorem sq_norm_toLp_two (ψ : R3SchwartzVelocity) :
    ‖(ψ.toLp 2 : R3L2Velocity)‖ ^ 2 = ∫ x : R3, ‖ψ x‖ ^ 2 := by
  rw [SchwartzMap.norm_toLp]
  exact sq_toReal_eLpNorm_two (ψ.memLp 2)

/-- Every derivative tuple of length `n ≤ 3` of a Schwartz velocity has `L²` norm at
most `(2π)³ ‖J³φ‖`. -/
theorem norm_toLp_tuple_le {n : ℕ} (hn : n ≤ 3) (v : Fin n → Fin 3)
    (φ : R3SchwartzVelocity) :
    ‖((∂^{r3TSelTupleDirections v} φ).toLp 2 : R3L2Velocity)‖ ≤
      (2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖ := by
  have hsq : ‖((∂^{r3TSelTupleDirections v} φ).toLp 2 : R3L2Velocity)‖ ^ 2 ≤
      ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖) ^ 2 := by
    rw [sq_norm_toLp_two]
    have h1 : (∫ x : R3, ‖(∂^{r3TSelTupleDirections v} φ) x‖ ^ 2) ≤
        r3TSelTupleEnergy n φ := by
      unfold r3TSelTupleEnergy
      exact Finset.single_le_sum
        (f := fun w : Fin n → Fin 3 =>
          ∫ x : R3, ‖(∂^{r3TSelTupleDirections w} φ) x‖ ^ 2)
        (fun w _ => integral_nonneg fun x => sq_nonneg _) (Finset.mem_univ v)
    have h2 : r3TSelTupleEnergy n φ ≤ ∑ k ∈ Finset.range 4, r3TSelTupleEnergy k φ := by
      refine Finset.single_le_sum (f := fun k => r3TSelTupleEnergy k φ)
        (fun k _ => ?_) (Finset.mem_range.mpr (by omega))
      unfold r3TSelTupleEnergy
      exact Finset.sum_nonneg fun w _ => integral_nonneg fun x => sq_nonneg _
    have h3 := (sum_tupleEnergies_comparison φ).2
    have hpow : (2 * π) ^ 6 * ‖r3SchwartzToHsCLM 3 φ‖ ^ 2 =
        ((2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖) ^ 2 := by ring
    linarith [h1, h2, h3, hpow.le, hpow.ge]
  have h0 : (0 : ℝ) ≤ (2 * π) ^ 3 * ‖r3SchwartzToHsCLM 3 φ‖ := by positivity
  nlinarith [norm_nonneg ((∂^{r3TSelTupleDirections v} φ).toLp 2 : R3L2Velocity)]


/-! ## Operator-norm sup constants for Schwartz derivatives -/

/-- Every Schwartz map on `R3` has a uniform bound on its pointwise Fréchet-derivative
operator norm. -/
theorem exists_fderiv_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : 𝓢(R3, F)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : R3, ‖fderiv ℝ (⇑φ) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := bddAbove_range_norm_fderiv_schwartz φ
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  exact le_max_of_le_left (hC ⟨x, rfl⟩)

/-- Every Schwartz map on `R3` is uniformly bounded. -/
theorem exists_sup_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : 𝓢(R3, F)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : R3, ‖φ x‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := φ.decay 0 0
  exact ⟨C, hC0.le, fun x => by simpa using hC x⟩

/-! ## Integration by parts on `R3` via the Fourier transform at frequency zero -/

/-- For an integrable differentiable function with integrable derivative, the integral of
any directional derivative vanishes: evaluate `𝓕(fderiv H) = (2πi ⟪·,w⟫)-multiplier`
at frequency zero. -/
theorem integral_fderiv_apply_eq_zero {H : R3 → ℂ} (hH : Integrable H volume)
    (hdiff : Differentiable ℝ H) (hH' : Integrable (fderiv ℝ H) volume) (m : R3) :
    ∫ x : R3, fderiv ℝ H x m = 0 := by
  have h0 : 𝓕 (fderiv ℝ H) 0 = ∫ x : R3, fderiv ℝ H x := by
    rw [Real.fourier_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp
  have h1 : 𝓕 (fderiv ℝ H) 0 = 0 := by
    rw [Real.fourier_fderiv hH hdiff hH']
    ext y
    simp [VectorFourier.fourierSMulRight]
  have h2 : (∫ x : R3, fderiv ℝ H x) = 0 := by rw [← h0, h1]
  calc (∫ x : R3, fderiv ℝ H x m)
      = (∫ x : R3, fderiv ℝ H x) m := (ContinuousLinearMap.integral_apply hH' m).symm
    _ = 0 := by rw [h2]; rfl

/-! ## Cauchy–Schwarz for integrals of nonnegative products -/

/-- Cauchy–Schwarz: `∫ f g ≤ √(∫ f²) √(∫ g²)` for nonnegative square-integrable
functions. -/
theorem integral_mul_le_sqrt_mul_sqrt {f g : R3 → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfm : AEStronglyMeasurable f (volume : Measure R3))
    (hgm : AEStronglyMeasurable g (volume : Measure R3))
    (hf2 : Integrable (fun x => f x ^ 2) volume)
    (hg2 : Integrable (fun x => g x ^ 2) volume) :
    ∫ x : R3, f x * g x ≤
      Real.sqrt (∫ x : R3, f x ^ 2) * Real.sqrt (∫ x : R3, g x ^ 2) := by
  have hfL : MemLp f 2 (volume : Measure R3) := (memLp_two_iff_integrable_sq hfm).mpr hf2
  have hgL : MemLp g 2 (volume : Measure R3) := (memLp_two_iff_integrable_sq hgm).mpr hg2
  have hinner : (inner ℝ (hfL.toLp f) (hgL.toLp g) : ℝ) = ∫ x : R3, f x * g x := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hfL.coeFn_toLp, hgL.coeFn_toLp] with x h1 h2
    rw [h1, h2]
    simp [mul_comm]
  have hFn : ‖hfL.toLp f‖ = Real.sqrt (∫ x : R3, f x ^ 2) := by
    have h1 : ‖hfL.toLp f‖ ^ 2 = ∫ x : R3, f x ^ 2 := by
      rw [MeasureTheory.Lp.norm_toLp _ hfL]
      refine (sq_toReal_eLpNorm_two hfL).trans
        (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_))
      show ‖f x‖ ^ 2 = f x ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
    rw [← h1, Real.sqrt_sq (norm_nonneg _)]
  have hGn : ‖hgL.toLp g‖ = Real.sqrt (∫ x : R3, g x ^ 2) := by
    have h1 : ‖hgL.toLp g‖ ^ 2 = ∫ x : R3, g x ^ 2 := by
      rw [MeasureTheory.Lp.norm_toLp _ hgL]
      refine (sq_toReal_eLpNorm_two hgL).trans
        (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_))
      show ‖g x‖ ^ 2 = g x ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
    rw [← h1, Real.sqrt_sq (norm_nonneg _)]
  calc (∫ x : R3, f x * g x)
      = (inner ℝ (hfL.toLp f) (hgL.toLp g) : ℝ) := hinner.symm
    _ ≤ ‖hfL.toLp f‖ * ‖hgL.toLp g‖ := real_inner_le_norm _ _
    _ = Real.sqrt (∫ x : R3, f x ^ 2) * Real.sqrt (∫ x : R3, g x ^ 2) := by
        rw [hFn, hGn]


/-! ## The quartic Gagliardo–Nirenberg interpolation (scalar Schwartz form) -/

set_option maxHeartbeats 1600000 in
/-- **Quartic interpolation by parts** (the Gagliardo–Nirenberg step of the BKM
commutator): for a scalar Schwartz function `u`, directions `p, q`, and any pointwise
bound `S` on `∂_p u`,

`∫ |∂_q ∂_p u|⁴ ≤ 9 S² ∫ |∂_q ∂_q ∂_p u|²`.

Proof: with `v = ∂_p u`, `w = ∂_q v`, write `|w|⁴ = (w̄²w)·w` and move the outer `q`
derivative off `w` by parts (`integral_fderiv_apply_eq_zero`), then Cauchy–Schwarz. -/
theorem r3TSel_gn_quartic (u : R3SchwartzScalar) (p q : R3) {S : ℝ}
    (hS : ∀ x : R3, ‖(∂_{p} u) x‖ ≤ S) :
    ∫ x : R3, ‖(∂_{q} (∂_{p} u)) x‖ ^ 4 ≤
      9 * S ^ 2 * ∫ x : R3, ‖(∂_{q} (∂_{q} (∂_{p} u))) x‖ ^ 2 := by
  set v : R3SchwartzScalar := ∂_{p} u with hvdef
  set w : R3SchwartzScalar := ∂_{q} v with hwdef
  set z : R3SchwartzScalar := ∂_{q} w with hzdef
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0)
  obtain ⟨Sw, hSw0, hSw⟩ := exists_sup_bound (F := ℂ) w
  obtain ⟨Cw', hCw'0, hCw'⟩ := exists_fderiv_bound (F := ℂ) w
  obtain ⟨Cv', hCv'0, hCv'⟩ := exists_fderiv_bound (F := ℂ) v
  set c : R3 → ℂ := fun x => (starRingEnd ℂ) (w x) with hcdef
  set h : R3 → ℂ := fun x => c x * c x * w x with hhdef
  set Hfun : R3 → ℂ := fun x => v x * h x with hHdef
  have hnorm_c : ∀ x, ‖c x‖ = ‖w x‖ := fun x => RCLike.norm_conj _
  have hcoe_c : (⇑(Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ ⇑w) = c := by
    funext y
    show Complex.conjCLE (w y) = (starRingEnd ℂ) (w y)
    simp
  have hc_cont : Continuous c := by
    rw [← hcoe_c]
    exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).continuous.comp w.continuous
  set Dc : R3 → (R3 →L[ℝ] ℂ) :=
    fun x => (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (fderiv ℝ (⇑w) x) with hDcdef
  have hcder : ∀ x : R3, HasFDerivAt c (Dc x) x := by
    intro x
    have h1 := ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt (x := w x)).comp x
      (w.hasFDerivAt x)
    rwa [hcoe_c] at h1
  have hnorm_Dc : ∀ x m, ‖Dc x m‖ = ‖fderiv ℝ (⇑w) x m‖ := by
    intro x m
    simp [hDcdef]
  set Dh : R3 → (R3 →L[ℝ] ℂ) :=
    fun x => (c x * c x) • fderiv ℝ (⇑w) x + w x • (c x • Dc x + c x • Dc x) with hDhdef
  have hhder : ∀ x : R3, HasFDerivAt h (Dh x) x := by
    intro x
    exact ((hcder x).mul (hcder x)).mul (w.hasFDerivAt x)
  have hDh_bound : ∀ x m, ‖Dh x m‖ ≤ 3 * ‖w x‖ ^ 2 * ‖fderiv ℝ (⇑w) x m‖ := by
    intro x m
    have h1 : ‖Dh x m‖ ≤ ‖c x * c x‖ * ‖fderiv ℝ (⇑w) x m‖ +
        ‖w x‖ * (‖c x‖ * ‖Dc x m‖ + ‖c x‖ * ‖Dc x m‖) := by
      simp only [hDhdef, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul]
      refine add_le_add le_rfl ?_
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul]
    rw [norm_mul, hnorm_c, hnorm_Dc] at h1
    nlinarith [norm_nonneg (w x), norm_nonneg (fderiv ℝ (⇑w) x m)]
  have hDh_opnorm : ∀ x, ‖Dh x‖ ≤ 3 * ‖w x‖ ^ 2 * ‖fderiv ℝ (⇑w) x‖ := by
    intro x
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun m => ?_
    refine (hDh_bound x m).trans ?_
    have h2 := (fderiv ℝ (⇑w) x).le_opNorm m
    nlinarith [norm_nonneg (w x), norm_nonneg m, norm_nonneg (fderiv ℝ (⇑w) x)]
  have hHder : ∀ x : R3, HasFDerivAt Hfun (v x • Dh x + h x • fderiv ℝ (⇑v) x) x :=
    fun x => (v.hasFDerivAt x).mul (hhder x)
  have hc_smooth : ContDiff ℝ (⊤ : ℕ∞) c := by
    rw [← hcoe_c]
    exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp (w.smooth ⊤)
  have hH_smooth : ContDiff ℝ (⊤ : ℕ∞) Hfun :=
    (v.smooth ⊤).mul ((hc_smooth.mul hc_smooth).mul (w.smooth ⊤))
  have hH_cont : Continuous Hfun := hH_smooth.continuous
  have hH'_cont : Continuous (fderiv ℝ Hfun) := by
    refine hH_smooth.continuous_fderiv ?_
    simp
  have hH_int : Integrable Hfun volume := by
    refine ((w.integrable).norm.const_mul (S * Sw ^ 2)).mono'
      hH_cont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    have hval : ‖Hfun x‖ = ‖v x‖ * (‖w x‖ ^ 2 * ‖w x‖) := by
      simp only [hHdef, hhdef, norm_mul, hnorm_c]
      ring
    rw [hval]
    have h1 := hS x
    have h2 := hSw x
    have h3 : (0 : ℝ) ≤ ‖w x‖ := norm_nonneg _
    have h4 : ‖w x‖ ^ 2 ≤ Sw ^ 2 := pow_le_pow_left₀ h3 h2 2
    calc ‖v x‖ * (‖w x‖ ^ 2 * ‖w x‖)
        ≤ S * (Sw ^ 2 * ‖w x‖) := by
          refine mul_le_mul h1 ?_ (by positivity) hS0
          exact mul_le_mul_of_nonneg_right h4 h3
      _ = S * Sw ^ 2 * ‖w x‖ := by ring
  have hH_diff : Differentiable ℝ Hfun := fun x => (hHder x).differentiableAt
  have hH'_int : Integrable (fderiv ℝ Hfun) volume := by
    refine ((w.integrable).norm.const_mul (3 * S * Sw * Cw' + Sw ^ 2 * Cv')).mono'
      hH'_cont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [(hHder x).fderiv]
    have h1 : ‖v x • Dh x + h x • fderiv ℝ (⇑v) x‖ ≤
        ‖v x‖ * ‖Dh x‖ + ‖h x‖ * ‖fderiv ℝ (⇑v) x‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul]
    have h2 : ‖h x‖ = ‖w x‖ ^ 2 * ‖w x‖ := by
      simp only [hhdef, norm_mul, hnorm_c]
      ring
    have h3 := hDh_opnorm x
    have h4 := hS x
    have h5 := hSw x
    have h6 := hCw' x
    have h7 := hCv' x
    have h8 : (0 : ℝ) ≤ ‖w x‖ := norm_nonneg _
    have h9 : (0 : ℝ) ≤ ‖fderiv ℝ (⇑w) x‖ := norm_nonneg _
    refine h1.trans ?_
    rw [h2]
    have h10 : ‖v x‖ * ‖Dh x‖ ≤ 3 * S * Sw * Cw' * ‖w x‖ := by
      have ha : ‖w x‖ ^ 2 * ‖fderiv ℝ (⇑w) x‖ ≤ (Sw * Cw') * ‖w x‖ := by
        have hb : ‖w x‖ ^ 2 * ‖fderiv ℝ (⇑w) x‖ =
            (‖w x‖ * ‖fderiv ℝ (⇑w) x‖) * ‖w x‖ := by ring
        rw [hb]
        refine mul_le_mul_of_nonneg_right ?_ h8
        exact mul_le_mul h5 h6 h9 hSw0
      calc ‖v x‖ * ‖Dh x‖
          ≤ S * (3 * (‖w x‖ ^ 2 * ‖fderiv ℝ (⇑w) x‖)) := by
            refine mul_le_mul h4 ?_ (norm_nonneg _) hS0
            calc ‖Dh x‖ ≤ 3 * ‖w x‖ ^ 2 * ‖fderiv ℝ (⇑w) x‖ := h3
              _ = 3 * (‖w x‖ ^ 2 * ‖fderiv ℝ (⇑w) x‖) := by ring
        _ ≤ S * (3 * ((Sw * Cw') * ‖w x‖)) := by
            refine mul_le_mul_of_nonneg_left ?_ hS0
            exact mul_le_mul_of_nonneg_left ha (by norm_num)
        _ = 3 * S * Sw * Cw' * ‖w x‖ := by ring
    have h11 : ‖w x‖ ^ 2 * ‖w x‖ * ‖fderiv ℝ (⇑v) x‖ ≤ Sw ^ 2 * Cv' * ‖w x‖ := by
      have ha : ‖w x‖ ^ 2 * ‖w x‖ * ‖fderiv ℝ (⇑v) x‖ =
          (‖w x‖ ^ 2 * ‖fderiv ℝ (⇑v) x‖) * ‖w x‖ := by ring
      rw [ha]
      refine mul_le_mul_of_nonneg_right ?_ h8
      exact mul_le_mul (pow_le_pow_left₀ h8 h5 2) h7 (norm_nonneg _) (by positivity)
    calc ‖v x‖ * ‖Dh x‖ + ‖w x‖ ^ 2 * ‖w x‖ * ‖fderiv ℝ (⇑v) x‖
        ≤ 3 * S * Sw * Cw' * ‖w x‖ + Sw ^ 2 * Cv' * ‖w x‖ := add_le_add h10 h11
      _ = (3 * S * Sw * Cw' + Sw ^ 2 * Cv') * ‖w x‖ := by ring
  have hzero := integral_fderiv_apply_eq_zero hH_int hH_diff hH'_int q
  have hpt : ∀ x : R3, fderiv ℝ Hfun x q = v x * (Dh x q) + h x * w x := by
    intro x
    rw [(hHder x).fderiv]
    have hfvq : fderiv ℝ (⇑v) x q = w x :=
      (SchwartzMap.lineDerivOp_apply_eq_fderiv q v x).symm
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, hfvq]
  have hfwq : ∀ x : R3, fderiv ℝ (⇑w) x q = z x := fun x =>
    (SchwartzMap.lineDerivOp_apply_eq_fderiv q w x).symm
  have hDhq_cont : Continuous fun x : R3 => Dh x q := by
    have hw' : Continuous fun x : R3 => fderiv ℝ (⇑w) x q := by
      have h1 : Continuous (fderiv ℝ (⇑w)) := by
        refine (w.smooth ⊤).continuous_fderiv ?_
        simp
      exact (ContinuousLinearMap.apply ℝ ℂ q).continuous.comp h1
    have hDcq : Continuous fun x : R3 => Dc x q := by
      have h2 : (fun x : R3 => Dc x q) =
          fun x => (Complex.conjCLE : ℂ →L[ℝ] ℂ) (fderiv ℝ (⇑w) x q) := by
        funext x
        simp [hDcdef]
      rw [h2]
      exact (Complex.conjCLE : ℂ →L[ℝ] ℂ).continuous.comp hw'
    have h3 : (fun x : R3 => Dh x q) = fun x =>
        (c x * c x) * (fderiv ℝ (⇑w) x q) +
          w x * (c x * (Dc x q) + c x * (Dc x q)) := by
      funext x
      simp only [hDhdef, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      try ring
    rw [h3]
    exact ((hc_cont.mul hc_cont).mul hw').add
      (w.continuous.mul ((hc_cont.mul hDcq).add (hc_cont.mul hDcq)))
  have hvDh_int : Integrable (fun x => v x * (Dh x q)) volume := by
    refine ((z.integrable).norm.const_mul (3 * S * Sw ^ 2)).mono'
      (v.continuous.mul hDhq_cont).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul]
    have h1 : ‖Dh x q‖ ≤ 3 * ‖w x‖ ^ 2 * ‖z x‖ := by
      have := hDh_bound x q
      rwa [hfwq x] at this
    have h2 := hS x
    have h3 := hSw x
    have h4 : (0 : ℝ) ≤ ‖w x‖ := norm_nonneg _
    have h5 : (0 : ℝ) ≤ ‖z x‖ := norm_nonneg _
    have h6 : ‖w x‖ ^ 2 ≤ Sw ^ 2 := pow_le_pow_left₀ h4 h3 2
    calc ‖v x‖ * ‖Dh x q‖
        ≤ S * (3 * ‖w x‖ ^ 2 * ‖z x‖) := by
          exact mul_le_mul h2 h1 (norm_nonneg _) hS0
      _ ≤ S * (3 * Sw ^ 2 * ‖z x‖) := by
          refine mul_le_mul_of_nonneg_left ?_ hS0
          refine mul_le_mul_of_nonneg_right ?_ h5
          exact mul_le_mul_of_nonneg_left h6 (by norm_num)
      _ = 3 * S * Sw ^ 2 * ‖z x‖ := by ring
  have hhw_int : Integrable (fun x => h x * w x) volume := by
    refine ((w.integrable).norm.const_mul (Sw ^ 3)).mono'
      ((((hc_cont.mul hc_cont).mul w.continuous).mul
        w.continuous)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have hval : ‖h x * w x‖ = (‖w x‖ ^ 2 * ‖w x‖) * ‖w x‖ := by
      simp only [hhdef, norm_mul, hnorm_c]
      ring
    rw [hval]
    have h2 := hSw x
    have h3 : (0 : ℝ) ≤ ‖w x‖ := norm_nonneg _
    have h4 : ‖w x‖ ^ 2 * ‖w x‖ ≤ Sw ^ 3 := by
      calc ‖w x‖ ^ 2 * ‖w x‖ = ‖w x‖ ^ 3 := by ring
        _ ≤ Sw ^ 3 := pow_le_pow_left₀ h3 h2 3
    exact mul_le_mul_of_nonneg_right h4 h3
  have hsplit : (∫ x : R3, (v x * (Dh x q) + h x * w x)) = 0 := by
    rw [show (fun x : R3 => v x * (Dh x q) + h x * w x) =
        fun x : R3 => fderiv ℝ Hfun x q from funext fun x => (hpt x).symm]
    exact hzero
  have hflip : (∫ x : R3, h x * w x) = - ∫ x : R3, v x * (Dh x q) := by
    have hadd := integral_add hvDh_int hhw_int
    rw [hadd] at hsplit
    exact eq_neg_of_add_eq_zero_right hsplit
  have hIcast : (∫ x : R3, h x * w x) =
      (((∫ x : R3, ‖w x‖ ^ 4) : ℝ) : ℂ) := by
    have hfun : (fun x : R3 => h x * w x) =
        fun x : R3 => (((‖w x‖ ^ 4 : ℝ)) : ℂ) := by
      funext x
      have h1 : c x * w x = (‖w x‖ : ℂ) ^ 2 := by
        show (starRingEnd ℂ) (w x) * w x = (‖w x‖ : ℂ) ^ 2
        rw [mul_comm, Complex.mul_conj']
      have h2 : h x * w x = (c x * w x) * (c x * w x) := by
        show (c x * c x * w x) * w x = (c x * w x) * (c x * w x)
        ring
      rw [h2, h1]
      push_cast
      ring
    rw [hfun]
    exact integral_ofReal
  set I : ℝ := ∫ x : R3, ‖w x‖ ^ 4 with hIdef
  set D : ℝ := ∫ x : R3, ‖z x‖ ^ 2 with hDdef
  have hI0 : 0 ≤ I := integral_nonneg fun x => by positivity
  have hD0 : 0 ≤ D := integral_nonneg fun x => by positivity
  have hwz_int : Integrable (fun x => 3 * S * (‖w x‖ ^ 2 * ‖z x‖)) volume := by
    refine ((z.integrable).norm.const_mul (3 * S * Sw ^ 2)).mono'
      ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (((continuous_const.mul
        ((w.continuous.norm.pow 2).mul z.continuous.norm)))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h2 := hSw x
      have h3 : (0 : ℝ) ≤ ‖w x‖ := norm_nonneg _
      have h5 : (0 : ℝ) ≤ ‖z x‖ := norm_nonneg _
      have h6 : ‖w x‖ ^ 2 ≤ Sw ^ 2 := pow_le_pow_left₀ h3 h2 2
      calc 3 * S * (‖w x‖ ^ 2 * ‖z x‖)
          ≤ 3 * S * (Sw ^ 2 * ‖z x‖) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right h6 h5
        _ = 3 * S * Sw ^ 2 * ‖z x‖ := by ring
  have hIneq : I ≤ 3 * S * ∫ x : R3, ‖w x‖ ^ 2 * ‖z x‖ := by
    have h1 : ((I : ℝ) : ℂ) = - ∫ x : R3, v x * (Dh x q) := by
      rw [← hIcast, hflip]
    have h2 : I = ‖((I : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hI0]
    rw [h2, h1, norm_neg]
    refine (norm_integral_le_integral_norm _).trans ?_
    have h3 : (∫ x : R3, ‖v x * (Dh x q)‖) ≤
        ∫ x : R3, 3 * S * (‖w x‖ ^ 2 * ‖z x‖) := by
      refine integral_mono hvDh_int.norm hwz_int fun x => ?_
      rw [norm_mul]
      have h4 : ‖Dh x q‖ ≤ 3 * ‖w x‖ ^ 2 * ‖z x‖ := by
        have := hDh_bound x q
        rwa [hfwq x] at this
      have h5 := hS x
      have h6 : (0 : ℝ) ≤ ‖w x‖ := norm_nonneg _
      have h7 : (0 : ℝ) ≤ ‖z x‖ := norm_nonneg _
      calc ‖v x‖ * ‖Dh x q‖
          ≤ S * (3 * ‖w x‖ ^ 2 * ‖z x‖) :=
            mul_le_mul h5 h4 (norm_nonneg _) hS0
        _ = 3 * S * (‖w x‖ ^ 2 * ‖z x‖) := by ring
    refine h3.trans_eq ?_
    rw [integral_const_mul]
  have hCS : (∫ x : R3, ‖w x‖ ^ 2 * ‖z x‖) ≤ Real.sqrt I * Real.sqrt D := by
    have hf2 : Integrable (fun x : R3 => (‖w x‖ ^ 2) ^ 2) volume := by
      refine ((w.integrable).norm.const_mul (Sw ^ 3)).mono'
        ((w.continuous.norm.pow 2).pow 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h2 := hSw x
      have h3 : (0 : ℝ) ≤ ‖w x‖ := norm_nonneg _
      have h4 : ‖w x‖ ^ 3 ≤ Sw ^ 3 := pow_le_pow_left₀ h3 h2 3
      calc (‖w x‖ ^ 2) ^ 2 = ‖w x‖ ^ 3 * ‖w x‖ := by ring
        _ ≤ Sw ^ 3 * ‖w x‖ := mul_le_mul_of_nonneg_right h4 h3
    have hg2 : Integrable (fun x : R3 => ‖z x‖ ^ 2) volume :=
      (memLp_two_iff_integrable_sq
        (z.continuous.aestronglyMeasurable.norm)).mp ((z.memLp 2).norm)
    have hcs := integral_mul_le_sqrt_mul_sqrt
      (f := fun x : R3 => ‖w x‖ ^ 2) (g := fun x : R3 => ‖z x‖)
      (fun x => by positivity) (fun x => norm_nonneg _)
      (w.continuous.norm.pow 2).aestronglyMeasurable
      z.continuous.norm.aestronglyMeasurable hf2 hg2
    refine hcs.trans_eq ?_
    have hquart : (∫ x : R3, (‖w x‖ ^ 2) ^ 2) = ∫ x : R3, ‖w x‖ ^ 4 :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [hquart]
  have hfinal : I ≤ 9 * S ^ 2 * D := by
    have h1 : I ≤ 3 * S * (Real.sqrt I * Real.sqrt D) := by
      refine hIneq.trans ?_
      nlinarith [hCS, Real.sqrt_nonneg I, Real.sqrt_nonneg D]
    have hsqI : Real.sqrt I * Real.sqrt I = I := Real.mul_self_sqrt hI0
    have hsqD : Real.sqrt D * Real.sqrt D = D := Real.mul_self_sqrt hD0
    nlinarith [Real.sqrt_nonneg I, Real.sqrt_nonneg D,
      sq_nonneg (Real.sqrt I - 3 * S * Real.sqrt D)]
  exact hfinal

end

end MNS2
