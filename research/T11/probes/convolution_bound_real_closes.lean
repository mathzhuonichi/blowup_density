import NSFormalization.Section3.T11.ConvolutionBoundReal

/-! Lane 328 probe: every target of the real-order convolution bound closes on
the canonical carriers, at a general real order `r ≥ 3` and at the two required
instances `r = 3` and `r = 7/2`, with two constant-mode data at each. -/

noncomputable section
open NSFormalization.Section3.T10 NSFormalization.Section3.T11

local instance convolutionRealProbeNormedGroup (s : ℝ) : NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance convolutionRealProbeNormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

/-! ## 1. The target at a general real order `r ≥ 3` -/

-- The bounded real bilinear map exists, with the order-`(r-1)` carrier as codomain.
example (r : ℝ) (hr : 3 ≤ r) (A B : PeriodicSobolev r) : PeriodicSobolev (r - 1) :=
  torusConvolutionCLM_real r hr A B

-- Its coefficients are the projected real-order convection symbol.
example (r : ℝ) (hr : 3 ≤ r) (A B : PeriodicSobolev r) (i : Fin 3) (k : PeriodicFrequency) :
    (torusConvolutionCLM_real r hr A B).1 i k = torusProjectedConvectionSymbolReal r A B i k :=
  torusConvolutionCLM_real_coeff r hr A B i k

-- Its operator norm obeys the explicit constant `9 · sqrt (2 · 4^r · ∑_k W(k)^(-r))`.
example (r : ℝ) (hr : 3 ≤ r) :
    ‖torusConvolutionCLM_real r hr‖ ≤ 9 * Real.sqrt (torusConvolutionBoundSquaredReal r) :=
  torusConvolutionCLM_real_norm_le r hr

example (r : ℝ) (hr : 3 ≤ r) (A B : PeriodicSobolev r) :
    ‖torusConvolutionCLM_real r hr A B‖ ≤ torusConvolutionConstant_real r * ‖A‖ * ‖B‖ :=
  torusConvolutionCLM_real_apply_norm_le r hr A B

-- Coefficient identity in the `.1 i k` form: lane 317's projected convection symbol
-- of the order-three reweighted data, transported by the weight `W(k)^((r-3)/2)`.
example (r : ℝ) (hr : 3 ≤ r) (A B : PeriodicSobolev r) (i : Fin 3) (k : PeriodicFrequency) :
    (torusConvolutionCLM_real r hr A B).1 i k =
      ((periodicFrequencyWeight k ^ ((r - 3) / 2) : ℝ) : ℂ) *
        torusProjectedConvectionSymbol
          (persistenceDown r 3 hr A) (persistenceDown r 3 hr B) i k :=
  torusConvolutionCLM_real_coeff_transport r hr A B i k

-- Reweighting compatibility between orders `r ≤ r'`.
example (r r' : ℝ) (hr : 3 ≤ r) (hr' : 3 ≤ r') (_hrr : r ≤ r')
    (A B : PeriodicSobolev r) (A' B' : PeriodicSobolev r')
    (hA : IsPeriodicReweight r r' A A') (hB : IsPeriodicReweight r r' B B') :
    IsPeriodicReweight (r - 1) (r' - 1)
      (torusConvolutionCLM_real r hr A B) (torusConvolutionCLM_real r' hr' A' B') :=
  torusConvolutionCLM_real_reweight r r' hr hr' hA hB

/-! ## 2. Instance `r = 3`: lane 313's target and lane 317's coefficients -/

example : (3 : ℝ) - 1 = 2 := by norm_num

example :
    ∃ Q : PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 2,
      ∀ A B i k, (Q A B).1 i k = torusProjectedConvectionSymbol A B i k :=
  torusConvolutionInput_ofReal

example : TorusConvolutionInput := torusConvolutionInput_ofReal

example (A B : PeriodicSobolev 3) (i : Fin 3) (k : PeriodicFrequency) :
    (torusConvolutionCLM_realAt 3 2 le_rfl A B).1 i k = torusProjectedConvectionSymbol A B i k := by
  rw [torusConvolutionCLM_realAt_coeff, torusProjectedConvectionSymbolReal_three]

example : ‖torusConvolutionCLM_realAt 3 2 le_rfl‖ ≤ torusConvolutionConstant_real 3 :=
  torusConvolutionCLM_realAt_norm_le 3 2 le_rfl

example (A B : PeriodicSobolev 3) (i : Fin 3) (k : PeriodicFrequency) :
    (torusConvolutionCLM_real 3 le_rfl A B).1 i k = torusProjectedConvectionSymbol A B i k :=
  torusConvolutionCLM_real_coeff_three A B i k

-- Two nonzero constant-mode data at order three.
example : ∃ A B : PeriodicSobolev 3, A ≠ 0 ∧ B ≠ 0 ∧
    torusConvolutionCLM_real 3 le_rfl A B = 0 := by
  let c : NavierStokes.ProblemStatement.Space := WithLp.toLp 2 (fun _ ↦ 1)
  let d : NavierStokes.ProblemStatement.Space := WithLp.toLp 2 (fun _ ↦ 2)
  refine ⟨torusConstantDatum 3 c, torusConstantDatum 3 d, ?_, ?_,
    torusConvolutionCLM_real_constants 3 le_rfl c d⟩
  · intro h
    have hc := congrArg
      (fun D : PeriodicSobolev 3 ↦ D.1 (0 : Fin 3) (0 : PeriodicFrequency)) h
    change (1 : ℂ) = 0 at hc
    exact one_ne_zero hc
  · intro h
    have hc := congrArg
      (fun D : PeriodicSobolev 3 ↦ D.1 (0 : Fin 3) (0 : PeriodicFrequency)) h
    change (2 : ℂ) = 0 at hc
    exact two_ne_zero hc

/-! ## 3. Instance `r = 7/2`: a genuinely non-integer order -/

example : (7 / 2 : ℝ) - 1 = 5 / 2 := by norm_num

example : (3 : ℝ) ≤ 7 / 2 := by norm_num

example (A B : PeriodicSobolev (7 / 2 : ℝ)) (i : Fin 3) (k : PeriodicFrequency) :
    (torusConvolutionCLM_realAt (7 / 2 : ℝ) (5 / 2 : ℝ) (by norm_num) A B).1 i k =
      torusProjectedConvectionSymbolReal (7 / 2 : ℝ) A B i k :=
  torusConvolutionCLM_realAt_coeff (7 / 2 : ℝ) (5 / 2 : ℝ) (by norm_num) A B i k

example : ‖torusConvolutionCLM_realAt (7 / 2 : ℝ) (5 / 2 : ℝ) (by norm_num)‖ ≤
    torusConvolutionConstant_real (7 / 2 : ℝ) :=
  torusConvolutionCLM_realAt_norm_le (7 / 2 : ℝ) (5 / 2 : ℝ) (by norm_num)

example (A B : PeriodicSobolev (7 / 2 : ℝ)) :
    ‖torusConvolutionCLM_real (7 / 2 : ℝ) (by norm_num) A B‖ ≤
      torusConvolutionConstant_real (7 / 2 : ℝ) * ‖A‖ * ‖B‖ :=
  torusConvolutionCLM_real_apply_norm_le (7 / 2 : ℝ) (by norm_num) A B

-- Two nonzero constant-mode data at order 7/2.
example : ∃ A B : PeriodicSobolev (7 / 2 : ℝ), A ≠ 0 ∧ B ≠ 0 ∧
    torusConvolutionCLM_real (7 / 2 : ℝ) (by norm_num) A B = 0 := by
  let c : NavierStokes.ProblemStatement.Space := WithLp.toLp 2 (fun _ ↦ 1)
  let d : NavierStokes.ProblemStatement.Space := WithLp.toLp 2 (fun _ ↦ 2)
  refine ⟨torusConstantDatum (7 / 2 : ℝ) c, torusConstantDatum (7 / 2 : ℝ) d, ?_, ?_,
    torusConvolutionCLM_real_constants (7 / 2 : ℝ) (by norm_num) c d⟩
  · intro h
    have hc := congrArg
      (fun D : PeriodicSobolev (7 / 2 : ℝ) ↦ D.1 (0 : Fin 3) (0 : PeriodicFrequency)) h
    change (1 : ℂ) = 0 at hc
    exact one_ne_zero hc
  · intro h
    have hc := congrArg
      (fun D : PeriodicSobolev (7 / 2 : ℝ) ↦ D.1 (0 : Fin 3) (0 : PeriodicFrequency)) h
    change (2 : ℂ) = 0 at hc
    exact two_ne_zero hc

/-! ## 4. The two instances are compatible: order transport from 3 to 7/2 -/

example (c d : NavierStokes.ProblemStatement.Space) :
    IsPeriodicReweight ((3 : ℝ) - 1) ((7 / 2 : ℝ) - 1)
      (torusConvolutionCLM_real 3 le_rfl (torusConstantDatum 3 c) (torusConstantDatum 3 d))
      (torusConvolutionCLM_real (7 / 2 : ℝ) (by norm_num)
        (torusConstantDatum (7 / 2 : ℝ) c) (torusConstantDatum (7 / 2 : ℝ) d)) :=
  torusConvolutionCLM_real_reweight 3 (7 / 2 : ℝ) le_rfl (by norm_num)
    (persistence_reweight_of_data (torusConstantDatum_isDatum 3 c)
      (torusConstantDatum_isDatum (7 / 2 : ℝ) c))
    (persistence_reweight_of_data (torusConstantDatum_isDatum 3 d)
      (torusConstantDatum_isDatum (7 / 2 : ℝ) d))
