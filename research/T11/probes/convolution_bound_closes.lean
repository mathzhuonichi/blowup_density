import NSFormalization.Section3.T11.ConvolutionBound

noncomputable section
open NSFormalization.Section3.T10 NSFormalization.Section3.T11

local instance convolutionProbeNormedGroup (s : ℝ) : NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance convolutionProbeNormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

-- Lane 313's target, copied verbatim after unfolding the named proposition.
example :
  ∃ Q : PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 3 →L[ℝ] PeriodicSobolev 2,
    ∀ A B i k, (Q A B).1 i k = torusProjectedConvectionSymbol A B i k :=
  torusConvolutionInput

example : TorusConvolutionInput := torusConvolutionInput

example (ν : ℝ) (hν : 0 < ν) :
    Nonempty (TorusTwoSpaceContract ν) :=
  torusTwoSpaceContract_nonempty' ν hν

example : Nonempty (TorusTwoSpaceContract 1) :=
  torusTwoSpaceContract_nonempty' 1 zero_lt_one

-- The realization and its bound use the same explicitly constructed map.
example (A B : PeriodicSobolev 3) (i : Fin 3) (k : PeriodicFrequency) :
    (torusConvolutionCLM A B).1 i k = torusProjectedConvectionSymbol A B i k :=
  torusConvolutionCLM_coeff A B i k

example : ‖torusConvolutionCLM‖ ≤ torusConvolutionConstant := torusConvolutionCLM_norm_le

-- Nonzero datum and force modes, without any residual input hypothesis.
example : ∃ A B : PeriodicSobolev 3,
    A ≠ 0 ∧ B ≠ 0 ∧ torusConvolutionCLM A B = 0 := by
  let c : NavierStokes.ProblemStatement.Space := WithLp.toLp 2 (fun _ ↦ 1)
  let A := torusConstantDatum 3 c
  have hA : A ≠ 0 := by
    intro h
    have hc := congrArg (fun D : PeriodicSobolev 3 ↦ D.1 (0 : Fin 3) (0 : PeriodicFrequency)) h
    change (1 : ℂ) = 0 at hc
    exact one_ne_zero hc
  exact ⟨A, A, hA, hA, torusConvolutionCLM_constants c c⟩
