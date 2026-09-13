import Mathlib
import Formal.TerminalFlowMapAmplification

namespace MNS2

open Set
open scoped Interval ContDiff

noncomputable section

section TerminalFlowMapOperatorNorm

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
variable {NSEvolvesAt : ℝ → V → V → Prop}

/--
For a nonzero radial datum, terminal-tail directional amplification forces the operator norm of the
Fréchet derivative itself to become arbitrarily large on every terminal tail.

This is the operator-norm form closest to the intended continuum condition-number criterion:

`∀ t₀ < T, ∀ N ≥ 0, ∃ t ∈ (t₀,T), ∃ a ∈ [0,1], N < ‖D(stateMap t)(a • d)‖`.

The only extra hypothesis beyond `terminal_directional_fderiv_unbounded_of_nonextendible` is
`d ≠ 0`, used to divide the standard estimate

`‖DΦ[d]‖ ≤ ‖DΦ‖ ‖d‖`

by the positive number `‖d‖`.
-/
theorem FlowMapUniformRestartPackage.terminal_fderiv_opNorm_unbounded_of_nonextendible
    {A : NavierStokesTimeBridgeAdapter V V NSEvolvesAt}
    {T : ℝ} {d : V} {CanExtend : Prop}
    (C : FlowMapUniformRestartPackage A T d CanExtend)
    (hnotExtend : ¬ CanExtend)
    (hd : d ≠ 0) :
    ∀ t₀ : ℝ, 0 ≤ t₀ → t₀ < T →
      ∀ N : ℝ, 0 ≤ N →
        ∃ t : ℝ, t₀ < t ∧ t < T ∧
          ∃ a : ℝ, a ∈ uIcc (0 : ℝ) 1 ∧
            N < ‖fderiv ℝ (A.stateMap t) (a • d)‖ := by
  intro t₀ ht₀0 ht₀T N hN
  have hdNorm : 0 < ‖d‖ := norm_pos_iff.mpr hd
  have hM : 0 ≤ N * ‖d‖ := mul_nonneg hN (norm_nonneg d)
  rcases C.terminal_directional_fderiv_unbounded_of_nonextendible hnotExtend
      t₀ ht₀0 ht₀T (N * ‖d‖) hM with
    ⟨t, ht₀t, htT, a, ha, hamp⟩
  let L : V →L[ℝ] V := fderiv ℝ (A.stateMap t) (a • d)
  have happly : ‖L d‖ ≤ ‖L‖ * ‖d‖ := L.le_opNorm d
  have hprod : N * ‖d‖ < ‖L‖ * ‖d‖ := hamp.trans_le happly
  have hop : N < ‖L‖ := by
    by_contra hnot
    have hle : ‖L‖ ≤ N := le_of_not_gt hnot
    have hmul : ‖L‖ * ‖d‖ ≤ N * ‖d‖ :=
      mul_le_mul_of_nonneg_right hle (norm_nonneg d)
    exact (not_lt_of_ge hmul) hprod
  exact ⟨t, ht₀t, htT, a, ha, by simpa [L] using hop⟩

/--
Compact single-tail wrapper for later filter/`limsup` formulations.
-/
theorem FlowMapUniformRestartPackage.exists_terminal_fderiv_opNorm_above
    {A : NavierStokesTimeBridgeAdapter V V NSEvolvesAt}
    {T : ℝ} {d : V} {CanExtend : Prop}
    (C : FlowMapUniformRestartPackage A T d CanExtend)
    (hnotExtend : ¬ CanExtend)
    (hd : d ≠ 0)
    {t₀ N : ℝ} (ht₀0 : 0 ≤ t₀) (ht₀T : t₀ < T) (hN : 0 ≤ N) :
    ∃ t : ℝ, t₀ < t ∧ t < T ∧
      ∃ a : ℝ, a ∈ uIcc (0 : ℝ) 1 ∧
        N < ‖fderiv ℝ (A.stateMap t) (a • d)‖ := by
  exact C.terminal_fderiv_opNorm_unbounded_of_nonextendible hnotExtend hd
    t₀ ht₀0 ht₀T N hN

end TerminalFlowMapOperatorNorm

end

end MNS2
