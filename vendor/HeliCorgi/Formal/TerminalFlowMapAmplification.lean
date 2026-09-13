import Mathlib
import Formal.UniformRestartContinuation

namespace MNS2

open Set
open scoped Interval ContDiff

noncomputable section

section TerminalFlowMapAmplification

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
variable {NSEvolvesAt : ℝ → V → V → Prop}

/--
Under a norm-controlled positive restart lifespan, finite-time nonextendibility forces directional
flow-map amplification on every terminal tail, not merely somewhere before the terminal time.

For every `t₀ < T` and every finite bound `M ≥ 0`, there is a later certified time `t ∈ (t₀,T)`
and a point `a • d` on the radial data segment for which

`M < ‖D(stateMap t)(a • d)[d]‖`.

The proof is the terminal restart argument localized to the tail.  If the directional derivative
were bounded by `M` throughout `(t₀,T)`, the exact radial bridge would bound the endpoint state by
`M` there.  Choosing `t` sufficiently close to `T` relative to the positive lifespan `lifespan M`
would then restart the solution past `T`, contradicting nonextendibility.
-/
theorem FlowMapUniformRestartPackage.terminal_directional_fderiv_unbounded_of_nonextendible
    {A : NavierStokesTimeBridgeAdapter V V NSEvolvesAt}
    {T : ℝ} {d : V} {CanExtend : Prop}
    (C : FlowMapUniformRestartPackage A T d CanExtend)
    (hnotExtend : ¬ CanExtend) :
    ∀ t₀ : ℝ, 0 ≤ t₀ → t₀ < T →
      ∀ M : ℝ, 0 ≤ M →
        ∃ t : ℝ, t₀ < t ∧ t < T ∧
          ∃ a : ℝ, a ∈ uIcc (0 : ℝ) 1 ∧
            M < ‖(fderiv ℝ (A.stateMap t) (a • d)) d‖ := by
  intro t₀ ht₀0 ht₀T M hM
  by_contra hlarge
  have hτ : 0 < C.lifespan M := C.lifespan_pos M hM
  let ε : ℝ := min ((T - t₀) / 2) (C.lifespan M / 2)
  let t : ℝ := T - ε
  have hgap2 : 0 < (T - t₀) / 2 := by
    linarith
  have hτ2 : 0 < C.lifespan M / 2 := by
    linarith
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min hgap2 hτ2
  have hεgap : ε ≤ (T - t₀) / 2 := by
    dsimp [ε]
    exact min_le_left _ _
  have hετ : ε ≤ C.lifespan M / 2 := by
    dsimp [ε]
    exact min_le_right _ _
  have ht₀ : t₀ < t := by
    dsimp [t]
    linarith
  have htT : t < T := by
    dsimp [t]
    linarith
  have ht0 : 0 ≤ t := ht₀0.trans (le_of_lt ht₀)
  have hpast : T < t + C.lifespan M := by
    dsimp [t]
    linarith
  have hdir :
      ∀ a : ℝ, a ∈ uIcc (0 : ℝ) 1 →
        ‖(fderiv ℝ (A.stateMap t) (a • d)) d‖ ≤ M := by
    intro a ha
    exact le_of_not_gt fun hgt =>
      hlarge ⟨t, ht₀, htT, a, ha, hgt⟩
  have hstate : ‖A.stateMap t d‖ ≤ M :=
    C.toContinuationPackage.endpoint_norm_le_of_radial_directional_bound
      ht0 htT hdir
  have hext : CanExtend :=
    C.restart_past_terminal M hM t ht0 htT hstate hpast
  exact hnotExtend hext

/--
A quantified tail form convenient for later conversion to filter/limsup language: every
pre-terminal neighborhood contains a point with directional amplification above every prescribed
finite threshold.
-/
theorem FlowMapUniformRestartPackage.eventually_arbitrarily_large_directional_fderiv
    {A : NavierStokesTimeBridgeAdapter V V NSEvolvesAt}
    {T : ℝ} {d : V} {CanExtend : Prop}
    (C : FlowMapUniformRestartPackage A T d CanExtend)
    (hnotExtend : ¬ CanExtend)
    {t₀ M : ℝ} (ht₀0 : 0 ≤ t₀) (ht₀T : t₀ < T) (hM : 0 ≤ M) :
    ∃ t : ℝ, t₀ < t ∧ t < T ∧
      ∃ a : ℝ, a ∈ uIcc (0 : ℝ) 1 ∧
        M < ‖(fderiv ℝ (A.stateMap t) (a • d)) d‖ := by
  exact C.terminal_directional_fderiv_unbounded_of_nonextendible hnotExtend
    t₀ ht₀0 ht₀T M hM

end TerminalFlowMapAmplification

end

end MNS2
