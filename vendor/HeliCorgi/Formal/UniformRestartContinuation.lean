import Mathlib
import Formal.FlowMapNonextendibilityCriterion

namespace MNS2

open Set
open scoped Interval ContDiff

noncomputable section

section UniformRestartContinuation

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
variable {NSEvolvesAt : ℝ → V → V → Prop}

/--
A local-restart version of the continuation interface.

Instead of assuming directly that a uniform endpoint bound implies continuation, this package asks
for a positive restart lifespan depending only on the norm bound.  If a pre-terminal state with norm
at most `R` is restarted at a time `t` for which the guaranteed lifespan crosses `T`, then the
solution is declared extendible.

This is still an abstract interface: no Navier--Stokes local well-posedness theorem is manufactured
here.  A concrete strong-solution carrier must supply `lifespan`, `lifespan_pos`, and
`restart_past_terminal` from its genuine local theory.
-/
structure FlowMapUniformRestartPackage
    (A : NavierStokesTimeBridgeAdapter V V NSEvolvesAt)
    (T : ℝ) (d : V) (CanExtend : Prop) where
  terminalTime_pos : 0 < T
  certified_before :
    ∀ t : ℝ, 0 ≤ t → t < T → t ∈ A.certifiedTimes
  radial_path_admissible :
    ∀ t : ℝ, ∀ (ht0 : 0 ≤ t) (htT : t < T),
      MapsTo (fun a : ℝ => a • d) (uIcc (0 : ℝ) 1) (A.admissible t)
  zero_fixed_before :
    ∀ t : ℝ, ∀ (ht0 : 0 ≤ t) (htT : t < T),
      A.stateMap t 0 = 0
  lifespan : ℝ → ℝ
  lifespan_pos :
    ∀ R : ℝ, 0 ≤ R → 0 < lifespan R
  restart_past_terminal :
    ∀ R : ℝ, 0 ≤ R →
      ∀ t : ℝ, 0 ≤ t → t < T →
        ‖A.stateMap t d‖ ≤ R →
        T < t + lifespan R →
        CanExtend

/--
A norm-controlled positive restart lifespan implies the continuation field used by
`FlowMapContinuationPackage`.

The proof is the standard terminal-time restart argument: for a uniform bound `R`, let
`τ = lifespan R > 0`, choose a time `t = T - ε` with
`ε = min (T/2) (τ/2)`, and restart there.  Then `0 ≤ t < T` while `T < t + τ`.
-/
theorem FlowMapUniformRestartPackage.continuation_of_uniform_endpoint_bound
    {A : NavierStokesTimeBridgeAdapter V V NSEvolvesAt}
    {T : ℝ} {d : V} {CanExtend : Prop}
    (C : FlowMapUniformRestartPackage A T d CanExtend)
    (hbound :
      ∃ R : ℝ, 0 ≤ R ∧
        ∀ t : ℝ, 0 ≤ t → t < T → ‖A.stateMap t d‖ ≤ R) :
    CanExtend := by
  rcases hbound with ⟨R, hR, hstate⟩
  have hτ : 0 < C.lifespan R := C.lifespan_pos R hR
  let ε : ℝ := min (T / 2) (C.lifespan R / 2)
  let t : ℝ := T - ε
  have hT2 : 0 < T / 2 := by
    linarith [C.terminalTime_pos]
  have hτ2 : 0 < C.lifespan R / 2 := by
    linarith
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min hT2 hτ2
  have hεT : ε ≤ T / 2 := by
    dsimp [ε]
    exact min_le_left _ _
  have hετ : ε ≤ C.lifespan R / 2 := by
    dsimp [ε]
    exact min_le_right _ _
  have ht0 : 0 ≤ t := by
    dsimp [t]
    linarith
  have htT : t < T := by
    dsimp [t]
    linarith
  have hpast : T < t + C.lifespan R := by
    dsimp [t]
    linarith
  exact C.restart_past_terminal R hR t ht0 htT (hstate t ht0 htT) hpast

/--
Every uniform-restart package canonically supplies the earlier continuation package.

This isolates the genuine PDE obligation at the level of local well-posedness: prove a positive
lifespan controlled by the chosen strong norm and prove that restarting with that lifespan preserves
the same continuum solution semantics.
-/
def FlowMapUniformRestartPackage.toContinuationPackage
    {A : NavierStokesTimeBridgeAdapter V V NSEvolvesAt}
    {T : ℝ} {d : V} {CanExtend : Prop}
    (C : FlowMapUniformRestartPackage A T d CanExtend) :
    FlowMapContinuationPackage A T d CanExtend where
  terminalTime_pos := C.terminalTime_pos
  certified_before := C.certified_before
  radial_path_admissible := C.radial_path_admissible
  zero_fixed_before := C.zero_fixed_before
  continuation_of_uniform_endpoint_bound :=
    C.continuation_of_uniform_endpoint_bound

/--
Consequently, finite-time nonextendibility plus a norm-controlled local restart theorem forces
arbitrarily large directional flow-map amplification on the radial data segment.
-/
theorem FlowMapUniformRestartPackage.directional_fderiv_unbounded_of_nonextendible
    {A : NavierStokesTimeBridgeAdapter V V NSEvolvesAt}
    {T : ℝ} {d : V} {CanExtend : Prop}
    (C : FlowMapUniformRestartPackage A T d CanExtend)
    (hnotExtend : ¬ CanExtend) :
    ∀ M : ℝ, 0 ≤ M →
      ∃ t : ℝ, 0 ≤ t ∧ t < T ∧
        ∃ a : ℝ, a ∈ uIcc (0 : ℝ) 1 ∧
          M < ‖(fderiv ℝ (A.stateMap t) (a • d)) d‖ := by
  exact C.toContinuationPackage.directional_fderiv_unbounded_of_nonextendible hnotExtend

end UniformRestartContinuation

end

end MNS2
