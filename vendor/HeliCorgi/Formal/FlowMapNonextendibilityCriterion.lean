import Mathlib
import Formal.NavierStokesTimeBridge

namespace MNS2

open Set
open scoped Interval ContDiff

noncomputable section

section FlowMapNonextendibilityCriterion

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
variable {NSEvolvesAt : ℝ → V → V → Prop}

/--
An explicit continuation interface for turning the exact radial flow-map bridge into a
finite-time nonextendibility criterion.

The bridge itself supplies the exact identity

`∫ a in 0..1, D(stateMap t)(a • d)[d] = stateMap t d`

once zero is fixed and the radial segment is admissible.  The only genuinely PDE-specific
continuation input is `continuation_of_uniform_endpoint_bound`: a uniform bound on the selected
continuum state up to the terminal time forces extendibility beyond that time.

This structure deliberately does *not* assert that any concrete Navier--Stokes function space
satisfies the continuation field.  Instantiating that field in a classical/strong solution space
is a later analytic obligation.
-/
structure FlowMapContinuationPackage
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
  continuation_of_uniform_endpoint_bound :
    (∃ R : ℝ, 0 ≤ R ∧
      ∀ t : ℝ, 0 ≤ t → t < T → ‖A.stateMap t d‖ ≤ R) →
      CanExtend

/--
At a certified pre-terminal time, a uniform bound on the directional flow-map derivative along
one radial data segment bounds the selected endpoint by the same constant.

The factor `|1 - 0|` is exactly one, so no extra geometric constant appears.
-/
theorem FlowMapContinuationPackage.endpoint_norm_le_of_radial_directional_bound
    {A : NavierStokesTimeBridgeAdapter V V NSEvolvesAt}
    {T : ℝ} {d : V} {CanExtend : Prop}
    (C : FlowMapContinuationPackage A T d CanExtend)
    {t M : ℝ} (ht0 : 0 ≤ t) (htT : t < T)
    (hbound :
      ∀ a : ℝ, a ∈ uIcc (0 : ℝ) 1 →
        ‖(fderiv ℝ (A.stateMap t) (a • d)) d‖ ≤ M) :
    ‖A.stateMap t d‖ ≤ M := by
  have ht : t ∈ A.certifiedTimes := C.certified_before t ht0 htT
  have hpath :
      MapsTo (fun a : ℝ => a • d) (uIcc (0 : ℝ) 1) (A.admissible t) :=
    C.radial_path_admissible t ht0 htT
  have hzero : A.stateMap t 0 = 0 := C.zero_fixed_before t ht0 htT
  have hbridge :=
    A.radial_bridge_at_time_of_zero_fixed t ht d hpath hzero
  rw [← hbridge]
  have hint :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun a : ℝ => (fderiv ℝ (A.stateMap t) (a • d)) d)
      (C := M)
      (a := (0 : ℝ)) (b := 1)
      (fun a ha => hbound a (Set.uIoc_subset_uIcc ha))
  simpa using hint

/--
Finite-time nonextendibility forces arbitrarily large directional flow-map amplification somewhere
on the radial data segment before the terminal time.

This is the contrapositive form needed for later continuum blow-up work:

`¬ CanExtend  →  ∀ M ≥ 0, ∃ t < T, ∃ a ∈ [0,1], M < ‖D(stateMap t)(a • d)[d]‖`.

No concrete Navier--Stokes continuation theorem is claimed here.  Such a theorem must instantiate
`continuation_of_uniform_endpoint_bound` in an appropriate strong-solution norm; in particular,
this file does not claim that the `L²(R³)` carrier alone supplies that property.
-/
theorem FlowMapContinuationPackage.directional_fderiv_unbounded_of_nonextendible
    {A : NavierStokesTimeBridgeAdapter V V NSEvolvesAt}
    {T : ℝ} {d : V} {CanExtend : Prop}
    (C : FlowMapContinuationPackage A T d CanExtend)
    (hnotExtend : ¬ CanExtend) :
    ∀ M : ℝ, 0 ≤ M →
      ∃ t : ℝ, 0 ≤ t ∧ t < T ∧
        ∃ a : ℝ, a ∈ uIcc (0 : ℝ) 1 ∧
          M < ‖(fderiv ℝ (A.stateMap t) (a • d)) d‖ := by
  intro M hM
  by_contra hlarge
  have hdir :
      ∀ t : ℝ, 0 ≤ t → t < T →
        ∀ a : ℝ, a ∈ uIcc (0 : ℝ) 1 →
          ‖(fderiv ℝ (A.stateMap t) (a • d)) d‖ ≤ M := by
    intro t ht0 htT a ha
    exact le_of_not_gt fun hgt =>
      hlarge ⟨t, ht0, htT, a, ha, hgt⟩
  have hstate :
      ∀ t : ℝ, 0 ≤ t → t < T → ‖A.stateMap t d‖ ≤ M := by
    intro t ht0 htT
    exact C.endpoint_norm_le_of_radial_directional_bound ht0 htT (hdir t ht0 htT)
  have hext : CanExtend :=
    C.continuation_of_uniform_endpoint_bound ⟨M, hM, hstate⟩
  exact hnotExtend hext

end FlowMapNonextendibilityCriterion

end

end MNS2
