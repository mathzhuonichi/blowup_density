import NSFormalization.Section3.T24.MultipleOmegaAssembled

/-! Deliberate mutation of the P5.2 momentum/solution dependency: this input
interface retains the component support statements but deletes
`regions_disjoint`. The production proof must fail when it tries to establish
component non-overlap, before `crossTransport_eq_zero`, `assembled_advection`,
`assembled_momentum`, and `solution` can be constructed. -/
noncomputable section

namespace Rev497DropRegionsDisjoint

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpaceTimeField)

structure MomentumInputsWithoutDisjoint where
  T : ℝ
  N : ℕ
  regionCenter : Fin N → Space
  regionRadius : Fin N → ℝ
  component : Fin N → SpaceTimeField
  component_support : ∀ j : Fin N, ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
    x ∉ Metric.ball (regionCenter j) (regionRadius j) → component j (t, x) = 0

/-- The original P5.2 non-overlap proof with `regions_disjoint` deleted. The
final line intentionally passes index inequality where disjoint balls are
required, exhibiting the load-bearing missing hypothesis. -/
example (d : MomentumInputsWithoutDisjoint) {i j : Fin d.N} (hij : i ≠ j)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) d.T) (x : Space)
    (hi : d.component i (t, x) ≠ 0) : d.component j (t, x) = 0 := by
  have hiB : x ∈ Metric.ball (d.regionCenter i) (d.regionRadius i) := by
    by_contra hout
    exact hi (d.component_support i t ht x hout)
  apply d.component_support j t ht x
  exact fun hjB ↦ Set.disjoint_left.mp hij hiB hjB

end Rev497DropRegionsDisjoint
