import NSFormalization.Source.ViscosityPacket

/-!
# The constant `M` of Lemma 2.2 as a least upper bound

`paper/sections/02-preliminaries.tex:130` names
`M := sup_{0≤t<1} ‖U(t)‖_{L²(R³)}` and asserts it is finite.  The source only
provides *an* upper bound, and for the kinetic energy `½∫‖u‖²` rather than the
`L²` norm: `NavierStokesR3.ProblemStatement.UniformFiniteEnergy`,
`vendor/NavierStokesAndEuler/NavierStokes/R3/ProblemStatement.lean:81-83`.  The
supremum itself is produced here, because `eq:packetEscale`,
`paper/sections/03-torus.tex:125-126`, asserts an equality
`‖U_ε‖_{L^∞(0,T;L²)} = ε^{1/2}M` that a mere upper bound cannot supply.
-/

noncomputable section

namespace NSFormalization.Section4.I01

open Set
open NavierStokes.ProblemStatement
open NavierStokesR3.CompactEnergy (l2Sq)
open NavierStokesR3.ProblemStatement (UniformFiniteEnergy kineticEnergy)

/-- The presingular `L²` norms of a uniformly finite-energy velocity have a
least upper bound.  Nonemptiness comes from `0 ∈ [0,1)`; the bound is
`√(2E)` for any kinetic-energy bound `E`. -/
theorem exists_l2_isLUB {u : VelocityField}
    (hE : UniformFiniteEnergy (Ico (0 : ℝ) 1) u) :
    ∃ M : ℝ, IsLUB ((fun t : ℝ => Real.sqrt (l2Sq u t)) '' Ico (0 : ℝ) 1) M := by
  obtain ⟨E, _, hb⟩ := hE
  refine Real.exists_isLUB ⟨Real.sqrt (l2Sq u 0), ⟨0, ⟨le_refl 0, by norm_num⟩, rfl⟩⟩ ?_
  refine ⟨Real.sqrt (2 * E), ?_⟩
  rintro y ⟨t, ht, rfl⟩
  refine Real.sqrt_le_sqrt ?_
  have hk := (hb t ht).2
  unfold kineticEnergy at hk
  unfold l2Sq
  linarith

end NSFormalization.Section4.I01
