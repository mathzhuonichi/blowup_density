import NSFormalization.Section4.C01.EnergyBounds

/-! REVIEW PROBE (lane 154), mutation A: the constant `2` on the right-hand side of
`energyDifferentialBound` is weakened to `1`.  The proof is the original one verbatim,
with only the two occurrences of the literal `2` on the right-hand side changed.
Expected: `linarith` fails — the Cauchy-Schwarz factor is load-bearing. -/

noncomputable section

open Set MeasureTheory Filter Topology
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open NavierStokes.ProblemStatement
open NSFormalization.Paper3
open scoped RealInnerProductSpace ContDiff

namespace NSFormalization.Section4.C01

open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)

variable {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {T : ℝ}

theorem energyDifferentialBound_MUT_A (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (E' : ℝ)
    (hderiv : HasDerivAt (fun s => l2Sq (slice w.velocity s)) E' t) :
    E' + 2 * ν * gradientSq (slice w.velocity t)
      ≤ 1 * l2Norm (slice f t) * l2Norm (slice w.velocity t) := by
  have hid := energyIdentity_l2Sq w hf ht
  have hE' : E' = -2 * ν * gradientSq (slice w.velocity t)
      + 2 * pairing (slice w.velocity t) (slice f t) := hderiv.unique hid
  have hkey : E' + 2 * ν * gradientSq (slice w.velocity t)
      = 2 * pairing (slice w.velocity t) (slice f t) := by rw [hE']; ring
  rw [hkey]
  have hcs := pairing_le_l2Norm_mul w hf (Ioo_subset_Ico_self ht) (le_of_lt ht.1)
  have hassoc : 1 * l2Norm (slice f t) * l2Norm (slice w.velocity t)
      = 1 * (l2Norm (slice f t) * l2Norm (slice w.velocity t)) := by ring
  rw [hassoc]
  linarith [hcs]

end NSFormalization.Section4.C01
