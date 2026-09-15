import NSFormalization.Section4.C01.EnergyDerivative
import NSFormalization.Section4.C01.ForceSlices
import NSFormalization.Section4.C01.Vocabulary

/-! Reviewer gap probe for lane 150: how far is `energyIdentity_classical_unconditional`
from the spec field `research/C01/Spec.lean:344` `energyIdentity`?

The spec asserts `HasDerivAt (fun s => l2Sq (slice w.velocity s)) (…) t`.  The lane's
theorem asserts `HasDerivAt (fun s => ‖(velocityField … (projIcc … s)).toLp‖ ^ 2) (…) t`.
This probe closes the LHS gap inside `formalization/` (it needs `norm_toLp_sq_eq_l2Sq`,
which is NOT `rfl`, plus the `projIcc` locality) and shows that the `pairing` side and the
raw gradient integrand are already `rfl`-shaped in the spec's vocabulary. -/

noncomputable section

open Set MeasureTheory Filter Topology
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev
open NavierStokes.ProblemStatement
open scoped RealInnerProductSpace ContDiff

namespace NSFormalization.Section4.C01

open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)

variable {ν : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField} {T : ℝ}

/-- The spec's LHS function, the spec's `pairing` integrand, and the raw gradient
integrand spelled with `coordinateVector` (the `Contracts.V1` spelling). -/
theorem rev150_energyIdentity_l2Sq (w : ClassicalSolutionR ν a f T) (hf : MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun s : ℝ => l2Sq (slice w.velocity s))
      (-2 * ν * (∫ x, ∑ i : Fin 3,
            ‖fderiv ℝ (slice w.velocity t) x (coordinateVector i)‖ ^ 2)
          + 2 * (∫ x, (inner ℝ (slice w.velocity t x) (slice f t x) : ℝ))) t := by
  have h := energyIdentity_classical_unconditional w hf ht
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds
      (show t ∈ Ioo (0 : ℝ) ((t + T) / 2) from ⟨ht.1, by linarith [ht.2]⟩)] with s hs
  have hsS : s ∈ Icc (0 : ℝ) ((t + T) / 2) := ⟨hs.1.le, hs.2.le⟩
  have hnn : (0 : ℝ) ≤ (t + T) / 2 := by linarith [ht.1, ht.2]
  rw [projIcc_of_mem hnn hsS]
  exact (norm_toLp_sq_eq_l2Sq
    (velocityField w (show (t + T) / 2 < T by linarith [ht.2]) ⟨s, hsS⟩)).symm

end NSFormalization.Section4.C01
