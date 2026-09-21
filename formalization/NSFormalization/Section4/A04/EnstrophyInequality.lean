import NSFormalization.Section4.C01.EnstrophyIdentityRaw

/-!
# P21 Route B, B1: inhomogeneous differentiated energy on R³

The revised article, `paper/revised/sections/02-preliminaries.tex:149–156`, says:
“For each initial velocity in the stated class and each force smooth into
 every H^m on compact time intervals ... a unique maximal smooth velocity” and
“[if] ∫₀ˢ ‖u(t)‖²_H² dt < ∞, then it extends smoothly beyond S”.
This module develops the general energy estimate for the separate H¹-uniform
restart obligation, not a newly displayed clause of that proposition.

`C01.enstrophyIdentity_gradientSq` differentiates only ∫|∇u|². Adding
`C01.energyIdentity_l2Sq` retains the L² energy, gradient dissipation and
ordinary force work. Identification with the registered Fourier norm is a B0
bridge, not implicit in the physical identity below.
-/

noncomputable section
open Set MeasureTheory
open NSFormalization.Section4.C01
namespace NSFormalization.Section4.A04

/-- Exact inhomogeneous physical H¹ energy identity, without smallness. -/
theorem inhomogeneousEnergyIdentity
    {ν T : ℝ} {a : A02.SpatialField} {f : A02.SpaceTimeField}
    (w : A02.ClassicalSolutionR ν a f T) (hf : A02.MemForceR f)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun s => l2Sq (slice w.velocity s) + gradientSq (slice w.velocity s))
      (-2 * ν * (gradientSq (slice w.velocity t) + laplacianSq (slice w.velocity t)) +
        2 * advectionWork (slice w.velocity t) +
        2 * pairing (slice w.velocity t) (slice f t) -
        2 * pairing (slice f t) (A05.lap (slice w.velocity t))) t := by
  have h := (energyIdentity_l2Sq w hf ht).add (enstrophyIdentity_gradientSq w hf ht)
  convert h using 1 <;> first | rfl | (simp only [gradientSq]; ring)

end NSFormalization.Section4.A04
