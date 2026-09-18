import NSFormalization.Section3.T11.EnergyIdentity

noncomputable section

namespace NSFormalization.Section3.T11.Review335Mutation

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField SpaceTimeScalar)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ContDiff ENNReal BigOperators ComplexConjugate

local instance reviewMutationNormedGroup (s : ℝ) : NormedAddCommGroup (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedAddCommGroup
local instance reviewMutationNormedSpace (s : ℝ) : NormedSpace ℝ (PeriodicSobolev s) :=
  realPeriodicSubmodule.normedSpace

/- This deliberately flips the diffusion sign in the main energy statement.
   The proof should fail by a conclusion mismatch, not by dropping a premise. -/
example {ν T : ℝ} {a : SpatialField} {f : SpaceTimeField}
    (w : ClassicalSolutionT ν a f T) (hf : ContDiff ℝ ∞ f) (m : ℕ) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T) {Gm Fm Nm : PeriodicSobolev (m : ℝ)}
    (hGm : IsPeriodicDatum (m : ℝ) (fun x ↦ w.velocity (t, x)) Gm)
    (hFm : IsPeriodicDatum (m : ℝ) (fun x ↦ f (t, x)) Fm)
    (hNm : IsPeriodicDatum (m : ℝ) (fun x ↦ convectionFieldT w.velocity (t, x)) Nm) :
    HasDerivAt (fun r ↦ torusSobolevNormAt (m : ℝ) w.velocity r ^ 2)
      (2 * ν * torusGradientNormAt (m : ℝ) w.velocity t ^ 2 +
        2 * torusRealPairing Gm Fm - 2 * torusRealPairing Gm Nm) t := by
  exact energyIdentity_of_classical w hf m ht hGm hFm hNm

end NSFormalization.Section3.T11.Review335Mutation
