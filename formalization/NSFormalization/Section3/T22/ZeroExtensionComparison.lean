import NSFormalization.Section3.T22.RestrictBridge
import NSFormalization.Section3.T22.ZeroExtRegularity
import NSFormalization.Section3.T22.CutoffDatum
import NSFormalization.Section3.T22.CutoffMultiplierField

/-!
# T22 U-Z1 — comparison with the literal zero extension

The left inequality is the restriction bridge from U-B1.  For the right
inequality, a smooth cutoff equal to one near the compact support of the zero
extension turns every admissible domain datum into a whole-space datum of that
zero extension; the remaining step is `ENNReal` infimum bookkeeping.
-/

noncomputable section

namespace NSFormalization.Section3.T22

open Set MeasureTheory Filter
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (SpatialField)
open scoped ContDiff ENNReal Topology

/-- **U-Z1.** The two-sided bounded-domain/zero-extension comparison, verbatim
the `BoundedDomainNormAPI.zeroExtensionComparison` field. -/
theorem zeroExtensionComparison :
    ∀ (Ω K : Set Space), IsOpen Ω → IsCompact K → K ⊆ Ω →
      ∀ s : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ z : SpatialField,
        ContDiffOn ℝ ∞ z Ω → tsupport (zeroExtension Ω z) ⊆ K →
        domainSobolevENorm Ω s (restrictField Ω z) ≤
            sobolevENorm s (zeroExtension Ω z) ∧
        sobolevENorm s (zeroExtension Ω z) ≤
            ENNReal.ofReal C * domainSobolevENorm Ω s (restrictField Ω z) := by
  intro Ω K hΩ hK hKΩ s
  obtain ⟨χ, hχs, hχc, hχΩ, hχ1⟩ := exists_cutoff hΩ hK hKΩ
  obtain ⟨C, hCpos, hCbound⟩ := cutoffMultiplier s χ hχs hχc
  refine ⟨C, hCpos, ?_⟩
  intro z hz hsupp
  constructor
  · exact domainSobolevENorm_le_sobolevENorm
  · have hpoint : ∀ A : {A : RealVectorSobolev s //
        restrictDatum Ω s A = restrictField Ω z},
        sobolevENorm s (zeroExtension Ω z) ≤ ENNReal.ofReal C * ‖A.1‖ₑ := by
      intro A
      obtain ⟨B, hcut, hBnorm⟩ := hCbound A.1
      have hBdatum : IsSobolevDatum s (zeroExtension Ω z) B :=
        isCutoffDatum_realizes_zeroExtension hχs hχc hχΩ hχ1 hcut A.2 hsupp
      exact (sobolevENorm_le_of_isSobolevDatum hBdatum).trans hBnorm
    by_cases hne : Nonempty {A : RealVectorSobolev s //
        restrictDatum Ω s A = restrictField Ω z}
    · have := hne
      rw [domainSobolevENorm, ENNReal.mul_iInf
        (fun h => absurd h ENNReal.ofReal_ne_top)]
      exact le_iInf hpoint
    · have : IsEmpty {A : RealVectorSobolev s //
        restrictDatum Ω s A = restrictField Ω z} := not_nonempty_iff.mp hne
      rw [domainSobolevENorm, iInf_of_empty,
        ENNReal.mul_top (by simpa using hCpos)]
      exact le_top

end NSFormalization.Section3.T22
