import NSFormalization.Source.BesselFractionalData
import NSFormalization.Source.RieszL2Fourier
import NSFormalization.Source.RieszPotentialLp

noncomputable section
namespace NSFormalization.Source.FractionalRepresentative
open MeasureTheory FourierTransform
open NSFormalization.Paper3
open NSFormalization.Source.BesselFractionalData
open NSFormalization.RieszPotentialLp NSFormalization.RieszComplexPotential
open scoped ENNReal SchwartzMap
abbrev Space := NSFormalization.RieszComplexPotential.Space

/-- Critical `L^p` representative attached to complete Sobolev data. -/
def representative {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    (h : SobolevHilbert a) : Space → ℂ :=
  complexPotential a (datum a ha.le h : Space → ℂ)

theorem representative_memLp {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    (h : SobolevHilbert a) :
    MemLp (representative ha ha3 h) (ENNReal.ofReal (targetExponent a)) volume := by
  refine ⟨(measurable_complexPotential_of_memLp a (Lp.memLp (datum a ha.le h))).aestronglyMeasurable, ?_⟩
  exact lt_of_le_of_lt (eLpNorm_complexPotential_le ha ha3 (Lp.memLp (datum a ha.le h))) ENNReal.ofReal_lt_top

 theorem representative_norm_bound {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    (h : SobolevHilbert a) :
    eLpNorm (representative ha ha3 h) (ENNReal.ofReal (targetExponent a)) volume ≤
      ENNReal.ofReal (potentialConstant a * (512:ℝ)^(1/targetExponent a) * (eLpNorm (datum a ha.le h) 2 volume).toReal) := by
  simpa [representative, eLpNorm_norm] using
    (eLpNorm_complexPotential_le ha ha3 (Lp.memLp (datum a ha.le h)))

 theorem multiplier_identity {a : ℝ} (ha : 0 < a) (ha3 : a < 3/2)
    (h : SobolevHilbert a) :
    NSFormalization.RieszSingularMultiplier.multiplier a ha.le ha3 (datum a ha.le h) =
      𝓕 (sobolevRealization a h) :=
  BesselFractionalData.multiplier_datum a ha.le ha3 h

end NSFormalization.Source.FractionalRepresentative
