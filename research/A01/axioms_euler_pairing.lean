import NSFormalization.Section4.A01.EulerPairing
import Euler.MeanSmoothRepresentative

open NSFormalization.Section4.A01
open MeasureTheory NavierStokes.ProblemStatement
open scoped LineDeriv SchwartzMap

-- All exported declarations depend only on the standard three axioms.
#print axioms complexComponentCLM
#print axioms coeFn_complexComponentCLM
#print axioms weakDeriv_pairing_of_translation_hasDerivAt
#print axioms hasDerivAt_meanTranslation_of_lift
#print axioms weakDeriv_pairing_of_lift_hasDerivAt
#print axioms exists_descend
#print axioms hasWeakDerivsL2_of_word
#print axioms hasWeakDerivsL2_of_cylinder
#print axioms exists_isSobolevDatum_m_of_cylinder
#print axioms exists_isSobolevDatum_m_ordinaryL2
#print axioms exists_isSobolevDatum_m_of_ae

/-- Non-vacuity of E2: its strong-`L²`-translation-derivative hypothesis is inhabited.  Any field with
a smooth `L²` translation orbit (`EulerMeanSmoothRepresentative.SmoothOrbit`, e.g. the smooth
representatives the cylinder theory produces) has `orbitDerivative z eⱼ` as the strong derivative
(`orbitDerivative_hasDerivAt`), so E2 fires and delivers the Schwartz pairing — the conclusion is not
about an empty hypothesis class. -/
theorem euler_pairing_nonvacuous
    (z : EulerMeanSolenoidal.L2) (hz : EulerMeanSmoothRepresentative.SmoothOrbit z)
    (j i : Fin 3) (ψ : SchwartzMap Space ℂ) :
    ∫ x, ψ x * ((EulerMeanSmoothRepresentative.orbitDerivative z (coordinateVector j) x i : ℝ) : ℂ)
      = ∫ x, (-∂_{coordinateVector j} ψ) x * ((z x i : ℝ) : ℂ) :=
  weakDeriv_pairing_of_translation_hasDerivAt j
    (EulerMeanSmoothRepresentative.orbitDerivative_hasDerivAt z hz (coordinateVector j)) i ψ

#print axioms euler_pairing_nonvacuous
