import NSFormalization.Section3.T21.Assembly
import NSFormalization.Section3.T21.Main
import NSFormalization.Section3.T20.Assembly

/-!
# T21 final assembly

This module closes the three reconciled assembly arrows and the two paper
statements using the canonical T19 and T20 inhabitants.  The chosen
non-density index is definitionally `criticalSmallnessH1`.
-/

noncomputable section

namespace NSFormalization.Section3.T21
set_option linter.defProp false

open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T19 (PeriodicDensityAPI periodicDensityAPI)
open NSFormalization.Section3.T20 (CriticalRegularityTAPI criticalRegularityT
  criticalSmallnessH1)
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)

/-- **`thm:main` in the paper's order, `03-torus.tex:6-16`.**  Clause (i)
followed by clause (ii)'s biconditional. -/
def mainStatement : Prop :=
  (∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ s : ℝ, s < 1 / 2 →
          RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)) ∧
    (∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ,
      RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T) ↔ s < 1 / 2)

/-- `03-torus.tex:523`: `thm:main` consumes exactly density and non-density. -/
def mainOfDensityAndNonDensity : Prop :=
  ∀ c : ℝ, PeriodicDensityAPI → NonDensityAPI c → MainTheoremAPI

/-- The two-input T19/T20 form of the final assembly. -/
def mainOfInputs : Prop :=
  PeriodicDensityAPI → CriticalRegularityTAPI → MainTheoremAPI

/-- The reconciled density/non-density arrow is inhabited.

The suffix distinguishes this arrow inhabitant from lane 474's already-landed
field-level helper `mainOfDensityAndNonDensity_holds`. -/
theorem mainOfDensityAndNonDensity_arrow_holds :
    mainOfDensityAndNonDensity :=
  fun _c D (N : NonDensityAPI _c) ↦
    mainOfDensityAndNonDensity_holds D N.nonDensity

/-- The canonical two-input arrow is inhabited. -/
theorem mainOfInputs_holds : mainOfInputs :=
  fun D K ↦ mainOfDensityAndNonDensity_holds D (nonDensityAPI K).nonDensity

/-- The closed nine-field non-density package, with the T20 constant exposed
as the canonical `criticalSmallnessH1`. -/
def closedNonDensityAPI : NonDensityAPI criticalSmallnessH1 :=
  nonDensityAPI criticalRegularityT

/-- The closed five-field main-theorem package. -/
def closedMainTheoremAPI : MainTheoremAPI :=
  mainTheoremAPI periodicDensityAPI closedNonDensityAPI.nonDensity

/-- Closed non-density record non-vacuity at the explicit canonical constant. -/
theorem nonemptyNonDensityAPI :
    Nonempty (NonDensityAPI criticalSmallnessH1) :=
  ⟨closedNonDensityAPI⟩

/-- Closed main-theorem record non-vacuity. -/
theorem nonemptyMainTheoremAPI : Nonempty MainTheoremAPI :=
  ⟨closedMainTheoremAPI⟩

/-- Witness-independent existence of a non-density package. -/
theorem exists_nonemptyNonDensityAPI :
    ∃ c : ℝ, Nonempty (NonDensityAPI c) :=
  ⟨criticalSmallnessH1, nonemptyNonDensityAPI⟩

/-- **`cor:nondensity`, `03-torus.tex:507-508`, unconditionally.** -/
theorem nonDensityStatement_unconditional : nonDensityStatement :=
  closedNonDensityAPI.nonDensity

/-- **`thm:main`, `03-torus.tex:6-16`, unconditionally.** -/
theorem mainStatement_holds : mainStatement :=
  ⟨closedMainTheoremAPI.fixedInitialDensity,
    closedMainTheoremAPI.zeroInitialDensityIff⟩

end NSFormalization.Section3.T21
