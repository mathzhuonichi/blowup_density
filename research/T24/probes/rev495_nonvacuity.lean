import NSFormalization.Section3.T24.ConservativeOmega

noncomputable section
namespace NSFormalization.Section3.T24.ReviewerProbe

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T23
open NSFormalization.Section4.A02 (SpaceTimeScalar)
open scoped ContDiff

/-- The concrete unit box `(0,1)^3`. -/
def unitBox : Set Space :=
  {x : Space | ∀ i : Fin 3, (0 : ℝ) < x i ∧ x i < 1}

theorem unitBox_isBox : IsBoxDomain unitBox := by
  exact ⟨(fun _ ↦ 0), (fun _ ↦ 1), (fun _ ↦ zero_lt_one), rfl⟩

def unitBoxCenter : Space :=
  WithLp.toLp 2 (fun _ : Fin 3 ↦ (1 / 2 : ℝ))

theorem unitBox_domain : IsBoundedBoxOrSmoothDomain unitBox := by
  refine ⟨unitBox_isBox.open_bounded.1, unitBox_isBox.open_bounded.2, ?_, Or.inl unitBox_isBox⟩
  exact ⟨unitBoxCenter, by intro i; constructor <;> norm_num [unitBoxCenter]⟩

/-- A smooth potential with a genuinely nonzero spatial gradient. -/
def linearPotential : SpaceTimeScalar := fun z ↦ z.2 0

theorem linearPotential_contDiff : ContDiff ℝ ∞ linearPotential := by
  exact (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd

theorem linearPotential_nonzero : linearPotential ≠ 0 := by
  intro h
  have hz := congrFun h ((0 : ℝ), coordinateVector 0)
  simp [linearPotential, coordinateVector] at hz

/-- The zero-potential instance is inhabited on the unit box. -/
def zeroPotentialRest :
    ClassicalSolutionOmega 1 unitBox 0 (conservativeForceOmega 0) 1 :=
  restSolutionOmega 1 unitBox unitBox_domain 0 contDiff_const 1 one_pos

/-- A nonzero-potential instance is inhabited on the same unit box. -/
def linearPotentialRest :
    ClassicalSolutionOmega 1 unitBox 0 (conservativeForceOmega linearPotential) 1 :=
  restSolutionOmega 1 unitBox unitBox_domain linearPotential linearPotential_contDiff 1 one_pos

example : Nonempty (ClassicalSolutionOmega 1 unitBox 0 (conservativeForceOmega 0) 1) :=
  ⟨zeroPotentialRest⟩

example :
    Nonempty (ClassicalSolutionOmega 1 unitBox 0
      (conservativeForceOmega linearPotential) 1) :=
  ⟨linearPotentialRest⟩

/-- The pairing theorem has a concrete application at the nonzero potential. -/
example (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
    (∫ x in unitBox,
      inner ℝ (conservativeForceOmega linearPotential (t, x))
        (linearPotentialRest.velocity (t, x))) = 0 :=
  potential_pairingOmega 1 1 one_pos unitBox unitBox_domain linearPotential
    linearPotential_contDiff linearPotentialRest t ht

end NSFormalization.Section3.T24.ReviewerProbe
