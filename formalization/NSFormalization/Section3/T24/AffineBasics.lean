import NSFormalization.Section3.T14.PacketEnergy

/-!
# T24a Ua1: affine geometry and kinematics

This is the canonical raw-field layer for the elementary fields of
`research/T24/Spec.lean`.  The packet structure is deliberately not imported:
the fields below take the physical velocity/pressure/force fields directly,
and the packet clauses used by a proof are ordinary hypotheses.  The analytic
force, energy, and non-isolation fields belong to later T24a units.
-/

noncomputable section

namespace NSFormalization.Section3.T24

open Set MeasureTheory
open NavierStokes.ProblemStatement
open scoped ContDiff ENNReal BigOperators

/-- `03-torus.tex:668-671`: the open cylinder supporting an affine variation. -/
def affineCylinder (c : Space) (r τ₀ τ₁ : ℝ) : Set SpaceTime :=
  Ioo τ₀ τ₁ ×ˢ Metric.ball c r

/-- `03-torus.tex:672-673`: smooth compactly supported solenoidal variations. -/
def AffineAdmissible (c : Space) (r τ₀ τ₁ : ℝ) (b : VelocityField) : Prop :=
  ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
    tsupport b ⊆ affineCylinder c r τ₀ τ₁ ∧
    (∀ t : ℝ, ∀ x : Space, spatialDivergence b t x = 0)

/-- `eq:affine`, `03-torus.tex:674`: `Ũ = U+b`. -/
def affineVelocity (U b : VelocityField) : VelocityField :=
  fun z ↦ U z + b z

/-- `eq:affine`, `03-torus.tex:674`: `P̃ = P`. -/
def affinePressure (P : PressureField) : PressureField := P

/-- The transport term `(v·∇)w` in the affine expansion. -/
def crossAdvection (v w : VelocityField) (t : ℝ) (x : Space) : Space :=
  spatialDerivative w t x (v (t, x))

/-- `eq:affine`, `03-torus.tex:674-676`: the corrected affine force. -/
def affineForce (ν : ℝ) (U F b : VelocityField) : VelocityField :=
  fun z ↦ F z + temporalDerivative b z.1 z.2 - ν • spatialLaplacian b z.1 z.2 +
    crossAdvection U b z.1 z.2 + crossAdvection b U z.1 z.2 +
    crossAdvection b b z.1 z.2

/-- The extended-real fixed-support `C^m` seminorm used by the later
non-isolation field. -/
def affineCkSeminorm (K : Set SpaceTime) (m : ℕ) (f : VelocityField) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range (m + 1), ⨆ z ∈ K, ‖iteratedFDeriv ℝ k f z‖ₑ

/-- Ua1 `radius_pos` (`Spec.lean:1014`). -/
theorem radius_pos {r : ℝ} (hr : 0 < r) : 0 < r := hr

/-- Ua1 `window` (`Spec.lean:1019`), with the parameter hypotheses from
`affineVariationStatement` supplied explicitly. -/
theorem window {τ₀ τ₁ : ℝ} (hτ₀ : 0 < τ₀) (hτ₀τ₁ : τ₀ < τ₁)
    (hτ₁ : τ₁ < 1) : 0 < τ₀ ∧ τ₀ < τ₁ ∧ τ₁ < 1 :=
  ⟨hτ₀, hτ₀τ₁, hτ₁⟩

/-- Ua1 `zero_initial` (`Spec.lean:1055`).  A variation supported in the
strictly positive-time cylinder vanishes at the initial slice. -/
theorem zero_initial {u : VelocityField} {c : Space} {r τ₀ τ₁ : ℝ}
    (hτ₀ : 0 < τ₀) (hu₀ : ∀ x : Space, u (0, x) = 0) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
      ∀ x : Space, affineVelocity u b (0, x) = 0 := by
  intro b hb x
  have hb₀ : b (0, x) = 0 := by
    apply image_eq_zero_of_notMem_tsupport (f := b)
    intro hz
    have hz' := hb.2.2.1 hz
    have htime : (0 : ℝ) ∈ Ioo τ₀ τ₁ := hz'.1
    linarith [hτ₀, htime.1]
  simp [affineVelocity, hu₀ x, hb₀]

/-- Ua1 `late_agreement` (`Spec.lean:1061`). -/
theorem late_agreement {u : VelocityField} {c : Space} {r τ₀ τ₁ : ℝ} :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
      ∀ t : ℝ, τ₁ ≤ t → ∀ x : Space,
        affineVelocity u b (t, x) = u (t, x) := by
  intro b hb t ht x
  have hbt : b (t, x) = 0 := by
    apply image_eq_zero_of_notMem_tsupport (f := b)
    intro hz
    have hz' := hb.2.2.1 hz
    have htime : (t : ℝ) ∈ Ioo τ₀ τ₁ := hz'.1
    exact (not_lt_of_ge ht) htime.2
  simp [affineVelocity, hbt]

/-- Ua1 `distinct` (`Spec.lean:1091`): translation by the base velocity is
injective on fields (and therefore on the admissible subclass). -/
theorem distinct {c : Space} {r τ₀ τ₁ : ℝ} (u : VelocityField) :
    ∀ b₁ b₂ : VelocityField,
      AffineAdmissible c r τ₀ τ₁ b₁ →
      AffineAdmissible c r τ₀ τ₁ b₂ → b₁ ≠ b₂ →
        affineVelocity u b₁ ≠ affineVelocity u b₂ := by
  intro b₁ b₂ _hb₁ _hb₂ hne heq
  apply hne
  apply add_right_injective u
  exact heq

end NSFormalization.Section3.T24
