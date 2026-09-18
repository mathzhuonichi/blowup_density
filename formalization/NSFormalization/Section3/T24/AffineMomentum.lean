import NavierStokes.ResidualCalculus
import NavierStokes.R3.ProblemStatement

/-!
# T24a / Ua3 — the `momentum` field of `AffineVariationAPI` (`prop:affine`, `eq:affine` ①)

Whole-space affine variation of the Theorem 1.1 packet `(U, P, F)`
(`paper/sections/03-torus.tex:668-696`, `eq:affine` `:674-676`).  For an admissible
perturbation `b` the varied velocity `U + b` with the packet pressure `P` solves
the forced Navier–Stokes equation with the six-term modified force
`F̃ = F + ∂ₜb − νΔb + (U·∇)b + (b·∇)U + (b·∇)b`.

The statement is carried over **raw packet fields** `U P F` (the reconciliation
rule "`formalization/` cannot import `Contracts.*`"): the only two packet clauses
this unit consumes are `velocity_smooth` (as `ContDiffOn ℝ ∞ U preSingularDomain`)
and `navier_stokes` (as the residual identity on `Ioo 0 1`), passed as explicit
hypotheses, exactly the pattern of `Section3/T14/PacketEnergy.lean`.  The probe
`research/T24/probes/affine_momentum_closes.lean` feeds `Bindings.packet ν hν`'s
fields to discharge the registered `AffineVariationAPI.momentum` obligation.

Reconciliation note (lane 398 / T24_SPLIT.md Ua3, RECONCILIATION.md §3): the
canonical `Section3/T24/AffineBasics.lean` vocabulary (`affineVelocity`,
`affineCylinder`, `AffineAdmissible`, `crossAdvection`, `affinePressure`,
`affineForce`) of lane 392 had not landed on this base, so the definitions this
unit needs are restated here verbatim from `research/T24/Spec.lean:961-990`
(namespace `NSFormalization.Section3.T24`); the assembly lane deduplicates.

The whole-space viscous residual `navierStokesResidual ν` and its component
operators are the registered ones (`NavierStokes.R3.ProblemStatement:57-63` and
`NavierStokes.ProblemStatement:59-96`, definitionally the `Contracts.V1` tokens).
The bilinear/linear operator algebra is the vendored `NavierStokes.ResidualCalculus`
(`temporalDerivative_add`, `advection_add`, `spatialLaplacian_add`) and the two
interior-smoothness helpers (`temporal_differentiable_of_presingular_smooth`,
`spatial_contDiff_of_presingular_smooth`), reused rather than reproved.
-/

noncomputable section

namespace NSFormalization.Section3.T24

open Set
open NavierStokes.ProblemStatement
open NavierStokes.ResidualCalculus
open scoped ContDiff

/-! ## T24a raw-field affine vocabulary (verbatim from `research/T24/Spec.lean:961-990`) -/

/-- `03-torus.tex:668-671`: the open spacetime cylinder `Q = B₀ × (τ₀,τ₁)`. -/
def affineCylinder (c : Space) (r τ₀ τ₁ : ℝ) : Set SpaceTime :=
  Ioo τ₀ τ₁ ×ˢ Metric.ball c r

/-- `03-torus.tex:672-673`: the admissible perturbation class
`b ∈ C_c^∞(Q;ℝ³)` with `∇·b = 0`. -/
def AffineAdmissible (c : Space) (r τ₀ τ₁ : ℝ) (b : VelocityField) : Prop :=
  ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
    tsupport b ⊆ affineCylinder c r τ₀ τ₁ ∧
    (∀ t : ℝ, ∀ x : Space, spatialDivergence b t x = 0)

/-- The transport term `(v·∇)w` of `eq:affine` (`03-torus.tex:674-676`). -/
def crossAdvection (v w : VelocityField) (t : ℝ) (x : Space) : Space :=
  spatialDerivative w t x (v (t, x))

/-- `eq:affine`, `03-torus.tex:674`: `Ũ = U + b`. -/
def affineVelocity (U b : VelocityField) : VelocityField :=
  fun z ↦ U z + b z

/-- `eq:affine`, `03-torus.tex:674`: `P̃ = P`. -/
def affinePressure (P : PressureField) : PressureField := P

/-- `eq:affine`, `03-torus.tex:674-676`: the six-term corrected force
`F̃ = F + ∂ₜb − νΔb + (U·∇)b + (b·∇)U + (b·∇)b`, transport terms in the
paper's order. -/
def affineForce (ν : ℝ) (U F b : VelocityField) : VelocityField :=
  fun z ↦ F z + temporalDerivative b z.1 z.2 - ν • spatialLaplacian b z.1 z.2 +
    crossAdvection U b z.1 z.2 + crossAdvection b U z.1 z.2 +
    crossAdvection b b z.1 z.2

/-! ## The `eq:affine` residual expansion ① -/

/-- Pointwise six-term expansion of the viscous residual along the affine
variation `U ↦ U + b`.  The advection is bilinear
(`advection (U+b) = advection U + (U·∇)b + (b·∇)U + (b·∇)b`) and `∂ₜ`, `Δ`, `∇p`
are additive; the pressure is unchanged (`P̃ = P`), so no pressure-derivative
hypothesis is needed.  The three transport tokens are exactly the last three
terms of `affineForce`; `(b·∇)b = crossAdvection b b = advection b`. -/
theorem navierStokesResidual_affine_expand
    {ν : ℝ} {U b : VelocityField} {P : PressureField} {t : ℝ} {x : Space}
    (hUt : DifferentiableAt ℝ (fun s : ℝ => U (s, x)) t)
    (hbt : DifferentiableAt ℝ (fun s : ℝ => b (s, x)) t)
    (hU2 : ContDiff ℝ 2 (fun y : Space => U (t, y)))
    (hb2 : ContDiff ℝ 2 (fun y : Space => b (t, y))) :
    NavierStokesR3.ProblemStatement.navierStokesResidual ν
        (affineVelocity U b) (affinePressure P) t x =
      NavierStokesR3.ProblemStatement.navierStokesResidual ν U P t x +
        temporalDerivative b t x - ν • spatialLaplacian b t x +
        crossAdvection U b t x + crossAdvection b U t x + crossAdvection b b t x := by
  have hUd : DifferentiableAt ℝ (fun y : Space => U (t, y)) x :=
    hU2.differentiable (by norm_num) x
  have hbd : DifferentiableAt ℝ (fun y : Space => b (t, y)) x :=
    hb2.differentiable (by norm_num) x
  simp only [NavierStokesR3.ProblemStatement.navierStokesResidual, affinePressure]
  unfold affineVelocity
  rw [temporalDerivative_add U b t x hUt hbt,
    advection_add U b t x hUd hbd,
    spatialLaplacian_add U b t x hU2 hb2]
  simp only [crossAdvection, advection, smul_add]
  abel

/-! ## Ua3 target: the `momentum` field, over raw packet fields -/

/-- `03-torus.tex:674-676,679`, `eq:affine` ①, `research/T24/Spec.lean:1047`
(`AffineVariationAPI.momentum`): the affine velocity `U + b` with the packet
pressure `P` solves the forced Navier–Stokes equation with the modified force
`affineForce` at every interior time `t ∈ (0,1)`.

Raw-field form: `U`'s presingular smoothness and the packet momentum identity
`navierStokesResidual ν U P = F` on `Ioo 0 1` are the two explicit hypotheses;
they are exactly the `PacketAPI` fields `velocity_smooth` and `navier_stokes`.
No pressure smoothness is required, because `P̃ = P` and the pressure gradient
cancels between the two residuals. -/
theorem momentum {ν : ℝ} {U F : VelocityField} {P : PressureField}
    (c : Space) (r τ₀ τ₁ : ℝ)
    (hvelocity_smooth : ContDiffOn ℝ ∞ U preSingularDomain)
    (hnavier_stokes : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
        NavierStokesR3.ProblemStatement.navierStokesResidual ν U P t x = F (t, x)) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
      ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
        NavierStokesR3.ProblemStatement.navierStokesResidual ν
            (affineVelocity U b) (affinePressure P) t x =
          affineForce ν U F b (t, x) := by
  intro b hb t ht x
  obtain ⟨hb_smooth, _hb_cs, _hb_supp, _hb_div⟩ := hb
  have hUt : DifferentiableAt ℝ (fun s : ℝ => U (s, x)) t :=
    temporal_differentiable_of_presingular_smooth U hvelocity_smooth t ht x
  have hbt : DifferentiableAt ℝ (fun s : ℝ => b (s, x)) t :=
    temporal_differentiable_of_presingular_smooth b hb_smooth.contDiffOn t ht x
  have hU2 : ContDiff ℝ 2 (fun y : Space => U (t, y)) :=
    (spatial_contDiff_of_presingular_smooth U hvelocity_smooth t ht).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hb2 : ContDiff ℝ 2 (fun y : Space => b (t, y)) :=
    (spatial_contDiff_of_presingular_smooth b hb_smooth.contDiffOn t ht).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  rw [navierStokesResidual_affine_expand hUt hbt hU2 hb2, hnavier_stokes t ht x]
  rfl

end NSFormalization.Section3.T24
