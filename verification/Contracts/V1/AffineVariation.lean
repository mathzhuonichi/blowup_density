import Contracts.V1.Data
import Contracts.V1.Packet

/-! Stable specification for the infinite-dimensional affine variations of the
registered whole-space packet.

Task `collaboration/tasks/T24.md`, graph node `T04`.  Version 1 fixes exactly
Proposition `prop:affine`, `paper/sections/03-torus.tex:668-696`, on the
**whole space**: the packet `(U,P,F)` of Theorem 1.1
(`paper/sections/01-introduction.tex:15-34`) is the registered `I01.packet`
vocabulary, the terminal time is literally the singular time `1`, and the
cylinder `Q = ball c r × (τ₀,τ₁)` is carried as a parameter.  It does not
assert `prop:multiple` (T24b), `prop:conservative` (T24c), any torus statement,
or any density consequence.

Inhabiting `AffineVariationAPI` is a real obligation: all thirteen fields
constrain the explicit affine velocity `U+b`, pressure `P` and six-term force
`F̃ = F + ∂ₜb − νΔb + (U·∇)b + (b·∇)U + (b·∇)b`, and none is an abstract
proposition variable.  Introducing `affineVariationStatement` asserts nothing.

Self-containedness.  The packet, the operators (`spatialDivergence`,
`spatialDerivative`, `temporalDerivative`, `spatialLaplacian`,
`navierStokesResidual`), the force class `CompactPositiveTimeSupport`, the
blow-up clause `SpeedUnboundedAtOne` (`Contracts/V1/Packet.lean`) and the
energy norm `energyENorm` (`Contracts/V1/Data.lean:475`) are **registered** and
imported, never copied.  Only the seven T24a notions that no registered module
carries are written out here — `affineCylinder`, `AffineAdmissible`,
`crossAdvection`, `affineVelocity`, `affinePressure`, `affineForce`,
`ckSeminormE` — each definitionally equal to the canonical
`NSFormalization.Section3.T24` declaration and each checked by a `rfl` bridge in
`verification/Bindings/AffineVariation.lean`.

Provenance: the text of every declaration below is copied token-for-token from
the reconciled specification `research/T24/Spec.lean:959-1121`
(`research/T24/RECONCILIATION.md` §2, `research/T24/T24_SPLIT.md` §0), with only
the namespace changed from `BlowupDensity.T24.Affine` to
`BlowupDensity.Contracts.V1`. -/

noncomputable section

namespace BlowupDensity.Contracts.V1

open Set MeasureTheory Filter Topology
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal BigOperators Topology

/-- `03-torus.tex:668-671`: the open spacetime cylinder `Q = B₀ × (τ₀,τ₁)`,
with `B₀` the open coordinate ball of centre `c` and radius `r` and `(τ₀,τ₁)`
the time window. -/
def affineCylinder (c : Space) (r τ₀ τ₁ : ℝ) : Set SpaceTime :=
  Ioo τ₀ τ₁ ×ˢ Metric.ball c r

/-- `03-torus.tex:672-673`: the admissible perturbation class
`b ∈ C_c^∞(Q;ℝ³)` with `∇·b = 0` — globally smooth, compactly supported inside
the open cylinder, and pointwise divergence-free. -/
def AffineAdmissible (c : Space) (r τ₀ τ₁ : ℝ) (b : SpaceTimeField) : Prop :=
  ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
    tsupport b ⊆ affineCylinder c r τ₀ τ₁ ∧
    (∀ t : ℝ, ∀ x : Space, spatialDivergence b t x = 0)

/-- The transport term `(v·∇)w` of `eq:affine` (`03-torus.tex:674-676`),
in the registered spatial Fréchet-derivative token. -/
def crossAdvection (v w : SpaceTimeField) (t : ℝ) (x : Space) : Space :=
  spatialDerivative w t x (v (t, x))

/-- `eq:affine`, `03-torus.tex:674`: `Ũ = U + b`. -/
def affineVelocity (U b : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ U z + b z

/-- `eq:affine`, `03-torus.tex:674`: `P̃ = P`. -/
def affinePressure (P : SpaceTimeScalar) : SpaceTimeScalar := P

/-- `eq:affine`, `03-torus.tex:674-676`: the six-term corrected force
`F̃ = F + ∂ₜb − νΔb + (U·∇)b + (b·∇)U + (b·∇)b`, in the registered operator
tokens with the transport terms in the paper's order. -/
def affineForce (ν : ℝ) (U F b : SpaceTimeField) : SpaceTimeField :=
  fun z ↦ F z + temporalDerivative b z.1 z.2 - ν • spatialLaplacian b z.1 z.2 +
    crossAdvection U b z.1 z.2 + crossAdvection b U z.1 z.2 +
    crossAdvection b b z.1 z.2

/-- `03-torus.tex:677,692-696`: the fixed-support `C^m` seminorm as an `ℝ≥0∞`
supremum `∑_{k≤m} ⨆_{z∈K} ‖D^k f(z)‖ₑ`.  The extended `ℝ≥0∞` codomain is the
same choice as `Contracts/V1/Data.lean:475` `energyENorm`: a real `sSup` of an
unbounded range takes its junk value `0`, which would make the non-isolation
`Tendsto` vacuous, whereas the `⨆` in `ℝ≥0∞` never does. -/
def ckSeminormE (K : Set SpaceTime) (m : ℕ) (f : SpaceTimeField) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range (m + 1), ⨆ z ∈ K, ‖iteratedFDeriv ℝ k f z‖ₑ

/-- Proposition `prop:affine` (`paper/sections/03-torus.tex:668-696`): the
infinite-dimensional affine family of variations of the registered whole-space
packet `P` (Theorem 1.1, `01-introduction.tex:15-34`) inside the fixed cylinder
`Q = ball c r × (τ₀,τ₁)`.

`Prop`-valued: with the cylinder `(c,r,τ₀,τ₁)` carried as a parameter the record
holds no data and introduces no new constant.  The terminal time is the packet's
singular time `1`; the velocity/pressure/force are the registered whole-space
quantities. -/
structure AffineVariationAPI {ν : ℝ} (P : PacketAPI ν)
    (c : Space) (r τ₀ τ₁ : ℝ) : Prop where
  /-- `03-torus.tex:671`: the localization ball `B₀` has positive radius.
  Non-vacuity: excludes the empty ball, so `AffineAdmissible` is inhabited. -/
  radius_pos : 0 < r
  /-- `03-torus.tex:670`: the time window is strictly interior,
  `0 < τ₀ < τ₁ < 1` — "away from the endpoints".
  Non-vacuity: this concrete strict chain keeps the cylinder off both `t=0`
  and the singular time `t=1`. -/
  window : 0 < τ₀ ∧ τ₀ < τ₁ ∧ τ₁ < 1
  /-- `03-torus.tex:681-683`: for every admissible `b` the corrected force `F̃`
  is smooth on all of spacetime (the correction extends smoothly by zero across
  the singularity at `t=1`).
  Exact quantifier order: `∀ b`, admissibility, then global smoothness.
  Non-vacuity: constrains the explicit `affineForce`, not a free proposition. -/
  force_smooth : ∀ b : SpaceTimeField, AffineAdmissible c r τ₀ τ₁ b →
    ContDiff ℝ ∞ (affineForce ν P.velocity P.force b)
  /-- `03-torus.tex:681-683`: for every admissible `b`, `F̃ ∈ C_c^∞(ℝ³×(0,∞))`
  — compact spacetime support in strictly positive time.
  Exact quantifier order: `∀ b`, admissibility, then the support predicate.
  Non-vacuity: `CompactPositiveTimeSupport` expands to compact support plus a
  positive-time inclusion for this explicit force. -/
  force_support : ∀ b : SpaceTimeField, AffineAdmissible c r τ₀ τ₁ b →
    CompactPositiveTimeSupport (affineForce ν P.velocity P.force b)
  /-- `03-torus.tex:673,679`: `∇·(U+b) = 0` on the presingular slab `[0,1)`.
  Exact quantifier order: `∀ b`, admissibility, `∀ t ∈ Ico 0 1`, `∀ x`.
  Non-vacuity: pins the divergence of the explicit `affineVelocity` to `0`;
  uses `∇·U=0` and `∇·b=0`, hence not a tautology. -/
  divergence_free : ∀ b : SpaceTimeField, AffineAdmissible c r τ₀ τ₁ b →
    ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
      spatialDivergence (affineVelocity P.velocity b) t x = 0
  /-- `03-torus.tex:674-676,679`, `eq:affine`:
  `∂ₜŨ + (Ũ·∇)Ũ − νΔŨ + ∇P̃ = F̃` at every interior time `(0,1)`.
  Exact quantifier order: `∀ b`, admissibility, `∀ t ∈ Ioo 0 1`, `∀ x`.
  Non-vacuity: equates the registered residual of the explicit affine fields
  with the explicit `affineForce`; true only because `P` solves the packet
  equation, so a genuine constraint. -/
  momentum : ∀ b : SpaceTimeField, AffineAdmissible c r τ₀ τ₁ b →
    ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
      navierStokesResidual ν (affineVelocity P.velocity b)
          (affinePressure P.pressure) t x =
        affineForce ν P.velocity P.force b (t, x)
  /-- `03-torus.tex:684-685`: zero initial data `Ũ(0,·) = 0` (`b=0` near `t=0`).
  Exact quantifier order: `∀ b`, admissibility, `∀ x`.
  Non-vacuity: pins the explicit affine velocity at `t=0` to `0`. -/
  zero_initial : ∀ b : SpaceTimeField, AffineAdmissible c r τ₀ τ₁ b →
    ∀ x : Space, affineVelocity P.velocity b (0, x) = 0
  /-- `03-torus.tex:684-685`: `Ũ = U` on the late interval `t ≥ τ₁` (`b=0` near
  `t=1`), hence the same late singular behaviour.
  Exact quantifier order: `∀ b`, admissibility, `∀ t`, `τ₁ ≤ t`, `∀ x`.
  Non-vacuity: forces the affine velocity to equal `U` past `τ₁`. -/
  late_agreement : ∀ b : SpaceTimeField, AffineAdmissible c r τ₀ τ₁ b →
    ∀ t : ℝ, τ₁ ≤ t → ∀ x : Space,
      affineVelocity P.velocity b (t, x) = P.velocity (t, x)
  /-- `03-torus.tex:686`: the same unbounded-speed limit at `t=1`,
  `limsup_{t↑1} ‖Ũ(t)‖_∞ = ∞`.
  Exact quantifier order: `∀ b`, admissibility, then `SpeedUnboundedAtOne`'s
  `M>0, δ>0` and witnesses.
  Non-vacuity: constrains the actual affine velocity near the singular time. -/
  speed_unbounded : ∀ b : SpaceTimeField, AffineAdmissible c r τ₀ τ₁ b →
    SpeedUnboundedAtOne (affineVelocity P.velocity b)
  /-- `03-torus.tex:686-687`: finite energy and dissipation,
  `‖Ũ‖_{E_1} < ∞`.
  Exact quantifier order: `∀ b`, admissibility, then finiteness.
  Non-vacuity: `energyENorm 1` is the registered `energyEssSup + energyGradient`,
  so this single bound asserts both finite energy and finite dissipation. -/
  energy_finite : ∀ b : SpaceTimeField, AffineAdmissible c r τ₀ τ₁ b →
    energyENorm 1 (affineVelocity P.velocity b) < ⊤
  /-- `03-torus.tex:688-691`: the family is genuinely infinite-dimensional — a
  countable admissible family that is `ℝ`-linearly independent (disjoint
  spatial supports of divergence-free curls).
  Exact quantifier order: `∃ b : ℕ → …`, then `(∀ n, admissible) ∧
  LinearIndependent`.
  Non-vacuity: asserts a concrete linearly independent sequence inside the
  admissible class, not an abstract "infinite-dimensional" phrase. -/
  infinite_dimensional : ∃ b : ℕ → SpaceTimeField,
    (∀ n : ℕ, AffineAdmissible c r τ₀ τ₁ (b n)) ∧ LinearIndependent ℝ b
  /-- `03-torus.tex:691`: `b ↦ U + b` is injective on the admissible class, so
  distinct perturbations give distinct velocities.
  Exact quantifier order: `∀ b₁ b₂`, both admissibility proofs, `b₁ ≠ b₂`.
  Non-vacuity: an inequality of explicit affine velocities. -/
  distinct : ∀ b₁ b₂ : SpaceTimeField,
    AffineAdmissible c r τ₀ τ₁ b₁ → AffineAdmissible c r τ₀ τ₁ b₂ →
      b₁ ≠ b₂ →
        affineVelocity P.velocity b₁ ≠ affineVelocity P.velocity b₂
  /-- `03-torus.tex:677,692-696`: non-isolation of the rescaled family — for
  each fixed nonzero admissible `b` and each order `m`, the `C^m` seminorm on
  `tsupport b` of the velocity difference `Ũ_{λb}−U` and of the force
  difference `F̃_{λb}−F` tends to `0` as `λ→0`.
  Exact quantifier order: `∀ b`, admissibility, `b ≠ 0`, `∀ m`, then the two
  `Tendsto … (𝓝 0) (𝓝 0)` limits.
  Non-vacuity: both limits constrain the explicit `ckSeminormE` of the explicit
  differences; convergence to `0` in `ℝ≥0∞` is not vacuous because the seminorm
  is an extended supremum, never the real `sSup` junk value. -/
  nonisolated : ∀ b : SpaceTimeField, AffineAdmissible c r τ₀ τ₁ b → b ≠ 0 →
    ∀ m : ℕ,
      Tendsto (fun lam : ℝ ↦ ckSeminormE (tsupport b) m
          (fun z ↦ affineVelocity P.velocity (lam • b) z - P.velocity z))
        (𝓝 0) (𝓝 0) ∧
      Tendsto (fun lam : ℝ ↦ ckSeminormE (tsupport b) m
          (fun z ↦ affineForce ν P.velocity P.force (lam • b) z - P.force z))
        (𝓝 0) (𝓝 0)

/-- `03-torus.tex:668-696`: the existence form of `prop:affine`.  For every
positive viscosity, every packet from Theorem 1.1, and every cylinder
`ball c r × (τ₀,τ₁)` with `0 < r` and `0 < τ₀ < τ₁ < 1`, the affine-variation
API is inhabited.  Introducing this definition proves no inhabitant. -/
def affineVariationStatement : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (P : PacketAPI ν) (c : Space) (r τ₀ τ₁ : ℝ),
    0 < r → 0 < τ₀ → τ₀ < τ₁ → τ₁ < 1 →
      Nonempty (AffineVariationAPI P c r τ₀ τ₁)

end BlowupDensity.Contracts.V1
