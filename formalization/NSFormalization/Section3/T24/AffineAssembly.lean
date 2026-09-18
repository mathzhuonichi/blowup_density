import NSFormalization.Section3.T24.AffineDivergence
import NSFormalization.Section3.T24.AffineEnergy
import NSFormalization.Section3.T24.AffineFamily
import NSFormalization.Section3.T24.AffineForce
import NSFormalization.Section3.T24.AffineMomentum
import NSFormalization.Section3.T24.AffineNonisolated
import NSFormalization.Section3.T24.AffineSpeed
import NSFormalization.Section4.I03.Energy

/-!
# T24a Ua9: the canonical assembly of `prop:affine`

`paper/sections/03-torus.tex:668-696` (`prop:affine`).  The eight T24a unit
modules each close one field of `research/T24/Spec.lean:1010-1116`
(`AffineVariationAPI`) over **raw** packet fields, because `formalization/`
cannot import `Contracts.*` (`research/T24/T24_SPLIT.md:33-47`).  This module

* bundles the raw packet clauses those units consume into `AffineRawData`;
* restates the thirteen `Spec.lean` fields over raw fields as
  `AffineVariationCanonical`;
* assembles the eight units into `affineVariationCanonical`, the single
  canonical proof term the registered contract's binding consumes; and
* closes the one clause of `AffineRawData` that the registered `PacketAPI`
  does **not** carry as a field, `‖U‖_{E_1} < ∞`, from the four clauses it does
  carry (`square_integrable`, `energy_isLUB`, `velocity_support` with
  `carrier_compact`, `dissipation_integrable`), which is the gap left open by
  lane 407 (`research/T24/ATTEMPTS_UA6.md`, "Open gap (not Ua6)").

Nothing here re-proves a unit: every field of `AffineVariationCanonical` is a
single application of a lane 392/398/402/403/407/414/417/424 theorem.
-/

noncomputable section

namespace NSFormalization.Section3.T24

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NavierStokesR3.CompactEnergy (l2Sq dissipation dissipation_nonneg)
open NSFormalization.Section4.I02 (spatialGradient eLpNorm_two_eq_ofReal_sqrt)
open NSFormalization.Section4.I03 (eLpNorm_spatialGradient_sq_slice)
open scoped ContDiff ENNReal BigOperators Topology

/-! ## 1. `‖U‖_{E_1} < ∞` from the registered packet's own clauses

`Contracts.V1.PacketAPI` carries `square_integrable`, `energy_isLUB`,
`velocity_support`/`carrier_compact` and `dissipation_integrable`, but no
assembled `E_1` bound; lane 407's `energy_finite` consumes the assembled bound.
The three lemmas below close that gap with raw hypotheses only. -/

/-- The `L^∞_t L²_x` half of `E_1` is bounded by the packet's least upper bound
`M = sup_{0≤t<1}‖U(t)‖₂`: on every presingular slice the spatial `eLpNorm` is
the honest `ofReal (√(l2Sq U t))` (no totalization gap, by
`I02.eLpNorm_two_eq_ofReal_sqrt` under `square_integrable`), and `M` dominates
each of those numbers. -/
theorem energyEssSup_le_of_isLUB {U : VelocityField} {M : ℝ}
    (hsquare : ∀ t ∈ Ico (0 : ℝ) 1,
      NavierStokesR3.ProblemStatement.SquareIntegrableAtTime U t)
    (hlub : IsLUB ((fun t : ℝ => Real.sqrt (l2Sq U t)) '' Ico (0 : ℝ) 1) M) :
    energyEssSup 1 U ≤ ENNReal.ofReal M := by
  refine essSup_le_of_ae_le _ ?_
  refine Filter.eventually_of_mem (self_mem_ae_restrict measurableSet_Ioo) ?_
  intro t ht
  have htIco : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  have hint : Integrable (fun x : Space => ‖U (t, x)‖ ^ 2) volume := hsquare t htIco
  have hmem : Real.sqrt (l2Sq U t) ∈
      (fun s : ℝ => Real.sqrt (l2Sq U s)) '' Ico (0 : ℝ) 1 := ⟨t, htIco, rfl⟩
  show eLpNorm (fun x : Space => U (t, x)) 2 volume ≤ ENNReal.ofReal M
  rw [eLpNorm_two_eq_ofReal_sqrt hint]
  exact ENNReal.ofReal_le_ofReal (hlub.1 hmem)

/-- The `L²_t Ḣ¹_x` half of `E_1` is finite: on every presingular slice the
squared gradient `eLpNorm` is exactly the dissipation rate
(`I03.eLpNorm_spatialGradient_sq_slice`, whose two slice hypotheses come from
`velocity_smooth` and `velocity_support` with `carrier_compact`), and the rate
is time integrable on `(0,1)` by `dissipation_integrable`. -/
theorem energyGradient_lt_top_of_dissipation {U : VelocityField} {K : Set Space}
    (hsmooth : ContDiffOn ℝ ∞ U preSingularDomain)
    (hK : IsCompact K)
    (hsupport : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => U (t, x)) ⊆ K)
    (hdissipation : IntegrableOn (dissipation U) (Ioo (0 : ℝ) 1)) :
    energyGradient 1 U < ⊤ := by
  have hslice : ∀ t ∈ Ioo (0 : ℝ) 1,
      (eLpNorm (fun x : Space => spatialGradient U t x) 2 volume) ^ (2 : ℝ) =
        ENNReal.ofReal (dissipation U t) := by
    intro t ht
    have htIco : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have hs : ContDiff ℝ ∞ (fun y : Space => U (t, y)) :=
      hsmooth.comp_contDiff (contDiff_const.prodMk contDiff_id)
        (fun y => ⟨htIco, mem_univ y⟩)
    have hcs : HasCompactSupport (fun y : Space => U (t, y)) :=
      hK.of_isClosed_subset (isClosed_tsupport _) (hsupport t htIco)
    exact eLpNorm_spatialGradient_sq_slice hs hcs
  have hlint : (∫⁻ t in Ioo (0 : ℝ) 1,
      (eLpNorm (fun x : Space => spatialGradient U t x) 2 volume) ^ (2 : ℝ)) =
      ENNReal.ofReal (∫ t in Ioo (0 : ℝ) 1, dissipation U t) := by
    rw [setLIntegral_congr_fun measurableSet_Ioo hslice]
    exact (ofReal_integral_eq_lintegral_ofReal hdissipation
      (Filter.Eventually.of_forall (fun t => dissipation_nonneg U t))).symm
  show (∫⁻ t in Ioo (0 : ℝ) 1,
      (eLpNorm (fun x : Space => spatialGradient U t x) 2 volume) ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) < ⊤
  rw [hlint]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top

/-- `‖U‖_{E_1} < ∞` for the registered packet velocity, from the four clauses
`PacketAPI` actually carries.  This is the input lane 407's `energy_finite`
asks for and the registered packet contract does not state. -/
theorem energyENorm_lt_top_of_packet {U : VelocityField} {K : Set Space} {M : ℝ}
    (hsmooth : ContDiffOn ℝ ∞ U preSingularDomain)
    (hK : IsCompact K)
    (hsupport : ∀ t ∈ Ico (0 : ℝ) 1, tsupport (fun x : Space => U (t, x)) ⊆ K)
    (hsquare : ∀ t ∈ Ico (0 : ℝ) 1,
      NavierStokesR3.ProblemStatement.SquareIntegrableAtTime U t)
    (hlub : IsLUB ((fun t : ℝ => Real.sqrt (l2Sq U t)) '' Ico (0 : ℝ) 1) M)
    (hdissipation : IntegrableOn (dissipation U) (Ioo (0 : ℝ) 1)) :
    energyENorm 1 U < ⊤ :=
  ENNReal.add_lt_top.mpr
    ⟨lt_of_le_of_lt (energyEssSup_le_of_isLUB hsquare hlub) ENNReal.ofReal_lt_top,
      energyGradient_lt_top_of_dissipation hsmooth hK hsupport hdissipation⟩

/-! ## 2. The raw packet clauses consumed by T24a

Exactly the clauses named in the eight unit reports
(`research/T24/REPORT_{392,398,402,403,407,414,417,424}.md` §1).  `PacketAPI`'s
`pressure_smooth`, `carrier`, `quietTime` block and zero-extension block are
**not** used: the pressure is unchanged by the variation (`P̃ = P`) and the
pressure gradient cancels between the two residuals. -/

/-- The raw packet data a whole-space affine variation consumes: the physical
fields `U, P, F` at viscosity `ν`, together with the eight `PacketAPI` clauses
(`velocity_smooth`, `force_smooth`, `force_support`, `zero_initial_velocity`,
`divergence_free`, `navier_stokes`, `speed_unbounded`) plus the assembled
energy bound `‖U‖_{E_1} < ∞` of §1. -/
structure AffineRawData (ν : ℝ) (U : VelocityField) (P : PressureField)
    (F : VelocityField) : Prop where
  /-- `U` is smooth on the presingular slab `[0,1) × R³`. -/
  velocity_smooth : ContDiffOn ℝ ∞ U preSingularDomain
  /-- `F` is smooth on all of spacetime. -/
  force_smooth : ContDiff ℝ ∞ F
  /-- `F` has compact spacetime support in strictly positive time. -/
  force_support : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport F
  /-- `U(0,·) = 0`. -/
  zero_initial_velocity : ∀ x : Space, U (0, x) = 0
  /-- `∇·U = 0` on `[0,1)`. -/
  divergence_free : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
    spatialDivergence U t x = 0
  /-- `∂ₜU + (U·∇)U − νΔU + ∇P = F` on `(0,1)`. -/
  navier_stokes : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
    NavierStokesR3.ProblemStatement.navierStokesResidual ν U P t x = F (t, x)
  /-- `limsup_{t↑1}‖U(t)‖_∞ = ∞`. -/
  speed_unbounded : SpeedUnboundedAtOne U
  /-- `‖U‖_{E_1} < ∞`; §1 derives it from the registered packet's clauses. -/
  energy_finite : energyENorm 1 U < ⊤

/-! ## 3. The thirteen `Spec.lean` fields over raw fields -/

/-- `research/T24/Spec.lean:1010-1116` (`AffineVariationAPI`), restated with the
packet record replaced by its raw fields `U, P, F`: the registered structure is
indexed by `P : PacketAPI ν`, which `formalization/` may not mention.  The field
names, order and statements are otherwise those of the Spec; the binding checks
each of them against the registered spelling by `rfl` bridges on the affine
vocabulary. -/
structure AffineVariationCanonical (ν : ℝ) (U : VelocityField) (P : PressureField)
    (F : VelocityField) (c : Space) (r τ₀ τ₁ : ℝ) : Prop where
  /-- `03-torus.tex:671`: the localization ball has positive radius. -/
  radius_pos : 0 < r
  /-- `03-torus.tex:670`: `0 < τ₀ < τ₁ < 1`. -/
  window : 0 < τ₀ ∧ τ₀ < τ₁ ∧ τ₁ < 1
  /-- `03-torus.tex:681-683`: the corrected force is globally smooth. -/
  force_smooth : ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
    ContDiff ℝ ∞ (affineForce ν U F b)
  /-- `03-torus.tex:681-683`: `F̃ ∈ C_c^∞(R³×(0,∞))`. -/
  force_support : ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
    NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport (affineForce ν U F b)
  /-- `03-torus.tex:673,679`: `∇·(U+b) = 0` on `[0,1)`. -/
  divergence_free : ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
    ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
      spatialDivergence (affineVelocity U b) t x = 0
  /-- `03-torus.tex:674-676,679` `eq:affine`: the varied momentum equation. -/
  momentum : ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
    ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν
          (affineVelocity U b) (affinePressure P) t x =
        affineForce ν U F b (t, x)
  /-- `03-torus.tex:684-685`: `Ũ(0,·) = 0`. -/
  zero_initial : ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
    ∀ x : Space, affineVelocity U b (0, x) = 0
  /-- `03-torus.tex:684-685`: `Ũ = U` for `t ≥ τ₁`. -/
  late_agreement : ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
    ∀ t : ℝ, τ₁ ≤ t → ∀ x : Space,
      affineVelocity U b (t, x) = U (t, x)
  /-- `03-torus.tex:686`: the same unbounded speed at `t = 1`. -/
  speed_unbounded : ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
    SpeedUnboundedAtOne (affineVelocity U b)
  /-- `03-torus.tex:686-687`: `‖Ũ‖_{E_1} < ∞`. -/
  energy_finite : ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
    energyENorm 1 (affineVelocity U b) < ⊤
  /-- `03-torus.tex:688-691`: a linearly independent admissible sequence. -/
  infinite_dimensional : ∃ b : ℕ → VelocityField,
    (∀ n : ℕ, AffineAdmissible c r τ₀ τ₁ (b n)) ∧ LinearIndependent ℝ b
  /-- `03-torus.tex:691`: distinct variations give distinct velocities. -/
  distinct : ∀ b₁ b₂ : VelocityField,
    AffineAdmissible c r τ₀ τ₁ b₁ → AffineAdmissible c r τ₀ τ₁ b₂ →
      b₁ ≠ b₂ →
        affineVelocity U b₁ ≠ affineVelocity U b₂
  /-- `03-torus.tex:677,692-696`: non-isolation of the rescaled family. -/
  nonisolated : ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b → b ≠ 0 →
    ∀ m : ℕ,
      Filter.Tendsto (fun lam : ℝ => affineCkSeminorm (tsupport b) m
          (fun z => affineVelocity U (lam • b) z - U z)) (𝓝 0) (𝓝 0) ∧
      Filter.Tendsto (fun lam : ℝ => affineCkSeminorm (tsupport b) m
          (fun z => affineForce ν U F (lam • b) z - F z)) (𝓝 0) (𝓝 0)

/-! ## 4. The assembly -/

/-- **T24a**, `prop:affine` (`paper/sections/03-torus.tex:668-696`): every raw
packet and every cylinder `ball c r × (τ₀,τ₁)` with `0 < r` and
`0 < τ₀ < τ₁ < 1` carry the thirteen affine-variation clauses.

Each field is one application of a T24a unit: lane 392 (`radius_pos`, `window`,
`zero_initial`, `late_agreement`, `distinct`), 402 (`divergence_free`), 398
(`momentum`), 414 (`force_smooth`, `force_support`), 403 (`speed_unbounded`),
407 (`energy_finite`), 417 (`infinite_dimensional`), 424 (`nonisolated`). -/
theorem affineVariationCanonical {ν : ℝ} {U : VelocityField} {P : PressureField}
    {F : VelocityField} (hraw : AffineRawData ν U P F)
    (c : Space) {r τ₀ τ₁ : ℝ}
    (hr : 0 < r) (hτ₀ : 0 < τ₀) (hτ₀τ₁ : τ₀ < τ₁) (hτ₁ : τ₁ < 1) :
    AffineVariationCanonical ν U P F c r τ₀ τ₁ where
  radius_pos := radius_pos hr
  window := window hτ₀ hτ₀τ₁ hτ₁
  force_smooth := force_smooth c r τ₀ τ₁ hτ₀ hτ₁ hraw.velocity_smooth hraw.force_smooth
  force_support := force_support c r τ₀ τ₁ hτ₀ hraw.force_support
  divergence_free := divergence_free c r τ₀ τ₁ hraw.velocity_smooth hraw.divergence_free
  momentum := momentum c r τ₀ τ₁ hraw.velocity_smooth hraw.navier_stokes
  zero_initial := zero_initial hτ₀ hraw.zero_initial_velocity
  late_agreement := late_agreement
  speed_unbounded := speed_unbounded c r τ₀ τ₁ hτ₁ hraw.speed_unbounded
  energy_finite := energy_finite c r τ₀ τ₁ hraw.energy_finite
  infinite_dimensional := infinite_dimensional c r τ₀ τ₁ hr hτ₀τ₁
  distinct := distinct U
  nonisolated := nonisolated c r τ₀ τ₁ hτ₀ hτ₁ hraw.velocity_smooth

end NSFormalization.Section3.T24
