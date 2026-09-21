import NSFormalization.Paper1.InsertionEnergy
import NSFormalization.Paper1.CorrectionMixedNorms
import NSFormalization.Source.PhysicalRemoval

/-!
# I02 draft specification: local vector potential and smooth correction

Task `collaboration/tasks/I02.md`, graph node `I02` in
`formalization/blueprint/DEPENDENCY_GRAPH.md:234-238`.

This file is a *specification draft only*.  It contains definitions and one
record of obligations.  It proves nothing with mathematical content, assumes
nothing, and introduces no `axiom`, no `sorry` and no abstract `Prop`
placeholder field: every propositional field is a fully spelled-out statement
about explicitly named objects.

## What is specified

The Euclidean (`ℝ³`) content of

* Lemma 3.4, "A local divergence-free cutoff" (`lem:potential`),
  `paper/sections/03-torus.tex:176-216`, and
* Lemma 3.5, "Bounds for the background correction" (`lem:correction`),
  `paper/sections/03-torus.tex:218-285`,

exactly as Theorem 4.2 (`thm:Rinsert`) reuses it.  Section 4 states the reuse
explicitly: "The vector potential in Lemma~\ref{lem:potential} is local, so its
proof applies in any Euclidean ball.  In Lemma~\ref{lem:correction}, the
support, derivative, energy, and mixed Lebesgue bounds are also local; only the
final transfer of fractional norms to the torus is unnecessary.  Thus the same
`w_ε` and `H_ε` are available on `ℝ³`, with the same uniform bounds."
(`paper/sections/04-whole-space.tex:23-29`).

Deliberately **out of scope**, and left to `I03`: the fractional bound
`eq:HHs` (`03-torus.tex:238-240`), the positive- and negative-order Sobolev
scaling `eq:RpositiveScale`/`eq:RnegativeScale`
(`04-whole-space.tex:63-78`), and every statement about the rescaled packet
`U_ε, P_ε, F_ε` other than the *support* facts that Lemma 3.4's cancellation
clause `eq:bgzero` needs.

Also out of scope: the reference `(v, π, g)` is taken here as a plain smooth
divergence-free field satisfying the momentum equation pointwise on an open
time slab.  No `D01` solution class, no maximal-solution theory and no force
class `F_R` is used; those enter only at `R42`.

## Conventions

* Time is the first spacetime coordinate
  (`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:33`).
* `Space = EuclideanSpace ℝ (Fin 3)` (`ibid.:30`); all measures are the ordinary
  Lebesgue `volume` on `ℝ³` and on `ℝ`.  Nothing here is periodic: although the
  reused declarations live under `formalization/NSFormalization/Paper1/`, their
  fields, integrals and supports are the Euclidean ones.
* `supp` of the manuscript is `tsupport`, the closure of the nonvanishing set.
* The paper's `∇×` is `NavierStokes.SpatialCurl.curl`, and its spacetime
  version with time frozen is `spatialCurl` (`ibid. SpatialCurl.lean:48,51`).
* The paper's "for all sufficiently small `ε`" is the single threshold `ε₀`
  together with the two smallness clauses `eps_time` and `eps_space`, which
  transcribe `2ε² < min(T,δ)` and `x₀ + εK_* ⊂ B` of
  `03-torus.tex:104-105, 212`.  One `ε`-family carries every conclusion, as
  required by `research/section4/STATEMENTS.md:190-192, 253-257`.
-/

noncomputable section

namespace BlowupDensity.I02.Draft

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space SpaceTime VelocityField PressureField
  temporalDerivative spatialDerivative spatialLaplacian spatialDivergence advection)
open NSFormalization.Paper1.CorrectionProfile (spatialCutoff temporalCutoff)
open NSFormalization.Paper1.InsertionEnergy (energyNorm velocityL2 gradientL2)
open NSFormalization.Paper1.CorrectionMixedNorms (mixedNorm)
open NSFormalization.Source (parabolicVelocity)
open NSFormalization.Source.PacketScaling (zeroPastField)
open scoped ContDiff ENNReal Topology

/-! ## 1. Named objects of the two lemmas -/

/-- `α(p,q) = -3 + 3/p + 2/q`, the packet force exponent of `eq:packetFscale`
(`paper/sections/03-torus.tex:130-131`).  The correction force gains exactly one
extra power, `eq:Hmixed` (`03-torus.tex:235-237`).  The endpoints `p = ∞` and
`q = ∞` are the convention `1/∞ = 0`, which `ENNReal.toReal` realizes as
`3 / (⊤ : ℝ≥0∞).toReal = 3 / 0 = 0`. -/
def alpha (p q : ℝ≥0∞) : ℝ := -3 + 3 / p.toReal + 2 / q.toReal

/-- `θ_ε(x) = θ((x - x₀)/ε)`, the first display of `eq:cutoff`
(`paper/sections/03-torus.tex:184`).  Reused verbatim from
`NSFormalization.Paper1.CorrectionProfile.spatialCutoff`
(`formalization/NSFormalization/Paper1/CorrectionProfile.lean:139-140`). -/
abbrev scaledSpatialCutoff (θ : Space → ℝ) (x₀ : Space) (ε : ℝ) : Space → ℝ :=
  spatialCutoff θ x₀ ε

/-- `η_ε(t) = η((t - T)/ε²)`, the second display of `eq:cutoff`
(`paper/sections/03-torus.tex:185`).  Reused verbatim from
`NSFormalization.Paper1.CorrectionProfile.temporalCutoff`
(`formalization/NSFormalization/Paper1/CorrectionProfile.lean:142-143`). -/
abbrev scaledTemporalCutoff (η : ℝ → ℝ) (T ε : ℝ) : ℝ → ℝ :=
  temporalCutoff η T ε

/-- `U_ε(x,t) = ε⁻¹ U((x-x₀)/ε, (t-t_ε)/ε²)` with `t_ε = T - ε²`, the first
display of `eq:scaling` (`paper/sections/03-torus.tex:112-113`), applied to the
zero extension of the packet velocity to nonpositive source time (clarification
`C1`, `03-torus.tex:108-111`).  Only its *support* enters `I02`; its equation,
energy and blowup belong to `I01`/`I03`.  Reused verbatim from
`NSFormalization.Source.InsertionFamily.velocity`'s third summand
(`formalization/NSFormalization/Source/InsertionFamily.lean:32-35`). -/
def scaledPacket (U : VelocityField) (x₀ : Space) (T ε : ℝ) : VelocityField :=
  parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U)

/-! ## 2. The contract -/

/-- Every obligation that the Euclidean halves of Lemma 3.4 and Lemma 3.5 place
on the local vector potential `A`, the cutoffs `θ, η`, the solenoidal correction
`w_ε` and the correction force `H_ε`, in exactly the form Theorem 4.2
(`thm:Rinsert`, `paper/sections/04-whole-space.tex:31-79`) consumes.

Layout of the fields.

* `ν … reference_equation`: the ambient data — viscosity, the singular time `T`,
  the regularity margin `δ`, and the reference `(v, π, g)`, taken as a plain
  smooth divergence-free classical solution on the open slab
  `(0, T+δ) × ℝ³`.
* `packet … packet_divergence_free`: the only packet facts Lemma 3.4 uses,
  restated here rather than imported from `research/I01/Spec.lean`'s
  `PacketAPI` (fields `velocity`, `carrier`, `carrier_compact`,
  `velocity_support`, `divergence_free`).
* `x₀ … eps_space`: the geometry `x₀ ∈ B = ball x₀ r`, the cutoffs and the
  smallness threshold `ε₀`.
* `potential_smooth`, `potential_formula`, `potential_curl`: Lemma 3.4's
  vector potential, `eq:potential`.
* `correction_formula … correction_cancels_germ`: the rest of Lemma 3.4.
* `force_formula … force_mixed_bound`: Lemma 3.5, minus `eq:HHs`.
* `corrected_background`, `perturbation_divergence_free`: the two extra
  conclusions that Theorem 4.2's proof extracts from these lemmas and that
  `research/section4/REVIEW.md:77-88` requires `R42` to re-export.

No field is a hypothesis about an unspecified proposition, and no field is
`True`, `∃ x, True` or any similar placeholder. -/
structure CorrectionAPI where
  -- ### Ambient data: viscosity, times, reference solution
  /-- Kinematic viscosity `ν`.  It multiplies only `Δw_ε` in `eq:H`
  (`paper/sections/03-torus.tex:221`). -/
  ν : ℝ
  /-- `ν > 0`, `paper/sections/04-whole-space.tex:32`. -/
  viscosity_pos : 0 < ν
  /-- The prescribed singular time `T`, `paper/sections/04-whole-space.tex:33`. -/
  T : ℝ
  /-- `T > 0`, `paper/sections/04-whole-space.tex:32`. -/
  time_pos : 0 < T
  /-- The regularity margin `δ`: the reference is regular through `T + δ`,
  `paper/sections/04-whole-space.tex:32-33`; `03-torus.tex:164-165`. -/
  δ : ℝ
  /-- `δ > 0`, `paper/sections/04-whole-space.tex:33`. -/
  margin_pos : 0 < δ
  /-- The reference velocity `v`, `paper/sections/03-torus.tex:164`.  Only its
  restriction to a fixed compact neighbourhood of `B` and of time `T` is used,
  `paper/sections/04-whole-space.tex:45`. -/
  v : VelocityField
  /-- The reference pressure `π`, `paper/sections/03-torus.tex:164`. -/
  π : PressureField
  /-- The reference force `g`, `paper/sections/03-torus.tex:164`. -/
  g : VelocityField
  /-- `v` is smooth on the open slab `(0, T+δ) × ℝ³`.  This is the Euclidean
  content of "smooth on `[0,T+δ]`" (`03-torus.tex:164`) that Lemmas 3.4 and 3.5
  actually use; no membership in a solution class is assumed. -/
  reference_smooth : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ (univ : Set Space))
  /-- `∇ · v = 0` on the slab.  This is the hypothesis "let `v` be smooth and
  divergence free in a spatial ball centered at `x₀`" of Lemma 3.4,
  `paper/sections/03-torus.tex:177`, in its global-in-space form. -/
  reference_divergence_free : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x : Space,
    spatialDivergence v t x = 0
  /-- `∂_t v + (v·∇)v - νΔv + ∇π = g` on the slab: the reference solves the
  momentum equation.  Used only to state `corrected_background`, which is the
  first display of Theorem 3.6's / Theorem 4.2's expansion,
  `paper/sections/03-torus.tex:321-325`, `04-whole-space.tex:50`. -/
  reference_equation : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x : Space,
    NSFormalization.Source.residual ν v π t x = g (t, x)

  -- ### Packet facts consumed by `eq:bgzero` (restated from `I01`)
  /-- The packet velocity `U` of Theorem 1.1, `paper/sections/01-introduction.tex:63-66`;
  `⟪I01:PacketAPI.velocity⟫`.  Its rescaling is `scaledPacket packet x₀ T ε`. -/
  packet : VelocityField
  /-- `K_*`: a compact set containing the packet carrier `K` and the spatial
  projection of `supp F`, `paper/sections/03-torus.tex:101-103`.  It is the set
  the spatial cutoff `θ` must dominate; `⟪I01:PacketAPI.carrier⟫` enlarged as at
  `03-torus.tex:101`. -/
  carrier : Set Space
  /-- `K_*` is compact, `paper/sections/03-torus.tex:101-102`;
  `⟪I01:PacketAPI.carrier_compact⟫`. -/
  carrier_compact : IsCompact carrier
  /-- `supp U(·,σ) ⊆ K_*` for every presingular reference time,
  `paper/sections/01-introduction.tex:24-25`; `⟪I01:PacketAPI.velocity_support⟫`.
  This is what turns `θ_ε = 1` near `x₀ + εK_*` into `eq:bgzero`. -/
  packet_support : ∀ σ ∈ Ico (0 : ℝ) 1,
    tsupport (fun y : Space => packet (σ, y)) ⊆ carrier
  /-- `∇ · U = 0`, `paper/sections/01-introduction.tex:22`;
  `⟪I01:PacketAPI.divergence_free⟫`.  Needed only for
  `perturbation_divergence_free`. -/
  packet_divergence_free : ∀ σ ∈ Ico (0 : ℝ) 1, ∀ y : Space,
    spatialDivergence packet σ y = 0
  /-- `U` is smooth on the presingular half-domain `[0,1) × ℝ³`,
  `paper/sections/01-introduction.tex:18-19`; `⟪I01:PacketAPI.velocity_smooth⟫`.
  Needed only so that `U_ε` has differentiable spatial slices in
  `perturbation_divergence_free`. -/
  packet_smooth : ContDiffOn ℝ ∞ packet NavierStokes.ProblemStatement.preSingularDomain
  /-- `τ`, the initial quiet interval of the packet, proof of Lemma 2.2,
  `paper/sections/02-preliminaries.tex:152`; `⟪I01:PacketAPI.quietTime⟫`. -/
  packetQuietTime : ℝ
  /-- `τ > 0`, `paper/sections/02-preliminaries.tex:152`;
  `⟪I01:PacketAPI.quiet_pos⟫`. -/
  packet_quiet_pos : 0 < packetQuietTime
  /-- `U = 0` on `(0,τ)`, `paper/sections/02-preliminaries.tex:152`;
  `⟪I01:PacketAPI.velocity_quiet⟫`.  With `packet_smooth` this is exactly the
  hypothesis of `NSFormalization.Source.PacketScaling.zeroPastField_smoothOn`
  (`formalization/NSFormalization/Source/PacketScaling.lean:373-377`), which
  makes the zero extension used by `scaledPacket` smooth. -/
  packet_quiet : ∀ σ ∈ Ioo (0 : ℝ) packetQuietTime, ∀ y : Space, packet (σ, y) = 0

  -- ### Geometry, cutoffs and the scale threshold
  /-- The centre `x₀ ∈ B` of the coordinate ball, `paper/sections/03-torus.tex:103`;
  clarification `C2` of `research/section4/STATEMENTS.md:342-344`. -/
  x₀ : Space
  /-- The radius of the ball `B = ball x₀ r` in which every perturbation lives,
  `paper/sections/04-whole-space.tex:33` ("fix any nonempty open ball
  `B ⊂ ℝ³`").  A general nonempty open ball contains such a ball around the
  chosen `x₀`, which is the reduction recorded in `C2`. -/
  r : ℝ
  /-- `r > 0`: `B` is nonempty, `paper/sections/04-whole-space.tex:33`. -/
  radius_pos : 0 < r
  /-- `θ ∈ C_c^∞(ℝ³)`, `paper/sections/03-torus.tex:181`. -/
  θ : Space → ℝ
  /-- `θ` is smooth, `paper/sections/03-torus.tex:181`. -/
  theta_smooth : ContDiff ℝ ∞ θ
  /-- `θ` has compact support, `paper/sections/03-torus.tex:181`. -/
  theta_compactSupport : HasCompactSupport θ
  /-- The open plateau of `θ`: `θ` equals one on a *neighbourhood* of `K_*`,
  `paper/sections/03-torus.tex:181`.  The Urysohn construction is
  `03-torus.tex:167-174`. -/
  plateau : Set Space
  /-- The plateau is open, `paper/sections/03-torus.tex:181-182` ("on a
  neighborhood of `K_*`"). -/
  plateau_open : IsOpen plateau
  /-- `K_* ⊆ plateau`, `paper/sections/03-torus.tex:181`. -/
  carrier_subset_plateau : carrier ⊆ plateau
  /-- `θ = 1` on the plateau, `paper/sections/03-torus.tex:181`. -/
  theta_one : EqOn θ (fun _ => 1) plateau
  /-- A radius containing `supp θ`; it fixes the constant in "supported inside
  the coordinate ball", `paper/sections/03-torus.tex:188, 212`.  It is the
  `R_*` of `research/section4/STATEMENTS.md:250`. -/
  θRadius : ℝ
  /-- `R_* > 0`. -/
  theta_radius_pos : 0 < θRadius
  /-- `supp θ ⊆ ball 0 R_*`, `paper/sections/03-torus.tex:212`. -/
  theta_support : tsupport θ ⊆ Metric.ball (0 : Space) θRadius
  /-- `η ∈ C_c^∞((-2,2))` equal to one on `[-1,1]`,
  `paper/sections/03-torus.tex:181-182`. -/
  η : ℝ → ℝ
  /-- `η` is smooth, `paper/sections/03-torus.tex:182`. -/
  eta_smooth : ContDiff ℝ ∞ η
  /-- `η` has compact support, `paper/sections/03-torus.tex:182`. -/
  eta_compactSupport : HasCompactSupport η
  /-- `η = 1` on `[-1,1]`, `paper/sections/03-torus.tex:182`.  This is what makes
  `η_ε = 1` throughout the active packet interval `[T-ε², T)`,
  `03-torus.tex:214-215`. -/
  eta_one : EqOn η (fun _ => 1) (Icc (-1 : ℝ) 1)
  /-- `supp η ⊆ (-2,2)`, `paper/sections/03-torus.tex:182`. -/
  eta_support : tsupport η ⊆ Ioo (-2 : ℝ) 2
  /-- The scale threshold of "for all sufficiently small `ε > 0`",
  `paper/sections/03-torus.tex:188`, `04-whole-space.tex:33`. -/
  ε₀ : ℝ
  /-- `ε₀ > 0`. -/
  eps_pos : 0 < ε₀
  /-- `ε₀ ≤ 1`, the normalization under which all constants below are uniform,
  `paper/sections/03-torus.tex:242`. -/
  eps_le_one : ε₀ ≤ 1
  /-- `2ε² < min(T, δ)`, `paper/sections/03-torus.tex:212`, and
  `03-torus.tex:104` (`2ε² < T`).  It puts the whole cutoff window inside
  `(0, T+δ)`, where the reference is regular. -/
  eps_time : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ
  /-- `εR_* < r`, i.e. `x₀ + εK_* ⊂ B` and the scaled support of `θ` is strictly
  inside the coordinate ball, `paper/sections/03-torus.tex:104-105, 212`;
  clarification `C2`, `research/section4/STATEMENTS.md:342-344`. -/
  eps_space : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θRadius < r

  -- ### Lemma 3.4, `eq:potential`: the local vector potential
  /-- `A`, the radial vector potential of `eq:potential`,
  `paper/sections/03-torus.tex:178-180`. -/
  potential : VelocityField
  /-- `A` is smooth wherever the reference is,
  `paper/sections/03-torus.tex:177-180`. -/
  potential_smooth : ContDiffOn ℝ ∞ potential (Ioo (0 : ℝ) (T + δ) ×ˢ (univ : Set Space))
  /-- `A(x,t) = ∫₀¹ r · v(x₀ + r y, t) × y dr` with `y = x - x₀`: the display
  `eq:potential`, `paper/sections/03-torus.tex:179`.  The cross product is
  `NSFormalization.Paper1.RadialPotential.cross`
  (`formalization/NSFormalization/Paper1/RadialPotential.lean:16-19`). -/
  potential_formula : ∀ t : ℝ, ∀ x : Space,
    potential (t, x) =
      ∫ ρ in (0 : ℝ)..1,
        ρ • NSFormalization.Paper1.RadialPotential.cross
          (v (t, x₀ + ρ • (x - x₀))) (x - x₀)
  /-- `∇ × A = v`, `paper/sections/03-torus.tex:181`.  The curl is spatial, with
  the physical time frozen. -/
  potential_curl : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x : Space,
    NavierStokes.SpatialCurl.curl (fun y : Space => potential (t, y)) x = v (t, x)

  -- ### Lemma 3.4, `eq:cutoff` and `eq:bgzero`: the solenoidal correction
  /-- The family `ε ↦ w_ε`.  One family carries every conclusion below, as
  `research/section4/STATEMENTS.md:190-192` demands. -/
  correction : ℝ → VelocityField
  /-- `w_ε = -∇ × (η_ε θ_ε A)`, the third display of `eq:cutoff`,
  `paper/sections/03-torus.tex:186`. -/
  correction_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    correction ε z =
      -NavierStokes.SpatialCurl.curl
        (fun y : Space =>
          (scaledTemporalCutoff η T ε z.1 * scaledSpatialCutoff θ x₀ ε y) •
            potential (z.1, y)) z.2
  /-- `w_ε` is a smooth field, `paper/sections/03-torus.tex:188`.  Smooth on all
  of spacetime: outside the cutoff support it is identically zero,
  `03-torus.tex:212`. -/
  correction_smooth : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ContDiff ℝ ∞ (correction ε)
  /-- `w_ε` is divergence free, `paper/sections/03-torus.tex:188`; "its
  divergence vanishes because it is a curl", `03-torus.tex:212`. -/
  correction_divergence_free : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t : ℝ, ∀ x : Space,
    spatialDivergence (correction ε) t x = 0
  /-- `w_ε` has compact spacetime support, `paper/sections/03-torus.tex:188`. -/
  correction_compactSupport : ∀ ε ∈ Ioc (0 : ℝ) ε₀, HasCompactSupport (correction ε)
  /-- `supp w_ε ⊆ (T-2ε², T+2ε²) × ball x₀ (εR_*)`: "supported inside the
  coordinate ball and in `(T-2ε², T+2ε²)`",
  `paper/sections/03-torus.tex:188-189`.  This is the `O(ε)` spatial ball and
  the `O(ε²)` duration. -/
  correction_support : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    tsupport (correction ε) ⊆
      Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ Metric.ball x₀ (ε * θRadius)
  /-- `supp w_ε ⊆ B` at every time: the perturbation stays inside the prescribed
  ball, `paper/sections/04-whole-space.tex:37-38`. -/
  correction_support_ball : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t : ℝ,
    tsupport (fun x : Space => correction ε (t, x)) ⊆ Metric.ball x₀ r
  /-- `w_ε = 0` for `t ≤ T - 2ε²`: the earlier history and the initial value are
  untouched, `paper/sections/03-torus.tex:333-335`,
  `04-whole-space.tex:35-36`. -/
  correction_vanishes_before : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t : ℝ, t ≤ T - 2 * ε ^ 2 →
    ∀ x : Space, correction ε (t, x) = 0
  /-- `eq:bgzero`, literal form: for each active time there is an *open
  neighbourhood* of `supp U_ε(t)` on which `v + w_ε = 0`,
  `paper/sections/03-torus.tex:190-193`. -/
  correction_cancels : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ioo (0 : ℝ) T,
    ∃ O : Set Space, IsOpen O ∧
      tsupport (fun y : Space => scaledPacket packet x₀ T ε (t, y)) ⊆ O ∧
      ∀ x ∈ O, v (t, x) + correction ε (t, x) = 0
  /-- `eq:bgzero`, germ form.  This is what the cross-advection cancellation
  actually consumes — "`b_ε = 0`, *including its derivatives*",
  `paper/sections/03-torus.tex:330`, `04-whole-space.tex:50` — and it is the
  exact hypothesis shape of
  `NSFormalization.Source.cross_advection_eq_zero`
  (`formalization/NSFormalization/Source/Insertion.lean:54-56`).  It follows
  from `correction_cancels` because an open set is a neighbourhood of each of
  its points. -/
  correction_cancels_germ : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ioo (0 : ℝ) T,
    ∀ x ∈ tsupport (fun y : Space => scaledPacket packet x₀ T ε (t, y)),
      ∀ᶠ y in 𝓝 x, v (t, y) + correction ε (t, y) = 0
  /-- `|∂_t^j ∂_x^β w_ε| ≤ C_{β,j} ε^{-2j-|β|}`, the first bound of
  `eq:derivativebounds`, `paper/sections/03-torus.tex:227-228`.  The constant
  depends only on the two derivative orders (`j` time directions, `m` spatial
  directions), never on `ε`, `03-torus.tex:242`. -/
  correctionDerivConst : ℕ → ℕ → ℝ
  /-- Nonnegativity of the derivative constants. -/
  correctionDerivConst_nonneg : ∀ j m : ℕ, 0 ≤ correctionDerivConst j m
  /-- The mixed derivative bound itself, with `j` unit time directions followed
  by `m` spatial directions of norm at most one,
  `paper/sections/03-torus.tex:227-228`. -/
  correction_derivative_bound : ∀ j m : ℕ, ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ z : SpaceTime,
    ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ (j + m) (correction ε) z
          (Fin.append (fun _ : Fin j => ((1 : ℝ), (0 : Space)))
            (fun i => ((0 : ℝ), u i)))‖
        ≤ correctionDerivConst j m * (ε⁻¹) ^ (2 * j + m)

  -- ### Lemma 3.5, `eq:H`: the correction force
  /-- The family `ε ↦ H_ε`, the same family as `ε ↦ w_ε`. -/
  forceCorrection : ℝ → VelocityField
  /-- `H_ε = ∂_t w_ε - νΔw_ε + (v·∇)w_ε + (w_ε·∇)v + (w_ε·∇)w_ε`, the display
  `eq:H`, `paper/sections/03-torus.tex:220-223`.  In Fréchet form
  `(w·∇)v = Dv(w)` and `(v·∇)w = Dw(v)`; the third summand below is `(w·∇)v`
  and the fourth is `(v·∇)w`. -/
  force_formula : ∀ ε : ℝ, ∀ t : ℝ, ∀ x : Space,
    forceCorrection ε (t, x) =
      temporalDerivative (correction ε) t x -
        ν • spatialLaplacian (correction ε) t x +
        spatialDerivative v t x (correction ε (t, x)) +
        spatialDerivative (correction ε) t x (v (t, x)) +
        advection (correction ε) t x
  /-- "`H_ε` is smooth across `T` and extends by zero to all times outside its
  cutoff support", `paper/sections/03-torus.tex:225`; "globally smooth ...
  including across `T`", `04-whole-space.tex:51`.  Global `ContDiff` on all of
  spacetime is exactly that statement: there is no seam at `T`. -/
  force_smooth : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ContDiff ℝ ∞ (forceCorrection ε)
  /-- `H_ε` has compact spacetime support, `paper/sections/03-torus.tex:225`;
  "spacetime compact", `04-whole-space.tex:51`. -/
  force_compactSupport : ∀ ε ∈ Ioc (0 : ℝ) ε₀, HasCompactSupport (forceCorrection ε)
  /-- `supp H_ε ⊆ supp w_ε ⊆ (T-2ε², T+2ε²) × ball x₀ (εR_*)`,
  `paper/sections/03-torus.tex:225`. -/
  force_support : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    tsupport (forceCorrection ε) ⊆
      Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ Metric.ball x₀ (ε * θRadius)
  /-- The temporal support of `H_ε` is a compact subset of `(0,∞)`, so the zero
  extension to nonpositive times is smooth and `g + H_ε` stays in the force
  class, `paper/sections/03-torus.tex:339`, `04-whole-space.tex:51`. -/
  force_positive_time : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ z ∈ tsupport (forceCorrection ε),
    0 < z.1
  /-- `g_ε - g` is spatially supported in `B`,
  `paper/sections/04-whole-space.tex:38`. -/
  force_support_ball : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ z ∈ tsupport (forceCorrection ε),
    z.2 ∈ Metric.ball x₀ r
  /-- The constant in "its spatial support has volume `O(ε³)`",
  `paper/sections/03-torus.tex:225`. -/
  spatialVolumeConst : ℝ
  /-- "Its spatial support has volume `O(ε³)`",
  `paper/sections/03-torus.tex:225`.  The spatial support is the projection of
  the compact spacetime support. -/
  force_spatial_volume : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    volume (Prod.snd '' tsupport (forceCorrection ε)) ≤
      ENNReal.ofReal (spatialVolumeConst * ε ^ 3)
  /-- "Its temporal support has length `O(ε²)`",
  `paper/sections/03-torus.tex:225`: the projection is contained in an interval
  of length `4ε²`. -/
  force_time_length : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    volume (Prod.fst '' tsupport (forceCorrection ε)) ≤ ENNReal.ofReal (4 * ε ^ 2)
  /-- `|∂_x^β H_ε| ≤ C_β ε^{-2-|β|}`, the second bound of
  `eq:derivativebounds`, `paper/sections/03-torus.tex:229-230`.  The constant
  depends only on `|β| = m`. -/
  forceDerivConst : ℕ → ℝ
  /-- Nonnegativity of the force derivative constants. -/
  forceDerivConst_nonneg : ∀ m : ℕ, 0 ≤ forceDerivConst m
  /-- The spatial derivative bound itself, over `m` spatial directions of norm
  at most one; `m = 0` is the amplitude bound `|H_ε| ≤ Cε^{-2}` used at
  `paper/sections/03-torus.tex:281-282` and `04-whole-space.tex:68`. -/
  force_derivative_bound : ∀ m : ℕ, ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ z : SpaceTime,
    ∀ u : Fin m → Space, (∀ i, ‖u i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ m (forceCorrection ε) z (fun i => ((0 : ℝ), u i))‖
        ≤ forceDerivConst m * (ε⁻¹) ^ (2 + m)

  -- ### Lemma 3.5, `eq:wE` and `eq:Hmixed`: the two norm bounds
  /-- The constant `C` of `eq:wE`, `paper/sections/03-torus.tex:234`.  It depends
  on `v` near `(x₀,T)`, on `θ, η` and on `ν`, but not on `ε`
  (`03-torus.tex:242`). -/
  energyConst : ℝ
  /-- The two finiteness statements that make `‖w_ε‖_{E_T}` an honest norm: the
  slicewise `L²` function is in `L^∞_t(0,T)` and the gradient function is in
  `L²_t(0,T)`.  `E_T = L^∞_tL²_x ∩ L²_t\dot H^1_x` on `(0,T)`,
  `paper/sections/01-introduction.tex` (`eq:Enorm`); realized by
  `NSFormalization.Paper1.InsertionEnergy.energyNorm`
  (`formalization/NSFormalization/Paper1/InsertionEnergy.lean:30-32`). -/
  correction_energy_memLp : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    MemLp (velocityL2 (correction ε)) ⊤ (volume.restrict (Ioo (0 : ℝ) T)) ∧
      MemLp (gradientL2 (correction ε)) 2 (volume.restrict (Ioo (0 : ℝ) T))
  /-- `‖w_ε‖_{E_T} ≤ C ε^{3/2}`, the display `eq:wE`,
  `paper/sections/03-torus.tex:234`.  Consumed by `eq:REclose`,
  `04-whole-space.tex:39-41`. -/
  correction_energy_bound : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    energyNorm T (correction ε) ≤ energyConst * ε ^ ((3 : ℝ) / 2)
  /-- The constants `C_{p,q}` of `eq:Hmixed`,
  `paper/sections/03-torus.tex:236`. -/
  mixedConst : ℝ≥0∞ → ℝ≥0∞ → ℝ
  /-- Each spatial slice of `H_ε` really lies in `L^p`, so the inner norm in
  `mixedNorm` is not the `⊤.toReal = 0` convention in disguise. -/
  force_spatial_memLp : ∀ p : ℝ≥0∞, ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t : ℝ,
    MemLp (fun x : Space => forceCorrection ε (t, x)) p volume
  /-- `‖H_ε‖_{L^q(0,∞;L^p)} ≤ C_{p,q} ε^{α(p,q)+1}`, the display `eq:Hmixed`,
  `paper/sections/03-torus.tex:235-237`, including both essential-supremum
  endpoints.  The time norm here runs over all of `ℝ`, which dominates the
  paper's `(0,∞)` norm and agrees with it because of `force_positive_time`. -/
  force_mixed_bound : ∀ p q : ℝ≥0∞, ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    mixedNorm p q (forceCorrection ε) ≤
      ENNReal.ofReal (mixedConst p q * ε ^ (alpha p q + 1))

  -- ### The two extra exports that Theorem 4.2's proof extracts
  /-- `∂_t b_ε + (b_ε·∇)b_ε - νΔb_ε + ∇π = g + H_ε` for `b_ε = v + w_ε`, the
  first display of the insertion proof, `paper/sections/03-torus.tex:321-325`,
  reused at `04-whole-space.tex:50`.  Note the pressure: it is the *unchanged*
  reference pressure `π`.  This is precisely why the pressure difference
  `p_ε - π` may be taken to be the compact packet representative `P_ε`
  (`04-whole-space.tex:51`, `research/section4/REVIEW.md:77-88`): the background
  correction contributes no pressure at all. -/
  corrected_background : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ioo (0 : ℝ) (T + δ),
    ∀ x : Space,
      NSFormalization.Source.residual ν (fun z => v z + correction ε z) π t x =
        g (t, x) + forceCorrection ε (t, x)
  /-- `u_ε - v = w_ε + U_ε` is divergence free at every presingular time,
  `paper/sections/03-torus.tex:333` ("each summand of the velocity is divergence
  free"), `04-whole-space.tex:37-38`.  Theorem 4.7 consumes this, and
  `research/section4/REVIEW.md:77-88` records that `R42` must export it. -/
  perturbation_divergence_free : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ioo (0 : ℝ) T,
    ∀ x : Space,
      spatialDivergence
        (fun z => correction ε z + scaledPacket packet x₀ T ε z) t x = 0

/-! ## 3. The existential form consumed downstream -/

/-- What `I03` and `R42` receive from `I02`: given the ambient data of
Theorem 4.2 — a viscosity, a singular time, a regularity margin, a smooth
divergence-free reference solving the momentum equation on `(0,T+δ) × ℝ³`, a
packet with compact carrier, and a nonempty ball — the potential, the cutoffs,
the correction and the correction force exist with all the properties above.
Introducing this definition asserts nothing. -/
def correctionStatement : Prop :=
  ∀ (ν T δ : ℝ) (v : VelocityField) (π : PressureField) (g U : VelocityField)
    (K : Set Space) (x₀ : Space) (r : ℝ),
    0 < ν → 0 < T → 0 < δ → 0 < r →
    ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ (univ : Set Space)) →
    (∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x : Space, spatialDivergence v t x = 0) →
    (∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x : Space,
      NSFormalization.Source.residual ν v π t x = g (t, x)) →
    IsCompact K →
    (∀ σ ∈ Ico (0 : ℝ) 1, tsupport (fun y : Space => U (σ, y)) ⊆ K) →
    (∀ σ ∈ Ico (0 : ℝ) 1, ∀ y : Space, spatialDivergence U σ y = 0) →
    ContDiffOn ℝ ∞ U NavierStokes.ProblemStatement.preSingularDomain →
    (∀ τ : ℝ, 0 < τ → (∀ σ ∈ Ioo (0 : ℝ) τ, ∀ y : Space, U (σ, y) = 0) →
    ∃ A : CorrectionAPI,
      A.ν = ν ∧ A.T = T ∧ A.δ = δ ∧ A.v = v ∧ A.π = π ∧ A.g = g ∧
        A.packet = U ∧ A.carrier = K ∧ A.x₀ = x₀ ∧ A.r = r)

end BlowupDensity.I02.Draft
