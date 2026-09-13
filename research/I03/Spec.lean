import Contracts.V1.Data
import Contracts.V1.Thresholds
import Contracts.V1.Packet

/-!
# I03 draft specification: same-family scaling and negative Sobolev norms

Task `collaboration/tasks/I03.md`, graph node `I03` in
`formalization/blueprint/DEPENDENCY_GRAPH.md`.

This file is a *specification draft only*.  It contains `def`s and one record of
obligations.  It proves nothing with mathematical content, assumes nothing, and
introduces no `axiom`, no `sorry` and no abstract `Prop` placeholder field:
every propositional field is a fully spelled-out statement about explicitly
named objects.

## What is specified

The scaling half of the proof of Theorem 4.2 (`thm:Rinsert`,
`paper/sections/04-whole-space.tex:31-79`), for **one** `ε`-family:

* the parabolic rescaling `eq:scaling` (`paper/sections/03-torus.tex:112-118`)
  of the fixed packet `(U, P, F)` of Theorem 1.1, placed at `x₀ ∈ B` with
  `t_ε = T - ε²`;
* the energy identities `eq:packetEscale` (`03-torus.tex:125-128`)
  `‖U_ε‖_{L^∞(0,T;L²)} = ε^{1/2}M` and `‖∇U_ε‖_{L²(0,T;L²)} = ε^{1/2}D`, the
  correction bound `eq:wE` (`03-torus.tex:234`) `‖w_ε‖_{E_T} ≤ Cε^{3/2}`, and
  their sum `eq:REclose` (`04-whole-space.tex:39-41`);
* the mixed identity `eq:packetFscale` (`03-torus.tex:129-131`);
* the positive-order display `eq:RpositiveScale`
  (`04-whole-space.tex:63-69`) for `0 ≤ s ≤ 1`;
* the negative-order display `eq:RnegativeScale`
  (`04-whole-space.tex:72-76`), stated *only* for `-3/2 < s < 0`, both in the
  homogeneous `L^q_tḢ^s_x` form that the Fourier calculation actually produces
  and in the inhomogeneous `L^q_tH^s_x` form obtained from
  `(1+|ξ|²)^s ≤ |ξ|^{2s}`;
* the reduction of every lower order to an intermediate index, the sentence
  "If `s ≤ -3/2`, choose `r ∈ (-3/2,-1/2)` with `r > s` and use
  `‖z‖_{H^s} ≤ ‖z‖_{H^r}`.  This last step avoids making any false homogeneous
  scaling assertion at indices where a generic compact profile can have an
  infinite homogeneous norm." (`04-whole-space.tex:78`);
* the resulting convergence `‖g_ε - g‖_{L^q_tH^s_x} → 0` for every
  `s < 2/q - 3/2` (`04-whole-space.tex:42`).

Everything is quantified over the *single* threshold `ε₀` and the *single*
family carried by the structure, as `research/section4/STATEMENTS.md:190-192,
217, 253-257` demands.

## Deliberately out of scope

* The insertion theorem itself: the maximal lifespan, the blowup, the history
  and support clauses, and membership `g_ε ∈ F_R`.  Those are `R42`.
* The construction of `w_ε` and `H_ε` and every property of theirs other than
  smoothness, compact support and the two bounds used here.  Those are `I02`,
  `research/I02/Spec.lean` `CorrectionAPI`; the fields `correction` and
  `forceCorrection` below are `⟪I02:CorrectionAPI.correction⟫` and
  `⟪I02:CorrectionAPI.forceCorrection⟫`, restated rather than imported because
  `research/I02/Spec.lean` is not a library module.
* The equation, incompressibility and blowup of the rescaled packet
  (`research/section4/STATEMENTS.md:281-286`, item 1): those are pure transport
  of `PacketAPI` through `eq:scaling` and belong with the insertion assembly,
  not with the norm estimates.  Recorded as a gap in
  `research/I03/COMPARISON.md`.

## Conventions

* Time is the first spacetime coordinate; `Space`, `SpaceTime`,
  `VelocityField`, `PressureField` and `zeroPastField` are the registered
  `verification/Contracts/V1/Packet.lean` spellings.
* Every Sobolev norm is the manuscript's **angular** one, through
  `Contracts.V1.Data`: `Data.forceSobolevENorm q s` is `‖·‖_{L^q(0,∞;H^s)}`,
  `Data.forceHomogeneousENorm q s` is `‖·‖_{L^q(0,∞;Ḣ^s)}`,
  `Data.mixedLebesgueENorm q p` is `‖·‖_{L^q(0,∞;L^p)}`, and `Data.energyENorm`,
  `Data.energyEssSup`, `Data.energyGradient` are `E_T` and its two summands.
  All force time norms run over `(0,∞)`, `01-introduction.tex:140`; "Each
  rescaled force has time support of length `O(ε²)`, including any part after
  `T`" (`04-whole-space.tex:77`) is why nothing is truncated at `T`.
* `β(q,s)` is `ThresholdAPI.exponent q s = 2/q - 3/2 - s`
  (`04-whole-space.tex:57-60`), never a local copy; `s_q = β(q,0)`.
* `ε^a` is `Real.rpow`.
* "For all sufficiently small `ε`" is the single threshold `ε₀`, with the two
  smallness clauses `eps_time` and `eps_space` transcribing `2ε² < min(T,δ)`
  and `x₀ + εK_* ⊂ B` (`03-torus.tex:104-105, 212`).
-/

noncomputable section

namespace BlowupDensity.I03.Draft

open Set MeasureTheory Filter Topology
open BlowupDensity.Contracts.V1
open scoped ContDiff ENNReal

/-! ## 1. The rescaled fields of `eq:scaling` -/

/-- `U_ε(x,t) = ε^{-1} U((x - x₀)/ε, (t - t_ε)/ε²)` with `t_ε = T - ε²`, the
first display of `eq:scaling` (`paper/sections/03-torus.tex:112-113`), applied
to the zero extension of the packet velocity to nonpositive source time
(clarification `C1`, `03-torus.tex:108-111`, `PacketAPI.force_zero_nonpos` and
`PacketAPI.velocity_extension_smooth`).

Written as `ε⁻¹ • (…)` with the *inverse* scale `k = ε⁻¹` appearing as
`k² = (ε⁻¹)²` in time and `k` in space, so that this is definitionally the
already proved `NSFormalization.Source.parabolicVelocity ε⁻¹ (T - ε^2) x₀`
(`formalization/NSFormalization/Source/ParabolicScaling.lean:93-94`) applied to
`zeroPastField U`, and definitionally the third summand of
`NSFormalization.Source.InsertionFamily.velocity`
(`formalization/NSFormalization/Source/InsertionFamily.lean:34-36`).  It is also
definitionally `research/I02/Spec.lean`'s `scaledPacket`. -/
def scaledVelocity (U : VelocityField) (x₀ : Space) (T ε : ℝ) : VelocityField :=
  fun z => ε⁻¹ • zeroPastField U ((ε⁻¹) ^ 2 * (z.1 - (T - ε ^ 2)), ε⁻¹ • (z.2 - x₀))

/-- `P_ε(x,t) = ε^{-2} P((x - x₀)/ε, (t - t_ε)/ε²)`, the second display of
`eq:scaling` (`paper/sections/03-torus.tex:114-115`).  Definitionally
`NSFormalization.Source.parabolicPressure ε⁻¹ (T - ε^2) x₀ (zeroPastField P)`
(`ParabolicScaling.lean:96-97`). -/
def scaledPressure (P : PressureField) (x₀ : Space) (T ε : ℝ) : PressureField :=
  fun z => (ε⁻¹) ^ 2 • zeroPastField P ((ε⁻¹) ^ 2 * (z.1 - (T - ε ^ 2)), ε⁻¹ • (z.2 - x₀))

/-- `F_ε(x,t) = ε^{-3} F((x - x₀)/ε, (t - t_ε)/ε²)`, the third display of
`eq:scaling` (`paper/sections/03-torus.tex:116-117`).  The packet force is
already its own zero extension (`PacketAPI.force_zero_nonpos`), so no
`zeroPastField` wrapper is needed and this is definitionally
`NSFormalization.Source.parabolicForce ε⁻¹ (T - ε^2) x₀`
(`ParabolicScaling.lean:99-100`). -/
def scaledForce (F : VelocityField) (x₀ : Space) (T ε : ℝ) : VelocityField :=
  fun z => (ε⁻¹) ^ 3 • F ((ε⁻¹) ^ 2 * (z.1 - (T - ε ^ 2)), ε⁻¹ • (z.2 - x₀))

/-- `α(p,q) = -3 + 3/p + 2/q`, the mixed packet-force exponent of
`eq:packetFscale` (`paper/sections/03-torus.tex:130-131`).  The endpoints
`p = ∞`, `q = ∞` are the convention `1/∞ = 0`, realized by
`ENNReal.toReal ⊤ = 0`.  Identical to `research/I02/Spec.lean`'s `alpha`, which
`CorrectionAPI.force_mixed_bound` uses with the extra power `α(p,q) + 1`. -/
def alpha (p q : ℝ≥0∞) : ℝ := -3 + 3 / p.toReal + 2 / q.toReal

/-! ## 2. The contract -/

/-- Every scaling obligation of the proof of Theorem 4.2 (`thm:Rinsert`,
`paper/sections/04-whole-space.tex:44-79`) together with the two energy
identities of Proposition 3.3 (`prop:scaling`, `03-torus.tex:122-131`) that it
reuses on `ℝ³`, all carried by **one** `ε`-family.

Layout of the fields.

* `ν … eps_space`: the ambient data — viscosity, the singular time `T`, the
  margin `δ`, the chosen packet, the ball geometry `x₀ ∈ B = ball x₀ r`, the
  threshold arithmetic, and the single scale threshold `ε₀` with its two
  smallness clauses.
* `correction … forceCorrection_compactSupport`: the two `I02` families `w_ε`
  and `H_ε`, restated with exactly the regularity that the negative-order
  Fourier estimates consume (a smooth compactly supported profile is what makes
  a `Ḣ^s` norm finite for `-3/2 < s < 0`).
* `packetEnergyIdentity … perturbationEnergyBound`: `eq:packetEscale`,
  `eq:wE`, `eq:REclose`.
* `packetMixedScaling`: `eq:packetFscale`.
* `packetPositiveScaling`, `correctionPositiveScaling`: `eq:RpositiveScale`.
* `packetNegativeHomogeneous … correctionNegativeScaling`:
  `eq:RnegativeScale`, restricted to `-3/2 < s < 0`.
* `forceDifference`, `forceDifference_formula`, `forceLowOrderBound`,
  `forceConvergence`: `g_ε - g = H_ε + F_ε`, the intermediate-index reduction,
  and the convergence clause of the theorem statement.

No field is a hypothesis about an unspecified proposition, and no field is
`True`, `∃ x, True` or any similar placeholder. -/
structure ScalingAPI where
  -- ### Ambient data
  /-- Kinematic viscosity `ν`, `paper/sections/04-whole-space.tex:32`. -/
  ν : ℝ
  /-- The fixed packet `(U, P, F)` of Theorem 1.1 at this viscosity, together
  with its Lemma 2.2 constants `M = energyBound` and `D = dissipationBound`.
  "Fix one solution from Theorem 1.1 and denote its velocity, pressure, and
  force by `(U,P,F)`", `paper/sections/01-introduction.tex:63-65`;
  `verification/Contracts/V1/Packet.lean` `PacketAPI`.  Carrying the packet as
  a field, not as a `∀`, is what makes `M`, `D` and the rescaled fields refer to
  one and the same choice. -/
  packet : PacketAPI ν
  /-- The prescribed singular time `T`, `paper/sections/04-whole-space.tex:33`. -/
  T : ℝ
  /-- `T > 0`, `paper/sections/04-whole-space.tex:32`. -/
  time_pos : 0 < T
  /-- The regularity margin: the reference is regular through `T + δ`,
  `paper/sections/04-whole-space.tex:32-33`.  Only its positivity and the
  smallness clause `eps_time` are used here; the reference solution itself
  enters through `I02`. -/
  δ : ℝ
  /-- `δ > 0`, `paper/sections/04-whole-space.tex:33`. -/
  margin_pos : 0 < δ
  /-- The centre of the coordinate ball, `x₀ ∈ B`,
  `paper/sections/03-torus.tex:103`; clarification `C2`,
  `research/section4/STATEMENTS.md:342-344`.  Same `x₀` as
  `⟪I02:CorrectionAPI.x₀⟫`. -/
  x₀ : Space
  /-- The radius of `B = ball x₀ r`, `paper/sections/04-whole-space.tex:33`
  ("fix any nonempty open ball `B ⊂ ℝ³`").  Same `r` as
  `⟪I02:CorrectionAPI.r⟫`. -/
  r : ℝ
  /-- `r > 0`: `B` is nonempty, `paper/sections/04-whole-space.tex:33`. -/
  radius_pos : 0 < r
  /-- `R_* = sup_{y ∈ K_*} |y|`, the radius carrying the compact set `K_*` of
  `paper/sections/03-torus.tex:101-103`; the `θRadius` of
  `⟪I02:CorrectionAPI.θRadius⟫`. -/
  carrierRadius : ℝ
  /-- `R_* > 0`. -/
  carrierRadius_pos : 0 < carrierRadius
  /-- `K ⊆ ball 0 R_*`: the packet carrier is inside the scaling radius,
  `paper/sections/03-torus.tex:101-102`. -/
  carrier_subset : packet.carrier ⊆ Metric.ball (0 : Space) carrierRadius
  /-- The spatial projection of `supp F` is inside the scaling radius too:
  "a compact set `K_*` containing `K` and the spatial projection of `supp F`",
  `paper/sections/03-torus.tex:101-102`. -/
  force_carrier_subset : ∀ z ∈ tsupport packet.force,
    z.2 ∈ Metric.ball (0 : Space) carrierRadius
  /-- The registered threshold arithmetic, `verification/Contracts/V1/Thresholds.lean`.
  `thresholds.exponent q s = 2/q - 3/2 - s` is the `β(q,s)` of
  `paper/sections/04-whole-space.tex:57-60`, and `thresholds.exponent q 0` is
  the threshold `s_q` of `04-whole-space.tex:8`.  Every exponent below is
  written through it, never through a local copy. -/
  thresholds : ThresholdAPI
  /-- The single scale threshold of "for all sufficiently small `ε > 0`",
  `paper/sections/04-whole-space.tex:33`.  One `ε₀`, one family, every
  conclusion: `research/section4/STATEMENTS.md:190-192, 217`. -/
  ε₀ : ℝ
  /-- `ε₀ > 0`. -/
  eps_pos : 0 < ε₀
  /-- `ε₀ ≤ 1`, the normalization under which all constants below are uniform
  and under which `ε^{β} → 0` is monotone in `β`,
  `paper/sections/03-torus.tex:242`. -/
  eps_le_one : ε₀ ≤ 1
  /-- `2ε² < min(T, δ)`, `paper/sections/03-torus.tex:104, 212`.  It puts
  `t_ε = T - ε² > 0`, so that "the positive-time domain includes the whole
  transformed support because `t_ε > 0` and the original force vanishes at
  negative times" (`03-torus.tex:148`) — the reason the `(0,∞)` time norms below
  see the entire rescaled force. -/
  eps_time : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ
  /-- `εR_* < r`, i.e. `x₀ + εK_* ⊂ B`, `paper/sections/03-torus.tex:104-105,
  212`; clarification `C2`. -/
  eps_space : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * carrierRadius < r

  -- ### The `I02` families, restated
  /-- `ε ↦ w_ε`, the solenoidal background correction of Lemma 3.4,
  `paper/sections/03-torus.tex:186`; `⟪I02:CorrectionAPI.correction⟫`.  The
  *same* family index `ε` as the rescaled packet above. -/
  correction : ℝ → VelocityField
  /-- `w_ε` is smooth, `paper/sections/03-torus.tex:188`;
  `⟪I02:CorrectionAPI.correction_smooth⟫`. -/
  correction_smooth : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ContDiff ℝ ∞ (correction ε)
  /-- `w_ε` has compact spacetime support, `paper/sections/03-torus.tex:188`;
  `⟪I02:CorrectionAPI.correction_compactSupport⟫`. -/
  correction_compactSupport : ∀ ε ∈ Ioc (0 : ℝ) ε₀, HasCompactSupport (correction ε)
  /-- `ε ↦ H_ε`, the correction force of Lemma 3.5, `eq:H`,
  `paper/sections/03-torus.tex:220-223`;
  `⟪I02:CorrectionAPI.forceCorrection⟫`.  Same family. -/
  forceCorrection : ℝ → VelocityField
  /-- `H_ε` is smooth across `T`, `paper/sections/03-torus.tex:225`,
  `04-whole-space.tex:51`; `⟪I02:CorrectionAPI.force_smooth⟫`.  Smoothness and
  compact support are exactly the hypotheses under which the rescaled
  correction profiles have uniformly finite homogeneous norms
  (`04-whole-space.tex:70-72`), so they are restated here rather than assumed
  silently. -/
  forceCorrection_smooth : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ContDiff ℝ ∞ (forceCorrection ε)
  /-- `H_ε` is spacetime compact, `paper/sections/03-torus.tex:225`;
  `⟪I02:CorrectionAPI.force_compactSupport⟫`. -/
  forceCorrection_compactSupport : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    HasCompactSupport (forceCorrection ε)

  -- ### `eq:packetEscale`, `eq:wE`, `eq:REclose`
  /-- `‖U_ε‖_{L^∞(0,T;L²)} = ε^{1/2}M`, the first identity of
  `eq:packetEscale`, `paper/sections/03-torus.tex:125-126`, reused verbatim on
  `ℝ³` by `04-whole-space.tex:21-23`.  An **equality**, not a bound: the
  amplitude factor `ε^{-1}` against the volume factor `ε³` is exact, and `M` is
  a least upper bound (`PacketAPI.energy_isLUB`). -/
  packetEnergyIdentity : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    Data.energyEssSup T (scaledVelocity packet.velocity x₀ T ε) =
      ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * packet.energyBound)
  /-- `‖∇U_ε‖_{L²(0,T;L²)} = ε^{1/2}D`, the second identity of
  `eq:packetEscale`, `paper/sections/03-torus.tex:127-128`: "squaring and
  integrating in both space and time gives `ε^{-4}ε³ε² = ε` times the original
  dissipation integral" (`03-torus.tex:145-146`), and `D` is
  `PacketAPI.dissipation_eq`. -/
  packetDissipationIdentity : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    Data.energyGradient T (scaledVelocity packet.velocity x₀ T ε) =
      ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * packet.dissipationBound)
  /-- The constant `C` of `eq:wE` and of `eq:REclose`; it depends on `v` near
  `(x₀,T)`, on the cutoffs and on `ν`, never on `ε`
  (`paper/sections/03-torus.tex:242`). -/
  correctionEnergyConst : ℝ
  /-- `C ≥ 0`. -/
  correctionEnergyConst_nonneg : 0 ≤ correctionEnergyConst
  /-- `‖w_ε‖_{E_T} ≤ Cε^{3/2}`, `eq:wE`, `paper/sections/03-torus.tex:234`;
  `⟪I02:CorrectionAPI.correction_energy_bound⟫`, restated here in the
  `Data.energyENorm` convention so that it composes with the two identities
  above. -/
  correctionEnergyBound : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    Data.energyENorm T (correction ε) ≤
      ENNReal.ofReal (correctionEnergyConst * ε ^ ((3 : ℝ) / 2))
  /-- `‖u_ε - v‖_{E_T} ≤ (M + D)ε^{1/2} + Cε^{3/2}`, `eq:REclose`,
  `paper/sections/04-whole-space.tex:39-41`: "Equation `eq:packetEscale` and the
  correction estimate in Lemma `lem:correction` give `eq:REclose` by the
  triangle inequality" (`04-whole-space.tex:55`).  The velocity difference is
  `u_ε - v = w_ε + U_ε`, so the statement is about the same `ε` in both
  summands. -/
  perturbationEnergyBound : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    Data.energyENorm T (fun z => correction ε z + scaledVelocity packet.velocity x₀ T ε z) ≤
      ENNReal.ofReal ((packet.energyBound + packet.dissipationBound) * ε ^ ((1 : ℝ) / 2) +
        correctionEnergyConst * ε ^ ((3 : ℝ) / 2))

  -- ### `eq:packetFscale`
  /-- `‖F_ε‖_{L^q(0,∞;L^p)} = ε^{α(p,q)}‖F‖_{L^q(0,∞;L^p)}` for `1 ≤ p, q ≤ ∞`,
  `eq:packetFscale`, `paper/sections/03-torus.tex:129-131`: "the force's spatial
  norm gains `ε^{-3+3/p}` and its time norm gains `ε^{2/q}`"
  (`03-torus.tex:148`), the essential-supremum endpoints included
  (`03-torus.tex:149`).  The time norms are over `(0,∞)` on both sides, which is
  legitimate because `t_ε > 0` (`eps_time`) and `F` vanishes at nonpositive
  times (`PacketAPI.force_zero_nonpos`). -/
  packetMixedScaling : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    Data.mixedLebesgueENorm q p (scaledForce packet.force x₀ T ε) =
      ENNReal.ofReal (ε ^ alpha p q) * Data.mixedLebesgueENorm q p packet.force

  -- ### `eq:RpositiveScale`
  /-- The constants `C_{q,s}` of the first line of `eq:RpositiveScale`,
  `paper/sections/04-whole-space.tex:66`. -/
  positiveConst : ℝ≥0∞ → ℝ → ℝ
  /-- `‖F_ε‖_{L^q_tH^s_x} ≤ C_{q,s}(ε^{2/q-3/2} + ε^{β(q,s)})` for `0 ≤ s ≤ 1`,
  the first line of `eq:RpositiveScale`,
  `paper/sections/04-whole-space.tex:64-66`.  The two summands are the
  inhomogeneous `L²` part and the homogeneous part of
  `‖z‖_{H^s} ≤ C_s(‖z‖₂ + ‖z‖_{Ḣ^s})` (`04-whole-space.tex:61-63`); the first
  exponent is `β(q,0) = 2/q - 3/2`, hence written through `thresholds`. -/
  packetPositiveScaling : ∀ (q : ℝ≥0∞), 1 ≤ q → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      Data.forceSobolevENorm q s (scaledForce packet.force x₀ T ε) ≤
        ENNReal.ofReal (positiveConst q s *
          (ε ^ thresholds.exponent q.toReal 0 + ε ^ thresholds.exponent q.toReal s))
  /-- The constants `C_{q,s}` of the second line of `eq:RpositiveScale`,
  `paper/sections/04-whole-space.tex:67-68`. -/
  correctionPositiveConst : ℝ≥0∞ → ℝ → ℝ
  /-- `‖H_ε‖_{L^q_tH^s_x} ≤ C_{q,s}(ε^{2/q-1/2} + ε^{β(q,s)+1})` for
  `0 ≤ s ≤ 1`, the second line of `eq:RpositiveScale`,
  `paper/sections/04-whole-space.tex:67-69`: "the uniformly smooth compact
  rescaled profile of Lemma `lem:correction`, whose amplitude is `ε^{-2}`"
  (`04-whole-space.tex:69`) — one power of `ε` better than the packet force,
  whose amplitude is `ε^{-3}`.  Its `q = 1` case is `eq:HHs`,
  `03-torus.tex:238-240`. -/
  correctionPositiveScaling : ∀ (q : ℝ≥0∞), 1 ≤ q → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      Data.forceSobolevENorm q s (forceCorrection ε) ≤
        ENNReal.ofReal (correctionPositiveConst q s *
          (ε ^ (thresholds.exponent q.toReal 0 + 1) +
            ε ^ (thresholds.exponent q.toReal s + 1)))

  -- ### `eq:RnegativeScale`, valid only for `-3/2 < s < 0`
  /-- The constants `C_{q,s}` of `eq:RnegativeScale` for the packet force,
  `paper/sections/04-whole-space.tex:74`. -/
  negativeConst : ℝ≥0∞ → ℝ → ℝ
  /-- `‖F_ε‖_{L^q_tḢ^s_x} ≤ C_{q,s}ε^{β(q,s)}` for `-3/2 < s < 0`: the
  homogeneous form of `eq:RnegativeScale` that the Fourier calculation actually
  produces, `paper/sections/04-whole-space.tex:70-76`.  The hypothesis
  `-3/2 < s` is the finiteness range: "For `-3/2 < s < 0`, every smooth compact
  profile has finite `Ḣ^s` norm.  Indeed, on `|ξ| < 1` its Fourier transform is
  bounded by its `L¹` norm and `∫_{|ξ|<1}|ξ|^{2s}dξ < ∞`; on `|ξ| ≥ 1` its `L²`
  norm suffices.  These bounds are uniform for the rescaled correction profiles,
  which have common compact support and uniform derivatives."
  (`04-whole-space.tex:70-72`).  Below `-3/2` the statement is *false* for a
  generic compact profile and is deliberately not asserted; `forceLowOrderBound`
  is the replacement.

  At `q = 2`, `s = -1` this is the homogeneous insertion estimate of
  Proposition 4.6, `‖F_ε‖_{L²_tḢ^{-1}_x} ≤ Cε^{1/2}`
  (`04-whole-space.tex:264-272`), since `thresholds.energy` gives
  `exponent 2 (-1) = 1/2`. -/
  packetNegativeHomogeneous : ∀ (q : ℝ≥0∞), 1 ≤ q → ∀ s : ℝ, -3 / 2 < s → s < 0 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      Data.forceHomogeneousENorm q s (scaledForce packet.force x₀ T ε) ≤
        ENNReal.ofReal (negativeConst q s * ε ^ thresholds.exponent q.toReal s)
  /-- `‖F_ε‖_{L^q_tH^s_x} ≤ C_{q,s}ε^{β(q,s)}` for `-3/2 < s < 0`, the first
  half of the display `eq:RnegativeScale`,
  `paper/sections/04-whole-space.tex:73-75`.  It follows from the homogeneous
  bound above by "Since `(1+|ξ|²)^s ≤ |ξ|^{2s}`" (`04-whole-space.tex:72-73`),
  with the same constant. -/
  packetNegativeScaling : ∀ (q : ℝ≥0∞), 1 ≤ q → ∀ s : ℝ, -3 / 2 < s → s < 0 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      Data.forceSobolevENorm q s (scaledForce packet.force x₀ T ε) ≤
        ENNReal.ofReal (negativeConst q s * ε ^ thresholds.exponent q.toReal s)
  /-- The constants `C_{q,s}` of `eq:RnegativeScale` for the correction force,
  `paper/sections/04-whole-space.tex:75`. -/
  correctionNegativeConst : ℝ≥0∞ → ℝ → ℝ
  /-- `‖H_ε‖_{L^q_tḢ^s_x} ≤ C_{q,s}ε^{β(q,s)+1}` for `-3/2 < s < 0`, the
  homogeneous form of the second half of `eq:RnegativeScale`.  The extra power
  is again the amplitude `ε^{-2}` against the packet's `ε^{-3}`.  At `q = 2`,
  `s = -1` this is `‖H_ε‖_{L²_tḢ^{-1}_x} ≤ Cε^{3/2}`,
  `paper/sections/04-whole-space.tex:271`. -/
  correctionNegativeHomogeneous : ∀ (q : ℝ≥0∞), 1 ≤ q → ∀ s : ℝ, -3 / 2 < s → s < 0 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      Data.forceHomogeneousENorm q s (forceCorrection ε) ≤
        ENNReal.ofReal (correctionNegativeConst q s *
          ε ^ (thresholds.exponent q.toReal s + 1))
  /-- `‖H_ε‖_{L^q_tH^s_x} ≤ C_{q,s}ε^{β(q,s)+1}` for `-3/2 < s < 0`, the second
  half of the display `eq:RnegativeScale`,
  `paper/sections/04-whole-space.tex:74-75`. -/
  correctionNegativeScaling : ∀ (q : ℝ≥0∞), 1 ≤ q → ∀ s : ℝ, -3 / 2 < s → s < 0 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      Data.forceSobolevENorm q s (forceCorrection ε) ≤
        ENNReal.ofReal (correctionNegativeConst q s *
          ε ^ (thresholds.exponent q.toReal s + 1))

  -- ### The force difference, the intermediate index, and convergence
  /-- `ε ↦ g_ε - g`, the whole force perturbation.  A field, so that the
  convergence clause and every bound above speak about one and the same
  family. -/
  forceDifference : ℝ → VelocityField
  /-- `g_ε - g = H_ε + F_ε`, from `g_ε = g + H_ε + F_ε`,
  `paper/sections/04-whole-space.tex:48`. -/
  forceDifference_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    forceDifference ε z = forceCorrection ε z + scaledForce packet.force x₀ T ε z
  /-- Every order below the threshold is reached from a *valid* homogeneous
  index by inhomogeneous monotonicity, never by a homogeneous claim outside
  `(-3/2, 0)`.  Transcribes `paper/sections/04-whole-space.tex:78`: "For `q = 1`,
  `eq:RpositiveScale` proves convergence for `0 ≤ s < 1/2`; all `s < 0` follow
  from `‖z‖_{H^s} ≤ ‖z‖₂`.  For `q = 2`, `eq:RnegativeScale` proves convergence
  for `-3/2 < s < -1/2`.  If `s ≤ -3/2`, choose `r ∈ (-3/2,-1/2)` with `r > s`
  and use `‖z‖_{H^s} ≤ ‖z‖_{H^r}`.  This last step avoids making any false
  homogeneous scaling assertion at indices where a generic compact profile can
  have an infinite homogeneous norm."

  The witness `r` exists by `ThresholdAPI.negativeIndex` when
  `s < -1/2 = thresholds.exponent 2 0`, and may be taken to be `s` itself when
  `-3/2 < s`; the conclusion carries `r`'s own subcritical exponent
  `β(q,r) > 0`, so `forceConvergence` follows.  The two conclusions use the
  constants of `eq:RnegativeScale` at the index `r`, i.e. the bounds are
  `‖F_ε‖_{L^q_tH^s} ≤ ‖F_ε‖_{L^q_tH^r} ≤ C_{q,r}ε^{β(q,r)}`. -/
  forceLowOrderBound : ∀ (q : ℝ≥0∞), (q = 1 ∨ q = 2) → ∀ s : ℝ,
      s < thresholds.exponent q.toReal 0 → s < 0 →
      ∃ r : ℝ, -3 / 2 < r ∧ r < 0 ∧ s ≤ r ∧ r < thresholds.exponent q.toReal 0 ∧
        ∀ ε ∈ Ioc (0 : ℝ) ε₀,
          Data.forceSobolevENorm q s (scaledForce packet.force x₀ T ε) ≤
              ENNReal.ofReal (negativeConst q r * ε ^ thresholds.exponent q.toReal r) ∧
            Data.forceSobolevENorm q s (forceCorrection ε) ≤
              ENNReal.ofReal (correctionNegativeConst q r *
                ε ^ (thresholds.exponent q.toReal r + 1))
  /-- `‖g_ε - g‖_{L^q_tH^s_x} → 0` as `ε ↓ 0`, for `q ∈ {1,2}` and every
  `s < s_q = 2/q - 3/2`: the force clause of Theorem 4.2,
  `paper/sections/04-whole-space.tex:42`, "For `q ∈ {1,2}` the force difference
  tends to zero in `L^q_tH^s_x` whenever `s < 2/q - 3/2`", and
  `04-whole-space.tex:43` "All of these conclusions hold for the same family of
  inserted solutions."  The limit is along `𝓝[>] 0`, the manuscript's `ε ↓ 0`,
  and the norm is the honest `ℝ≥0∞`-valued one, so convergence also asserts
  eventual finiteness. -/
  forceConvergence : ∀ (q : ℝ≥0∞), (q = 1 ∨ q = 2) → ∀ s : ℝ,
    s < thresholds.exponent q.toReal 0 →
      Tendsto (fun ε : ℝ => Data.forceSobolevENorm q s (forceDifference ε))
        (𝓝[>] 0) (𝓝 0)

/-! ## 3. Named projections and the existential form consumed downstream -/

/-- `U_ε`, the rescaled packet velocity of this family. -/
def ScalingAPI.U (A : ScalingAPI) (ε : ℝ) : VelocityField :=
  scaledVelocity A.packet.velocity A.x₀ A.T ε

/-- `P_ε`, the rescaled packet pressure of this family. -/
def ScalingAPI.P (A : ScalingAPI) (ε : ℝ) : PressureField :=
  scaledPressure A.packet.pressure A.x₀ A.T ε

/-- `F_ε`, the rescaled packet force of this family. -/
def ScalingAPI.F (A : ScalingAPI) (ε : ℝ) : VelocityField :=
  scaledForce A.packet.force A.x₀ A.T ε

/-- `u_ε - v = w_ε + U_ε`, the velocity difference bounded by `eq:REclose`
(`paper/sections/04-whole-space.tex:37-41`). -/
def ScalingAPI.perturbation (A : ScalingAPI) (ε : ℝ) : VelocityField :=
  fun z => A.correction ε z + A.U ε z

/-- What `R42` and `R46` receive from `I03`: given the ambient data of
Theorem 4.2 — a viscosity with its chosen packet, a singular time, a regularity
margin, a ball, and the two `I02` families for that ball — the whole scaling
package exists on one common `ε`-family.  The packet is pinned by `HEq` because
`PacketAPI` is indexed by the viscosity.  Introducing this definition asserts
nothing. -/
def scalingStatement : Prop :=
  ∀ (ν : ℝ) (packet : PacketAPI ν) (T δ : ℝ) (x₀ : Space) (r : ℝ)
    (w H : ℝ → VelocityField) (thresholds : ThresholdAPI),
    0 < T → 0 < δ → 0 < r →
    ∃ A : ScalingAPI,
      A.ν = ν ∧ HEq A.packet packet ∧ A.T = T ∧ A.δ = δ ∧ A.x₀ = x₀ ∧ A.r = r ∧
        A.correction = w ∧ A.forceCorrection = H ∧ A.thresholds = thresholds

end BlowupDensity.I03.Draft
