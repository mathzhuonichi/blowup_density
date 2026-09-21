import Contracts.V1.Correction
import Contracts.V1.Thresholds

/-! Stable specification for the same-family parabolic rescaling of Section 4.

Task `collaboration/tasks/I03.md`, graph node `I03`.  Version 1 fixes the
scaling half of the proof of Theorem 4.2 (`thm:Rinsert`,
`paper/sections/04-whole-space.tex:31-79`) for **one** `eps`-family:

* the parabolic rescaling `eq:scaling` (`paper/sections/03-torus.tex:112-118`)
  of the fixed packet `(U, P, F)` of Theorem 1.1, placed at `x0` with
  `t_eps = T - eps^2`;
* Proposition 3.3's transport (`prop:scaling`, `03-torus.tex:122-131`), reused
  verbatim on `R^3` by `04-whole-space.tex:21-23`: the rescaled fields solve the
  momentum equation at the **same** viscosity, stay divergence free, and have
  unbounded speed at `T`;
* the energy identities `eq:packetEscale` (`03-torus.tex:125-128`)
  `‖U_eps‖_{L^inf(0,T;L^2)} = eps^{1/2}M` and
  `‖grad U_eps‖_{L^2(0,T;L^2)} = eps^{1/2}D`, and their sum with `eq:wE`
  (`03-torus.tex:234`), which is `eq:REclose` (`04-whole-space.tex:39-41`);
* the mixed identity `eq:packetFscale` (`03-torus.tex:129-131`);
* the positive-order display `eq:RpositiveScale` (`04-whole-space.tex:63-69`)
  for `0 <= s <= 1`;
* the **inhomogeneous** half of the negative-order display `eq:RnegativeScale`
  (`04-whole-space.tex:72-76`), stated only for `-3/2 < s < 0`;
* the intermediate-index reduction of every lower order
  (`04-whole-space.tex:78`) and the force-convergence clause of the theorem
  statement, `‖g_eps - g‖_{L^q_t H^s_x} -> 0` for every `s < 2/q - 3/2`
  (`04-whole-space.tex:42-43`).

Deliberately **out of scope**.

* The **homogeneous** clauses of `eq:RnegativeScale`, i.e. the bounds on
  `‖F_eps‖_{L^q_t dot H^s_x}` and `‖H_eps‖_{L^q_t dot H^s_x}`.  They are
  collected in the separate, **unregistered** `HomogeneousScalingAPI` below,
  with the reason recorded there.  Only the inhomogeneous consequences, which
  are what Theorem 4.2 actually consumes, are in `ScalingAPI`.
* The insertion theorem itself: the maximal lifespan, the blow-up of the
  assembled solution, the history and support clauses, and membership of
  `g_eps` in the force class.  Those are `R42`.
* The construction of `w_eps` and `H_eps`: that is `I02`, and this record
  carries the registered `Contracts.V1.CorrectionAPI` as a field rather than
  restating any of it.

## Conventions

* Time is the first spacetime coordinate, as in `Contracts.V1.Packet`.
* Every Sobolev and Lebesgue norm is the canonical Section 4 one of
  `Contracts.V1.Data`: `Data.forceSobolevENorm q s` is `‖.‖_{L^q(0,inf;H^s)}`,
  `Data.mixedLebesgueENorm q p` is `‖.‖_{L^q(0,inf;L^p)}`, and
  `Data.energyENorm`, `Data.energyEssSup`, `Data.energyGradient` are `E_T` and
  its two summands.  All force time norms run over `(0,infinity)`
  (`01-introduction.tex:140`); "Each rescaled force has time support of length
  `O(eps^2)`, including any part after `T`" (`04-whole-space.tex:77`) is why
  nothing is truncated at `T`.
* `beta(q,s)` is `ThresholdAPI.exponent q s = 2/q - 3/2 - s`
  (`04-whole-space.tex:57-60`), never a local copy; `s_q = beta(q,0)`.
* `eps^a` is `Real.rpow`.
* The ambient geometry is **not** restated: `T`, `delta`, `x0`, `r` and the
  radius `R_*` are the fields `correction.T`, `correction.delta`,
  `correction.x0`, `correction.r`, `correction.thetaRadius` of the carried
  `CorrectionAPI`.  This makes the identifications that
  `research/I03/COMPARISON.md` 2.3 demands definitional instead of leaving them
  as equations for `R42` to check.  The scale threshold is the one place where
  an inequality rather than an equation is right: `eps0 <= correction.eps0`,
  because `I03` may legitimately shrink the threshold further but may never
  enlarge it past the range on which `I02`'s bounds hold.
* "For all sufficiently small `eps`" is the single threshold `eps0` with the
  two smallness clauses `eps_time` and `eps_space`, transcribing
  `2 eps^2 < min(T,delta)` and `x0 + eps K_* subset B`
  (`03-torus.tex:104-105, 212`).

## Self-containedness

Only `Contracts.V1.Correction` (hence `Contracts.V1.Data` and
`Contracts.V1.Packet`) and `Contracts.V1.Thresholds` are imported.  `U_eps` and
`alpha` are reused from `Contracts.V1.Correction` rather than copied again;
`scaledPressure`, `scaledForce` and `SpeedUnboundedAt` are written out here,
and `verification/Bindings/Scaling.lean` carries one `rfl` bridge theorem for
each, exactly as `verification/Bindings/Correction.lean` does for `I02`.

Cross references for the copied notions: `parabolicPressure` and
`parabolicForce` are
`formalization/NSFormalization/Source/ParabolicScaling.lean:95-100`;
`SpeedUnboundedAt` is
`formalization/NSFormalization/Source/PacketScaling.lean:22-24`.
-/

noncomputable section

namespace BlowupDensity.Contracts.V1

open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal

/-! ## 1. The rescaled fields of `eq:scaling` -/

/-- `P_eps(x,t) = eps^{-2} P((x - x0)/eps, (t - t_eps)/eps^2)` with
`t_eps = T - eps^2`, the second display of `eq:scaling`
(`paper/sections/03-torus.tex:114-115`), applied to the zero extension of the
packet pressure to nonpositive source time (clarification `C1`,
`03-torus.tex:108-111`, `PacketAPI.pressure_extension_smooth`).

Written through `dilateField` with the inverse scale `k = eps^{-1}` so that it
is definitionally `NSFormalization.Source.parabolicPressure eps⁻¹ (T - eps^2) x0`
applied to `zeroPastField P`; the binding records that by `rfl`. -/
def scaledPressure (Pr : PressureField) (x₀ : Space) (T ε : ℝ) : PressureField :=
  dilateField ((ε⁻¹) ^ 2) ((ε⁻¹) ^ 2) ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField Pr)

/-- `F_eps(x,t) = eps^{-3} F((x - x0)/eps, (t - t_eps)/eps^2)`, the third
display of `eq:scaling` (`paper/sections/03-torus.tex:116-117`).  The packet
force is already its own zero extension (`PacketAPI.force_zero_nonpos`), so no
`zeroPastField` wrapper appears and this is definitionally
`NSFormalization.Source.parabolicForce eps⁻¹ (T - eps^2) x0`. -/
def scaledForce (F : VelocityField) (x₀ : Space) (T ε : ℝ) : VelocityField :=
  dilateField ((ε⁻¹) ^ 3) ((ε⁻¹) ^ 2) ε⁻¹ (T - ε ^ 2) x₀ F

/-- "have unbounded speed at `T`", `prop:scaling`,
`paper/sections/03-torus.tex:123`: the pointwise reading of
`limsup_{t up T} ‖u(t)‖_inf = infinity` that `PacketAPI.speed_unbounded` uses at
`T = 1`.  Written character for character as
`NSFormalization.Source.PacketScaling.SpeedUnboundedAt`, and at `T = 1` it is
`Contracts.V1.SpeedUnboundedAtOne`; the binding records both by `rfl`. -/
def SpeedUnboundedAt (T : ℝ) (u : VelocityField) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
    ∃ t : ℝ, ∃ x : Space, t ∈ Ioo 0 T ∧ T - δ < t ∧ M < ‖u (t, x)‖

/-! ## 2. The contract -/

/-- Every scaling obligation of the proof of Theorem 4.2 (`thm:Rinsert`,
`paper/sections/04-whole-space.tex:44-79`) together with the two energy
identities and the transport clause of Proposition 3.3 (`prop:scaling`,
`03-torus.tex:122-131`) that it reuses on `R^3`, all carried by **one**
`eps`-family and one packet.

Layout of the fields.

* `correction`, `thresholds`, `carrier_subset`: the ambient data.  The `I02`
  record supplies the singular time `T`, the margin `delta`, the ball
  `B = ball x0 r`, the cutoff radius `R_*`, the correction `w_eps`, the
  correction force `H_eps` and their bounds; `ThresholdAPI` supplies
  `beta(q,s)`; `carrier_subset` places the packet carrier `K` inside `R_*` and
  is derived from `I02`'s plateau data, not assumed.
* `eps0 ... eps_space`: the single scale threshold, below `I02`'s.
* `scaledEquation`, `scaledDivergenceFree`, `scaledBlowup`: the first sentence
  of `prop:scaling` (`03-torus.tex:123, 141`), transported to `R^3`.
* `packetEnergyIdentity`, `packetDissipationIdentity`,
  `correctionEnergyBound`, `perturbationEnergyBound`: `eq:packetEscale`,
  `eq:wE` and `eq:REclose`.
* `packetMixedScaling`: `eq:packetFscale`.
* `packetPositiveScaling`, `correctionPositiveScaling`: `eq:RpositiveScale`.
* `packetNegativeScaling`, `correctionNegativeScaling`: the inhomogeneous half
  of `eq:RnegativeScale`, restricted to `-3/2 < s < 0`.
* `forceLowOrderBound`, `forceConvergence`: `04-whole-space.tex:78` and the
  force clause of the theorem statement, `04-whole-space.tex:42-43`.

No field is a hypothesis about an unspecified proposition, and no field is
`True`, `exists x, True` or any similar placeholder. -/
structure ScalingAPI (ν : ℝ) (P : PacketAPI ν) where
  -- ### Ambient data
  /-- The registered `I02` record for the same viscosity and the same packet:
  the reference `(v, pi, g)`, the singular time `T`, the margin `delta`, the
  ball `B = ball x0 r`, the cutoffs, the correction `w_eps` and the correction
  force `H_eps` with all their bounds.  Lemmas 3.4 and 3.5,
  `paper/sections/03-torus.tex:176-285`, as Theorem 4.2 reuses them
  (`04-whole-space.tex:23-29`).  Carrying the whole record, rather than
  restating `w_eps` and `H_eps`, is what makes "all of these conclusions hold
  for the same family of inserted solutions" (`04-whole-space.tex:43`)
  structural. -/
  correction : CorrectionAPI ν P
  /-- The registered threshold arithmetic,
  `verification/Contracts/V1/Thresholds.lean`.  `thresholds.exponent q s` is
  the `beta(q,s) = 2/q - 3/2 - s` of `paper/sections/04-whole-space.tex:57-60`
  and `thresholds.exponent q 0` is the threshold `s_q` of
  `04-whole-space.tex:8`.  Every exponent below is written through it. -/
  thresholds : ThresholdAPI
  /-- `K subset ball 0 R_*`: the packet carrier lies inside the cutoff radius,
  `paper/sections/03-torus.tex:101-102`.  It is a consequence of `I02`'s
  plateau data, so it costs the caller nothing.

  The manuscript's `K_*` at `03-torus.tex:101-102` is larger: it also contains
  the spatial projection of `supp F`.  That enlargement is **not** a field of
  this record.  `I02` fixes `theta_radius` from the packet carrier alone
  (`CorrectionAPI.carrier_subset_plateau` mentions only `K`), so no consumer
  that obtains its `CorrectionAPI` from `correctionStatement` can supply it,
  and no conclusion below uses it; carrying it would have been an obligation
  nothing can discharge.  A consumer that needs `supp F_eps subset B` must get
  the enlarged radius from a future `I02` version.  See
  `research/I03/ATTEMPTS.md` 2. -/
  carrier_subset : P.carrier ⊆ Metric.ball (0 : Space) correction.θRadius
  /-- The single scale threshold of "for all sufficiently small `eps > 0`",
  `paper/sections/04-whole-space.tex:33`.  One `eps0`, one family, every
  conclusion. -/
  ε₀ : ℝ
  /-- `eps0 > 0`. -/
  eps_pos : 0 < ε₀
  /-- `eps0 <= 1`, the normalization under which all constants below are
  uniform and under which `eps^beta` is monotone in `beta`,
  `paper/sections/03-torus.tex:242`. -/
  eps_le_one : ε₀ ≤ 1
  /-- `eps0 <= eps0(I02)`: the scaling family is a sub-family of the correction
  family, so every `I02` bound is available on the whole range used here.  An
  inequality, not an equation: `I03` may shrink the threshold further, and
  `research/I03/COMPARISON.md` 2.3 records that it may never enlarge it. -/
  eps_le_correction : ε₀ ≤ correction.ε₀
  /-- `2 eps^2 < min(T, delta)`, `paper/sections/03-torus.tex:104, 212`.  It
  puts `t_eps = T - eps^2 > 0`, which is why the `(0,infinity)` force time
  norms below see the entire rescaled force (`03-torus.tex:148`). -/
  eps_time : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min correction.T correction.δ
  /-- `eps R_* < r`, i.e. `x0 + eps K_* subset B`,
  `paper/sections/03-torus.tex:104-105, 212`. -/
  eps_space : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * correction.θRadius < correction.r

  -- ### `prop:scaling`: equation, incompressibility, blowup
  /-- "The fields in `eq:scaling` solve the momentum equation at viscosity
  `nu`", `prop:scaling`, `paper/sections/03-torus.tex:123`, reused verbatim on
  `R^3` by `04-whole-space.tex:21-23` ("Use the scaling `eq:scaling` directly,
  without periodization").  The viscosity is **unchanged**: "every term of the
  momentum equation gains the common factor `eps^{-3}` ... no viscosity
  rescaling occurs" (`03-torus.tex:141`).  The statement covers the whole
  inactive past `t <= t_eps` as well, which is what `04-whole-space.tex:36`
  (`u_eps = v` for `0 <= t <= T - 2 eps^2`) needs. -/
  scaledEquation : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t : ℝ, t < correction.T → ∀ x : Space,
    navierStokesResidual ν
        (scaledPacket P.velocity correction.x₀ correction.T ε)
        (scaledPressure P.pressure correction.x₀ correction.T ε) t x =
      scaledForce P.force correction.x₀ correction.T ε (t, x)
  /-- "Incompressibility is preserved", `prop:scaling`,
  `paper/sections/03-torus.tex:141`.  It is one of the two summands of
  `CorrectionAPI.perturbation_divergence_free`. -/
  scaledDivergenceFree : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t : ℝ, t < correction.T →
    ∀ x : Space,
      spatialDivergence (scaledPacket P.velocity correction.x₀ correction.T ε) t x = 0
  /-- "... and have unbounded speed at `T`", `prop:scaling`,
  `paper/sections/03-torus.tex:123`, from the speed identity
  `‖U_eps(t)‖_inf = eps^{-1}‖U(sigma)‖_inf` (`03-torus.tex:142-143`).  This is
  the `limsup_{t up T}‖u_eps(t)‖_inf = infinity` clause of Theorem 4.2
  (`04-whole-space.tex:35`) before the background `v + w_eps` is added back. -/
  scaledBlowup : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    SpeedUnboundedAt correction.T (scaledPacket P.velocity correction.x₀ correction.T ε)

  -- ### `eq:packetEscale` and `eq:REclose`
  /-- `‖U_eps‖_{L^inf(0,T;L^2)} = eps^{1/2}M`, the first identity of
  `eq:packetEscale`, `paper/sections/03-torus.tex:125-126`, reused verbatim on
  `R^3` by `04-whole-space.tex:21-23`.  An **equality**, not a bound: the
  amplitude factor `eps^{-1}` against the volume factor `eps^3` is exact, and
  `M = P.energyBound` is a least upper bound (`PacketAPI.energy_isLUB`), not
  merely an upper bound. -/
  packetEnergyIdentity : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    Data.energyEssSup correction.T
        (scaledPacket P.velocity correction.x₀ correction.T ε) =
      ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * P.energyBound)
  /-- `‖grad U_eps‖_{L^2(0,T;L^2)} = eps^{1/2}D`, the second identity of
  `eq:packetEscale`, `paper/sections/03-torus.tex:127-128`: "squaring and
  integrating in both space and time gives `eps^{-4} eps^3 eps^2 = eps` times
  the original dissipation integral" (`03-torus.tex:145-146`), with
  `D = P.dissipationBound` fixed by `PacketAPI.dissipation_eq`. -/
  packetDissipationIdentity : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    Data.energyGradient correction.T
        (scaledPacket P.velocity correction.x₀ correction.T ε) =
      ENNReal.ofReal (ε ^ ((1 : ℝ) / 2) * P.dissipationBound)
  /-- The constant `C` of `eq:wE` and of `eq:REclose`, `03-torus.tex:234, 242`.
  It is `I02`'s own `energyConst`, made **nonnegative**: `CorrectionAPI` carries
  no sign condition on `energyConst`, and a negative one would make
  `eq:REclose` assert something *smaller* than the triangle inequality
  delivers.  `correctionEnergyBound` below pins this constant to `I02`'s bound,
  so nothing is lost. -/
  correctionEnergyConst : ℝ
  /-- `C >= 0`. -/
  correctionEnergyConst_nonneg : 0 ≤ correctionEnergyConst
  /-- `‖w_eps‖_{E_T} <= C eps^{3/2}`, `eq:wE`, `paper/sections/03-torus.tex:234`,
  with this record's constant: `CorrectionAPI.correction_energy_bound` restated
  so that `eq:REclose` and `eq:wE` use *the same* `C`. -/
  correctionEnergyBound : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    Data.energyENorm correction.T (correction.correction ε) ≤
      ENNReal.ofReal (correctionEnergyConst * ε ^ ((3 : ℝ) / 2))
  /-- `‖u_eps - v‖_{E_T} <= (M + D) eps^{1/2} + C eps^{3/2}`, `eq:REclose`,
  `paper/sections/04-whole-space.tex:39-41`: "Equation `eq:packetEscale` and the
  correction estimate in Lemma `lem:correction` give `eq:REclose` by the
  triangle inequality" (`04-whole-space.tex:55`).  The velocity difference is
  `u_eps - v = w_eps + U_eps`, the constants are *the same* `M`, `D` of
  Lemma 2.2 and *the same* `C = correction.energyConst` of `eq:wE`, and the
  `eps` is the same in both summands. -/
  perturbationEnergyBound : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    Data.energyENorm correction.T
        (fun z => correction.correction ε z +
          scaledPacket P.velocity correction.x₀ correction.T ε z) ≤
      ENNReal.ofReal ((P.energyBound + P.dissipationBound) * ε ^ ((1 : ℝ) / 2) +
        correctionEnergyConst * ε ^ ((3 : ℝ) / 2))

  -- ### `eq:packetFscale`
  /-- `‖F_eps‖_{L^q(0,inf;L^p)} = eps^{alpha(p,q)} ‖F‖_{L^q(0,inf;L^p)}` for
  `1 <= p, q <= infinity`, `eq:packetFscale`,
  `paper/sections/03-torus.tex:129-131`: "the force's spatial norm gains
  `eps^{-3+3/p}` and its time norm gains `eps^{2/q}`" (`03-torus.tex:148`), the
  essential-supremum endpoints included (`03-torus.tex:149`).  The time norms
  are over `(0,infinity)` on both sides, which is legitimate because
  `t_eps > 0` (`eps_time`) and `F` vanishes at nonpositive times
  (`PacketAPI.force_zero_nonpos`).  `1 <= p` is the `Fact` instance
  `Data.mixedLebesgueENorm` requires and `1 <= q` is the manuscript's own range
  (`03-torus.tex:132`). -/
  packetMixedScaling : ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ q → ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    Data.mixedLebesgueENorm q p (scaledForce P.force correction.x₀ correction.T ε) =
      ENNReal.ofReal (ε ^ alpha p q) * Data.mixedLebesgueENorm q p P.force

  -- ### `eq:RpositiveScale`
  /-- The constants `C_{q,s}` of the first line of `eq:RpositiveScale`,
  `paper/sections/04-whole-space.tex:66`. -/
  positiveConst : ℝ≥0∞ → ℝ → ℝ
  /-- `‖F_eps‖_{L^q_t H^s_x} <= C_{q,s}(eps^{2/q-3/2} + eps^{beta(q,s)})` for
  `0 <= s <= 1`, the first line of `eq:RpositiveScale`,
  `paper/sections/04-whole-space.tex:64-66`.  The two summands are the
  inhomogeneous `L^2` part and the homogeneous part of
  `‖z‖_{H^s} <= C_s(‖z‖_2 + ‖z‖_{dot H^s})` (`04-whole-space.tex:61-63`); the
  first exponent is `beta(q,0) = 2/q - 3/2`, hence written through
  `thresholds`.  The manuscript's displays live in the `q in {1,2}` context;
  quantifying over every `q >= 1` (including `q = infinity`, where
  `q.toReal = 0`) is a harmless strengthening matched by the source. -/
  packetPositiveScaling : ∀ (q : ℝ≥0∞), 1 ≤ q → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      Data.forceSobolevENorm q s
          (scaledForce P.force correction.x₀ correction.T ε) ≤
        ENNReal.ofReal (positiveConst q s *
          (ε ^ thresholds.exponent q.toReal 0 + ε ^ thresholds.exponent q.toReal s))
  /-- The constants `C_{q,s}` of the second line of `eq:RpositiveScale`,
  `paper/sections/04-whole-space.tex:67-68`. -/
  correctionPositiveConst : ℝ≥0∞ → ℝ → ℝ
  /-- `‖H_eps‖_{L^q_t H^s_x} <= C_{q,s}(eps^{2/q-1/2} + eps^{beta(q,s)+1})` for
  `0 <= s <= 1`, the second line of `eq:RpositiveScale`,
  `paper/sections/04-whole-space.tex:67-69`: "the uniformly smooth compact
  rescaled profile of Lemma `lem:correction`, whose amplitude is `eps^{-2}`"
  (`04-whole-space.tex:69`) -- one power of `eps` better than the packet force,
  whose amplitude is `eps^{-3}`.  Its `q = 1` case is `eq:HHs`,
  `03-torus.tex:238-240`. -/
  correctionPositiveScaling : ∀ (q : ℝ≥0∞), 1 ≤ q → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      Data.forceSobolevENorm q s (correction.forceCorrection ε) ≤
        ENNReal.ofReal (correctionPositiveConst q s *
          (ε ^ (thresholds.exponent q.toReal 0 + 1) +
            ε ^ (thresholds.exponent q.toReal s + 1)))

  -- ### `eq:RnegativeScale`, inhomogeneous half, valid only for `-3/2 < s < 0`
  /-- The constants `C_{q,s}` of `eq:RnegativeScale` for the packet force,
  `paper/sections/04-whole-space.tex:74`. -/
  negativeConst : ℝ≥0∞ → ℝ → ℝ
  /-- `‖F_eps‖_{L^q_t H^s_x} <= C_{q,s} eps^{beta(q,s)}` for `-3/2 < s < 0`,
  the packet half of the display `eq:RnegativeScale`,
  `paper/sections/04-whole-space.tex:73-75`.  The hypothesis `-3/2 < s` is the
  finiteness range of the homogeneous profile norm that produces it: "For
  `-3/2 < s < 0`, every smooth compact profile has finite `dot H^s` norm ...
  These bounds are uniform for the rescaled correction profiles, which have
  common compact support and uniform derivatives." (`04-whole-space.tex:70-72`).
  Below `-3/2` no homogeneous claim is made; `forceLowOrderBound` is the
  replacement.

  At `q = 2`, `s = -1` this is the inhomogeneous form of the insertion estimate
  of Proposition 4.6, `04-whole-space.tex:264-272`, since `ThresholdAPI.energy`
  gives `exponent 2 (-1) = 1/2`. -/
  packetNegativeScaling : ∀ (q : ℝ≥0∞), 1 ≤ q → ∀ s : ℝ, -3 / 2 < s → s < 0 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      Data.forceSobolevENorm q s
          (scaledForce P.force correction.x₀ correction.T ε) ≤
        ENNReal.ofReal (negativeConst q s * ε ^ thresholds.exponent q.toReal s)
  /-- The constants `C_{q,s}` of `eq:RnegativeScale` for the correction force,
  `paper/sections/04-whole-space.tex:75`. -/
  correctionNegativeConst : ℝ≥0∞ → ℝ → ℝ
  /-- `‖H_eps‖_{L^q_t H^s_x} <= C_{q,s} eps^{beta(q,s)+1}` for `-3/2 < s < 0`,
  the correction half of the display `eq:RnegativeScale`,
  `paper/sections/04-whole-space.tex:74-75`.  The extra power is again the
  amplitude `eps^{-2}` against the packet's `eps^{-3}`. -/
  correctionNegativeScaling : ∀ (q : ℝ≥0∞), 1 ≤ q → ∀ s : ℝ, -3 / 2 < s → s < 0 →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      Data.forceSobolevENorm q s (correction.forceCorrection ε) ≤
        ENNReal.ofReal (correctionNegativeConst q s *
          ε ^ (thresholds.exponent q.toReal s + 1))

  -- ### The intermediate index and the convergence clause
  /-- The constants of the intermediate-index reduction.  They carry three
  indices, not two: the norm is measured at the order `s`, the decay rate comes
  from the intermediate order `r`, and the manuscript's own constants
  `C_{q,s}` in `eq:RnegativeScale` are stated at one order only.  The
  normalization constant relating the manuscript's angular transform
  (`01-introduction.tex:91`) to the cycles convention of the implementation is
  `(2 pi)^{|s|}`, which genuinely depends on `s` and is unbounded as
  `s -> -infinity`, so it cannot be absorbed into a constant indexed by `r`
  alone.  See `research/I03/ATTEMPTS.md`. -/
  lowOrderConst : ℝ≥0∞ → ℝ → ℝ → ℝ
  /-- Every order below the threshold is reached from a *valid* index by
  inhomogeneous monotonicity, never by a homogeneous claim outside `(-3/2,0)`.
  This is the content of `paper/sections/04-whole-space.tex:78`: "For `q = 1`,
  `eq:RpositiveScale` proves convergence for `0 <= s < 1/2`; all `s < 0` follow
  from `‖z‖_{H^s} <= ‖z‖_2`.  For `q = 2`, `eq:RnegativeScale` proves
  convergence for `-3/2 < s < -1/2`.  If `s <= -3/2`, choose `r in (-3/2,-1/2)`
  with `r > s` and use `‖z‖_{H^s} <= ‖z‖_{H^r}`.  This last step avoids making
  any false homogeneous scaling assertion at indices where a generic compact
  profile can have an infinite homogeneous norm."

  One uniform route is stated for both `q`: a single witness
  `r in (-3/2, 0)` with `s <= r` and `r < s_q`, and both conclusions at that
  `r`.  A witness always exists -- take `r := s` when `-3/2 < s`, and otherwise
  `ThresholdAPI.negativeIndex` supplies `r in (-3/2,-1/2)` with `s < r` -- and
  at `q = 1` this uses a negative `r` where the paper uses `r = 0`; both are
  legitimate, and the negative one keeps the statement inside the range where
  `packetNegativeScaling` is available.  It also matches the source, which
  lowers to a fixed negative index for every `q`. -/
  forceLowOrderBound : ∀ (q : ℝ≥0∞), (q = 1 ∨ q = 2) → ∀ s : ℝ,
      s < thresholds.exponent q.toReal 0 → s < 0 →
      ∃ r : ℝ, -3 / 2 < r ∧ r < 0 ∧ s ≤ r ∧ r < thresholds.exponent q.toReal 0 ∧
        ∀ ε ∈ Ioc (0 : ℝ) ε₀,
          Data.forceSobolevENorm q s
                (scaledForce P.force correction.x₀ correction.T ε) ≤
              ENNReal.ofReal (lowOrderConst q s r * ε ^ thresholds.exponent q.toReal r) ∧
            Data.forceSobolevENorm q s (correction.forceCorrection ε) ≤
              ENNReal.ofReal (lowOrderConst q s r *
                ε ^ (thresholds.exponent q.toReal r + 1))
  /-- `‖g_eps - g‖_{L^q_t H^s_x} -> 0` as `eps` decreases to `0`, for
  `q in {1,2}` and every `s < s_q = 2/q - 3/2`: the force clause of
  Theorem 4.2, `paper/sections/04-whole-space.tex:42`, "For `q in {1,2}` the
  force difference tends to zero in `L^q_t H^s_x` whenever `s < 2/q - 3/2`",
  and `04-whole-space.tex:43` "All of these conclusions hold for the same family
  of inserted solutions."  The force difference is `g_eps - g = H_eps + F_eps`
  (`04-whole-space.tex:48`), written out here so that the clause and every
  bound above speak about one and the same family.  The limit is along
  `nhdsWithin 0 (Ioi 0)`, the manuscript's `eps` decreasing to `0`, and the norm
  is the honest `ENNReal`-valued one, so convergence also asserts eventual
  finiteness. -/
  forceConvergence : ∀ (q : ℝ≥0∞), (q = 1 ∨ q = 2) → ∀ s : ℝ,
    s < thresholds.exponent q.toReal 0 →
      Tendsto (fun ε : ℝ => Data.forceSobolevENorm q s
          (fun z => correction.forceCorrection ε z +
            scaledForce P.force correction.x₀ correction.T ε z))
        (𝓝[>] 0) (𝓝 0)

/-! ## 3. Named projections -/

/-- `U_eps`, the rescaled packet velocity of this family,
`paper/sections/03-torus.tex:112-113`. -/
def ScalingAPI.U {ν : ℝ} {P : PacketAPI ν} (A : ScalingAPI ν P) (ε : ℝ) : VelocityField :=
  scaledPacket P.velocity A.correction.x₀ A.correction.T ε

/-- `P_eps`, the rescaled packet pressure of this family,
`paper/sections/03-torus.tex:114-115`. -/
def ScalingAPI.P {ν : ℝ} {P : PacketAPI ν} (A : ScalingAPI ν P) (ε : ℝ) : PressureField :=
  scaledPressure P.pressure A.correction.x₀ A.correction.T ε

/-- `F_eps`, the rescaled packet force of this family,
`paper/sections/03-torus.tex:116-117`. -/
def ScalingAPI.F {ν : ℝ} {P : PacketAPI ν} (A : ScalingAPI ν P) (ε : ℝ) : VelocityField :=
  scaledForce P.force A.correction.x₀ A.correction.T ε

/-- `u_eps - v = w_eps + U_eps`, the velocity difference bounded by
`eq:REclose` (`paper/sections/04-whole-space.tex:37-41`). -/
def ScalingAPI.perturbation {ν : ℝ} {P : PacketAPI ν} (A : ScalingAPI ν P)
    (ε : ℝ) : VelocityField :=
  fun z => A.correction.correction ε z + A.U ε z

/-- `g_eps - g = H_eps + F_eps`, the force difference of
`paper/sections/04-whole-space.tex:48`. -/
def ScalingAPI.forceDifference {ν : ℝ} {P : PacketAPI ν} (A : ScalingAPI ν P)
    (ε : ℝ) : VelocityField :=
  fun z => A.correction.forceCorrection ε z + A.F ε z

/-! ## 4. The existential form consumed downstream -/

/-- What `R42` and `R46` receive from `I03`: given a packet and the registered
`I02` record for that packet, the whole scaling package exists on the **same**
correction record and on a sub-family of the same `eps`-family.  There is no
side condition: every hypothesis is already a field of `PacketAPI` or of
`CorrectionAPI`.

`A.correction = C` is an equation, not an existential: the scaling estimates
are proved for the very correction and correction force that `I02` produced,
which is what "all of these conclusions hold for the same family of inserted
solutions" (`paper/sections/04-whole-space.tex:43`) asserts.  The threshold
arithmetic is likewise the caller's own `ThresholdAPI`.  The one thing `I03`
reserves is the right to shrink the scale threshold, recorded inside
`ScalingAPI` as `eps_le_correction`.

Introducing this definition asserts nothing. -/
def scalingStatement : Prop :=
  ∀ (ν : ℝ) (P : PacketAPI ν) (C : CorrectionAPI ν P) (th : ThresholdAPI),
    ∃ A : ScalingAPI ν P, A.correction = C ∧ A.thresholds = th

/-! ## 5. The homogeneous clauses: stated, deliberately **not** registered -/

/-- The two homogeneous clauses of `eq:RnegativeScale`
(`paper/sections/04-whole-space.tex:70-76`), in the homogeneous form that the
Fourier calculation of `04-whole-space.tex:70-72` actually produces, with
`Data.forceHomogeneousENorm` as the norm.

**This structure is deliberately not registered in
`verification/contracts.json`, because it is not proved.**  Nothing in the
project bounds the *homogeneous* norm of a *scaled* field: the homogeneous
profile norm is used only on the unscaled profile, and
`Data.forceHomogeneousENorm` together with `Data.IsHomogeneousDatum` has no
witness-producing construction at all (the inhomogeneous counterpart is the
whole `RealVectorSobolev` realization of
`formalization/NSFormalization/Paper3/AngularRealVectorBochner.lean`; the
homogeneous side has none).  Since `forceHomogeneousENorm` is an infimum and
the empty infimum in `ENNReal` is `top`, both fields below are unprovable until
such a witness exists.

The missing piece has a name: it is unit **`U7c`** of
`research/I03/COMPARISON.md` 5 -- a homogeneous counterpart of
`formalization/NSFormalization/Paper3/AngularRealVectorBochner.lean`, i.e. a
`RealVectorSobolev`-valued realization for the weight `abs(xi)^{-s}` -- together
with the two small units `U7a` (the exact homogeneous change of variables) and
`U7b` (its `L^q_t` form).  On the task graph it belongs to node **`B02`**
("Homogeneous H-minus-one approximation",
`formalization/blueprint/DEPENDENCY_GRAPH.md:322`), whose **unit 6** is the same
obligation, recorded as `D01` unit `L6` ("the `dot H^{-1}` realization is well
posed", `research/D01/COMPARISON_A.md:102`): `Paper3/HomogeneousRealization.lean`
deliberately builds no `L^2 -> S'` homogeneous multiplier, so nothing produces
the datum.  `research/I03/COMPARISON.md` 2.4 and `research/I03/ATTEMPTS.md` 4
record the same gap.

**Consequence for `R46`.**  Proposition 4.6's `L^2(0,infinity;dot H^{-1})`
clause (`04-whole-space.tex:212-226`) blocks on exactly this and on nothing
else: the inhomogeneous route that `ScalingAPI` takes does not reach a
homogeneous norm.  Theorem 4.2 itself does **not** block on it -- every clause
of `04-whole-space.tex:42` is inhomogeneous, and `packetNegativeScaling` and
`correctionNegativeScaling` supply it. -/
structure HomogeneousScalingAPI (ν : ℝ) (P : PacketAPI ν) where
  /-- The scaling package whose family the two clauses below refer to. -/
  scaling : ScalingAPI ν P
  /-- The constants `C_{q,s}` of `eq:RnegativeScale` for the packet force in
  its homogeneous form, `paper/sections/04-whole-space.tex:74`. -/
  packetHomogeneousConst : ℝ≥0∞ → ℝ → ℝ
  /-- `‖F_eps‖_{L^q_t dot H^s_x} <= C_{q,s} eps^{beta(q,s)}` for
  `-3/2 < s < 0`: the homogeneous form of `eq:RnegativeScale` that the Fourier
  calculation produces, `paper/sections/04-whole-space.tex:70-76`.  At `q = 2`,
  `s = -1` this is the homogeneous insertion estimate of Proposition 4.6,
  `‖F_eps‖_{L^2_t dot H^{-1}_x} <= C eps^{1/2}`
  (`04-whole-space.tex:264-272`). -/
  packetNegativeHomogeneous : ∀ (q : ℝ≥0∞), 1 ≤ q → ∀ s : ℝ, -3 / 2 < s → s < 0 →
    ∀ ε ∈ Ioc (0 : ℝ) scaling.ε₀,
      Data.forceHomogeneousENorm q s
          (scaledForce P.force scaling.correction.x₀ scaling.correction.T ε) ≤
        ENNReal.ofReal (packetHomogeneousConst q s *
          ε ^ scaling.thresholds.exponent q.toReal s)
  /-- The constants `C_{q,s}` of `eq:RnegativeScale` for the correction force
  in its homogeneous form, `paper/sections/04-whole-space.tex:75`. -/
  correctionHomogeneousConst : ℝ≥0∞ → ℝ → ℝ
  /-- `‖H_eps‖_{L^q_t dot H^s_x} <= C_{q,s} eps^{beta(q,s)+1}` for
  `-3/2 < s < 0`.  At `q = 2`, `s = -1` this is
  `‖H_eps‖_{L^2_t dot H^{-1}_x} <= C eps^{3/2}`,
  `paper/sections/04-whole-space.tex:271`. -/
  correctionNegativeHomogeneous : ∀ (q : ℝ≥0∞), 1 ≤ q → ∀ s : ℝ, -3 / 2 < s → s < 0 →
    ∀ ε ∈ Ioc (0 : ℝ) scaling.ε₀,
      Data.forceHomogeneousENorm q s (scaling.correction.forceCorrection ε) ≤
        ENNReal.ofReal (correctionHomogeneousConst q s *
          ε ^ (scaling.thresholds.exponent q.toReal s + 1))

end BlowupDensity.Contracts.V1
