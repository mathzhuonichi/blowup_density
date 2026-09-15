import Contracts.V1.Scaling

/-! Stable specification for the inserted family of Theorem 4.2.

Task `collaboration/tasks/R42.md`, graph node `R42`.  Version 1 fixes the
assembled conclusion of Theorem 4.2 (`thm:Rinsert`,
`paper/sections/04-whole-space.tex:31-43`) **except** the two clauses that need
the maximal-lifespan theory:

* `T^nu_{max,R}(a, g_eps) = T` (`04-whole-space.tex:34`), and
* the definite article of "*the* solution ... regular through `T + delta`"
  (`04-whole-space.tex:32`), i.e. `T + delta < T^nu_{max,R}(a, g)`.

Both are collected in the **unregistered** `InsertionLifespanAPI` at the end of
this file, with the reason recorded there.  Everything else Theorem 4.2 asserts
is a field of `InsertionFamilyAPI`, for one `eps`-family and one `eps0`.

## What this record composes

`InsertionFamilyAPI nu P` carries a registered `ScalingAPI nu P` (`I03.scaling`,
which itself carries the registered `CorrectionAPI nu P` of `I02.correction`,
which is stated over the registered `PacketAPI nu` of `I01.packet`) together
with the reference solution in the `D01` class `Data.ClassicalSolutionR`.  The
three displays of the proof (`04-whole-space.tex:47-49`)

  `u_eps = v + w_eps + U_eps`,  `p_eps = pi + P_eps`,  `g_eps = g + H_eps + F_eps`

are the `*_formula` fields; every remaining field is a conclusion of
Theorem 4.2 about that one family.

## The reference: `Data.ClassicalSolutionR`, not the bare smooth field

`CorrectionAPI` takes the reference as a plain smooth divergence-free field
solving the momentum equation on the open slab `(0, T+delta) x R^3`
(`Correction.lean`, fields `reference_smooth` through `reference_equation`).
This record takes the stronger, manuscript-literal hypothesis: a
`Data.ClassicalSolutionR nu a g (T + delta)`, the `D01` transcription of
`02-preliminaries.tex:28-36` and `prop:local`, whose `velocity` and `pressure`
are the `CorrectionAPI`'s `v` and `pi`.  Every hypothesis `I02` needs is a
consequence -- `Ioo 0 (T+delta) subset Ico 0 (T+delta)` for the two smoothness
and the divergence fields, and `momentum` is literally the same statement -- so
the composition is possible in this direction and not the other.  Four
conclusions of Theorem 4.2 are only available this way:

* `initial` (`u_eps(.,0) = a`, "the same initial velocity",
  `04-whole-space.tex:13, 53`) needs `ClassicalSolutionR.initial`;
* `incompressible` at `t = 0` needs `ClassicalSolutionR.divergence`, which holds
  on `Ico 0 (T+delta)`, while `CorrectionAPI.reference_divergence_free` starts
  at `Ioo`;
* `velocity_smooth` and `pressure_smooth` on `Ico 0 T` -- smoothness up to
  and including `t = 0`, one-sided there -- need
  `ClassicalSolutionR.velocity_smooth`/`pressure_smooth`, which hold on
  `Ico 0 (T+delta)`; `CorrectionAPI.reference_smooth` and
  `reference_pressure_smooth` are on the *open* slab `Ioo 0 (T+delta)` and
  reach no initial time;
* naming `a` at all -- the datum of the lifespan clauses -- needs a solution
  class.

## Time guards

The velocity conclusions carry `0 <= t < T` (`04-whole-space.tex:36, 38`;
`research/section4/STATEMENTS.md` 9.15): the inserted velocity lives on `[0,T)`
only.  `momentum` is imposed on `Ioo 0 T`, matching
`Data.ClassicalSolutionR.momentum` and `PacketAPI.navier_stokes`: the two-sided
`temporalDerivative` of a field smooth only on `[0,T) x R^3` need not exist at
`t = 0`.  The force conclusions carry no guard: `g_eps - g` is defined on all of
`(0,infinity)` and is generally nonzero after `T` ("Each rescaled force has time
support of length `O(eps^2)`, including any part after `T`",
`04-whole-space.tex:77`; clarification `C3`).

## The ball

The manuscript fixes "any nonempty open ball `B`" (`04-whole-space.tex:32`).
`CorrectionAPI` fixes a coordinate ball `ball x0 r` inside it (clarification
`C2`, `research/section4/STATEMENTS.md:342-344`), and that is the ball used
below through `InsertionFamilyAPI.ball`.  Every support conclusion stated in
`ball x0 r` transfers to a larger prescribed `B` by `Set.Subset.trans`, so
nothing is lost.

## Self-containedness

Only `Contracts.V1.Scaling` is imported, hence transitively
`Contracts.V1.{Correction, Packet, Data, Thresholds}`.  No notion is copied:
`scaledPacket`, `scaledPressure`, `scaledForce`, `navierStokesResidual`,
`spatialDivergence`, `SpeedUnboundedAt` come from those contracts, and the
norms, the force class `F_c` and the solution class come from
`Contracts.V1.Data`.  `verification/Bindings/InsertionFamily.lean` therefore
carries no new `rfl` bridge; the bridges of `Bindings/{Correction, Scaling}`
already pin every notion used here.

No field is a hypothesis about an unspecified proposition, and no field is
`True`, `exists x, True` or any similar placeholder.
-/

noncomputable section

namespace BlowupDensity.Contracts.V1

open Set MeasureTheory Filter Topology
open scoped ContDiff ENNReal

/-- Theorem 4.2 (`thm:Rinsert`, `paper/sections/04-whole-space.tex:31-43`) for
one `eps`-family, minus the two lifespan clauses of `InsertionLifespanAPI`.

Layout of the fields.

* `scaling ... reference_pressure`: the ambient data.  The registered `I03`
  record supplies `T`, `delta`, the ball `B = ball x0 r`, the packet rescalings
  `U_eps, P_eps, F_eps`, the correction `w_eps`, the correction force `H_eps`
  and all their bounds; `reference` is the `D01` solution whose velocity and
  pressure are `I02`'s `v` and `pi`.
* `eps0 ... eps_le_scaling`: the single scale threshold, at or below `I03`'s.
  It is strictly below in the implementation: `R42` must additionally fit the
  *force* carrier `x0 + eps K_*` inside `B`, and `I03`'s `eps_space` calibrates
  only the *velocity* carrier.  See `research/R42/COMPARISON.md`.
* `velocity, pressure, force` and the three `*_formula` fields: the displays
  `04-whole-space.tex:47-49`.
* `velocity_smooth ... history`: the inserted triple is a classical trajectory
  on `[0,T)` with the reference's initial value and earlier history,
  `04-whole-space.tex:36, 50-52`.
* `velocityDifference_support ... forceDifference_ball`: the localization
  clauses, `04-whole-space.tex:37-38` and `:51`.
* `blowup`, `energyRate`, `forceConvergence`: `04-whole-space.tex:35`,
  `eq:REclose` (`:39-41`) and `:42-43`. -/
structure InsertionFamilyAPI (ν : ℝ) (P : PacketAPI ν) where
  -- ### Ambient data
  /-- The registered `I03` record for the same viscosity and the same packet.
  It carries `I02`'s `CorrectionAPI`, hence the singular time `T`, the margin
  `delta`, the reference `(v, pi, g)`, the ball `B = ball x0 r`, the cutoffs,
  `w_eps`, `H_eps` and every bound of `eq:packetEscale`, `eq:wE`,
  `eq:packetFscale`, `eq:RpositiveScale` and `eq:RnegativeScale`.  Carrying the
  whole record is what makes "All of these conclusions hold for the same family
  of inserted solutions" (`paper/sections/04-whole-space.tex:43`) structural
  rather than an equation between separately produced families. -/
  scaling : ScalingAPI ν P
  /-- `a`, the initial velocity of `04-whole-space.tex:32`
  ("the solution for `a` in `X_R` and `g` in `F_R`"). -/
  a : Data.SpatialField
  /-- The reference is *the* classical solution for `(a, g)` on `[0, T+delta)`:
  "regular through `T + delta` for some `delta > 0`",
  `paper/sections/04-whole-space.tex:32`, in the `D01` class
  `Data.ClassicalSolutionR` (`02-preliminaries.tex:28-36`).  The nesting of the
  margin noted at `research/section4/STATEMENTS.md:333-337` is resolved as that
  file recommends: one `delta`, the `I02` margin, and a solution on
  `[0, T+delta)`. -/
  reference : Data.ClassicalSolutionR ν a scaling.correction.g
    (scaling.correction.T + scaling.correction.δ)
  /-- The reference velocity is `I02`'s `v`, so the correction, the cancellation
  `eq:bgzero` and `corrected_background` are about this very solution. -/
  reference_velocity : reference.velocity = scaling.correction.v
  /-- The reference pressure is `I02`'s `pi`. -/
  reference_pressure : reference.pressure = scaling.correction.π

  -- ### The single scale threshold
  /-- The `eps0` of "For all sufficiently small `eps > 0`",
  `paper/sections/04-whole-space.tex:32`.  One threshold, one family, every
  conclusion below. -/
  ε₀ : ℝ
  /-- `eps0 > 0`. -/
  eps_pos : 0 < ε₀
  /-- `eps0 <= eps0(I03)`: the inserted family is a sub-family of the scaling
  family, so every `I03` and `I02` bound is available on the whole range used
  here. -/
  eps_le_scaling : ε₀ ≤ scaling.ε₀

  -- ### The three displays of the proof
  /-- `eps |-> u_eps`, the inserted velocity. -/
  velocity : ℝ → VelocityField
  /-- `eps |-> p_eps`, the inserted pressure. -/
  pressure : ℝ → PressureField
  /-- `eps |-> g_eps`, the inserted force. -/
  force : ℝ → VelocityField
  /-- `u_eps = v + w_eps + U_eps`, the first display of
  `paper/sections/04-whole-space.tex:47`. -/
  velocity_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    velocity ε z = scaling.correction.v z + scaling.correction.correction ε z +
      scaling.U ε z
  /-- `p_eps = pi + P_eps`, the second display of
  `paper/sections/04-whole-space.tex:47`.  This is the manuscript's chosen
  *compact* pressure gauge: "The pressure difference may be chosen to be the
  compact scalar `P_eps`" (`04-whole-space.tex:51`), which is generally not the
  gauge produced by `Data.pressurePotential`. -/
  pressure_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    pressure ε z = scaling.correction.π z + scaling.P ε z
  /-- `g_eps = g + H_eps + F_eps`, the third display of
  `paper/sections/04-whole-space.tex:48`. -/
  force_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    force ε z = scaling.correction.g z + scaling.correction.forceCorrection ε z +
      scaling.F ε z

  -- ### A classical trajectory on `[0,T)` with the reference's past
  /-- `u_eps` is smooth on `[0,T) x R^3`, one-sided at `t = 0`: the smoothness
  half of "there are `g_eps` in `F_R` and a solution `u_eps`"
  (`paper/sections/04-whole-space.tex:32`), in the shape of
  `Data.ClassicalSolutionR.velocity_smooth`. -/
  velocity_smooth : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ContDiffOn ℝ ∞ (velocity ε)
      (Ico (0 : ℝ) scaling.correction.T ×ˢ (univ : Set Space))
  /-- `p_eps` is smooth on `[0,T) x R^3`. -/
  pressure_smooth : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ContDiffOn ℝ ∞ (pressure ε)
      (Ico (0 : ℝ) scaling.correction.T ×ˢ (univ : Set Space))
  /-- `u_eps(.,0) = a`: "The initial value and earlier history are unchanged",
  `paper/sections/04-whole-space.tex:53`; "the same initial velocity",
  `04-whole-space.tex:13`. -/
  initial : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ x : Space, velocity ε (0, x) = a x
  /-- `div u_eps = 0` on `[0,T)`, including `t = 0`.  The manuscript's
  `eq:NS` incompressibility for the inserted solution, transported from the
  reference (`Data.ClassicalSolutionR.divergence`) and from
  `CorrectionAPI.perturbation_divergence_free`. -/
  incompressible : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) scaling.correction.T, ∀ x : Space,
      spatialDivergence (velocity ε) t x = 0
  /-- `d_t u_eps + (u_eps.grad)u_eps - nu Laplacian u_eps + grad p_eps = g_eps`
  at every interior time before `T`: "expansion of the equation leaves only the
  cross-advection terms ... Thus the two terms vanish pointwise everywhere, and
  the equation is exact" (`paper/sections/04-whole-space.tex:51`).  The
  viscosity is the reference's own `nu`. -/
  momentum : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ioo (0 : ℝ) scaling.correction.T, ∀ x : Space,
      navierStokesResidual ν (velocity ε) (pressure ε) t x = force ε (t, x)
  /-- `u_eps = v` for `0 <= t <= T - 2eps^2`, the third display of
  `paper/sections/04-whole-space.tex:36`. -/
  history : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t : ℝ, 0 ≤ t →
    t ≤ scaling.correction.T - 2 * ε ^ 2 → ∀ x : Space,
      velocity ε (t, x) = scaling.correction.v (t, x)

  -- ### Localization inside the ball
  /-- "The velocity difference is supported inside `B` at every `t < T`",
  `paper/sections/04-whole-space.tex:37-38`. -/
  velocityDifference_support : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) scaling.correction.T,
      tsupport (fun x : Space => velocity ε (t, x) - scaling.correction.v (t, x)) ⊆
        Metric.ball scaling.correction.x₀ scaling.correction.r
  /-- `u_eps - v` is divergence free at every presingular time, including
  `t = 0`.  Not displayed in Theorem 4.2, but displayed in the torus twin,
  Theorem 3.6(iii) (`paper/sections/03-torus.tex:295, 332`), and consumed by
  Theorem 4.7 (`04-whole-space.tex:306, 308`);
  `research/section4/REVIEW.md:77-88` requires `R42` to export it.  Its source
  is `CorrectionAPI.perturbation_divergence_free`. -/
  velocityDifference_divFree : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) scaling.correction.T, ∀ x : Space,
      spatialDivergence (fun z => velocity ε z - scaling.correction.v z) t x = 0
  /-- `p_eps - pi = P_eps`, the compact pressure representative of
  `paper/sections/04-whole-space.tex:51`, in gauge-free pointwise form.  It is
  `pressure_formula` read as a difference, and it is what makes the next field
  a statement about a *compact* scalar. -/
  pressureDifference_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    pressure ε z - scaling.correction.π z = scaling.P ε z
  /-- The pressure difference is supported inside `B` at every `t < T`: the
  localization half of "the compact scalar `P_eps`",
  `paper/sections/04-whole-space.tex:51`.  Consumed by Theorem 4.7
  (`04-whole-space.tex:306`);
  `research/section4/REVIEW.md:77-88` requires `R42` to export it. -/
  pressureDifference_support : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) scaling.correction.T,
      tsupport (fun x : Space => pressure ε (t, x) - scaling.correction.π (t, x)) ⊆
        Metric.ball scaling.correction.x₀ scaling.correction.r
  /-- `g_eps - g` is in `C_c^infinity(R^3 x (0,infinity))`: "Both force
  corrections are globally smooth and spacetime compact, including across `T`"
  (`paper/sections/04-whole-space.tex:51`), which is the class
  `Data.MemForceCompact` (`F_c`, `04-whole-space.tex:185`).  Together with the
  next field this is the theorem's `g_eps - g in C_c^infinity(B x (0,infinity))`
  (`04-whole-space.tex:38`). -/
  forceDifference_compact : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    Data.MemForceCompact (fun z => force ε z - scaling.correction.g z)
  /-- The spatial half of `g_eps - g in C_c^infinity(B x (0,infinity))`,
  `paper/sections/04-whole-space.tex:38`: the whole spacetime support projects
  into `B`, at every time, including the part after `T`. -/
  forceDifference_ball : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ z ∈ tsupport (fun z => force ε z - scaling.correction.g z),
      z.2 ∈ Metric.ball scaling.correction.x₀ scaling.correction.r

  -- ### The three quantitative clauses
  /-- `limsup_{t up T} ‖u_eps(t)‖_infinity = infinity`,
  `paper/sections/04-whole-space.tex:35`, in the pointwise form
  `Contracts.V1.SpeedUnboundedAt` that `I01` and `I03` use for the packet and
  its rescaling (`PacketAPI.speed_unbounded`, `ScalingAPI.scaledBlowup`): at
  every level `M` and every left neighbourhood of `T` there is a presingular
  time and a point where `‖u_eps‖` exceeds `M`.

  *Relation to the displayed clause, and why this form is registered.*  In
  isolation the pointwise statement is the **weaker** one: an essential
  supremum exceeding `M` forces a positive-measure set of such points, hence a
  point, while a single point carries no measure.  Here the two are
  **equivalent** for every inhabitant of this record, because `velocity_smooth`
  is co-carried: for `t` in `Ioo 0 T` the slice `u_eps(t, .)` is continuous, so
  `exists x, M < ‖u_eps(t,x)‖` opens a nonempty open set on which the same
  strict inequality holds, and that set has positive Lebesgue measure, forcing
  the essential supremum above `M` as well.  The pointwise form is registered
  because `Contracts.V1.Data` fixes no spatial `L^infinity` norm and no
  left-hand `limsup`, and because it is exactly what the sources produce.

  Stating the manuscript's display literally would need three `D01` additions:
  a spatial `L^infinity` e-norm (`eLpNorm . top volume` on the slice), the left
  limit `limsup ... (nhdsWithin T (Iio T)) = top`, and the bridge "continuous
  slice implies `essSup = supremum over x of ‖.‖`".  With those, this field
  yields the display immediately.  The deviation from
  `research/section4/STATEMENTS.md:255-258` is recorded in the registry scope.

  The background contributes nothing: `v + w_eps` vanishes on a neighbourhood
  of `supp U_eps(t)` (`eq:bgzero`), so at the witness points
  `u_eps = U_eps`. -/
  blowup : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    SpeedUnboundedAt scaling.correction.T (velocity ε)
  /-- `‖u_eps - v‖_{E_T} <= (M + D) eps^{1/2} + C eps^{3/2}`, the display
  `eq:REclose`, `paper/sections/04-whole-space.tex:39-41`, with `M, D` the
  packet constants of Lemma 2.2 (`PacketAPI.energyBound`,
  `PacketAPI.dissipationBound`) and `C` the `eps`-independent constant of
  `eq:wE` carried by `I03` (`ScalingAPI.correctionEnergyConst`).  The norm is
  the canonical `ENNReal`-valued `Data.energyENorm`, so the bound cannot be met
  vacuously. -/
  energyRate : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    Data.energyENorm scaling.correction.T
        (fun z => velocity ε z - scaling.correction.v z) ≤
      ENNReal.ofReal ((P.energyBound + P.dissipationBound) * ε ^ ((1 : ℝ) / 2) +
        scaling.correctionEnergyConst * ε ^ ((3 : ℝ) / 2))
  /-- "For `q` in `{1,2}` the force difference tends to zero in `L^q_t H^s_x`
  whenever `s < 2/q - 3/2`", `paper/sections/04-whole-space.tex:42`, along
  `eps` decreasing to zero.  The exponent is `ThresholdAPI.exponent q 0 = s_q`;
  the norm is `Data.forceSobolevENorm`, over the manuscript's `(0,infinity)`, so
  convergence also asserts eventual finiteness. -/
  forceConvergence : ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ,
    s < scaling.thresholds.exponent q.toReal 0 →
      Tendsto (fun ε : ℝ => Data.forceSobolevENorm q s
          (fun z => force ε z - scaling.correction.g z))
        (𝓝[>] 0) (𝓝 0)

/-! ## Named projections -/

namespace InsertionFamilyAPI

variable {ν : ℝ} {P : PacketAPI ν} (A : InsertionFamilyAPI ν P)

/-- The singular time `T` of `paper/sections/04-whole-space.tex:32`. -/
def T : ℝ := A.scaling.correction.T

/-- The regularity margin `delta`, `paper/sections/04-whole-space.tex:32`. -/
def margin : ℝ := A.scaling.correction.δ

/-- The reference velocity `v`, `paper/sections/04-whole-space.tex:32`. -/
def v : VelocityField := A.scaling.correction.v

/-- The reference pressure `pi`, `paper/sections/04-whole-space.tex:32`. -/
def π : PressureField := A.scaling.correction.π

/-- The reference force `g`, `paper/sections/04-whole-space.tex:32`. -/
def g : VelocityField := A.scaling.correction.g

/-- The coordinate ball `B = ball x0 r` of `paper/sections/04-whole-space.tex:32`,
inside the prescribed nonempty open ball (clarification `C2`). -/
def ball : Set Space :=
  Metric.ball A.scaling.correction.x₀ A.scaling.correction.r

/-- `u_eps - v = w_eps + U_eps`, the velocity difference of
`paper/sections/04-whole-space.tex:37-41`. -/
def velocityDifference (ε : ℝ) : VelocityField := fun z => A.velocity ε z - A.v z

/-- `g_eps - g = H_eps + F_eps`, the force difference of
`paper/sections/04-whole-space.tex:38, 42`. -/
def forceDifference (ε : ℝ) : VelocityField := fun z => A.force ε z - A.g z

end InsertionFamilyAPI

/-! ## The existential form consumed downstream -/

/-- What `R41D`, `R46` and `R47` receive from `R42`: given a packet, the
registered `I03` record for that packet, and a classical reference solution on
`[0, T+delta)` whose velocity and pressure are the ones `I02` corrected, the
whole inserted family exists on the **same** scaling record and on a sub-family
of the same `eps`-family.

`A.scaling = S` is an equation, not an existential: the inserted family is built
from the very `w_eps`, `H_eps`, `U_eps`, `P_eps`, `F_eps` that `I02` and `I03`
produced, which is what "All of these conclusions hold for the same family of
inserted solutions" (`paper/sections/04-whole-space.tex:43`) asserts.  The one
thing `R42` reserves is the right to shrink the scale threshold, recorded inside
`InsertionFamilyAPI` as `eps_le_scaling`.

Introducing this definition asserts nothing. -/
def insertionFamilyStatement : Prop :=
  ∀ (ν : ℝ) (P : PacketAPI ν) (S : ScalingAPI ν P) (a : Data.SpatialField)
    (R : Data.ClassicalSolutionR ν a S.correction.g (S.correction.T + S.correction.δ)),
    R.velocity = S.correction.v → R.pressure = S.correction.π →
      ∃ A : InsertionFamilyAPI ν P, A.scaling = S ∧ A.a = a

/-! ## The lifespan clauses: stated, deliberately **not** registered -/

/-- The two clauses of Theorem 4.2 that `InsertionFamilyAPI` omits
(`paper/sections/04-whole-space.tex:32, 34`).

**This structure is deliberately not registered in
`verification/contracts.json`, because it is not proved.**  Both fields need
task `A02` (uniqueness and the maximal classical solution, `prop:local`,
`02-preliminaries.tex:105`), which has no contract yet, and the second
additionally needs `A03`'s `‖z‖_infinity <= C‖z‖_{H^2}`
(`eq:Rproduct`, `appendix-a-local-theory.tex:9-13`), registered as
`A03.bounded_representative` in the jet form of
`Contracts.V1.BoundedRep.BoundedRepresentativeAPI`.

* `referenceLifespan` is the definite article of "*the* solution for `a` in
  `X_R` and `g` in `F_R`, regular through `T + delta`"
  (`04-whole-space.tex:32`): the reference must be *the* maximal solution, so
  its lifespan must exceed `T + delta`.  `Data.maximalLifespanR` is a supremum
  over horizons carrying *a* classical solution, so from
  `InsertionFamilyAPI.reference` alone one gets only the lower bound
  `ofReal (T+delta) <= maximalLifespanR nu a g`, with no uniqueness; the strict
  inequality and the identification of the solution are `A02`'s.

* `lifespan` is `T^nu_{max,R}(a, g_eps) = T` (`04-whole-space.tex:34`).  The
  proof (`04-whole-space.tex:52-54`) has two halves.  `>= T` needs
  `prop:local`'s uniqueness to identify the constructed `u_eps` with the maximal
  solution -- `InsertionFamilyAPI` supplies the constructed trajectory
  (`velocity_smooth`, `initial`, `incompressible`, `momentum`) but not the two
  remaining fields of `Data.ClassicalSolutionR`, `sobolev` and
  `pressure_gradient`, nor `g_eps in F_R`; see `research/R42/COMPARISON.md`.
  `<= T` is the continuation argument: an extension through `T` would be
  bounded in `C_t H^2` near `T`, hence in `L^infinity_x` by `A03`, contradicting
  `InsertionFamilyAPI.blowup`.  That step needs `A02`'s continuation criterion
  in a form that no registered contract states. -/
structure InsertionLifespanAPI (ν : ℝ) (P : PacketAPI ν) where
  /-- The inserted family whose lifespan the two clauses below describe. -/
  family : InsertionFamilyAPI ν P
  /-- "*The* solution for `a` in `X_R` and `g` in `F_R`, regular through
  `T + delta`", `paper/sections/04-whole-space.tex:32`; the field
  `referenceLifespan` of `research/section4/STATEMENTS.md:245`. -/
  referenceLifespan :
    ENNReal.ofReal (family.T + family.margin) <
      Data.maximalLifespanR ν family.a family.g
  /-- `T^nu_{max,R}(a, g_eps) = T`, the first display of
  `paper/sections/04-whole-space.tex:34`. -/
  lifespan : ∀ ε ∈ Ioc (0 : ℝ) family.ε₀,
    Data.maximalLifespanR ν family.a (family.force ε) =
      ENNReal.ofReal family.T

end BlowupDensity.Contracts.V1
