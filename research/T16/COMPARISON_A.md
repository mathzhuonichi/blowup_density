# T16 draft A comparison

## Paper clause to Lean field

The existential witnesses `θ`, `plateau`, `θRadius`, `η`, `ε₀`, `potential`,
and `correction` are parameters of the `Prop`-valued
`LocalDivergenceFreeCutoffAPI`.  They are existentially quantified, in that
order, by `localDivergenceFreeCutoffStatement`.  This is necessary because Lean
does not generate a data-valued projection from a structure in `Prop`.

| Paper clause | Lean spelling |
|---|---|
| Fixed coordinate ball whose closure is in a fundamental cube (`03-torus.tex:22-23`) | `cubeOrigin` and premise `Metric.closedBall x₀ r ⊆ fundamentalCubeInterior cubeOrigin` |
| `K_*` compact (`03-torus.tex:101-102`) | premise `IsCompact Kstar` |
| Scaled packet support lies in `x₀ + ε K_*` (`03-torus.tex:101-120`) | premise on `tsupport (localizedVelocity ε (t, ·))` and `periodicCopies (scaledSpatialSet x₀ ε Kstar)` |
| Reference is smooth near the ball and time `T` (`03-torus.tex:163-177`) | `ContDiffOn` premise on `(0,T+δ) × ball x₀ r` |
| Reference is periodic on the torus (`02-preliminaries.tex:28`) | `UnitSpatialPeriodsOn` premise |
| Reference is divergence free in the ball (`03-torus.tex:177`) | `spatialDivergence` premise restricted to the ball |
| Spatial smooth Urysohn cutoff (`03-torus.tex:167-174,181`) | `theta_smooth`, `theta_compactSupport` |
| Urysohn cutoff takes values in `[0,1]` (`03-torus.tex:171-172`) | `theta_nonneg`, `theta_le_one` |
| `θ=1` near `K_*` (`03-torus.tex:172,181`) | `plateau_open`, `prescribed_subset_plateau`, `theta_one` |
| Fixed compact spatial support (`03-torus.tex:168-172`) | `theta_radius_pos`, `theta_support` |
| Time cutoff is smooth and compactly supported (`03-torus.tex:173-174,182`) | `eta_smooth`, `eta_compactSupport` |
| Same Urysohn range for the time cutoff (`03-torus.tex:173-174`) | `eta_nonneg`, `eta_le_one` |
| `η=1` on `[-1,1]` (`03-torus.tex:182`) | `eta_one` |
| `supp η ⊂ (-2,2)` (`03-torus.tex:182`) | `eta_support` |
| “For sufficiently small `ε`” (`03-torus.tex:188`) | witness `ε₀` and `eps_pos` |
| `2 ε² < min(T,δ)` (`03-torus.tex:212`) | `eps_time` |
| Scaled spatial support lies strictly in the coordinate ball (`03-torus.tex:212`) | `eps_space` |
| Radial potential is smooth (`03-torus.tex:177-181`) | `potential_smooth` |
| Display `eq:potential` (`03-torus.tex:178-180`) | `potential_formula` |
| `∇×A=v` (`03-torus.tex:181,196-210`) | `potential_curl` |
| Display `eq:cutoff`, `w_ε=-∇×(η_ε θ_ε A)` (`03-torus.tex:183-187`) | `correction_formula` on the chosen coordinate ball |
| Zero extension is globally smooth (`03-torus.tex:188,212`) | `correction_smooth` |
| The resulting torus field is periodic (`03-torus.tex:188,212`) | `correction_periodic` |
| The correction is divergence free (`03-torus.tex:188,212`) | `correction_divergence_free` |
| Spatial and temporal support (`03-torus.tex:188-189,212`) | `correction_support` |
| `v+w_ε=0` on an open neighborhood of `supp U_ε(t)` during the active interval (`03-torus.tex:190-193,214-215`) | `correction_cancels`, with `t ∈ Ico (T-ε²) T` |

There is no universal numerical constant in Lemma `lem:potential`.  The two
real size witnesses introduced by the spelling, `θRadius` and `ε₀`, each have
an explicit positivity field.  No bound from `lem:correction` is included.

## Representation and specification choices

- The physical torus layer is a field on `ℝ³` with unit spatial periods.  This
  follows the Section 3 representation decision and the local `Paper1` layer.
- `periodicCopies S` is the union of all integer translates of `S`.  A nonzero
  periodic lift cannot have compact support in all of `ℝ³`, so the torus
  support clause is `tsupport w_ε ⊆ time-window × periodicCopies(local-ball)`.
  It is the physical-lift version of “one copy is supported inside the
  coordinate ball.”
- The unperiodized formula `eq:cutoff` is asserted on the chosen coordinate
  ball.  The separate `correction_periodic` and `correction_support` fields
  specify its global periodic extension.  Asserting the raw compact-cutoff
  formula at every `x : ℝ³` would contradict nonzero periodicity.
- The coordinate cube has an arbitrary lower corner `cubeOrigin`; it is not
  silently fixed to `[0,1]³`.
- Small scales use `ε ∈ Ioc 0 ε₀`, matching the registered I02 contract.  This
  is equivalent to the paper's “all sufficiently small positive `ε`” after
  decreasing the threshold.
- The active interval in `eq:bgzero` is exactly `[T-ε²,T)`, not all of `(0,T)`.
  The stronger all-presingular-time I02 clause uses that the packet is empty
  before its start; T16 does not need to restate that separate packet fact.
- The open neighborhood is represented in the physical lift.  Since both the
  packet and corrected background are periodic, this represents an open
  neighborhood on the quotient torus without introducing a second field type.
- The preceding Urysohn paragraph explicitly says the cutoff values lie in
  `[0,1]`; the four range fields preserve that clause even though the displayed
  lemma only repeats compact smoothness and the plateau/support conditions.
- No mean-zero conclusion is imposed on `w_ε`: it follows analytically for a
  periodic curl but is not a stated clause of `lem:potential` and is not needed
  for `eq:bgzero`.

The provisional T10 block makes the chosen coefficient representation visible:

- scalar coefficients live in `lp (Fin 3 → ℤ) 2`;
- vector coefficients use the Euclidean `PiLp 2` product;
- `periodicSobolevWeight s k = (1+4π²|k|²)^(s/2)`;
- `periodicHomogeneousWeight s k = |2πk|^s`, with the omitted zero mode set to
  zero;
- `IsPeriodicMeanZero` is exactly vanishing of every `k=0` component;
- `periodicMeanZeroPart z = z - periodicMean z`.

Every declaration in that block is marked “NEEDS REGISTRATION / TO BE ALIGNED
WITH T10.”  These definitions are not used to hide a missing T16 proposition.

## Ambiguities requiring reconciliation

1. T10 must decide the final names and whether a real conjugate-symmetric
   coefficient subtype is bundled into `PeriodicVectorDatum`.  Draft A relates
   data to a real physical field, which forces the symmetry semantically, but
   does not bundle it into the carrier.
2. T10 must decide whether total periodic Sobolev norms remain `ℝ≥0∞`-valued
   infima, as in Section 4 `Data.lean`, or are finite real norms on a bundled
   completed space.  Draft A follows the Section 4 fail-safe style.
3. The task dependency is only T10, while `eq:bgzero` mentions the scaled
   packet.  Draft A therefore quantifies an arbitrary `localizedVelocity`
   family and assumes its already-known scaled support for every positive
   scale.  T14/T15 can later discharge that premise without changing T16.
4. The paper writes `A(x,t)` and `U_ε(t)` informally, whereas the registered
   vocabulary is time-first.  All Lean fields use `(t,x)`.
5. The paper's phrase “supported inside the coordinate ball” is quotient-level.
   The chosen `periodicCopies` spelling should be checked against whatever
   single-copy support predicate T10/T13 register.
6. `potential_smooth` is local to the open ball, as the lemma states.  The
   Section 4 I02 contract assumes a globally smooth reference and exports a
   globally smooth potential; adopting that stronger hypothesis on T³ is
   possible but unnecessary.
7. The API is `Prop`-valued as requested, so data witnesses cannot be structure
   projections.  They are explicit parameters under the existential in the
   statement.  If registration instead wants downstream projection syntax, it
   will need a `Type`-valued witness structure plus a separate `Prop` predicate.

## Needs a lemma

- Radial potential on a convex ball: the displayed interval integral is smooth
  and its spatial curl is the divergence-free reference field.
- Smooth spatial Urysohn cutoff for a compact `K_*` inside an open reference
  ball, including `[0,1]` range, open plateau, and a support radius.
- Smooth one-dimensional cutoff with `[0,1]` range, value one on `[-1,1]`, and
  support in `(-2,2)`.
- Threshold selection: from `T,δ,r>0` and the fixed cutoff support, choose one
  `ε₀>0` satisfying both `2ε²<min(T,δ)` and `ε θRadius<r` for every
  `ε∈(0,ε₀]`.
- Smooth gluing by zero at the coordinate-ball boundary, followed by unit
  periodization; prove both global `ContDiff` and `UnitSpatialPeriodsOn`.
- Support transport through multiplication, spatial curl, scaling, and
  periodization, yielding the `periodicCopies` support inclusion.
- Divergence of the spatial curl is zero for the globally glued field.
- Plateau cancellation: on `[T-ε²,T)`, `η_ε=1`; near the scaled `K_*`,
  `θ_ε=1` with zero derivatives; hence `w_ε=-v` on an open neighborhood of the
  localized packet support.
- T10 alignment lemmas: the zero Fourier coefficient equals the cube mean;
  `periodicMeanZeroPart` has zero mode zero; uniqueness/finiteness of the
  weighted `lp` datum; and agreement of the datum infimum with the intended
  Fourier-series Sobolev and homogeneous norms.

## Section 4 counterpart

The counterpart is node I02:

- `verification/Contracts/V1/Correction.lean`, structure
  `BlowupDensity.Contracts.V1.CorrectionAPI` and proposition
  `correctionStatement`;
- `verification/Contracts/V2/Correction.lean`, whose
  `prescribed_subset_plateau` fixes the full prescribed `K_*` clause;
- `verification/Bindings/Correction.lean`, definition
  `BlowupDensity.Bindings.correction`.

Coincident T16 fields deliberately retain the I02 names:
`theta_smooth`, `theta_compactSupport`, `plateau_open`,
`prescribed_subset_plateau`, `theta_one`, `theta_radius_pos`, `theta_support`,
`eta_smooth`, `eta_compactSupport`, `eta_one`, `eta_support`, `eps_pos`,
`eps_time`, `eps_space`, `potential_smooth`, `potential_formula`,
`potential_curl`, `correction_formula`, `correction_smooth`,
`correction_divergence_free`, `correction_support`, and
`correction_cancels`.

The torus-only field is `correction_periodic`.  Conversely, the R³-only global
`correction_compactSupport` is intentionally absent: it is false for a nonzero
periodic physical lift.  I02's correction-force family `H_ε`, derivative and
norm bounds, corrected momentum residual, and perturbation-divergence export
belong to T17/T18 rather than this T16 statement.
