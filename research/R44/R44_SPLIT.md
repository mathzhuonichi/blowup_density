# R44 — Proposition 4.4 proof-route split (`prop:Rcritical2`)

Paper statement `paper/sections/04-whole-space.tex:136-144`; proof `:145-174`.
Reconciled API `research/R44/Spec.lean`
(`BlowupDensity.R44.Draft.RCritical2API`, nine fields); source gap table
`research/R44/COMPARISON.md` §4; decisions `RECONCILIATION.md`.

This table distinguishes the registered contract registry from research specs.
“Blocks stating” below means either the final nine-field R44 API or a clean
PDE-level intermediate.  The final API itself is already fully statable from
`Contracts.V1.Data`; all remaining hard items block its proof/binding, not its
well-formedness.

Lean delivered in this lane is
`NSFormalization.Section4.R44.Pieces`: three R44-specific scalar/constant
theorems.  The identical `ℝ≥0∞` power pin and C01 gate discharge are reused from
`R43.Pieces`, not copied.

## 0. Historical registration audit (lane 166 baseline)

The table below records the original split baseline. Lane 227 consumes the now
present A05 V2, C01 V4, A02 `exists_maximal'`, and A04
`extendsBeyond_of_memForceR'`; their old absence claims are historical.
The current proof status is in rows S2–S6 and the gap summary below.

`verification/contracts.json` has 26 entries.  The relevant scopes are:

| need | registry result | exact registered supply / exclusion |
|---|---|---|
| finite `L²_t H^{-1/2}` norm for `f ∈ 𝓕_ℝ` | **registered** | `D01.datum_lemmas_v2`, **V2**, field `forceSobolevENorm_ne_top`, with `s := -1/2`, `m := 0`, `q := 2`; inherited by `D01.datum_lemmas_v3`, V3 |
| C01 constant `C₁`, `criticalL3`, and the exact `ℝ≥0∞` nonlinear gate vocabulary | **registered** | `C01.energy_absorption_partial`, **V1**, fields `C₁`, `C₁_pos`, `trilinearAbsorbed`; this does not include eq:RH1 |
| ordinary energy bound eq:RL2 | **registered** | `C01.energy_absorption_partial_v3`, **V3**, field `l2Bound` (and `energyDifferentialBound`) |
| eq:RH1, `sobolevTwoFourier`, `h2TimeIntegralZeroDatum` | **not registered** | expressly excluded by the V3 scope; these are proposed **C01 V4** fields (`research/C01/Spec.lean:532,555,599`) |
| `‖u‖₃ ≤ Cemb‖u‖_{H^{1/2}}`, derivative/J `L³` embeddings | **not registered** | `A05.gradient_l6`, **V1**, contains only `gradientLSix`; the critical clauses in `research/A05/Spec.lean:366,384,406` require **A05 V2** |
| continuation `extendsBeyond` at finite `S` | **not proved or registered on this branch** | `A04.energy_high_partial_v2`, **V2**, stops at `highContinuationIntegral`; `extendsBeyond` is the proposed **A04 V3** field (`research/A04/Spec.lean:613`) |
| maximal solution family | **registered, conditional** | `A02.maximal_partial_v2`, **V2**, field `exists_maximal`; its A01 local-solution clause remains an explicit hypothesis |
| `J`, exact Bessel-weight identity, `H^{-1/2}` duality | **proved locally; not registered** | lane 218: `Section4/R44/JWeight.lean` defines the weighted-carrier `Jmul`, `Y/Z/B`, proves `weight_identity`, `force_pairing_le`, and `force_pairing_le'`; a later contract/binding lane is still owed |
| eq:Rcritical2 and first-exit closure | **absent as PDE result** | C01 V1–V3 explicitly exclude eq:Rcritical2; its scalar closure is now in `R44.Pieces`, but the PDE inequality is R44-owned gap G2 |

This corrects one stale statement in the reconciled comparison: registration gap
G6 there is now closed by `D01.datum_lemmas_v2` V2.  The registered field proves
finiteness only; it does not provide the time-slice/integral identity needed by
the energy argument.

## 1. Proof rows

Write, on a presingular interval,

```lean
Y t = ‖u(t)‖_{H^(1/2)}
Z t = ‖∇u(t)‖_{H^(1/2)}
B t = ‖f(t)‖_{H^(-1/2)}
```

as finite real norms coming from the appropriate Sobolev data.  These equations
are notation for the proposed datum-path definitions, not existing declarations.

### S1 — `J`-weighted identity and eq:Rcritical2 (G1 + G2, L)

Paper `:145-164`.  The clean PDE-level target is:

```lean
∀ t ∈ Set.Ioo (0 : ℝ) T,
  ∃ E' : ℝ,
    HasDerivAt (fun s => Y s ^ 2) E' t ∧
    (Y t ≤ theta * ν →
      E' + ν * Z t ^ 2 ≤
        C₂ * ν * Y t ^ 2 + C₃ * ν⁻¹ * B t ^ 2)
```

with `0 < theta`, `0 ≤ C₂`, `0 < C₃`, all universal.  Its analytic subrows are:

| subrow | exact need | owner / size / dependencies | blocker |
|---|---|---|---|
| S1a | define `J=(I-Δ)^(1/2)` on the datum carrier and prove `‖u‖²_{H^(3/2)} = Y² + Z²`, i.e. the exact weight identity, plus `abs ⟪f,Ju⟫ ≤ B * sqrt (Y²+Z²)` | **closed in lane 218**, `Section4/R44/JWeight.lean`; one satisfiable `JWeightDatum` restriction | no longer a proof blocker; registration remains |
| S1b | differentiate `Y²`, identify the `J`-weighted momentum pairing, remove pressure, and evaluate dissipation | **closed in lane 222**, `Section4/R44/EnergyIdentity.lean`; `energy_identity` for every classical solution, no extra analytic hypothesis | no longer a proof blocker; registration remains |
| S1c | `abs ⟪(u·∇)u,Ju⟫ ≤ C₀ * Y * (Y²+Z²)` | **R44-own G2**, L; depends on **A05 V2** (`velocityCriticalL3`, derivative/J critical embeddings) and G1 | blocks proving |
| S1c status | **closed (lane 220, `Section4/R44/TrilinearJ.lean`)**: `advection_pairing_le : abs (advectionJPairing h ha) ≤ trilinearConstJ * Y * (Y² + Z²)`, `trilinearConstJ = 3·criticalL3Const³`; carrier package `AdvectionJDatum` | R44 | — |
| S1d | Young/absorption under `Y ≤ theta*ν`, producing the displayed target | **R44-own G2**, S once S1a–c exist | blocks proving |

To feed S2 this must be assembled as one `E' : ℝ → ℝ` with
`IntervalIntegrable E' volume 0 S` on each `0 ≤ S < T`; the pointwise existential alone does not
discharge `Pieces.lean:162-163`.

No registered field supplies S1.  The unregistered implementation now supplies
S1a and S1b, while S1c--S1d remain open on this baseline.  `C01.energy_absorption_partial` V1 concerns
the `-Δu` test used by eq:RH1, not the `Ju` test.

### S2 — Grönwall, explicit radius, first exit (closed conditional only on S1)

Lane 227: `Section4/R44/Endpoint.lean`, `Y_bound_of_differential`.
The only named input is `RCritical2Differential w hf`: one `E' : ℝ → ℝ`,
`IntervalIntegrable E' volume 0 b` for every `0 ≤ b < T`, and precisely the
S1 derivative/conditional inequality on `Ioo 0 T`. Integrability is required on
closed **presingular** windows, not at a potentially singular classical endpoint.

The fixed universal constants are

```
theta = min R43.criticalConst (1 / (100 * (A05.criticalL3Const + 1)^3))
C₂ = 2, C₃ = 4
c = theta / (4 * (C₃ + 1)) = theta / 20
C = C₂ + 1 = 3
radius ν S = c * ν^(3/2 : ℝ) * exp (-(C*ν*S)).
```

All positivity and radius arithmetic are proved. S1d must supply the displayed
inequality at these fixed constants; this lane does not claim that derivation.
For `0 ≤ b < T`, `b ≤ S`, and the exact global inhomogeneous L² smallness
hypothesis, the result is `∀ t ∈ Icc 0 b, Y(slice w.velocity t) ≤ theta*ν/2`.

G3 is discharged here: `forceB_continuousOn`, `force_norm_eq_path`, and
`forceB_prefix_le`. The order-two force path supplied by `MemForceR` lowers to
order `-1/2`; datum uniqueness identifies its eLpNorm with the path infimum.
`eLpNorm_two_sq` and restriction monotonicity bound every `∫₀ᵇ B²` by the
square of the exact global force norm. No replacement force norm is assumed.
The velocity norm is continuous by `energyVelocity_smooth`; composition with
`projIcc` gives the global continuous extension required by `Pieces`.
`radius_forces_gronwall_small` and `criticalSquaredNormBound_radius` then close
first exit without any further analytic input.

### S3 — critical embedding and C01 absorption (closed from S2)

`velocity_dot_le_sobolev` proves the homogeneous-to-inhomogeneous comparison
on classical slices using the contractive Bessel-to-homogeneous map.
`absorption_of_differential` combines it with `A05.velocityCriticalL3` and
`R43.criticalL3_gate_enorm`. The fixed `theta ≤ R43.criticalConst` supplies
`C₁*Cemb*theta ≤ 1/4`, independently of viscosity. Thus the exact C01 gate is

```
ENNReal.ofReal A05.gradientL6Const * C01.criticalL3 (C01.slice w.velocity t)
  ≤ ENNReal.ofReal (ν / 4).
```

### S4 — finite H² budget and maximal endpoint gluing (closed from S3)

`maximal_absorption_of_differential` transfers the gate through A02's maximal
family. For every `0 < L ≤ S` with `ofReal L ≤ maximalLifespanR ν 0 f`,
`maximal_h2TimeIntegral_of_differential` gives the explicit C01 V4 budget

```
∫⁻ t in Ioo 0 L, sobolevENorm 2 (slice u t) ^ (2 : ℝ)
  ≤ ofReal (32*L*(forcePrimitive f L)^2
      + 32*(ν⁻¹)^2*∫ t in 0..L, l2Sq (slice f t)).
```

The unscaled force quantities are finite because `MemForceR f`; they are not
assumed small. `R43.MaximalEndpoint.maximal_h2TimeIntegral` (declaration in
namespace `R43`) reuses C01's uniform bound on shorter Ioc intervals and passes
to their union. No terminal value `u(L)` is assigned. G4 is closed by this
reuse, including the hypothetical finite maximal endpoint.

`maximal_squaredHTwoIntegral_of_differential` uses the existing G5 identity
`R43.enorm_npow_two_eq_rpow_two` and proves A04's integral is not top.

### S5 — exclude lifespan at or before S (closed from S4)

`rcritical2_endpoint_of_differential` uses unconditional A02
`exists_maximal'`. If the lifespan were at most `ofReal S`, it would be finite
and positive. Put `L = lifespan.toReal`; the maximal family supplies
`SolvesBelow` at L. S4 supplies its finite H² integral; unconditional A04
`extendsBeyond_of_memForceR'` gives `ofReal L < lifespan`, contradicting
`ofReal L = lifespan`. No restart/local-existence hypothesis is retained.

### S6 — exact a = 0 API and non-density (closed conditional only on S1)

The final conclusion is exactly

```
ENNReal.ofReal S < maximalLifespanR ν (fun _ => 0) f
```

under `MemForceR f` and
`forceSobolevENormL2 (-1 / 2) f < ENNReal.ofReal (radius ν S)`.
`rcritical2_endpoint` is an **instantiation skeleton**: it takes the universal
S1 provider and then has `RCritical2API.main`'s remaining binders. It is not an
unconditional proof, and no complete API witness is claimed.

`research/R44/axioms_endpoint.lean` proves `EndpointConformance.main` and
`EndpointConformance.nonDensityBallZero` in exact `Contracts.V1.Data`
vocabulary. The second is the specified contradiction with breakdown-set
membership. The same file proves zero force meets the actual strict radius
hypothesis, checks `A04.zeroSol` with `E' = 0`, and applies the new endpoint
at zero force after proving S1 for every zero-force solution by uniqueness.

## 2. Current gap summary (lane 227)

| id | current status | remaining obligation |
|---|---|---|
| G1 | closed locally by 218 | registration only |
| G2 | S1b closed by 222; S1 is the sole named input to 227 | S1c/S1d derivation and locally integrable derivative assembly |
| G3 | closed by 227 | none for endpoint proof |
| G4 | closed by reuse of R43 maximal-endpoint gluing and A02 family | none |
| G5 | closed by R43 natural-square/rpow pin | none |
| A05 V2 | present, consumed | no added hypothesis |
| C01 V4 | present, consumed | no added hypothesis |
| A02/A04 | unconditional implementation consumed | no local-solution or continuation input |
| S2–S6 | assembled, conditional only on `RCritical2Differential` | S1 provider, then final contract registration |

The unconditional Proposition 4.4 remains pending S1. The endpoint assembly
and its force-path, norm, gluing, and continuation obligations are proved.

## Status after lane 229 (2026-09-16)

**S1 (a–d), S2–S6, G2, G4, G5 closed in implementation.** `Section4/R44/Absorption.lean` (S1d: lane 228 adapted to lane 227's constants, monotonicity adapter `rCritical2Differential_of_classical`), `Endpoint.lean` (lane 227: S2–S6 conditional on S1), `Prop44.lean` (`rcritical2_endpoint_unconditional`; all nine `RCritical2API` field values with `c = theta/20`, `C = 3`, `radius ν S = theta/20·ν^{3/2}·e^{−3νS}`), `Section4/R41/NonDensityL2.lean` (the `q = 2` non-density clause, `s ≥ -1/2`). Earlier "pending" wording in the tables above is superseded. Registration: lane 231.
