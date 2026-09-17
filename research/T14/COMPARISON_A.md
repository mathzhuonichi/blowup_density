# T14 draft A comparison

## Paper clause to Lean field

`TorusPacketEnergyAPI nu` extends the already registered
`BlowupDensity.Contracts.V1.PacketAPI nu`.  “Inherited” below therefore means
the field is reused literally, with no T14 restatement.

| Paper clause | Source | Draft A statement |
|---|---|---|
| `∀ ν > 0, ∃ (U,P,F,K)` | `01-introduction.tex:15-19` | `torusPacketEnergyStatement`; the chosen form is `TorusPacketEnergyFamily.select : ∀ nu, 0 < nu → ...` |
| Fields `U`, `P`, `F`, compact `K` | `01-introduction.tex:16-19` | inherited `velocity`, `pressure`, `force`, `carrier`, `carrier_compact` |
| `U,P` smooth on `R³ × [0,1)` and `F ∈ C_c^∞(R³ × (0,∞))` | `01-introduction.tex:16-19,61-63` | inherited `velocity_smooth`, `pressure_smooth`, `force_smooth`, `force_support` |
| One spatial carrier for `supp U(t) ∪ supp P(t)` | `01-introduction.tex:24-25` | inherited `velocity_support`, `pressure_support` |
| Momentum equation, divergence free, zero initial velocity | `01-introduction.tex:20-23` | inherited `navier_stokes`, `divergence_free`, `zero_initial_velocity` |
| Unbounded speed as `t ↑ 1` | `01-introduction.tex:26-29` | inherited `speed_unbounded` |
| `M := sup_{0≤t<1} ‖U(t)‖₂ < ∞` | `02-preliminaries.tex:127-131` | inherited real datum `energyBound`, `square_integrable`, and exact `energy_isLUB` |
| `D := ‖∇U‖_{L²((0,1)×R³)} < ∞` | `02-preliminaries.tex:127-132` | inherited real datum `dissipationBound`, `dissipation_integrable`, and `dissipation_eq` |
| `N(t) := ∫₀ᵗ ‖F(s)‖₂ ds` | `02-preliminaries.tex:141` | local `packetForceAccumulation`; flagged for T14 registration |
| `‖U(t)‖₂² + 2ν∫₀ᵗ‖∇U‖₂² ≤ 2∫₀ᵗ‖F‖₂N = N(t)²` | `02-preliminaries.tex:145-149`, `eq:packetenergy` | new `packet_energy`; the two relations in the chained display are a conjunction under the same `∀ t ∈ [0,1)` |
| A common initial interval on which `F,U,P` vanish | `02-preliminaries.tex:133,152` | inherited `quietTime`, `quiet_pos`, `quiet_lt_one`, `force_quiet`, `velocity_quiet`, `pressure_quiet` |
| Smooth zero extensions of `U,P` to negative time | `02-preliminaries.tex:133,152`; consumed at `03-torus.tex:109-111,141` | inherited `velocity_extension_smooth`, `pressure_extension_smooth` |
| Force is the smooth zero extension at nonpositive source time | `03-torus.tex:108-109` | inherited `force_zero_nonpos` together with `force_smooth` |
| The zero-extended fields still satisfy the equation and incompressibility | consumer at `03-torus.tex:123,141` | inherited `extension_navier_stokes`, `extension_divergence_free` |

The “Consequently” nonexistence conclusion of `thm:packet`
(`01-introduction.tex:30-33`) is not consumed by Section 3 and remains outside
the API, matching the registered I01 contract.

## Choices in draft A

- The imported object remains the Euclidean packet.  Compact support is the
  reason its sufficiently small rescaling can be placed in a coordinate ball;
  `03-torus.tex:101-120` performs the rescaling, placement, and periodization.
  An arbitrary unscaled compact carrier need not lie in one unit fundamental
  cube, so this draft does not assert an unscaled torus periodization.
- No T10 periodic-field or weighted `lp (Fin 3 → ℤ) 2` definition is copied.
  The weight `(1 + 4π²|k|²)^(s/2)` first matters for the periodic Sobolev
  estimate in T13/T15, not for the Euclidean source energy in T14.
- Spatial `L²` norms are represented by `Real.sqrt (l2Sq field t)`, exactly as
  in registered `PacketAPI.energy_isLUB`.  The gradient-square integrand is the
  registered `dissipation`.
- The paper's integrals from `0` to `t` are set integrals over `Ioc 0 t`.
  Since the draft quantifies `t ∈ Ico 0 1`, there is no orientation issue, and
  endpoints are null.
- The chained display `A ≤ B = C` is encoded as `(A ≤ B) ∧ (B = C)`.  This
  preserves both relations instead of weakening the display to `A ≤ C`.
- Finiteness of `M` and `D` is represented by real-valued data plus their exact
  characterizations and integrability fields.  No `ℝ≥0∞` infinity value can
  occur.
- `TorusPacketEnergyAPI` structurally extends `PacketAPI` rather than copying
  all of its data and proposition fields.  This makes literal reuse mechanically
  visible and leaves only `packet_energy` as the new T14 obligation.

## Ambiguities and scope boundaries

1. The label `thm:packet` occurs at `01-introduction.tex:15`, not in
   `03-torus.tex`; Section 3 imports and rescales it.  Draft A follows the
   actual source location.
2. `lem:packetenergy` is likewise a Euclidean statement.  There is no new
   torus energy integral at T14.  The torus-specific facts are the later
   single-copy change-of-variables identities in `eq:packetEscale`
   (`03-torus.tex:125-128`), which belong to T15.
3. The paper writes a pointwise supremum for `M`, whereas the later scaling
   proposition writes an `L∞` time norm.  Registered I01 chose `IsLUB` of the
   pointwise continuous slice norms.  Equality with the essential supremum is
   a downstream lemma, not an additional definition here.
4. `eq:packetenergy` is stated in the proof rather than in the one-sentence
   lemma header, but T14's task card explicitly requires the exact inequality,
   so it is a field.
5. The pressure is fixed to zero on the quiet interval using compact spatial
   support.  This is stronger than merely obtaining a spatially constant
   pressure and is already recorded by I01.
6. `PacketAPI` also records that the zero-extended triple solves the equation
   and remains divergence free.  These are consumer-ready consequences rather
   than extra torus assumptions; Draft A inherits rather than duplicates them.

## Needs a lemma

- Prove `packet_energy` for `Bindings.packet nu hnu`: the local energy identity,
  compact-support integration by parts, the regularized square-root estimate,
  and monotone convergence are the steps in
  `02-preliminaries.tex:136-150`.
- Prove the exact right-hand equality
  `2 ∫₀ᵗ ‖F(s)‖₂ N(s) ds = N(t)^2`, including absolute continuity of `N`.
- Bridge `PacketAPI.energy_isLUB` to the essential `L∞(0,1;L²)` norm used by
  `eq:packetEscale`; continuity of packet slices should remove the pointwise /
  essential-supremum gap.
- In T15, prove that after the rescaled carrier lies in the fixed coordinate
  ball, periodization contains exactly one copy and preserves the spatial
  `L²` and gradient integrals.
- Register `packetForceAccumulation` (or align its final name with the accepted
  T14 contract) and extend the existing binding by the proved
  `packet_energy` field.

## Section 4 counterparts and verbatim reuse

- `verification/Contracts/V1/Packet.lean`: `PacketAPI` is the direct contract
  counterpart.  Every inherited field listed in the table is reusable
  verbatim; in particular `M`, `D`, quietness, and both smooth zero extensions
  are not torus redefinitions.
- `verification/Bindings/Packet.lean`: `Bindings.packet nu hnu` is the selected
  packet to reuse.  It supplies the entire inherited base object.  T14 needs
  only a proof of the new `packet_energy` field to upgrade it to Draft A's API.
- `formalization/NSFormalization/Section4/I01/Energy.lean` supplies the exact
  least upper bound used for `M`.
- `formalization/NSFormalization/Section4/I01/Quiet.lean` supplies the common
  interval for `F,U,P`.
- `formalization/NSFormalization/Section4/I01/Extension.lean` supplies the
  smooth negative-time extensions and the extended equation/divergence facts.

Thus `lem:packetenergy` adds no genuinely torus-native clause.  Relative to the
registered Section 4 API, Draft A adds exactly its displayed energy chain.  The
torus construction reuses all packet fields after T15 has made the support a
single periodized copy.
