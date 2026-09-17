# T14 reconciled comparison

This file merges the independent comparisons from lanes 273 (Draft A) and 274
(Draft B) under the binding rulings in `research/T14/RECONCILIATION.md`.  T14
imports the already registered Euclidean packet; the torus placement and
periodization begin only at `paper/sections/03-torus.tex:101-123`.

## Paper clause → Lean field, provenance, and ruling

“Inherited” means a literal field of
`BlowupDensity.Contracts.V1.PacketAPI ν`, not a T14 restatement.

| Paper clause | Source | Draft A | Draft B | Reconciled statement / ruling |
|---|---|---|---|---|
| For every `ν > 0`, choose packet data | `01-introduction.tex:15-19,61-67`; consumed at `03-torus.tex:101-111` | `torusPacketEnergyStatement`; selected `TorusPacketEnergyFamily.select` | `packetImportStatement`; no selected family | Keep B's `packetImportStatement` and A's data-carrying family, renamed `PacketImportFamily`; quantifier order is `∀ ν, 0 < ν → ...`. |
| Data `U,P,F,K` | `01-introduction.tex:16-19,24-25` | inherited | inherited | Inherited `velocity`, `pressure`, `force`, `carrier`; no duplicate data. |
| Positive viscosity belongs to the same packet | `01-introduction.tex:16` | inherited | inherited | Inherited `viscosity_pos`; the outer positivity hypothesis is retained in both final existence/family forms. |
| `U,P` smooth on `R³×[0,1)`; `F ∈ C_c∞(R³×(0,∞))` | `01-introduction.tex:16-19,61-63` | inherited | inherited | Inherited `velocity_smooth`, `pressure_smooth`, `force_smooth`, `force_support`. |
| One compact spatial carrier for the velocity and pressure slices | `01-introduction.tex:17-18,24-25` | inherited | inherited | Inherited `carrier_compact`, `velocity_support`, `pressure_support`. |
| Momentum equation, incompressibility, zero initial velocity | `01-introduction.tex:20-23` | inherited | inherited | Inherited `navier_stokes`, `divergence_free`, `zero_initial_velocity`. |
| Speed becomes unbounded at the singular time | `01-introduction.tex:26-29`; consumed at `03-torus.tex:122-123` | inherited | inherited | Inherited `speed_unbounded`. |
| `M := sup_{0≤t<1} ‖U(t)‖₂ < ∞` | `02-preliminaries.tex:127-131` | inherited exact real datum and `IsLUB` | same | Inherited `energyBound`, `square_integrable`, `energy_isLUB`; no weaker arbitrary bound. |
| `D := ‖∇U‖_{L²((0,1)×R³)} < ∞` | `02-preliminaries.tex:127-132` | inherited exact real datum/integral | same | Inherited `dissipationBound`, `dissipation_integrable`, `dissipation_eq`. |
| `N(t) := ∫₀ᵗ ‖F(s)‖₂ ds` | `02-preliminaries.tex:141` | `packetForceAccumulation`, using `Ioc` | `accumulatedForce`, using `Ioo` | Keep B's name and `Ioo`, as explicitly ruled.  Lebesgue-null endpoints make the paper readings agree. |
| `‖U(t)‖₂² + 2ν∫₀ᵗ‖∇U‖₂² ≤ 2∫₀ᵗ‖F‖₂N` for `0≤t<1` | `02-preliminaries.tex:145-148`; feeds `03-torus.tex:125-128` | first conjunct of `packet_energy` | `PacketEnergyAPI.energy_le_work` | Keep B's separate field over a given `P : PacketAPI ν`; exact factors `2ν` and `2`, with `∀ t ∈ Ico 0 1`. |
| `2∫₀ᵗ‖F‖₂N = N(t)²` | `02-preliminaries.tex:148` | second conjunct of `packet_energy` | `PacketEnergyAPI.work_eq_square` | Keep B's separate equality field.  This preserves both links of the printed chain. |
| The energy assertion constrains the imported packet itself | `02-preliminaries.tex:123-150` | one extended structure with a conjunction | predicate `PacketEnergyAPI P` and `PacketImportAPI.energy` | Keep B's packaging: the reusable `Prop` record is indexed by a concrete packet, and `PacketImportAPI.energy` applies it to `toPacketAPI`. |
| Common initial interval where `F,U,P` vanish | `02-preliminaries.tex:133,152` | inherited | inherited | Inherited `quietTime`, `quiet_pos`, `quiet_lt_one`, `force_quiet`, `velocity_quiet`, `pressure_quiet`. |
| `U,P` extend smoothly by zero to negative time | `02-preliminaries.tex:133,152`; used at `03-torus.tex:109-111,141` | inherited | inherited | Inherited `velocity_extension_smooth`, `pressure_extension_smooth`. |
| The globally represented force is zero at nonpositive source time | `03-torus.tex:108-109` | inherited | inherited | Inherited `force_zero_nonpos` together with `force_smooth` and `force_support`. |
| The zero-extended fields retain the PDE and incompressibility | consumed at `03-torus.tex:122-123,141` | inherited | inherited | Inherited `extension_navier_stokes`, `extension_divergence_free`. |
| The source packet is not yet a periodic field | placement at `03-torus.tex:101-120` | explicit scope boundary | explicit scope boundary | No T10 physical/coefficient object appears in a T14 declaration.  Single-copy periodization, pressure normalization, and torus norm identities belong to T15. |

The “Consequently” nonexistence clause after `thm:packet`
(`01-introduction.tex:30-33`) is not consumed by the Section 3 construction and
remains outside T14, matching the registered packet contract.

## Structural reconciliation

The final declarations are:

1. `accumulatedForce`, Draft B's `Ioo` definition of `N`;
2. `PacketEnergyAPI P : Prop`, with the two numerical fields from Draft B;
3. `PacketImportAPI ν extends PacketAPI ν`, with `energy` about the inherited
   packet;
4. `packetImportStatement`, Draft B's proposition in the paper's quantifier
   order; and
5. `PacketImportFamily`, Draft A's selected family under the binding final name.

Draft B also proposed the stronger helper
`packetEnergyStatement : ∀ (ν) (P : PacketAPI ν), PacketEnergyAPI P`.
The reconciliation's exhaustive selection in §3 names
`PacketEnergyAPI`/`PacketImportAPI`/`packetImportStatement` plus
`PacketImportFamily`, so the universal helper is not in `Spec.lean`.  The
predicate remains independently reusable without asserting that stronger
theorem as part of the specification.

## T10 vocabulary reuse

`Spec.lean` starts with the same imports as `research/T10/Spec.lean`
(`Contracts.V1.Data` and `Mathlib.Analysis.Fourier.AddCircleMulti`) and then
imports `Contracts.V1.Packet`.  A `research/` source file is not an importable
Lake module, so T14 does not import T10 by file path.

The minimal copied subset of T10 is empty.  This is substantive, not an
omission: the binding reconciliation says the object is still the Euclidean
source packet, and every type in its energy display comes from the registered
`PacketAPI`.  Therefore no local copy of `PeriodicSobolev`, `IsPeriodicDatum`,
`periodicSobolevENorm`, `IsPeriodicHomogeneousDatum`,
`periodicHomogeneousENorm`, `meanT`, `torusLift`, or
`periodicFourierCoeff` is permitted or needed.  T14 thereby reuses the T10
vocabulary boundary without creating a competing periodic vocabulary.

## Proof dependencies

The proof/registration lane can enhance the already selected
`BlowupDensity.Bindings.packet ν hν`; it must not replace the inherited packet.
The exact dependency surface is:

1. `verification/Bindings/Packet.lean:104` supplies the concrete
   `PacketAPI ν`, including exact `M/D`, quietness, and zero-extension fields.
   The latter come from
   `Section4/I01/Energy.exists_l2_isLUB`,
   `Section4/I01/Quiet.exists_packet_quiet`, and
   `Section4/I01/Extension.extension_smoothOn` /
   `extension_navierStokes` / `extension_divergence_free`; T14 need not reprove
   them.
2. `NSFormalization.Source.PacketEnergy.packet_energy`
   (`Source/PacketEnergy.lean:143`) derives
   `E(t)+2ν∫₀ᵗd(s)ds ≤ N(t)²` from the compact packet PDE.  Its scalar core is
   `NSFormalization.Paper1.energy_add_dissipation_le_primitive_sq`
   (`Paper1/ScalarEnergy.lean:180`), which itself uses the zero-data
   `sqrt_energy_le_primitive` (`ScalarEnergy.lean:77`).  These are the exact
   Grönwall-free lemmas anticipated by the reconciliation; the generalized
   wrapper `Section4/C01.sqrt_energy_le_primitive'`
   (`C01/EnergyBounds.lean:180`) is not needed for zero initial data.
3. An adapter must restrict the registered smoothness/support/PDE fields to
   each compact slab `[0,b]`, `b<1`, provide a compact spatial carrier for force
   slices from `PacketAPI.force_support`, and bridge the contract definitions
   `l2Sq`, `dissipation`, and residual to the source definitions.  Existing
   `Bindings/Packet.lean` already has the three relevant `rfl` bridges
   `l2Sq_eq`, `dissipation_eq`, and `navierStokesResidual_eq_source`.
4. A small FTC lemma is still needed: for
   `b(t)=sqrt (l2Sq F t)` and `N(t)=∫₀ᵗb`, prove
   `2∫₀ᵗ b(s)N(s) ds=N(t)^2`.  The ingredients are
   `Source.PacketEnergy.primitive_regular` plus Mathlib's product/FTC theorem
   `intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt` (or an equivalent
   derivative-of-`N²` argument).  Then convert interval integrals to the
   specification's `Ioo` set integrals using
   `intervalIntegral.integral_of_le` and
   `MeasureTheory.integral_Ioc_eq_integral_Ioo`.  Rewriting this equality in
   `Source.PacketEnergy.packet_energy` gives `energy_le_work`.
5. Assemble `PacketImportAPI ν`, then define `PacketImportFamily.select` from
   the same enhanced `Bindings.packet ν hν`; `packetImportStatement` follows by
   `Nonempty.intro`.

### Exact T10 lemma dependency

No T10 theorem is needed to prove either field of `PacketEnergyAPI`.  In the
numbered “Needs a lemma” list of `research/T10/COMPARISON.md`, the dependency
set for T14 is therefore **empty**: items 1–17 concern quotient-torus lifts,
Fourier data, means, Leray, pressure normalization, periodic energy, or periodic
classical solutions, none of which occurs in the T14 types.

For downstream scope only, T15's conversion of this packet to a periodic one
will need T10 item 1 (the `torusLift`/unit-cube Haar bridge), item 2 (physical
`L²` and full-gradient Parseval identities when moving to coefficients), and
item 12 / the eventual `TorusDataAPI.energy_eq_physical` field (physical versus
coefficient energy).  T13/T15's real-order `H^s` estimate additionally uses
item 3's exact periodic weight and smooth-data existence.  Those are not proof
hypotheses of T14 and are deliberately absent from `PacketEnergyAPI`.

## Open questions for the owner

1. Should the eventual registered contract expose Draft B's stronger universal
   `packetEnergyStatement` for every `PacketAPI`, or keep exactly the
   reconciliation's selected existential/family surface?  `Spec.lean` follows
   the binding §3 list and omits the universal theorem.
2. Should the proof lane register a reusable generic FTC lemma for
   `2∫ bN=N²`, or keep it private to the T14 binding?  The equality is the one
   genuinely new obligation not already packaged by
   `Source.PacketEnergy.packet_energy`.
3. Is the DAG edge `T10 → T14` intended only as a vocabulary/scheduling gate?
   The reconciled mathematical statement and proof use no periodic datum; the
   first exact T10 lemmas enter at T15.
4. The lane brief points to `03-torus.tex:21-60`, which is
   `lem:localization`, whereas `lem:packetenergy` is actually
   `02-preliminaries.tex:127-153`.  This spec cites the true source and also the
   exact Section 3 consumption lines.  Should the task metadata be corrected?
5. For registration, should T14 extend the existing `PacketAPI` in the T01
   bucket, or live in T02 beside the scaling consumer?  The statement is neutral
   but the reconciliation leaves the bucket as `T01/T02`.
