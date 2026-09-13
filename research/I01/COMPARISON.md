# I01 — Packet energy and early vanishing: source-to-target comparison

Draft specification: `research/I01/Spec.lean`, namespace `BlowupDensity.I01.Draft`,
structure `PacketAPI (ν : ℝ)` plus `packetStatement` and `PacketFamily`.

Target statements:

* restated Theorem 1.1 (`thm:packet`), `paper/sections/01-introduction.tex:15-34`;
* Lemma 2.2 (`lem:packetenergy`), `paper/sections/02-preliminaries.tex:127-153`;
* consumers: Proposition 3.3 (`prop:scaling`), `paper/sections/03-torus.tex:101-159`,
  and Theorem 4.2 (`thm:Rinsert`), `paper/sections/04-whole-space.tex:31-79`;
* force zero-extension convention `C1`,
  `logs/SOL_MAX_AUDIT_SYNTHESIS_20260912.md:51-73`.

Everything cited below as "existing" was read in this worktree; line numbers are
current as of commit `4ba9f2b`.

## What the consumers actually use

Listing the packet properties consumed downstream, so the record can be checked
for both completeness and absence of dead weight.

| Consumer | Packet property used | Location |
|---|---|---|
| `prop:scaling` | zero extension of `U,P` to negative time; zero extension of `F` | `03-torus.tex:108-119` |
| `prop:scaling` | momentum equation at viscosity `ν`, incompressibility, "start from zero" | `03-torus.tex:123, 141` |
| `prop:scaling` | `‖U_ε‖_{L^∞(0,T;L²)} = ε^{1/2}M`, `‖∇U_ε‖_{L²(0,T;L²)} = ε^{1/2}D` | `03-torus.tex:124-128` (`eq:packetEscale`) |
| `prop:scaling` | unbounded speed at `T` via `‖U_ε(t)‖_∞ = ε^{-1}‖U(σ)‖_∞` | `03-torus.tex:123, 141-143` |
| `prop:scaling` | spatial support of `U,P` and of `F` inside `K_*`, so `x₀+εK_* ⊂ B` | `03-torus.tex:101-107` |
| `prop:scaling` | `F` smooth, compactly supported in space-time, zero at negative source time | `03-torus.tex:108-109, 120` |
| `thm:Rinsert` | same list, without periodization; plus `u_ε = v` for `t ≤ T-2ε²`, which needs the *inactive past* of the zero extension | `04-whole-space.tex:20-29, 36, 53` |
| `thm:Rinsert` | `(M+D)ε^{1/2}` in `eq:REclose` | `04-whole-space.tex:39-41, 53` |
| `thm:Rinsert` | smoothness of `F_ε`, `H_ε` "across `T`", i.e. of the extension through the seam | `04-whole-space.tex:51` |

Not consumed by Section 4, and therefore deliberately **excluded** from
`PacketAPI`: the "Consequently ..." clause of Theorem 1.1
(`paper/sections/01-introduction.tex:30-33`, no global finite-energy smooth
solution).  In Lean that clause is
`¬ Nonempty NavierStokesR3.ProblemStatement.GlobalFiniteEnergySolution`
(`vendor/NavierStokesAndEuler/NavierStokes/R3/ProblemStatement.lean:125-135,150-153`),
it belongs to node `U01`, and Section 4 never invokes it: `thm:Rinsert` derives
breakdown from `SpeedUnboundedAtOne` plus `prop:local`, not from the OpenAI
nonexistence corollary.

## Field-by-field comparison

`SPE = formalization/NSFormalization/Source/SelectedPacketEnergy.lean`,
`VP  = formalization/NSFormalization/Source/ViscosityPacket.lean`,
`PE  = formalization/NSFormalization/Source/PacketEnergy.lean`,
`PEP = formalization/NSFormalization/Source/PacketEndpoint.lean`,
`PP  = formalization/NSFormalization/Source/PacketPressure.lean`,
`PFE = formalization/NSFormalization/Source/PacketForceExtension.lean`,
`PS  = formalization/NSFormalization/Source/PacketScaling.lean`,
`R3PS = vendor/NavierStokesAndEuler/NavierStokes/R3/ProblemStatement.lean`,
`PS0 = vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean`,
`R3CC = vendor/NavierStokesAndEuler/NavierStokes/R3CompactCandidate.lean`,
`R3CE = vendor/NavierStokesAndEuler/NavierStokes/R3/CompactEnergy.lean`.

Throughout, "**from `CandidateProperties`**" means: the field is literally a
projection of
`NavierStokesR3.ProblemStatement.CandidateProperties ν u p f K` (`R3PS:92-109`)
as produced by
`NSFormalization.Source.selected_packet_every_viscosity` (`VP:131-151`).

| Field | Paper claim and location | Existing declaration | Notes on mismatch |
|---|---|---|---|
| `velocity`, `pressure`, `force`, `carrier` | `u, p, f, K` of Thm 1.1, `01-introduction.tex:17-19`; renamed `(U,P,F)` at `01-introduction.tex:63-66` | `selected_packet_every_viscosity`, `VP:131-135` (existential over `u p f K`) | Existing statement is `∃`; the record turns it into named data. Section 4 needs one *fixed* packet per `ν`, hence `PacketFamily.select`; see split unit 8. |
| `energyBound` (`M`) | `M := sup_{0≤t<1}‖U(t)‖₂`, `02-preliminaries.tex:130` | **gap** (no declaration names `M`) | Only an *upper bound* exists (`UniformFiniteEnergy`, `R3PS:81-83`), and it bounds `kineticEnergy = ½∫‖u‖²` (`R3PS:76-77`), not `‖u(t)‖₂`. See `energy_isLUB`. |
| `dissipationBound` (`D`) | `D := ‖∇U‖_{L²((0,1)×ℝ³)}`, `02-preliminaries.tex:131` | **gap** (no declaration names `D`) | Integrability exists; the *number* `D` is nowhere defined. See `dissipation_eq`. |
| `quietTime` (`τ`) | `F = 0` on `[0,τ]` for some `τ>0`, proof of Lem. 2.2, `02-preliminaries.tex:152` | partial: the concrete selected packet has `τ = 3/8`, `SPE:52,78` (`∀ t, |t| ≤ 3/8 → …`), from `NavierStokes.TimeLocalization.activatedVelocity_zero_early` / `activatedPressure_zero_early`, `vendor/.../TimeLocalization.lean:57,61` | `3/8` is an artifact of the OpenAI time switch, not of the manuscript. The manuscript derives `τ` from compactness of `supp_t F` inside `(0,∞)`. Generic derivation is missing; see split unit 1. |
| `viscosity_pos` | "For every `ν>0`", `01-introduction.tex:16` | hypothesis `hν : 0 < ν` of `selected_packet_every_viscosity`, `VP:131` | Exact match. |
| `velocity_smooth` | `u` smooth on `ℝ³×[0,1)`, `01-introduction.tex:18-19` | from `CandidateProperties.velocity_smooth`, `R3PS:94` | `preSingularDomain = Ico 0 1 ×ˢ univ` (`PS0:42`); `ContDiffOn` relative to the closed-at-zero half domain, matching "smooth on `[0,1)`". `∞` is the `ContDiff` scope's "all finite orders", not analytic. |
| `pressure_smooth` | same, `01-introduction.tex:18-19` | from `CandidateProperties.pressure_smooth`, `R3PS:95` | Same convention. |
| `force_smooth` | `F ∈ C_c^∞(ℝ³×(0,∞))`, `01-introduction.tex:17`; smooth zero extension, `C1` | from `CandidateProperties.force_smooth`, `R3PS:101` (`ContDiff ℝ ∞ f`, global) | Global (not `futureDomain`-relative) smoothness. Produced by `PFE.zeroPast_smooth`, `PFE:15-32`, and transported to arbitrary `ν` by `viscosity_candidate_properties`, `VP:118-121`. This is exactly the `C1` extension. |
| `force_support` | compact support in `ℝ³×(0,∞)`, `01-introduction.tex:17-18, 61-63` | from `CandidateProperties.force_support`, `R3PS:102`; `CompactPositiveTimeSupport`, `R3PS:66-67`; built by `PFE.zeroPast_compact` `PFE:36-49` and `PFE.zeroPast_support_positive` `PFE:53-65` | Match. `tsupport f ⊆ Ioi 0 ×ˢ univ` is the closed-support reading of `C_c^∞` in an open set. |
| `carrier_compact` | `K ⊂ ℝ³` compact, `01-introduction.tex:17-18` | from `CandidateProperties.support_compact`, `R3PS:96` | `K = Ku ∪ Kp` in `SPE:99`, then `a • K` in `VP:139-140`; a single `K` for both fields, as the paper requires. |
| `velocity_support` | `supp u(·,t) ⊆ K`, `0≤t<1`, `01-introduction.tex:24-25` | from `CandidateProperties.velocity_support`, `R3PS:97-98` | `tsupport` (closure of nonzero set) is used, i.e. the paper's `supp`. Note `R3CC.Properties` (`R3CC:28-31`) states only the pointwise "zero outside `K`" form; `PEP.tsupport_subset_of_zero_outside`, `PEP:142-148`, bridges the two. |
| `pressure_support` | same, `01-introduction.tex:24-25` | from `CandidateProperties.pressure_support`, `R3PS:99-100` | Same bridge, `SPE:104-110`. |
| `zero_initial_velocity` | `u(·,0)=0`, `eq:packet`, `01-introduction.tex:22` | from `CandidateProperties.zero_initial_velocity`, `R3PS:103` | Exact match. |
| `divergence_free` | `∇·u=0`, `eq:packet`, `01-introduction.tex:22` | from `CandidateProperties.divergence_free`, `R3PS:104-105` | Imposed on `Ico 0 1` (including `t=0`), stronger than the interior-only reading; harmless. |
| `navier_stokes` | `∂_t u+(u·∇)u-νΔu+∇p=f`, `eq:packet`, `01-introduction.tex:20-23` | from `CandidateProperties.navier_stokes`, `R3PS:106-107`; residual `R3PS:57-62` | Imposed on the open interval `Ioo 0 1` only, matching "no derivative of an arbitrary extension at `t=0`". `ν` multiplies only the spatial Laplacian, as in `eq:NS`. `NSFormalization.Source.residual` (`Source/Insertion.lean:21-24`) is the *same* expression under a different name; the two are definitionally equal (`Source/Insertion.lean:26-28` records the `ν=1` case). |
| `speed_unbounded` | `limsup_{t↑1}‖u(t)‖_∞ = ∞`, `eq:packetblowup`, `01-introduction.tex:28` | from `CandidateProperties.speed_unbounded`, `R3PS:109`; `SpeedUnboundedAtOne`, `PS0:94-96` | Pointwise form `∀M>0 ∀δ>0 ∃t∈(0,1), 1-δ<t, ∃x, M<‖u(t,x)‖`. For continuous compactly supported slices this is equivalent to the `limsup` of the sup-norm being `∞`; the equivalence is asserted in the vendor docstring (`R3PS:85-87`) but **is not proved anywhere**. Not needed by Section 4, which only uses the pointwise form (`04-whole-space.tex:53`). Flagged, not a blocker. |
| `square_integrable` | implicit in `‖u(t)‖_{L²}`, `01-introduction.tex:27`, and `M`, `02-preliminaries.tex:130` | first component of `UniformFiniteEnergy` in `CandidateProperties.energy_bounded`, `R3PS:82-83`, proved in `PEP.compact_properties_uniform_finite_energy`, `PEP:171-183` | Exact match (`SquareIntegrableAtTime`, `R3PS:71-72`). |
| `energy_isLUB` | `M := sup_{0≤t<1}‖U(t)‖₂ < ∞`, `02-preliminaries.tex:130`; `sup_{0≤t<1}‖u(t)‖_{L²}<∞`, `01-introduction.tex:27` | **gap**: only `∃E≥0, ∀t∈[0,1), ½∫‖u‖² ≤ E` exists — `CandidateProperties.energy_bounded` (`R3PS:108`), `PEP.compact_properties_endpoint` (`PEP:152-166`, in the sharper form `l2Sq u t ≤ B²` with `B = sup_{t∈[0,1]}‖F(t)‖₂` from `PEP.uniform_force_norm`, `PEP:24-33` — the Lean proof bounds the manuscript's `N(t) = ∫₀ᵗ‖F‖₂` by `tB ≤ B`), `PEP.presingular_energy_and_dissipation` (`PEP:68-140`), `PE.packet_energy` (`PE:143-181`), transported to all `ν` by `VP.viscosity_uniform_energy` (`VP:69-79`) | Three mismatches: (i) kinetic energy `½∫‖u‖²` vs `L²` norm `√(∫‖u‖²)` — `l2Sq`, `R3CE:190`; (ii) *an* upper bound vs *the* least upper bound; (iii) the existing bound is at the level of `l2Sq`, so `M = √(sup l2Sq)`. Existence of the supremum needs nonemptiness (`0 ∈ Ico 0 1`) plus `BddAbove`. See split unit 2. |
| `dissipation_integrable` | monotone convergence step, `02-preliminaries.tex:150` | `selected_packet_every_viscosity`, `VP:134`: `IntegrableOn (dissipation u) (Ioo 0 1)`; from `PEP.compact_properties_endpoint` `PEP:152-166`, `PEP.integrable_open_of_bounded_primitives` `PEP:38-64`, `PE.packet_dissipation` `PE:233-255`; `ν`-transport by `VP.viscosity_dissipation` `VP:81-98` | Exact match. `dissipation u t = Σᵢ∫‖∂ᵢu(t)‖²` (`R3CE:195-196`) is `‖∇U(t)‖₂²`. Open interval `Ioo 0 1`, so no endpoint claim at `t=1`. |
| `dissipation_eq` | `D := ‖∇U‖_{L²((0,1)×ℝ³)}`, `02-preliminaries.tex:131` | **gap**: the integral `∫_{(0,1)} dissipation U` is never named; only the bound `∫₀^t dissipation ≤ (∫₀^t‖F‖₂)²/(2ν)` exists, `PE.packet_dissipation` `PE:233-255` | Definitional only once `dissipation_integrable` is available. Note the manuscript's `D` has *no* `ν` in it, while the source bound is `O(ν^{-1/2})`; `eq:packetEscale` and `eq:REclose` use `D` itself, so no `ν`-uniformity is claimed. See split unit 3. |
| `quiet_pos`, `quiet_lt_one` | "vanish on an initial time interval", `02-preliminaries.tex:133`; `τ>0`, `02-preliminaries.tex:152` | partial, `τ=3/8`: `SPE.selected_compact_smooth_energy_packet` `SPE:70-86`, `VP:135` | `3/8 < 1` holds for the concrete packet. Generic route needs split unit 1. |
| `force_quiet` | `F=0` on `[0,τ]`, `02-preliminaries.tex:152` | partial: `SPE.selected_early_energy_packet` `SPE:47-66` gives `∀ t ∈ Ioo 0 (3/8), ∀x, f(t,x)=0` — but only for the *pre-extension* force, and `selected_packet_every_viscosity` (`VP:131-135`) does **not** re-export it | Recoverable generically from `force_support`: `tsupport F` compact and `⊆ Ioi 0 ×ˢ univ`, so its time projection has a positive minimum. That is the manuscript's own argument and is missing in Lean. Split unit 1. |
| `velocity_quiet` | `U=0` on `[0,τ]` from `eq:packetenergy`, `02-preliminaries.tex:152` | `VP:135` (`|t| ≤ 3/8 → u(t,x)=0`), from `SPE:59-62` via `TimeLocalization.activatedVelocity_zero_early`; the *manuscript's* proof is `PE.vanishes_before_forcing`, `PE:197-229` | Two independent routes. The source route is a property of the OpenAI time switch, not of the energy estimate; `PE.vanishes_before_forcing` is the faithful one and is already proved for arbitrary `ν ≥ 0`. Interval shape: source gives `|t| ≤ 3/8` (so also negative times), spec asks `Ioo 0 τ` — strictly weaker, fine. |
| `pressure_quiet` | `∇P=0` there, then compact support ⇒ `P=0`, `02-preliminaries.tex:152` | `VP:135`; faithful route `PP.pressure_vanishes_on_quiet_interval` `PP:55-69` with `PP.compact_pressure_eq_zero` `PP:17-30` and `PP.residual_eq_pressure_on_quiet_interval` `PP:33-52` | Same two routes. `PP` is stated for `NSFormalization.Source.residual ν`, i.e. arbitrary `ν`. |
| `force_zero_nonpos` | `C1`, `logs/SOL_MAX_AUDIT_SYNTHESIS_20260912.md:51-73`; inserted text `03-torus.tex:108-109` | `NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport.eq_zero_of_nonpos`, `R3PS:173-178` | Exact match; a direct consequence of `force_support`. Kept as an explicit field because `C1` is a stated *convention* that Section 3/4 formulas depend on. |
| `velocity_extension_smooth` | "extend smoothly by zero to negative times", `02-preliminaries.tex:133`; used at `03-torus.tex:108-111, 141` | `PS.zeroPastField_smoothOn`, `PS:373-391` (`ContDiffOn ℝ ∞ (zeroPastField f) (Iio 1 ×ˢ univ)` from presingular smoothness + a quiet germ `Ioo 0 ε`); `zeroPastField` def at `PS:243-244` | Available but **never instantiated at the selected packet**. Domain `Iio 1 ×ˢ univ` is the right target: smooth on all negative times, up to but excluding the singular time. Split unit 4. |
| `pressure_extension_smooth` | same | same lemma, `PS:373-391`, applied to a `PressureField` (it is generic over `[NormedAddCommGroup V]`) | Same. Split unit 4. |
| `extension_navier_stokes` | "the fields solve the momentum equation at viscosity `ν`", `03-torus.tex:123, 141`; needed for `t ≤ T-2ε²`, `04-whole-space.tex:36` | `PS.zeroPastField_equation`, `PS:471-486` — exactly this statement, for arbitrary `ν`, at every `t < 1`, including the seam `t = 0` | Stated with `NSFormalization.Source.residual ν` rather than `NavierStokesR3.ProblemStatement.navierStokesResidual ν`; the two unfold to the same expression (compare `Source/Insertion.lean:21-24` with `R3PS:57-62`); the bridge was checked in this worktree and closes by `rfl`. Split unit 5. |
| `extension_divergence_free` | "incompressibility is preserved", `03-torus.tex:141` | **gap** at this exact shape; the argument is inlined inside `PS.delayed_parabolic_divergence`, `PS:506-524` (which proves it for the *already rescaled* field) | Needs the un-rescaled statement `∀ t<1, spatialDivergence (zeroPastField U) t x = 0`. Split unit 6. |

### Conventions that had to be chosen, and why

* **Time domain.** `U,P` live on `[0,1)` (`preSingularDomain`), the equation on
  `(0,1)`, the force on all of `ℝ×ℝ³` with support in `t>0`.  The zero
  extensions live on `(-∞,1)×ℝ³`.  This is the OpenAI convention and matches
  the paper, which never differentiates `U` at `t=0` from the left before the
  extension is in place.
* **`ν`-dependence.**  Theorem 1.1 quantifies over `ν`, and Lemma 2.2 is stated
  for the *fixed* packet chosen after Theorem 1.1.  Hence `PacketAPI ν` and a
  separate `PacketFamily` for the choice.  `M` and `D` are fields of
  `PacketAPI ν`, so they may depend on `ν`; the manuscript never claims
  `ν`-uniformity for them, and Section 4 fixes `ν` throughout.
* **Which "selected" packet.**  The chain is
  `ActualCandidateAssembly.selected_witness`
  (`vendor/.../ActualCandidateAssembly.lean:1177`) →
  `R3CompactCandidate.of_localized_fields` (`R3CC:248-252`) →
  `R3CompactCandidate.selected_compact_candidate`
  (`vendor/.../R3ActualCandidate.lean:18-21`) →
  `SPE.selected_candidate_properties` (`SPE:90-114`) →
  `VP.selected_packet_every_viscosity` (`VP:131-151`).  The last step is a pure
  *spatial* dilation with `a = √ν` (`VP:136-142`, `Source/ViscosityScaling.lean:18-22`):
  time is not rescaled, so the singular time stays at `1` and the quiet
  interval stays `|t| ≤ 3/8`.  This is *not* the parabolic scaling of
  `eq:scaling`; the two must not be confused.
* **Real vs complex.** All fields are real: `Space = EuclideanSpace ℝ (Fin 3)`
  (`PS0:30`), `VelocityField = ℝ × Space → Space`, `PressureField = ℝ × Space → ℝ`
  (`PS0:35-36`), matching "All fields are real"
  (`paper/sections/02-preliminaries.tex:5`).
* **Support sets.** The record uses one `carrier` for `U` and `P`, as Theorem 1.1
  does.  Section 3 additionally needs `K_*` containing `K` *and the spatial
  projection of* `supp F` (`03-torus.tex:101-102`); that is an I02/I03 obligation
  and is deliberately not a field here — `force_support` already pins `supp F`
  compactly.
* **Measure.** All spatial integrals are ordinary Lebesgue volume on `ℝ³`
  (`R3CE:8-12`), and `l2Sq`/`dissipation` are totalized Bochner integrals, so
  `square_integrable` is stated separately rather than left implicit.

## Bounded implementation split

Nine lemma-sized units.  Units 1-7 close the gaps; unit 8 builds the record;
unit 9 is the acceptance binding.  No unit reproves anything already available.

| # | Unit | Statement to prove | Builds on |
|---|---|---|---|
| 1 | `force_quiet_of_compactPositiveTimeSupport` | For `f : VelocityField` with `CompactPositiveTimeSupport f`, there is `τ` with `0 < τ`, `τ < 1` and `∀ t < τ, ∀ x, f (t,x) = 0`. | `R3PS:66-67`; compactness of `tsupport f` and continuity of `Prod.fst`; `IsCompact.exists_isMinOn` on the time projection (empty support handled by taking `τ = 1/2`). This is the manuscript's own argument, `02-preliminaries.tex:152`. |
| 2 | `packet_l2_isLUB` | From `UniformFiniteEnergy (Ico 0 1) u` obtain `M` with `IsLUB ((fun t => √(l2Sq u t)) '' Ico 0 1) M`, and `0 ≤ M`. | `R3PS:81-83`, `R3CE:190`; `Real.exists_isLUB` with nonemptiness from `0 ∈ Ico 0 1` and `BddAbove` from `kineticEnergy u t ≤ E` (so `l2Sq u t ≤ 2E`, `√· ≤ √(2E)`). Sharper input available from `PEP.compact_properties_endpoint`, `PEP:152-166`. |
| 3 | `packet_dissipation_norm` | Define `D := √(∫ t in Ioo 0 1, dissipation u t)` and record `0 ≤ D` and `D^2 = ∫ …`. | `VP:134` (`IntegrableOn`), `R3CE:198` (`dissipation_nonneg`), `Real.sq_sqrt`. |
| 4 | `packet_extension_smooth` | `ContDiffOn ℝ ∞ (zeroPastField U) (Iio 1 ×ˢ univ)` and the same for `P`. | direct application of `PS.zeroPastField_smoothOn` (`PS:373-391`) with `ε = 3/8` from `VP:135`, and `CandidateProperties.velocity_smooth`/`pressure_smooth` (`R3PS:94-95`). |
| 5 | `residual_eq_navierStokesResidual` and `packet_extension_equation` | `NSFormalization.Source.residual ν u p t x = NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x` (**checked in this worktree: closes by `rfl`**); then `∀ t<1, ∀x, navierStokesResidual ν (zeroPastField U) (zeroPastField P) t x = zeroPastField F (t,x)`. | `Source/Insertion.lean:21-24`, `R3PS:57-62`, `PS.zeroPastField_equation` (`PS:471-486`) with `ε = 3/8`. |
| 6 | `zeroPastField_divergence_free` | `∀ t < 1, ∀ x, spatialDivergence (zeroPastField u) t x = 0` from `divergence_free` on `Ico 0 1`. | `PS.zeroPastField_of_pos`/`_of_nonpos` (`PS:246-252`), copying the case split already written inside `PS.delayed_parabolic_divergence` (`PS:506-524`); `PS0:67-68`. |
| 7 | `packet_force_zero_nonpos` | `∀ t ≤ 0, ∀ x, F (t,x) = 0`. | `R3PS:173-178` applied to `CandidateProperties.force_support`. Trivial; separated only so unit 8 is pure assembly. |
| 8 | `selected_packetAPI` | `∀ ν, 0 < ν → PacketAPI ν` (hence `packetStatement` and a `PacketFamily`), by `Classical.choice` on `VP.selected_packet_every_viscosity`. | `VP:131-151` for fields 1-4 and every `CandidateProperties` projection, plus units 1-7. Note `VP:135` already supplies `velocity_quiet`/`pressure_quiet` at `τ = 3/8`; unit 1 supplies `force_quiet`, and `min` of the two `τ`'s is used. |
| 9 | `Contracts/V1/Packet.lean` + `Bindings` + axiom test | Promote the reviewed `PacketAPI`/`PacketFamily` to `BlowupDensity.Contracts.V1`, register a typed binding to the unit-8 term, and add the `#print axioms` test. | pattern of `verification/Contracts/V1/Thresholds.lean` and `verification/contracts.json`. |

Optional follow-ups, **not** part of I01 (recorded so they are not lost):

* `A. extension energy at the sup level` — `IsLUB ((fun t => √(l2Sq (zeroPastField U) t)) '' Iio 1) M`
  and `IntegrableOn (dissipation (zeroPastField U)) (Iio 1)`.  Needed by I03 for
  `eq:packetEscale`, since the rescaled time interval `(0,T)` pulls back to
  `((0-t_ε)/ε², 1)`, which reaches negative reference times.  Groundwork exists:
  `PS.zeroPastField_uniform_energy` (`PS:286-297`),
  `PS.zeroPastField_dissipation_integrable` (`PS:260-264`),
  `PS.zeroPastField_speed` (`PS:278-282`).
* `B. limsup form of blowup` — prove
  `SpeedUnboundedAtOne u ↔ limsup_{t↑1} ‖u(t)‖_∞ = ∞` for continuous compactly
  supported slices, closing the docstring claim at `R3PS:85-87`.  Not consumed
  by Section 4.
* `C. K_*` — the enlarged compact set of `03-torus.tex:101-102` containing `K`
  and the spatial projection of `supp F`; belongs to I02/I03.
