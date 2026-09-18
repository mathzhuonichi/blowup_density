# T18 reconciled — `thm:insertion` clause → Lean field table

Theorem `thm:insertion` (exact local insertion on `T³`),
`paper/sections/03-torus.tex:287-311`; proof `:312-346`.
File: `research/T18/Spec.lean`, structure `BlowupDensity.T18.Spec.PeriodicInsertionAPI`
(**11 parameters, 45 fields**), `def periodicInsertionStatement`.
Base draft: **B** (lane 357); four structural corrections imported from **A** (lane 356)
per `research/T18/RECONCILIATION.md` §3.
Templates: `Contracts/V1/InsertionFamily.lean` (`InsertionFamilyAPI`, R42) and
`Contracts/V2/InsertionLifespan.lean` (`InsertionLifespanV2API`, R42.v2).

## Parameters (objects the proof is *given*, `:287-289,312-314`)

| Lean parameter | Paper object | A / B provenance | R42 counterpart | reconciliation ruling |
|---|---|---|---|---|
| `ν : ℝ` | viscosity | both | `InsertionFamilyAPI (ν)` | — |
| `P : PacketImportAPI ν` | fixed energy-enhanced whole-space packet `(U,P,F,M,D)` | **A** (B had bare `PacketAPI`) | `InsertionFamilyAPI (P)` | **A** — `M,D`, energy/scaling identities need the energy-enhanced packet (§2 row 1) |
| `place : T15.Draft.PlacementData P.toPacketAPI` | `:101-107` `T,B,x₀,K_*,ε₀,2ε²<T,x₀+εK_*⊆B` | both (A's namespace) | folded into `scaling.correction` | base B, A's `PlacementData` |
| `scaling : ScalingAPI P place` | `prop:scaling` rescaled/periodized packet + its identities | **A** (B threaded none) | `scaling : ScalingAPI ν P` (R42 consumes registered R³ one) | **A** — torus `ScalingAPI` unregistered, must be threaded (§2 row 1) |
| `a : SpatialField`, `g : SpaceTimeField` | `:289` `v(0)=a`, reference force `g` | both | `InsertionFamilyAPI.a`, `scaling.correction.g` | base B |
| `r δ : ℝ` | coordinate-ball radius `r`; margin `δ` | both | `scaling.correction.r`, `.δ` | base B |
| `D : T16.Draft.CutoffData` | `lem:potential` cutoffs `θ,η`, potential `A`, family `w_ε` | both (A's name `D`) | inside `scaling.correction` | base B, A's name |
| `reference : ClassicalSolutionT ν a g (place.T+δ)` | `:287-288` `(v,π,g)` regular through `T+δ` | both | `InsertionFamilyAPI.reference` (R³ class) | base B (inline `reference.velocity`, no `v,π` pins) |
| `correction : CorrectionAPI ν place reference.velocity r δ D` | `lem:correction` `H_ε` + `eq:wE`/`eq:Hmixed`/`eq:HHs`; carries `LocalPotentialAPI`+`LocalizationAPI` | both | bundled in `scaling` | base B |

Not threaded (dropped from A per §3): `localTheory : PeriodicLocalTheoryAPI`,
`continuation : PeriodicContinuationH3API`, `calculus : MeanZeroSobolevCalculusAPI`
— all consumed at proof time (T11 registered+inhabited; `H²↪L∞` a Mathlib fact),
not hypotheses.

## Hypotheses (paper givens not forced by parameter types)

| Field | Paper | A / B | R42 counterpart | ruling |
|---|---|---|---|---|
| `delta_pos` (`δ>0`) | `:288` | both | reference horizon `T+δ` | keep |
| `reference_force_mem` (`g∈𝓕`) | `:289` | both | `memForce` | keep |
| `initial_mem` (`a∈𝓧`) | `:289` | both | `a` typed by solution | keep |
| `ε₀, eps_pos` | `:290` "sufficiently small `ε`" | **B** (field; A had it a parameter) | `ε₀, eps_pos` | **B** — R42 shape (§2) |
| `eps_le_scaling` (`≤ place.ε₀`) | `:290,103` | A (`eps_le_scaling`) | `eps_le_scaling` | keep (scaling bounds over `Ioc 0 place.ε₀`) |
| `eps_le_cutoff` (`≤ D.ε₀`) | `:290,312` | B | — | keep |

## Inserted triple and `eq:insertion` (`:314`)

| Field | Clause | A / B | R42 counterpart | ruling |
|---|---|---|---|---|
| `velocity, pressure, force` | `ε↦(u_ε,p_ε,g_ε)` | both (`pressure : SpaceTimeScalar` from B) | same | B's `SpaceTimeScalar` type |
| `velocity_formula` | `u_ε=v+w_ε+U_ε`; `U_ε=periodizedScaledVelocity P x₀ T ε` | A's scaling field | `velocity_formula` | **A** — scaling record's periodized field (§3.1) |
| `pressure_formula` | `p_ε=normalizePressureT(π+P_ε)`; `P_ε=periodizedScaledPressure P x₀ T ε` | B spelling + A's scaling field | **TORUS** vs R42 compact gauge `π+P_ε` | binding spelling `normalize(π+P_ε)` (§3), scaling's `periodizedScaledPressure` (§3.1); `= π+normalize(P_ε)` since `π` mean-zero |
| `force_formula` | `g_ε=g+H_ε+F_ε`; `H_ε=correctionForce ν v D ε`, `F_ε=periodizedScaledForce P x₀ T ε` | A's scaling field | `force_formula` | **A** — scaling field (§3.1) |

## Solution / lifespan / blow-up (clause (i), `:291-292,338-345`)

| Field | Clause | A / B | R42 counterpart | ruling |
|---|---|---|---|---|
| `force_mem` (`g_ε∈𝓕`) | `:289,339` | both | — | keep both |
| `forceDifference_mem` (`g_ε-g∈𝓕`) | `:339-341` | **B** | `forceDifference_compact` | **B** — keep both (§2) |
| `velocity_smooth, pressure_smooth, initial, incompressible, momentum, history, velocity_periodic` | `:329-337`, (ii) `:294` | **B** (explicit; A folded into `solution`) | R42 explicit (+`velocity_periodic` torus) | **B** (§2 kinematic row) |
| `solution` | `:338,344-345` full-horizon `ClassicalSolutionT` | both | `InsertionLifespanV2API.solution` | keep |
| `maximal` | `:342-344` **TORUS** `IsMaximalPeriodicSolution` | both | `.maximal` | keep |
| `lifespan` (`T_max=T`) | (i) `:291,344-345` | both | `InsertionLifespanAPI.lifespan` | keep |
| `blowup` (`SpeedUnboundedAt`) | (i) `:291-292` | both | `InsertionFamilyAPI.blowup` | keep |
| `blowup_limsup` (`limsupLeft…speedENorm=⊤`) | (i) `:291-292` | **B** | `.blowup_limsup` | **B** — ess-sup `limsup=∞` literal (A's `breakdown` dropped as redundant, §2) |

## Two vanishing cross-transport terms (`:322-328`)

| Field | Clause | A / B | R42 counterpart | ruling |
|---|---|---|---|---|
| `crossTransport_background_advects_packet` | `(b_ε·∇)U_ε=0`, `b_ε=v+w_ε` | B names, A's `periodizedScaledVelocity`, interval `Ico` (B) | R42 folds into `momentum` prose | B names + `Ico`; U_ε via scaling field (§3.4) |
| `crossTransport_packet_advects_background` | `(U_ε·∇)b_ε=0` | same | same | same |

Written with registered `spatialDerivative` (directional Fréchet), copied
`correctedBackground` (`b_ε`), scaling's `periodizedScaledVelocity` (`U_ε`).
"Both terms are identically zero" (`:325`) ⇒ two `= 0` fields on `Ico 0 T`.

## Localization (clause (iii), `:293-295`)

| Field | Clause | A / B | R42 counterpart | ruling |
|---|---|---|---|---|
| `velocityDifference_divFree` | `:295` div-free | both | `velocityDifference_divFree` | keep |
| `diffSupportRadius(_pos)` | `:293-295` radius `ρ` for `O(ε)` diameter | B | — | keep |
| `velocityDifference_support` | `:295` ⊆ **TORUS** `periodicSet (ball x₀ (ε·ρ))` | **B** | `velocityDifference_support` (single ball) | **B** — A's single-ball form is **FALSE** for a periodic difference (§"False clauses"); B captures `O(ε)` diameter + periodic support |
| `diffSupport_in_chart` | `:293-295` "inside the chosen ball" | B | implicit in R42 | keep |

## Three closeness rates (clause (iv), `:296-306`) + `s<0` tail (`:309-310`)

| Field | Clause | A / B | R42 counterpart | ruling |
|---|---|---|---|---|
| `energyRate` | `eq:Eclose` `:300-302` `(M+D)ε^{1/2}+Cε^{3/2}`; `M=P.energyBound`,`D=P.dissipationBound`,`C=correction.energyConst`; torus `energyENormT` | **B** (A had a free `energyRateConst`+`_memLp`) | `energyRate` | **B** — `C` **is** `correction.energyConst` (`eq:wE`); `energyENormT` has no representative-⨅, no `MemLp` guard (§2) |
| `forceDiffMixedConst(_nonneg)` | `eq:Fclose` constant | both | — | keep |
| `forceDifference_mixed_memLp` | honest torus mixed path `MemMixedLebesgueT q p` | **A** (B had per-slice `MemLp`) | — | **A** — per-slice `MemLp` does not exclude `⨅=⊤` trap (§2, §3.2) |
| `forceDifference_mixed_bound` | `eq:Fclose` `‖g_ε-g‖_{L^q_tL^p_x}≤C_{p,q}(ε^{α}+ε^{α+1})`, `α`=registered `Contracts.V1.alpha` | B (copied `mixedLebesgueENormT`) | R42 has only `forceConvergence` | keep; registered `alpha` (§2) |
| `forceDiffSobolevConst(_pos)` | `eq:Hsclose` constant, `0≤s<1/2` | both | — | keep |
| `forceDifference_sobolev_memLp` | honest `L¹_tH^s` path `MemForceSobolevT 1 s`, `0≤s<1/2` | B (separate field) | — | **B granularity** (guard identical, §2) |
| `forceDifference_sobolev_bound` | `eq:Hsclose` `‖g_ε-g‖_{L¹_tH^s_x}≤C_s(ε^{1/2-s}+ε^{3/2-s})`, `0≤s<1/2`; registered `forceSobolevENormT 1 s` | B | — | keep; **TORUS** range stops `<1/2` |
| `forceDifference_negativeSobolev_tendsto` | `:309-310` `s<0`: diff→0 in `L¹_tH^s` | both | `forceConvergence` | keep |
| `negative_s_memLp` | honest `s<0` paths `MemForceSobolevT 1 s` | **A** (B had none) | — | **A** — convergence of an `⨅`-norm to `0` needs it eventually `<⊤` (§2, §3.3) |

Every totalized Bochner norm carries its integrability/class guard; `ν>0` is a
hypothesis of `periodicInsertionStatement` (and `correction.viscosity_pos`);
`ε∈Ioc 0 ε₀` guards every quantitative field.

## Proof dependencies (copied from RECONCILIATION.md §4; the assembly lane will consume)

- **T11** (registered, inhabited — `Bindings/TorusLocalTheory.lean:355,387`):
  `torusLocalTheoryAPI.{velocity_unique, regularity, solution}` for `maximal` and
  the `≥T` half of `lifespan` (`:342-344`);
  `torusContinuationH3API.{higherOrderBound, restartBeyond, lifespanInfiniteOfLocallyFinite}`
  for the `≤T` half (`:344-345`) against `blowup_limsup`.
- **T15** (`scaling` parameter): `packetEnergyIdentity`/`packetDissipationIdentity`
  → `(M+D)ε^{1/2}` of `energyRate`; `packetMixedScaling` → `ε^{α}` of
  `forceDifference_mixed_bound`; `packetSobolevBound`/`forceConvergence` → `ε^{1/2−s}`
  of `forceDifference_sobolev_bound` and the `s<0` tail;
  `velocity_singleCopy`/`pressure_singleCopy`/`force_singleCopy` +
  `solution`/`unboundedSpeed`/`force_mem` for the periodization, blow-up and force class.
- **T16/T17** (`correction`/`D`): `LocalPotentialAPI.{potential_curl, correction_cancels}`
  (via `correction.potential`) → the two `crossTransport_*` zeros (`eq:bgzero` ⇒
  `b_ε=0` near `supp U_ε`); `CorrectionAPI.{energyConst→correction_energy_bound
  (eq:wE), mixedConst→force_mixed_bound (eq:Hmixed), sobolevConst→force_sobolev_bound
  (eq:HHs), force_smooth/force_periodic/force_support}` → the
  `Cε^{3/2}`/`ε^{α+1}`/`ε^{3/2−s}` correction terms and `force_mem`/`forceDifference_mem`.
- **T13** (via `correction.localization`): `LocalizationAPI` transfers Euclidean
  `Ḣ^s` to `H^s(T³)` for `eq:Hsclose`.

## Open questions for the owner (RECONCILIATION.md §4)

1. **Registration gap** (both COMPARISONs flag it). The torus
   `ScalingAPI`/`PlacementData`/`PacketImportAPI` are consumed by T18 but live only
   in `research/T15/Spec.lean`. T18 therefore threads `scaling : ScalingAPI P place`
   as a parameter (unlike R42, which consumes the registered whole-space `ScalingAPI`).
   Decide whether to **promote the T15 torus scaling chain to a registered
   `Contracts/V1` contract** before/at T18 assembly; if promoted, T18's `scaling`
   parameter can become a consumed registered fact.
2. Confirm no torus V2 ess-sup `breakdownSetT` export is wanted (A's `breakdown`
   dropped as redundant); `blowup_limsup` (R42.v2 shape) is retained instead.
3. Confirm the pressure-gauge reading `p_ε = normalizePressureT (π + P_ε)`
   (literal `:318-320`); it equals `π + normalize(P_ε)` because `reference` carries
   `pressure_gauge`, so either is acceptable if a later lane prefers A's spelling.
