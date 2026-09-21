# I03 attempts, gaps and paper–Lean differences

Lane 021, task **I03** ("Same-family scaling and negative norms"), 2026-09-13.
Registered contract: `I03.scaling`, `verification/Contracts/V1/Scaling.lean`,
binding `verification/Bindings/Scaling.lean`, test `verification/Tests/Scaling.lean`.
Input specification: [`Spec.lean`](Spec.lean) (accepted, 49 fields),
[`COMPARISON.md`](COMPARISON.md), [`REVIEW.md`](REVIEW.md).

This file records what did **not** work, what needed new mathematics, where the
Lean statement deviates from `Spec.lean` or from the manuscript, and the exact
status of the homogeneous clauses.  Positive results are in the contract's own
doc comments.

---

## 1. The one structural discovery that shaped the lane

`Spec.lean`'s migration note said the contract-level record should take
`C : CorrectionAPI ν P` as a field.  The obvious reading — *`I03` receives an
abstract `C` and must prove Sobolev decay for `C.forceCorrection`* — looked
unreachable: every scaling estimate in the tree
(`Paper1/CorrectionVectorNorms.lean`, `Paper1/CorrectionForceNorms.lean`) is
about the **concrete** `Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)`,
and the abstract regularity, support and derivative fields of `CorrectionAPI`
do not by themselves imply any `L^q_t H^s_x` decay (they would need a Sobolev
interpolation argument that does not exist in the tree).

The first plan was therefore to **copy** the ~430-line construction of
`verification/Bindings/Correction.lean` into `Bindings/Scaling.lean`, because
`Bindings.correction` is a tactic-built `def` whose internal cutoffs `θ`, `η`
are `Classical.choose` applications and therefore not recoverable from the
`CorrectionAPI` value it returns.

That copy turned out to be unnecessary.  `CorrectionAPI` does **not** merely
constrain `w_eps` and `H_eps`: three of its fields are exact *formulas* —
`potential_formula` (`eq:potential`), `correction_formula` (`eq:cutoff`) and
`force_formula` (`eq:H`).  Together they pin

* `C.potential = RadialPotential.timePotential C.v C.x₀`,
* `C.correction ε = CorrectionProfile.physicalCorrection C.v C.x₀ C.T C.θ C.η ε`,
* `C.forceCorrection ε = Source.correctionForce ν C.v (physicalCorrection C.v C.x₀ C.T C.θ C.η ε)`,

for *any* inhabitant of `CorrectionAPI`.  These are
`Bindings.potential_eq`, `Bindings.correction_eq`, `Bindings.forceCorrection_eq`
(`verification/Bindings/Scaling.lean`), each a `funext` followed by the field
and one `rfl`.  So the whole `Paper1` estimate library applies to an abstract
`I02` record, and `scalingStatement` could be strengthened from "there exists
some family" to the equation **`A.correction = C`**: `I03` proves its estimates
for the very correction `I02` produced.

Cost of that route, and the one place it bites: the `Paper1` estimates assume a
**globally** smooth reference, while `CorrectionAPI.reference_smooth` gives only
`ContDiffOn` on the slab `(0, T+delta) x R^3`.  The bridge is the window
extension `V` of `Paper1.TimeExtension.exists_global_reference_extension`
together with the slicewise congruence lemmas of
`NSFormalization.Section4.I02.Reference`, exactly as `Bindings/Correction.lean`
uses them — but that bridge needs `2 eps^2 <= window` with
`window = min(T,delta)/4`, which `CorrectionAPI.eps_time` (`2 eps^2 < min(T,delta)`)
does **not** give.  Hence `ScalingAPI.ε₀ = min C.ε₀ (sqrt (window C / 2))` and
the field `eps_le_correction : ε₀ ≤ correction.ε₀`.  This is precisely the
"`I03` may shrink the threshold but never enlarge it" that `Spec.lean`'s
migration note anticipated; it is why the relation is an inequality.

---

## 2. Deviations from `Spec.lean`, field by field

| `Spec.lean` | contract | why |
|---|---|---|
| `ν`, `T`, `δ`, `x₀`, `r`, `carrierRadius` as fields + pinning equations | not fields: the record reads `correction.T`, `correction.δ`, `correction.x₀`, `correction.r`, `correction.θRadius`, and `ν`/`P` are structure parameters | the identifications `Spec.lean` demanded become definitional instead of ten fields with no proof content; `R42` can no longer mismatch them |
| `packet : PacketAPI ν` field | structure parameter `ScalingAPI (ν) (P : PacketAPI ν)` | avoids the `HEq` in `scalingStatement` that `Spec.lean` needed |
| `correction`, `correction_smooth`, `correction_compactSupport`, `forceCorrection`, `forceCorrection_smooth`, `forceCorrection_compactSupport` (six restated `I02` fields) | deleted; `correction : CorrectionAPI ν P` | the migration `Spec.lean` prescribes |
| `correctionEnergyConst`, `correctionEnergyConst_nonneg`, `correctionEnergyBound` | **kept** (not replaced by `correction.energyConst`) | `CorrectionAPI` carries no sign condition on `energyConst`, and with a negative one `eq:REclose` would assert *less* than the triangle inequality delivers, making the field false. The contract's constant is `max C.energyConst 0` and `correctionEnergyBound` pins it to `I02`'s bound, so nothing is lost |
| `carrier_subset` | kept, but **derived** in the binding from `carrier_subset_plateau` + `theta_one` + `theta_support` | not an extra obligation on the caller |
| `force_carrier_subset` | **dropped** (revision 2, after `REVIEW_CONTRACT.md` 5.1 item 4) | it was the `K -> K_*` enlargement of `03-torus.tex:101-102`, first kept as a field and as a premise of `scalingStatement`. Two facts killed it: **(i)** no conclusion of `ScalingAPI` uses it -- the binding stored the premise verbatim and it was a pure pass-through; **(ii)** *the obligation was unmet downstream*. A consumer can only obtain a `CorrectionAPI` through `correctionStatement`, whose witness `Bindings.correction` fixes `θRadius := R = Rb + 1` from `P.carrier` alone (`verification/Bindings/Correction.lean:174-178`), and `PacketAPI.force_support` is only `CompactPositiveTimeSupport force`, which says nothing about `carrier`. So `R42` could never have discharged the premise, and `I03` cannot manufacture the enlargement either. The record therefore no longer mentions `K_*`; a consumer that needs `supp F_eps subset B` must get the enlarged radius from an `I02` V2 that lets the caller pin `θRadius` above a given compact set. `carrier_subset` (the `K` half) survives because it is *derived* from `I02`'s plateau data |
| `packetNegativeHomogeneous`, `correctionNegativeHomogeneous` | moved to the **unregistered** `HomogeneousScalingAPI` | see §4 |
| `forceLowOrderBound` with constants `negativeConst q r` / `correctionNegativeConst q r` | new constant family `lowOrderConst : ℝ≥0∞ → ℝ → ℝ → ℝ`, indexed by `(q, s, r)` | see §3 |
| `forceDifference` + `forceDifference_formula` fields | the sum is written out inline in `forceConvergence`, and `ScalingAPI.forceDifference` is a projection `def` after the structure | the formula field carried no content once the sum is inlined |
| `scalingStatement` quantifying over `w`, `H` with seven `I02` premises | `∀ ν P (C : CorrectionAPI ν P) th, ∃ A, A.correction = C ∧ A.thresholds = th` | strictly stronger and it removes the `HIGH` defect that `REVIEW.md` issue 1 found in revision 1. Since revision 2 there is **no side condition at all**: every hypothesis is a field of `PacketAPI` or `CorrectionAPI` |

Ranges and exponents are unchanged from `Spec.lean`: `0 ≤ s ≤ 1` for
`eq:RpositiveScale`, `-3/2 < s < 0` for `eq:RnegativeScale`, `1 ≤ q` (including
`q = ⊤`) for both, `q ∈ {1,2}` for the two clauses that the theorem statement
itself restricts, and every exponent is written through `ThresholdAPI.exponent`.

---

## 3. The `(2π)^{|s|}` constant, and why `forceLowOrderBound` needed a third index

`Contracts.V1.Data.forceSobolevENorm` is the manuscript's **angular** norm
(`01-introduction.tex:91`), realized as an infimum over `RealVectorSobolev s`
datum paths.  Every scaling estimate in the tree is in Mathlib's **cycles**
convention.  The two are related by the two-sided equivalence with constant
`Source.frequencyUnit ^ |s| = (2π)^{|s|}`
(`Source/AngularForceNorms.lean:19`), *not* by an isometry.

The transport is one-directional and that is enough: exhibiting the single
admissible angular datum path `Section4.I03.angularPath` bounds the infimum, so

`Data.forceSobolevENorm q s F ≤ ofReal ((2π)^{|s|}) * eLpNorm (vectorFourierSobolevNorm s F) q volume`

(`Bindings.forceSobolevENorm_le_cycles`).  The constant is `ε`-free, so it is
absorbed into `positiveConst`, `correctionPositiveConst`, `negativeConst`,
`correctionNegativeConst` — which is legitimate because those are existentially
quantified constants of `eq:RpositiveScale`/`eq:RnegativeScale`.

**Where it forced a statement change.**  `Spec.lean`'s `forceLowOrderBound`
measures the norm at order `s` but states the bound with the constant
`negativeConst q r` at the *intermediate* order `r`.  The transported constant
carries `(2π)^{|s|}`, which depends on `s` and is unbounded as `s → -∞`, so it
cannot be absorbed into a constant indexed by `r` alone.  Two options were
considered:

1. index the constant by `(q, s, r)` — taken; the contract declares
   `lowOrderConst : ℝ≥0∞ → ℝ → ℝ → ℝ` with a docstring saying exactly this;
2. state the intermediate-index clause in the cycles convention — rejected: the
   contract must not mention an implementation convention.

Nothing mathematical is lost: the paper's `C_{q,s}` in `eq:RnegativeScale` are
unspecified constants, and the two conclusions of `forceLowOrderBound` still
share **one** constant, as `Spec.lean` demanded.

`Spec.lean`'s choice of a single uniform intermediate index for both `q ∈ {1,2}`
(rather than the paper's `r = 0` at `q = 1`) is kept unchanged, with the witness
`r := s` when `-3/2 < s` and `ThresholdAPI.negativeIndex` otherwise.

---

## 4. The homogeneous clauses: exact status

**Not proved, not registered.**  `HomogeneousScalingAPI` in
`verification/Contracts/V1/Scaling.lean` states the two clauses
(`packetNegativeHomogeneous`, `correctionNegativeHomogeneous`) with
`Data.forceHomogeneousENorm`, and the module docstring says they are
deliberately outside `contracts.json`.

What is missing is not an estimate but a **witness constructor**.
`Data.forceHomogeneousENorm q s f` is an infimum over paths satisfying
`Data.IsHomogeneousPath`, which needs `Data.IsHomogeneousDatum`
(`ĥ = |ξ|^{-s} G`, `Data.lean:324`).  Nothing in the project ever produces one:
`grep` for `IsHomogeneousDatum` / `forceHomogeneousENorm` finds no user outside
`Contracts/V1/Data.lean`, and `Paper3/HomogeneousRealization.lean` is 26 lines
that carry one bound and construct no datum.  Since the empty infimum in
`ℝ≥0∞` is `⊤`, both clauses are *unprovable* until such a constructor exists —
this is not a matter of effort inside the lane.

The missing unit is `COMPARISON.md` §5's **U7c**, which on the task graph belongs to node **`B02`** ("Homogeneous H-minus-one approximation", `formalization/blueprint/DEPENDENCY_GRAPH.md:322`) — its **unit 6** is the same obligation, recorded as `D01` unit `L6` (`research/D01/COMPARISON_A.md:102`).  Concretely: the homogeneous counterpart of
the 143-line `Paper3/AngularRealVectorBochner.lean`, i.e. a
`RealVectorSobolev s`-valued realization for the homogeneous weight, together
with U7a (the exact homogeneous change of variables
`∫ |ξ|^{2s} |𝓕(concentratedForce k f)|² = k^{3+2s} ∫ |ξ|^{2s}|𝓕 f|²`, which is
*easier* than its inhomogeneous twin `FourierScaling.lean:51` because the weight
is exactly homogeneous) and U7b (its `L^q_t` form, mirroring
`TimeNormScaling.lean:133`).  U7a and U7b were not attempted in this lane
because they do not unblock anything registered here.

**Consequence, stated precisely.**

* Theorem 4.2 does **not** block on this.  Every clause of
  `04-whole-space.tex:42` is inhomogeneous, and `packetNegativeScaling`,
  `correctionNegativeScaling`, `forceLowOrderBound` and `forceConvergence`
  supply it.  The paper derives the inhomogeneous bound from the homogeneous
  one via `(1+|ξ|²)^s ≤ |ξ|^{2s}` (`04-whole-space.tex:72-73`); the Lean route
  reaches the same inhomogeneous conclusion directly through
  `Source.force_eLpNorm_negative_epsilon`, whose right-hand side is the
  homogeneous norm of the **profile** — a finite quantity on `-3/2 < s ≤ 0`
  (`Paper3/HomogeneousTime.lean:82,108`) — and whose left-hand side is already
  the inhomogeneous norm of the **scaled** field.  So the paper's intermediate
  homogeneous display for the scaled field is never needed for Theorem 4.2.
* **Proposition 4.6 (`R46`) blocks on U7c and on nothing else.**  Its
  `L²(0,∞;Ḣ^{-1})` clause (`04-whole-space.tex:212-226`) is a statement about
  `Data.forceHomogeneousENorm`, and no inhomogeneous route reaches it.

---

## 5. Paper–Lean differences worth recording

1. **`eq:packetEscale`'s `L^∞L²` clause is an equality with a least upper
   bound.**  The source had only inequalities
   (`PacketScaling.uniform_l2Norm_parabolic:118` with an arbitrary bound `N`;
   `Paper1/InsertionEnergy.lean:203`).  The equality is now proved
   (`Section4/I03/Energy.lean`, `energyEssSup_scaled_eq`).  The `≥` half is the
   only place in the project that consumes `PacketAPI.energy_isLUB` as a
   *least* upper bound rather than as a bound, and it needs a genuinely new
   ingredient: continuity of `σ ↦ l2Sq (zeroPastField U) σ` on `(0,1)`, proved
   by dominated convergence against `K.indicator` with the sup bound from
   `IsCompact.exists_bound_of_continuousOn` on `Icc a b ×ˢ K`.  Without it, an
   essential supremum can only be bounded above, since a single near-maximal
   time is a null set.
2. **`eq:REclose` has the paper's exact shape, not the source's.**
   `Paper1.InsertionEnergy.insertion_energy_bound:327` proves
   `√(2(Aε³+Bε)) + √(2(Cε³+Dε))` with four opaque constants.  The contract's
   `perturbationEnergyBound` is `(M+D)ε^{1/2} + Cε^{3/2}` with *the* Lemma 2.2
   constants and *the* `eq:wE` constant, obtained instead from the two exact
   identities plus the `E_T` triangle inequality
   (`verification/Bindings/ScalingEnergy.lean`).
3. **`eq:packetFscale` is an equality.**  The source had only
   `MixedForceScaling.compact_force_mixed_bound:62`, an inequality with a
   support-indicator constant.  The equality needed two observations: the
   spatial and temporal change-of-variable lemmas are already equalities
   (`eLpNorm_spatial_scale`, `eLpNorm_parabolic_time`), and
   `Data.mixedLebesgueENorm`'s defining infimum is *attained*, because any two
   admissible Bochner slice paths of one field agree at every nonnegative time
   (`Bindings.mixedLebesgueENorm_eq`).  The restriction from `ℝ` to `(0,∞)` is
   free because `t_ε = T - ε² > 0` and the packet force vanishes at nonpositive
   times — the manuscript's own argument at `03-torus.tex:148`.
4. **`ε₀` is strictly smaller than `I02`'s.**  See §1.  The manuscript says only
   "for all sufficiently small `ε`", so this is faithful; but a consumer that
   assumed `A.ε₀ = C.ε₀` would be wrong, and `eps_le_correction` says so.
5. **`x₀` is the centre of the ball.**  Unchanged from `Spec.lean` §2.7 and from
   `I02`: the record works in `B = ball x₀ r`, and `R42`, whose statement
   quantifies over a given ball `B₀`, must perform the shrink
   `ball x₀ r ⊆ B₀` itself.  Nothing here records it.
6. **`q = ⊤` is admitted** in the four Sobolev display fields (`REVIEW.md`
   issue 4).  Harmless strengthening, matched by the source, which quantifies
   over all `q : ℝ≥0∞`.

---

## 6. New Lean written for this lane, field by field

Nothing below existed before; everything else is reuse.  New modules:
`formalization/NSFormalization/Section4/I03/{Angular,Energy,Mixed}.lean` and
`verification/Bindings/{Scaling,ScalingNorms,ScalingEnergy}.lean`.

| contract field | new lemma(s) it required | where |
|---|---|---|
| all four Sobolev display fields, `forceLowOrderBound`, `forceConvergence` | the **angular datum path**: `components`, `angularPath`, `angularPath_pairing`, `memLp_angularPath`, `norm_realVectorSlice`, `norm_angularPath_le`, `eLpNorm_angularPath_le` | `Section4/I03/Angular.lean` |
| same | the infimum step `forceSobolevENorm_le_cycles`, the cycles-side bounds `cycles_packet_positive/negative/mono`, the finiteness lemmas `profile_positive_finite`, `profile_homogeneous_finite`, the packaging `sobolev_bound_of_cycles`, and the squeeze `forceSobolevENorm_tendsto_zero` | `Bindings/ScalingNorms.lean` |
| `forceLowOrderBound` | monotonicity in the Sobolev index for the **vector** norm: `fourierSobolevSq_mono`, `vectorFourierSobolevNorm_mono`, `eLpNorm_vectorFourierSobolevNorm_mono` (the tree had only the scalar `fourierSobolevNorm_mono_of_compact`) | `Bindings/Scaling.lean` |
| `scaledEquation`, `scaledDivergenceFree`, `scaledBlowup` | `zeroPastField_force`, `source_time_lt_one`, `scaled_equation`, `scaled_divergence_free`, `scaled_blowup` — thin, but the composition `parabolic_equation` + `PacketAPI.extension_navier_stokes` had no user | `Bindings/Scaling.lean` |
| `packetEnergyIdentity` | **new mathematics**: `eLpNorm_spatialGradient_sq_slice` (per-slice restatement of the I02 lemma), `le_essSup_of_le_on_pos_measure`, `continuousAt_l2Sq_zeroPastField`, `energyEssSup_scaled_le` and the `≥` half `le_energyEssSup_scaled`; the essential-supremum **equality** with the least upper bound `M` is the only consumer of `PacketAPI.energy_isLUB` as a *least* bound in the project | `Section4/I03/Energy.lean` |
| `packetDissipationIdentity` | `scaled_smoothOn`, `scaled_slice_contDiff`, `scaled_slice_hasCompactSupport`, `scaled_dissipation_integrableOn`, `scaled_total_dissipation`, `energyGradient_scaled_eq` | `Section4/I03/Energy.lean` |
| `perturbationEnergyBound` | the whole `E_T` triangle inequality: `energyEssSup_add_le`, `spatialGradient_add`, `energyGradient_add_le`, `energyENorm_add_le`, plus the two time-measurability dischargers `aemeasurable_eLpNorm_spatialGradient_of_contDiff(On)` (joint continuity of `(t,x) ↦ fderiv (z(t,·)) x` + Tonelli) and the eight slice-regularity lemmas of its §6 | `Bindings/ScalingEnergy.lean` |
| `packetMixedScaling` | `positiveMixedNorm`, `positiveMixedNorm_eq_volume`, `spatial_slice_norm_parabolicForce` (the `ENNReal` — not `.toReal` — spatial identity), `mixedNorm_parabolicForce`, `positiveMixedNorm_parabolicForce`, `eLpNorm_slicePath_eq`; plus `mixedLebesgueENorm_eq` (the infimum is attained) and `mixedLebesgueENorm_scaledForce` | `Section4/I03/Mixed.lean`, `Bindings/Scaling.lean` |
| `correctionPositiveScaling`, `correctionNegativeScaling`, `forceLowOrderBound` | `potential_eq`, `correction_eq`, `forceCorrection_eq` (§1), the window extension `window`, `exists_window_extension`, `temporalCutoff_zero_outside`, `correction_eq_extension`, `forceCorrection_eq_extension`, and `correction_cycles_positive/negative` | `Bindings/Scaling.lean` |
| `ε₀`, `eps_*` | `scalingThreshold` and its six properties, `carrier_subset_ball` | `Bindings/Scaling.lean` |

### Failed or abandoned approaches

1. **Copying the `I02` construction into `Bindings/Scaling.lean`** (≈430 lines).
   Started, then abandoned once §1's formula fields were noticed.  It would have
   worked but would have duplicated a frozen file and made
   `scalingStatement` deliver "some correction" instead of "`= C`".
2. **Deriving the correction's Sobolev decay from the abstract `CorrectionAPI`
   fields alone** (smoothness, compact support, `force_support`,
   `force_derivative_bound` at `m = 0`, `force_mixed_bound`).  Rejected: the
   `s`-dependence of `eq:RpositiveScale` is genuine, and monotonicity in `s`
   runs the wrong way (`‖z‖_{H^s} ≤ ‖z‖_{H^1}` gives `ε^{β(q,1)+1}`, which for
   `ε ≤ 1` is *larger* than the required `ε^{β(q,s)+1}`).  Reaching it would
   need Sobolev interpolation, which the tree does not have.
3. **Stating `forceLowOrderBound` with `negativeConst q r`** as `Spec.lean` does.
   Not provable through the angular/cycles bridge; see §3.
4. **Using `correction.energyConst` directly in `eq:REclose`.**  Not provable,
   and in fact false for a negative constant; see §2.
