# I02 attempts and decisions

Lane `011-I02-contract`, branch `erenup/011-I02-contract`, 2026-09-13.
Outcome: `I02.correction` (V1) registered; `make check`, `make test`,
`make test-mutations` green; transitive axioms of
`BlowupDensity.Tests.checkedCorrection` exactly
`propext`, `Classical.choice`, `Quot.sound`.

This is the positive-and-negative record required by `CLAUDE.md` rule 4.  It is
**not** in `collaboration/tasks/I02.md`, which `experiments/tasks.py render`
overwrites wholesale.

## 0. What was built

| file | role |
|---|---|
| `verification/Contracts/V1/Correction.lean` | `CorrectionAPI ν P` (73 fields) + `correctionStatement` |
| `verification/Bindings/Correction.lean` | 13 bridge theorems + `Bindings.correction` |
| `verification/Tests/Correction.lean` | `checkedCorrection` + `run_cmd TestSupport.checkAxioms` |
| `formalization/NSFormalization/Section4/I02/Reference.lean` | slab → global congruence (units 1–2) |
| `formalization/NSFormalization/Section4/I02/Support.lean` | support measures, scaled plateau openness, packet vacuity (units 6–7) |
| `formalization/NSFormalization/Section4/I02/Energy.lean` | `E_T` transport into `Data.energyENorm` (unit 8) |
| `formalization/NSFormalization/Section4/I02/Mixed.lean` | `L^q_tL^p_x` transport into `Data.mixedLebesgueENorm` |

## 1. Rejected design: define `w_ε` from the globally extended reference `V`

The obvious route was to take `V` from `TimeExtension.exists_global_reference_extension`
and set `correction ε := physicalCorrection V x₀ T θ η ε`.  Every existing
estimate then applies verbatim, because they all assume `hv : ContDiff ℝ ∞ v`
globally.

**Rejected.**  `correction_formula` and `potential_formula` are stated with the
*given* `v` (that is what `eq:potential` and `eq:cutoff` say), and they are
required for **all** `ε`, not only small ones.  With `correction ε` built from
`V` those two fields would be false for large `ε`, and the only repair would be
to restrict them to `ε ∈ Ioc 0 ε₀` — a weakening of the accepted spec.

**Decision.**  Everything is defined from the *given* `v`:
`potential := RadialPotential.timePotential v x₀`,
`correction ε := physicalCorrection v x₀ T θ η ε`,
`forceCorrection ε := Source.correctionForce ν v (correction ε)`.
`potential_formula`, `correction_formula` and `force_formula` are then literally
`rfl`, for every `ε`.  Each *estimate* is transported from `V` through two
function equalities proved once in the binding:

* `hcorr : ∀ ε ∈ Ioc 0 ε₀, physicalCorrection v … ε = physicalCorrection V … ε`,
* `hforce : ∀ ε ∈ Ioc 0 ε₀, correctionForce ν v (…v…) = correctionForce ν V (…V…)`.

Both are *equalities of functions*, not just agreement on the window, because
off the window both sides vanish: at `|t − T| > δ₁ ≥ 2ε²` the temporal cutoff
`η_ε(t)` is zero, so `LocalCutoff.localCorrection_zero_of_time` kills the
correction, and `LocalizedInsertion.correctionForce_eq_zero_outside` kills the
force.  Inside the window the slices of `v` and `V` agree.

## 2. The slab/global mismatch is slicewise, so units 1–2 collapsed

`COMPARISON.md` §2 item 1 and `REVIEW.md`'s "largest remaining item" both
estimated the global-vs-slab bridge as the biggest piece, because
`hv : ContDiff ℝ ∞ v` occurs in roughly sixty declarations across
`PR/CP/CFP/CE/CMN/CVN/IE/LI`.  In fact **no** existing estimate had to be
re-proved.  The reason is that the reference enters the correction chain only
through one time slice at a time:

* `RadialPotential.timePotential v x₀ (t,x) = centeredPotential (v (t,·)) x₀ x`;
* `LocalCutoff.localCorrection` is a *spatial* curl of that potential;
* `Source.correctionForce ν v w (t,x)` touches `v` only as `v (t,x)` and
  `fderiv ℝ (v (t,·)) x`.

So three one-line congruence lemmas (`timePotential_congr_slice`,
`localCorrection_congr_slice`, `correctionForce_congr_slice`, all in
`Section4/I02/Reference.lean`) do the whole job, and the window extension `V` is
needed only as a *witness* for the estimates, never as the object the contract
talks about.  Follow-up **A** of `COMPARISON.md` ("a `ContDiffOn`-hypothesis
version of the whole `PR`/`CP`/`CFP` chain") is therefore **not** needed for
I02, and I03 can reuse the same two-line transport.

Two genuinely new statements were needed:

* `timePotential_contDiffOn` — the `ContDiffOn` companion of
  `RadialPotential.timePotential_contDiff`, for `potential_smooth` on the whole
  slab `(0,T+δ)` (not just the `2ε²` window).  Proof: at each slab time,
  `TimeExtension.timeTruncation` gives a globally smooth field agreeing with `v`
  on a time neighbourhood, and the potential of the two agree there by the
  congruence lemma, so `ContDiffAt` holds pointwise.  `exists_local_truncation`
  isolates that step.
* `spatialCurl_timePotential_on` — `potential_curl` needs **no** extension at
  all: `RadialPotential.curl_centeredPotential` only wants smoothness and
  divergence-freeness of the single slice `v (t,·)`, both of which
  `SpatialCurl.contDiff_spatialSlice` reads off the slab hypotheses.  The
  `∀ t, ∀ x` global `hdiv` in `RadialPotential.spatialCurl_timePotential` is an
  over-assumption of that declaration, not of the mathematics.

## 3. The two norm transports (the real work)

The contract states `eq:wE` and `eq:Hmixed` against the *registered* Section 4
norms `Contracts.V1.Data.energyENorm` and
`Contracts.V1.Data.mixedLebesgueENorm`, which are `ℝ≥0∞`-valued, not against the
implementation's real-valued `InsertionEnergy.energyNorm` and
`CorrectionMixedNorms.mixedNorm`.  Neither transport existed.

`Contracts/V1/Data.lean` lives in the `verification` package, so the
`formalization` modules cannot mention it.  The transport lemmas are therefore
stated about the raw expressions (`essSup (fun t => eLpNorm …)`,
`(∫⁻ t in Ioo 0 T, (eLpNorm …)^2)^{1/2}`, `⨅ over Lp paths`), and the final
identification is one `rfl` bridge in the binding (`energyENorm_eq`,
`spatialGradient_eq`, `mixedLebesgueENorm_le`).

### 3.1 `E_T`

`Section4/I02/Energy.lean`.  `eLpNorm_two_eq_ofReal_sqrt` identifies the spatial
`L²` seminorm with `ENNReal.ofReal ∘ Real.sqrt` of the Bochner square integral
(so the `ℝ≥0∞` bound is not vacuous), `norm_spatialGradient_sq` identifies the
`PiLp 2` gradient norm with `NavierStokesR3.CompactEnergy.dissipation`, and
`energyEssSup_le` / `energyGradient_le` turn the two existing *squared* `ε³`
bounds (`CE.physicalCorrection_uniform_energy`,
`IE.correction_gradientSquare_bound`) into the two `ℝ≥0∞` summands.
`sqrt_mul_cube` is the `√(Aε³) = √A · ε^{3/2}` step.

Neither `IE.energyNorm_le_of_squared_bounds` nor `IE.gradientNorm_eq_timeL2`
(the declaration `REVIEW.md` issue 4 asked `COMPARISON.md` to name) is used in
the end: both are about the real-valued `energyNorm`, and going through them
would have meant proving `ENNReal`-to-real round trips.  Going straight from the
two squared bounds to the `ℝ≥0∞` norm is shorter and avoids `toReal`.

**Failed first attempt.**  `eLpNorm_two_eq_ofReal_sqrt` was first stated only for
`f : Space → Space`.  Applying it to the gradient, which is
`Space → WithLp 2 (Fin 3 → Space)`, made Lean loop in `whnf` (200k and then 1M
heartbeats).  Generalising the codomain to any `NormedAddCommGroup` fixed it and
the file compiles in ~3 s.  The error message was a plain timeout, not a type
mismatch, so this cost two build cycles.

**Direction of `ENNReal.ofReal_rpow_of_nonneg`.**  It is
`ofReal x ^ p = ofReal (x ^ p)`, not the reverse; three `rw [← …]` had to become
`rw [… ]`.

### 3.2 `L^q(0,∞;L^p)`

`Section4/I02/Mixed.lean`.  `Data.mixedLebesgueENorm q p f` is an **infimum over
strongly measurable Bochner paths** `ℝ → L^p(R³)` that represent the slices of
`f`, over `(0,∞)`.  Bounding it means *exhibiting* one such path, and the only
real content is its strong measurability.

`continuous_slicePath` proves `t ↦ [H(t,·)] ∈ L^p` is continuous for `H`
continuous with compact spacetime support: `H` is uniformly continuous
(`HasCompactSupport.uniformContinuous_of_continuous`), all slices vanish off the
one compact set `Prod.snd '' tsupport H`, and `eLpNorm_le_of_ae_bound` on
`volume.restrict` of that set turns a uniform pointwise bound into
`(volume B)^{1/p} · ofReal ε'`.  This works uniformly in `p`, including
`p = ⊤`, because `⊤.toReal⁻¹ = 0` and `x ^ 0 = 1`.  Continuity gives strong
measurability because `ℝ` is second countable.  `exists_slicePath` then packages
the path with `eLpNorm G q positiveTimeMeasure ≤ CMN.mixedNorm p q H`; the
inequality is `Measure.restrict_le_self` plus `Lp.enorm_toLp`, and it is an
inequality only because `CMN.mixedNorm` integrates time over all of `ℝ` while
the registered norm uses `(0,∞)`.

**`Fact (1 ≤ p)`.**  `Data.mixedLebesgueENorm` needs it for the `Lp` norm, so the
contract field quantifies `∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)]`.  In the binding,
`exists_slicePath` has `p` only in its conclusion, so it must be applied as
`exists_slicePath (p := p) …`; without that the instance search reports
`Fact (1 ≤ ?m)` stuck.

## 4. Compile failures worth recording

* **`obtain` in a `Type`-valued goal.**  Same pitfall as I01 §3: the binding's
  goal is `CorrectionAPI ν P`, a `Type`, so `obtain ⟨V, …⟩ := exists_…` fails
  with "recursor `Exists.casesOn` can only eliminate into `Prop`".  Five
  `obtain`s became `choose` (`V`, `Rb`, `θ/O`, `η`, `Ae`, `De`).  The `obtain`
  inside the `force_mixed_bound` field is fine, because that goal *is* a `Prop`.
* **`SpatialCurl.contDiff_spatialSlice` is typed for `VelocityField`.**  Using it
  on the pressure `π : PressureField` elaborated into a nonsense goal.  The
  pressure slice uses `hπ.comp_contDiff (contDiff_const.prodMk contDiff_id) …`
  instead, the pattern of `LocalizedInsertion.inserted_equation`.
* **`simpa` does not unfold `Contracts.V1.spatialDivergence`.**  Its closing
  `exact` failed against the upstream `spatialDivergence` even though the two are
  `rfl`-equal (the bridge is in `Bindings/Packet.lean`).  A preceding `show` with
  the upstream spelling fixes it.  Plain `exact` and `rw` were fine throughout.
* **`isDefEq` blowup inside the big `def`.**  `iInf_le _ ⟨G, …⟩` against the
  unfolded `Data.mixedLebesgueENorm` timed out at 2M heartbeats *inside* the
  assembly (about forty hypotheses in context) and succeeds instantly as the
  standalone `mixedLebesgueENorm_le`.  The same treatment (`energyENorm_eq`,
  proved by `rfl` at top level) removed a second timeout in
  `correction_energy_bound`.  Lesson: unfold registered `Data` definitions in a
  top-level `rfl` lemma, never inside the assembly.
  `set_option maxHeartbeats 2000000` is still set on `Bindings.correction`; the
  assembly is 300 lines with a large local context.
* **`positivity` cannot see `set`-bound positivity.**  `0 ≤ (ε * R)^3` with
  `R : ℝ := Rb + 1` introduced by `set` failed; `pow_nonneg (mul_nonneg …) 3`
  works.
* **`rw [← ENNReal.ofReal_toReal h]` rewrites too much.**  In
  `force_mixed_bound` it also rewrote the `Cm p q` *inside* the right-hand
  `(Cm p q).toReal`, leaving
  `(ENNReal.ofReal (Cm p q).toReal).toReal`.  Rewriting forward
  (`ENNReal.ofReal_mul`, then `ENNReal.ofReal_toReal`, then `mul_comm`) is the
  clean order.

## 5. Fields that needed a new lemma

Everything else is a projection or a one-line composition of existing
declarations.

* **`potential_smooth`** — `timePotential_contDiffOn` (new; §2).
* **`potential_curl`** — `spatialCurl_timePotential_on` (new wrapper; §2).
* **`correction_cancels`** — the open-neighbourhood form of `eq:bgzero` needed
  two new pieces: `isOpen_spaceMap_image` (the scaled plateau `x₀ + ε·O` is open,
  since `y ↦ x₀ + ε•y` is a homeomorphism for `ε ≠ 0`) and
  `scaledPacket_slice_empty` (**the vacuity step** that `REVIEW.md` issue 5 asked
  for: for `t ≤ t_ε = T − ε²` the rescaled packet slice is identically zero, so
  `O = ∅` is an admissible open neighbourhood).  Without the second, the field is
  false on `(0, t_ε]`, because `PR.physical_removes` only cancels on
  `[T−ε², T+ε²]` and `v + w_ε` is generally nonzero on the plateau before that.
* **`force_spatial_volume`, `force_time_length`** — `spatial_support_volume` and
  `temporal_support_length` (new).  `Measure.addHaar_ball` gives
  `volume (ball x₀ (εR)) = ofReal ((εR)³) · volume (ball 0 1)`, so
  `spatialVolumeConst = R³ · (volume (ball 0 1)).toReal`; the duration is
  `Real.volume_Ioo` on `(T−2ε², T+2ε²)`.  No declaration in the tree measured
  either support.
* **`correction_energy_bound`** — §3.1 (new module).
* **`force_mixed_bound`** — §3.2 (new module).
* **`correction_gradient_memLp`** — `continuous_spatialGradient`,
  `hasCompactSupport_spatialGradient`, `spatialGradient_memLp` (new, in
  `Energy.lean`); `PiLp.continuous_toLp` is the step that was not obvious.
* **`perturbation_divergence_free`** — `LocalizedInsertion.inserted_divergence`
  instantiated at `v := 0` (its statement is for `v + w + U`), plus
  `PS.dilate_smoothOn` and `PS.delayed_parabolic_divergence` for `U_ε`.  Split
  unit 10 predicted exactly this.  The `Ico 0 T` of `REVIEW.md` issue 1 comes for
  free from `inserted_divergence`.

## 6. Deviations from the accepted `research/I02/Spec.lean`

All are either instructed, review-mandated, or strengthenings.  None weakens a
statement.

1. **Packet fields replaced by the registered `I01.packet` API.**  The structure
   is `CorrectionAPI (ν : ℝ) (P : Contracts.V1.PacketAPI ν)`, and the draft's
   nine packet fields (`packet`, `carrier`, `carrier_compact`, `packet_support`,
   `packet_divergence_free`, `packet_smooth`, `packetQuietTime`,
   `packet_quiet_pos`, `packet_quiet`) are gone; `P.velocity`, `P.carrier`,
   `P.carrier_compact`, `P.velocity_support`, `P.divergence_free` and
   `P.velocity_extension_smooth` are used instead.  `viscosity_pos` is
   `P.viscosity_pos`.
   *Consequence worth flagging:* the draft's `carrier` was the **enlarged** `K_*`
   of `03-torus.tex:101-102` (containing `K` and the spatial projection of
   `supp F`), while `P.carrier` is the packet's own `K`.  I02 only ever uses the
   *velocity* support, so `K` suffices and the plateau condition
   `carrier_subset_plateau` is correspondingly weaker (easier to satisfy) — the
   contract is not weakened, because nothing in I02 asserts anything about
   `supp F`.  I03/R42 must supply the enlargement themselves; `IF:218-234`
   already builds it inline.
2. **`perturbation_divergence_free` on `Ico 0 T`** instead of `Ioo 0 T`
   (`REVIEW.md` issue 1).  Strengthening.
3. **`reference_pressure_smooth` added.**  `Source.corrected_background` needs
   `DifferentiableAt ℝ (π (t,·)) x`, and the draft assumed no regularity of `π`
   at all.  The manuscript's hypothesis is "a reference solution `(v,π,g)` smooth
   on `[0,T+δ]`" (`03-torus.tex:164`), so this is a paper hypothesis that the
   draft simply dropped; without it `corrected_background` is not provable.  It
   is a *hypothesis* field, so adding it weakens the contract slightly; it is the
   minimum the display of `03:321-325` needs.
4. **The two bounds use the registered `Data` norms** (`energyENorm`,
   `mixedLebesgueENorm`) rather than `InsertionEnergy.energyNorm` and
   `CorrectionMixedNorms.mixedNorm`.  Both registered norms are `ℝ≥0∞`-valued, so
   the bounds cannot be met vacuously; `mixedLebesgueENorm` also runs over the
   manuscript's `(0,∞)` rather than all of `ℝ`.
5. **`correction_energy_memLp` split and restated.**  The draft asserted
   `MemLp (velocityL2 w) ⊤` and `MemLp (gradientL2 w) 2` — both
   `InsertionEnergy` notions, not importable into a contract.  They are replaced
   by the slicewise `correction_slice_memLp`
   (`MemLp (w (t,·)) 2 volume`) and `correction_gradient_memLp`
   (`MemLp (Data.spatialGradient w t ·) 2 volume`), which are what removes the
   totalization caveat in `Data.energyEssSup` / `Data.energyGradient`.
6. **`correctionStatement` reflowed** (`REVIEW.md` issue 2).  It is now
   parameterised by `P : PacketAPI ν` (so the quiet time lives in `P`, and the
   draft's dangling `∀ τ` binder is gone) and it pins seven data identities
   `A.T = T ∧ A.δ = δ ∧ A.v = v ∧ A.π = π ∧ A.g = g ∧ A.x₀ = x₀ ∧ A.r = r`, so no
   extension of the reference may be substituted for `v`.
7. **Docstring citations renumbered** (`REVIEW.md` issue 3): `ν,T>0` → `04:8`;
   `δ>0` and "any nonempty open ball" → `04:32`; the `b_ε` expansion → `04:51`;
   "each summand … divergence free" → `03:332`.

## 7. Paper / Lean differences found

* **`α(p,q)` sign convention.**  The paper writes the correction-force bound as
  `ε^{-2+3/p+2/q} = ε^{α(p,q)+1}` (`03:235-237`); the Lean source
  (`CMN.physical_force_mixed_bound`) carries the first spelling and the contract
  the second.  `Bindings.alpha_add_one` proves they agree, endpoints included
  (`⊤.toReal = 0`).
* **`η` is smaller than the paper's.**  `LC.exists_temporal_cutoff 0 1` returns a
  `ContDiffBump` with support `closedBall 0 (3/2)`, strictly inside the paper's
  `(-2,2)`.  Harmless: `eta_support` is an upper bound.
* **The paper's `∂_x^β` is a multi-index; the Lean bound is directional.**  Both
  derivative fields use `m` spatial directions of norm ≤ 1 (and `j` unit time
  directions), which is the shape of `CP:291` and `CFP:270`; the coordinate form
  is the case `u i = coordinateVector (β i)`.  Section 4 only uses `m = 0`
  (`04:68`).
* **`B = ball x₀ r` with the scaling centre at the ball centre** (clarification
  C2).  The paper leaves `x₀ ∈ B` free.  Every nonempty open ball contains a
  concentric sub-ball, so nothing is lost; recorded in the `r` docstring.
* **`ε₀` recipe.**  The paper says "for sufficiently small `ε`".  The binding
  takes `ε₀ = min 1 (min (r/(R+1)) √(δ₁/2))` with `δ₁ = min(T,δ)/4`, which gives
  `ε R < r`, `2ε² ≤ δ₁` (needed for the window congruence, and strictly stronger
  than the paper's `2ε² < min(T,δ)`) and `ε ≤ 1` (the normalization under which
  all the source constants are uniform).

## 8. Not verified by this lane

* The mathematics of the `Paper1`/`Source` correction chain itself.  The binding
  demonstrably inhabits `CorrectionAPI` on standard axioms, but the
  597-module closure of `Tests.Correction` was not re-audited.
* `eq:HHs` and every fractional/negative-order bound — `I03`, by design.
* Theorem 4.2's lifespan, blow-up and density conclusions — `R42`.
* **`experiments/check_contracts.py --base-ref erenup/integration` currently
  fails, for a reason unrelated to this lane.**  `erenup/integration` moved on
  after this worktree branched (`acef508`, "Data.lean: correct the s >= 3/2
  docstring and the L1-cap-L2 caveat", plus lanes 013/014/015 bookkeeping), so
  the checker sees `verification/Contracts/V1/Data.lean` as "changed".  The diff
  is **docstrings only** and in the opposite direction (integration is newer).
  Against the lane's merge base `c8bde6e` the same command passes with
  `base_compatibility_checked: true` and three registered contracts.  The lane
  needs a rebase onto `erenup/integration` before the PR; nothing in
  `Correction.lean`, the binding or the new proof modules depends on the changed
  docstrings.
