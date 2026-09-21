# R42 — Theorem 4.2 clause by clause (lane 027, `R42.insertion_family` v1)

Source of truth: `paper/sections/04-whole-space.tex:31-79` (`thm:Rinsert`), with the torus twin
`paper/sections/03-torus.tex:290-340` (Theorem 3.6) for the two clauses Theorem 4.2's *statement*
omits but its proof and Theorem 4.7 use. Skeleton compared against:
`research/section4/STATEMENTS.md` §2 (`RInsertAPI`).

Contract: `verification/Contracts/V1/InsertionFamily.lean` (`InsertionFamilyAPI ν P`).
Binding: `verification/Bindings/InsertionFamily.lean` (`Bindings.insertionFamily`).
Proof module: `formalization/NSFormalization/Section4/R42/Assembly.lean`.
Acceptance: `verification/Tests/InsertionFamily.lean` (`checkedInsertionFamily`).

Everything below is for **one** family and **one** threshold `ε₀ = Bindings.threshold S`.

Registered scope (`verification/contracts.json`): Theorem 4.2's inserted family and all its
quantitative clauses **except** the maximal-lifespan identification and the reference-lifespan
clause; `g_ε ∈ F_R` and the `ClassicalSolutionR` fields `sobolev`/`pressure_gradient` for `u_ε`
are **not** asserted (§4.3); the blow-up clause is registered in the pointwise
`SpeedUnboundedAt` form (§4.1).

## 1. The statement's own clauses

| # | Theorem 4.2 clause (line) | `InsertionFamilyAPI` field | supplied by | gap |
|---|---|---|---|---|
| 0 | `(v,π,g)` is *the* solution, regular through `T+δ` (`:32`) | `reference`, `reference_velocity`, `reference_pressure` | `Data.ClassicalSolutionR ν a g (T+δ)`, a hypothesis field | the definite article (`T+δ < T_max`) is **excluded**, see §3 |
| 1 | `T^ν_{max,R}(a,g_ε) = T` (`:34`) | — | — | **excluded**, `InsertionLifespanAPI.lifespan`, needs A02 + A03 |
| 2 | `limsup_{t↑T}‖u_ε(t)‖_∞ = ∞` (`:35`) | `blowup` | `ScalingAPI.scaledBlowup` + `CorrectionAPI.correction_cancels_germ` via `Source.inserted_speed` | form deviation, §4.1 |
| 3 | `u_ε = v` on `0 ≤ t ≤ T-2ε²` (`:36`) | `history` | `CorrectionAPI.correction_vanishes_before` + `PacketScaling.zeroPast_dilate_early` | none |
| 3′ | "the same initial velocity" (`:13`, `:53`) | `initial` | `ClassicalSolutionR.initial` + `history` at `t = 0` | none |
| 4 | velocity difference supported in `B` for `t < T` (`:37-38`) | `velocityDifference_support` | `CorrectionAPI.correction_support_ball`; `PacketScaling.delayed_full_support` + `ScalingAPI.carrier_subset` + `ScalingAPI.eps_space` | none |
| 5 | `g_ε - g ∈ C_c^∞(B × (0,∞))` (`:38`) | `forceDifference_compact` (the `C_c^∞(R³×(0,∞))` half) + `forceDifference_ball` (the `B` half) | `CorrectionAPI.force_smooth/force_compactSupport/force_positive_time/force_support_ball`; `PacketScaling.parabolicForce_smooth/parabolicForce_positive_support` + the new `R42.parabolicForce_ball` | the `B` half needs the `K → K_*` enlargement, §4.2 |
| 6 | `‖u_ε-v‖_{E_T} ≤ (M+D)ε^{1/2}+Cε^{3/2}` (`:39-41`) | `energyRate` | `ScalingAPI.perturbationEnergyBound` verbatim | none |
| 7 | `‖g_ε-g‖_{L^q_tH^s} → 0` for `s < 2/q-3/2`, `q ∈ {1,2}` (`:42`) | `forceConvergence` | `ScalingAPI.forceConvergence` verbatim | none |
| 8 | "all of these conclusions hold for the same family" (`:43`) | structural: one `ε₀`, one `velocity/pressure/force`, one carried `scaling` record | — | none |
| 9 | "there are `g_ε ∈ F_R` and a solution `u_ε`" (`:33`) | partially: `velocity_smooth`, `pressure_smooth`, `initial`, `incompressible`, `momentum` | see §2 | `g_ε ∈ F_R` and two `ClassicalSolutionR` fields missing, §4.3 |

## 2. The proof's clauses that the statement does not display

| Proof clause (line) | field | supplied by | gap |
|---|---|---|---|
| `u_ε = v + w_ε + U_ε`, `p_ε = π + P_ε`, `g_ε = g + H_ε + F_ε` (`:47-49`) | `velocity_formula`, `pressure_formula`, `force_formula` (`rfl`) | definitions `Bindings.insertedVelocity/insertedPressure/insertedForce` | none |
| "the two cross terms vanish pointwise everywhere, and the equation is exact" (`:50-51`) | `momentum` | `CorrectionAPI.corrected_background` + `ScalingAPI.scaledEquation` + `CorrectionAPI.correction_cancels_germ`, composed by the new `R42.inserted_equation_slab` over `Source.exact_insertion` | none |
| incompressibility of `u_ε` (`eq:NS`; torus twin `03-torus.tex:332`) | `incompressible` | `ClassicalSolutionR.divergence` + `CorrectionAPI.perturbation_divergence_free`, composed by the new `R42.inserted_divergence_slab` | none |
| "the pressure difference may be chosen to be the compact scalar `P_ε`" (`:51`) | `pressureDifference_formula` (the gauge choice, `p_ε-π = P_ε`) + `pressureDifference_support` (compactness inside `B`) | `pressure_formula`; `PacketScaling.delayed_pressure_support` + `PacketAPI.pressure_support` + `ScalingAPI.carrier_subset` | none |
| `u_ε - v` divergence free (`03-torus.tex:295, 332`; consumed by Thm 4.7 at `:306,:308`) | `velocityDifference_divFree` | `CorrectionAPI.perturbation_divergence_free` verbatim | none |
| smoothness of the inserted triple on `[0,T)×R³` | `velocity_smooth`, `pressure_smooth` | `ClassicalSolutionR.velocity_smooth/pressure_smooth`, `CorrectionAPI.correction_smooth`, `PacketAPI.velocity_extension_smooth`/`pressure_extension_smooth` through the new `R42.dilate_smoothOn_target` | none |

`research/section4/REVIEW.md:77-88` requires `R42` to re-export `velDivFree` and `pressureCompact`;
both are present, with the provenance that file demands (`I02` for the first, the proof's gauge
choice for the second).

## 3. Excluded on purpose: `InsertionLifespanAPI` (unregistered)

`Contracts/V1/InsertionFamily.lean`, last structure. Two fields, **not** in `contracts.json`:

* `referenceLifespan : ofReal (T+δ) < maximalLifespanR ν a g` — the definite article of
  `04-whole-space.tex:32`. From `InsertionFamilyAPI.reference` one gets only
  `ofReal (T+δ) ≤ maximalLifespanR ν a g` (`maximalLifespanR` is a supremum over horizons
  carrying *a* classical solution, `Data.lean:657`), and no uniqueness at all. **A02.**
* `lifespan : maximalLifespanR ν a g_ε = ofReal T` — `04-whole-space.tex:34`. The `≥ T` half
  needs `prop:local`'s uniqueness plus the two missing `ClassicalSolutionR` fields of §4.3;
  the `≤ T` half is `04-whole-space.tex:53`: an extension through `T` is bounded in `C_tH²`,
  hence in `L^∞` by `A03` (`eq:Rproduct`), contradicting `blowup`. **A02 + A03.**
  `A03.bounded_representative` is registered but only in the *jet* form
  (`Contracts/V1/BoundedRepresentative.lean`); its equivalence with the datum form
  `Data.MemHInfty` is explicitly not asserted there, so even the `≤ T` half is two steps away.

`Source/InsertionBreakdown.lean` proves a lifespan *equality* already, but against
`SmoothLifespan.Flow`, not `Data.ClassicalSolutionR`/`maximalLifespanR`; it is not reusable here
without a bridge between the two lifespan notions. Recorded, not attempted.

## 4. Interface gaps found

### 4.1 `blowup` is the pointwise form, not `limsup = ⊤`

`research/section4/STATEMENTS.md:255-258` asks for
`⟪D01:limsupLeft⟫ T (fun t => normLinfty (u_ε t)) = ⊤` and says "do not substitute the equivalent
`¬ BoundedNear` restatement". The registered contracts supply only
`Contracts.V1.SpeedUnboundedAt` (`Scaling.lean:131`, `PacketAPI.speed_unbounded`,
`ScalingAPI.scaledBlowup`), the pointwise reading, and `Data.lean` has **no** `L^∞` norm and no
left limsup at all. Why the pointwise form is the right one to register, as the field's docstring
now says:

1. it is what `PacketAPI.speed_unbounded` and `ScalingAPI.scaledBlowup` produce, so no
   translation layer is invented at the assembly; and
2. it is **equivalent** to the displayed clause for every inhabitant of this record. In isolation
   the pointwise statement is the *weaker* one — an essential supremum above `M` forces a
   positive-measure set of such points, hence a point, not conversely. What closes the converse
   is `velocity_smooth`, which this record co-carries: for `t ∈ Ioo 0 T` the slice is continuous,
   so one witness point opens a nonempty open, hence positive-measure, set on which the same
   strict inequality holds, forcing `esssup > M`.

(The first draft of this file and of the docstring claimed the pointwise form was *stronger*
"since it exhibits points", and justified it by `v` being possibly unbounded. Both were wrong —
an unbounded `v` trivializes both readings equally — and were corrected before merge.)

Action for D01: the literal display needs a spatial `L^∞` e-norm (`eLpNorm · ⊤ volume` on the
slice), `limsup … (𝓝[<] T) = ⊤`, and the bridge "continuous slice ⇒ `essSup = ⨆ x, ‖·‖ₑ`". With
those three, `blowup` gives the display immediately, since the witnesses are points of
`supp U_ε` where `u_ε = U_ε`. The deviation from `research/section4/STATEMENTS.md:255-258` is now
recorded in the `contracts.json` scope, not only in the docstring.

### 4.2 `K → K_*`: `ScalingAPI.eps_space` is calibrated to the wrong carrier — MEDIUM

This is the gap flagged by `research/I03/REVIEW_CONTRACT.md` §5.1 item 4 and
`research/I02/ATTEMPTS.md` §6 item 1, met head-on by the assembly.

* The manuscript's `K_*` (`03-torus.tex:101-102`) contains the packet carrier `K` **and** the
  spatial projection of `supp F`. `CorrectionAPI.carrier_subset_plateau` mentions only
  `P.carrier = K`, `theta_support` ties `θRadius` to `supp θ`, and `ScalingAPI.eps_space` reads
  `ε * θRadius < r`. **No registered field relates `θRadius` to `supp F`**, and
  `correctionStatement` existentially binds `θRadius`, so a consumer that obtains its
  `CorrectionAPI` through `checkedCorrection` cannot recover the relation.
* Consequence: clause 5's `B` half (`supp(g_ε-g) ⊆ B`) is **not derivable from `ScalingAPI`
  alone**. `ScalingAPI.carrier_subset` puts `U_ε` and `P_ε` inside `B`; nothing puts `F_ε` there.
* **How R42 discharges it, without weakening anything.** `PacketAPI.force_support.1` is
  `HasCompactSupport P.force`, so `Prod.snd '' tsupport P.force` is compact, hence bounded:
  `R42.exists_spatial_radius` produces `R_F > 0` with `supp F` projecting into `ball 0 R_F`
  (`Section4/R42/Assembly.lean`). `Bindings.threshold S := min S.ε₀ (r / (R_F + 1))` then forces
  `ε * R_F < r` (`Bindings.force_space_bound`), and `R42.parabolicForce_ball` concludes.
  This is exactly what `Source/InsertionFamily.lean:218-234` does inline
  (`Kall = K ∪ Prod.snd '' tsupport f`), lifted to the contract layer.
* **Price, and what should change upstream.** `InsertionFamilyAPI.ε₀` is `≤ ScalingAPI.ε₀` —
  the field `eps_le_scaling` is an inequality and the witness is the `min` above, so equality
  holds exactly when `S.ε₀ ≤ r/(R_F+1)` and the bound is strict otherwise. Every `I02`/`I03`
  bound survives on the smaller range, so nothing is lost mathematically, but the "same family"
  identity now carries two thresholds. The clean repair is an `I02` V2 in which
  the caller may pin `θRadius` above a prescribed compact set — then `eps_space` alone would
  place all five rescaled fields in `B` and `R42` could take `ε₀ = S.ε₀`. Until then every
  consumer of `I03` that touches `F_ε`'s support pays this same shrink.

### 4.3 `g_ε ∈ F_R` and the missing two `ClassicalSolutionR` fields — the real blocker for A02

Theorem 4.2 asserts `g_ε ∈ F_R` and that `u_ε` is *a solution*. `InsertionFamilyAPI` gives the
inserted triple as a classical trajectory (`velocity_smooth`, `pressure_smooth`, `initial`,
`incompressible`, `momentum`) but **not** `Data.ClassicalSolutionR ν a g_ε T`, and **not**
`Data.MemForceR g_ε`. Both are blocked on the same missing D01 unit, and both were deliberately
not attempted in this lane:

* `Data.MemForceR f` (`Data.lean:544`) requires, for every `m : ℕ`, a datum path
  `G : ℝ → RealVectorSobolev m` with `IsSobolevPath m f G`, **`ContDiffOn ℝ ∞ G futureTimes`**,
  and `MemLp G 1/2 forceTimeMeasure`. `Section4/I03/Angular.lean` builds exactly such a path for
  a *smooth compactly supported* field (`angularPath`, `angularPath_pairing`,
  `memLp_angularPath`) — but **not** its `ContDiffOn` in time, which nothing in the project
  constructs, and not the additivity `IsSobolevPath m g G₁ → IsSobolevPath m φ G₂ →
  IsSobolevPath m (g+φ) (G₁+G₂)` needed to add it to the reference force. The statement wanted
  is `F_R + C_c^∞(R³×(0,∞)) ⊆ F_R`, listed as a D01 need at
  `research/section4/STATEMENTS.md:270` and not yet a lemma.
* `Data.ClassicalSolutionR`'s remaining two fields are `sobolev` (a *continuous* order-`m` datum
  path for `u_ε` on `Ico 0 T`) and `pressure_gradient` (`∇p_ε ∈ L²` slicewise). The second is
  routine (`MemLp.add` on `ClassicalSolutionR.pressure_gradient` and the compactly supported
  smooth `∇P_ε`); the first needs the same datum machinery as `MemForceR`, in a
  continuous-in-time form.

The easy half of clause 1, `ofReal T ≤ maximalLifespanR ν a g_ε`, **is statable** — it is a
well-formed `Prop` — but it is **undischargeable** here: the supremum in `maximalLifespanR` ranges
over `Nonempty (ClassicalSolutionR ν a f S)`, and nothing produces an inhabitant at `f = g_ε`.
So the `≥ T` half of the lifespan is *not* purely an A02 obligation: it needs this D01 unit first.
And the D01 unit alone will not close it either — `InsertionFamilyAPI` deliberately carries no
`hg : Data.MemForceR scaling.correction.g`, and since `g_ε = g + H_ε + F_ε`, an `R42` V2 asserting
`memF` must add that hypothesis field (`research/R42/ATTEMPTS.md` §5b item 2).

### 4.4 Two smaller interface frictions (no action needed)

* `Source.inserted_equation`/`inserted_divergence` (`Source/LocalizedInsertion.lean:96,132`)
  demand a *globally* smooth reference (`ContDiff ℝ ∞ v`, `∀ t x, div v = 0`). A
  `Data.ClassicalSolutionR` is smooth only on `Ico 0 (T+δ) ×ˢ univ`. The two slab versions
  `R42.inserted_equation_slab` / `inserted_divergence_slab` are the whole content of the new
  proof module; they consume `Source.exact_insertion` unchanged.
* `NavierStokes.SpatialCurl.contDiff_spatialSlice` is stated for `VelocityField` only, so the
  pressure slices go through `ContDiffOn.comp_contDiff` by hand.

## 5. Deviations from `research/section4/STATEMENTS.md` §2(iv) `RInsertAPI`

| skeleton field | here | why |
|---|---|---|
| `ν T δ`, `hν hT hδ`, `thresholds`, `a g ha hg`, `v π`, `B hB` | inside the carried `scaling.correction` and `reference` | `I02`/`I03` already fix `T`, `δ`, `v`, `π`, `g`, `x₀`, `r`, `ThresholdAPI`; restating them would create identities for `R42` to discharge. `ha : a ∈ X_R` and `hg : g ∈ F_R` are **not** fields: nothing below uses them, and `ClassicalSolutionR` already carries the regularity actually consumed |
| `isSol`, `lifespan` | absent | §3, §4.3 |
| `referenceLifespan` | `InsertionLifespanAPI` | §3 |
| `memF` | absent | §4.3 |
| `blowup` (`limsupLeft = ⊤`) | `SpeedUnboundedAt` | §4.1 |
| `history`, `velSupport`, `velDivFree`, `forceDiff`, `pressureCompact`, `energyRate`, `forceConvergence` | `history`, `velocityDifference_support`, `velocityDifference_divFree`, `forceDifference_compact`+`forceDifference_ball`, `pressureDifference_formula`+`pressureDifference_support`, `energyRate`, `forceConvergence` | same content; `forceDiff` and `pressureCompact` are each split into the class half and the ball half so that the unprovable-from-`I03` part (§4.2) is isolated |
| — | `velocity_smooth`, `pressure_smooth`, `initial`, `incompressible`, `momentum`, the three `*_formula` | added: the proof's own conclusions, and the part of "a solution `u_ε`" that *is* available |

The `0 ≤ t` guards of the skeleton are kept on every velocity/pressure clause; the force clauses
carry no guard (clarification `C3`). `momentum` uses `Ioo 0 T`, matching
`Data.ClassicalSolutionR.momentum` and `PacketAPI.navier_stokes`, because `temporalDerivative` is
two-sided.

## 6. What downstream can now use

`R47` (`04-whole-space.tex:306-308`) consumes `velocityDifference_support`,
`velocityDifference_divFree`, `pressureDifference_support` and `forceDifference_ball` — all
present. `R46`'s `L²_tḢ^{-1}` clause still blocks on `HomogeneousScalingAPI` (I03 §5), untouched
here. `R41D` needs `lifespan`, so it still blocks on §3.
