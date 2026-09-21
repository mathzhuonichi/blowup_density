# ATTEMPTS — A04 `hpr` (pressure drop, SL4 / lane 121)

Target: the `hpr : ⟪G, P⟫ = 0` input of `A04.inner_energy_assembly`
(`Section4/A04/HighEnergy.lean`), `G` the order-`m` datum of `u(t,·)`, `P` that of `∇p(t,·)`.
New module `formalization/NSFormalization/Section4/A04/PressureDrop.lean` (namespace
`NSFormalization.Section4.A04`). Route chosen = the "cheap" operator-algebra route of
`research/D01/REVIEW_SL8_ASSEMBLY.md` §7 (Leray self-adjointness + solenoidality), NOT the
representative integration-by-parts route.

## What compiled (final)

Three recorded steps + four MAINT-flagged `L²`/ambient lemmas, all standard 3 axioms
(`research/A04/axioms_hpr.lean`), `lake build … PressureDrop` green, `lake env lean` silent,
`make check` green.

- `coordinates_inner_bilin` — bilinear form of `Leray.coordinates_inner_self`.
- `complementSymbolComplex_inner_left` — fibre symbol self-adjoint (`isSelfAdjoint_starProjection`).
- `lerayComplementL2_inner_left` — `lerayComplementL2` complex self-adjoint.
- `lerayComplementAmbient_inner_left` — ambient multiplier complex self-adjoint (conjugation by the
  `coordinates`/`assemble` `q=2` isometry).
- `carrier_inner_eq` — `⟪A,B⟫_ℝ = Re ⟪AmbA, AmbB⟫_ℂ` (lane-082 bridges).
- **(S)** `lerayComplement_selfAdjoint` + `inner_lerayComplement_eq_zero_of_eq_zero`.
- **(S–M)** `velocity_datum_lerayComplement_eq_zero` (+ helper `isSobolevDatum_zero`).
- **(S)** `pressure_drop` (the `hpr`), with the fit `example` against `inner_energy_assembly`.

## Route decisions / things ruled out

1. **Abstract "idempotent + `‖·‖≤1` ⟹ self-adjoint" (Route A) — not available in this Mathlib.**
   `lerayComplement` IS idempotent (`Leray.lerayComplement_idempotent`) and contractive
   (`Leray.lerayComplement_opNorm_le_one`), which classically forces an orthogonal projection.
   But Mathlib only has `IsIdempotentElem.isSelfAdjoint_iff_isStarNormal`
   (`Mathlib/Analysis/InnerProductSpace/Adjoint.lean:450`) and the CStar
   `isStarProjection_iff_isIdempotentElem_and_isStarNormal` — both need `IsStarNormal` as INPUT,
   which we do not have without the adjoint. `grep` for `_of_norm_le_one` / `isSelfAdjoint_of…` over
   `Mathlib/Analysis/InnerProductSpace/` found no contractive-idempotent lemma. So the abstract
   route was abandoned in favour of the explicit conjugation route.

2. **Explicit conjugation route (Route B) — used.** `Leray.lerayComplement s` is the restriction of
   `Leray.lerayComplementAmbient = coordinates ∘ lerayComplementL2 ∘ assemble`
   (`Leray.lerayComplement_toAmbient`). Self-adjointness reduces to (i) the fibre symbol
   `complementSymbolComplex ξ = (ℂ ∙ ξ_ℂ).starProjection` being self-adjoint
   (`isSelfAdjoint_starProjection` + `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`),
   propagated to `lerayComplementL2` via `lerayComplementL2_ae` + `L2.inner_def`; (ii) the
   `coordinates`/`assemble` `q=2` isometry preserving the complex inner product bilinearly
   (`coordinates_inner_bilin`, re-proved from `Leray.coordinates_ae` since the tree only exports the
   diagonal `Leray.coordinates_inner_self`); (iii) the carrier real inner product being `Re` of the
   ambient complex one (lane 082 `Paper3.real_inner_eq_re_complex` +
   `Paper3.realSobolev_inner_eq_ambient`, and `PiLp.inner_apply` + `map_sum` over `RCLike.re`).

3. **Step (S–M) lift order 0 → order m.** No injectivity/isometry lemma for `lowerVectorL` exists in
   `LerayLowering.lean`/`HalfOrder.lean` (checked), so the lift routes through
   `Leray.isSobolevDatum_lower_iff` + `isSobolevDatum_unique` instead: `lowerVectorL m 0 (I−P)ₘG = 0`
   (via `Leray.lerayComplement_lowerVectorL` + order-0 transversality of `u`), then the iff makes
   `(I−P)ₘG` an order-`m` datum of the zero field, and uniqueness against `isSobolevDatum_zero` gives
   `(I−P)ₘG = 0`. This mirrors lane 117's `isSobolevDatum_pressureGradient_lerayComplement`.

4. **Divergence in the `partialDeriv` shape is defeq.**
   `∑ j, partialDeriv j (fun y => u.velocity (t,y)) x j` is definitionally `spatialDivergence
   u.velocity t x`, so `hdiv := fun x => u.divergence t ⟨le_of_lt ht.1, ht.2⟩ x` typechecks with no
   conversion (same trick `MomentumSlice.sum_partialDeriv_temporalDerivative_eq_zero` relies on).

## Namespace pitfalls hit

- `MemForceR` is ambiguous under `open …D01` + `open …A02 (… MemForceR)` (two `rfl`-equal defs). Fix:
  open `A02` WITHOUT `MemForceR`, keep `open …D01`, so `MemForceR = D01.MemForceR`; it is defeq to
  the `A02.MemForceR` that `momentum_datum` uses, and D01 lemmas (`smoothL2_momentumResidual_slice`,
  `pin_pressureGradient_datum`) accept it — exactly as `MomentumDatum.lean` itself does.
- `RealSobolevHilbert` is `NSFormalization.Source.RealSobolev.RealSobolevHilbert`, NOT `Paper3.*`.
- `Paper3.realSobolevInnerProductSpace` (lane 053) IS on integration now
  (`Paper3/RealPositiveDensity.lean:27`), despite HighEnergy's stale "in PR" docstring.

## Probes (kept, standalone, no axioms)

`research/A04/probes/hpr_probe1.lean` (bilinear coordinates inner + fibre + L² self-adjoint),
`hpr_probe2.lean` (`carrier_inner_eq` + WithLp round trip). The full module supersedes them.

## Review follow-up (lane 121 reviewer — ACCEPT-WITH-NOTES, `research/A04/REVIEW_HPR.md`)

Accepted as-is; the notes below are record/MAINT items, applied here without changing any statement.

- **`velocity_datum_lerayComplement_eq_zero` holds verbatim on `Ico 0 T`.** The reviewer restated it
  with `ht : t ∈ Ico 0 T`, `set_option autoImplicit false`, and the **identical proof body**
  (including `hdiv := fun x => u.divergence t ht x`, the §4 defeq), standard axioms
  (`/tmp/rev121/ico.lean`). `Ioo` is inherited only because `pressure_drop` genuinely needs it —
  both `D01.smoothL2_momentumResidual_slice` (`MomentumSlice.lean:65`) and
  `D01.pin_pressureGradient_datum` (`PressureJets.lean:115`) take `t ∈ Ioo 0 T`. **Possible
  strengthening, NOT applied**: the statement is frozen at `Ioo` for the assembly's shape; the free
  `Ico` form (reusable at `t = 0`) is a V2/MAINT candidate.
- **MAINT (finding 9, MED): `velocity_datum_lerayComplement_eq_zero` duplicates
  `D01/PressureJets.lean` near-verbatim** — `:71-77` (`hi4`, order-0 transversality of `∂ₜu`) is
  line-for-line the `hc0` block, and `:97-112` (`isSobolevDatum_pressureGradient_lerayComplement`'s
  order-0→order-`m` lift) is the same `h0m`/`isSobolevDatum_lower`/`isSobolevDatum_unique`/
  `lerayComplement_lowerVectorL`/`isSobolevDatum_lower_iff` skeleton. Before the D01/A04 SIMP pass,
  factor a shared `D01.Leray` pair — `lerayComplement_datum_eq_zero_of_divergence_free` (subsuming
  both order-0 uses and this lane's order-`m` statement) + `lerayComplement_datum_lift` — and derive
  all three call sites from it.
- **`isSobolevDatum_zero` has now been hand-written by three lanes** (lane 117 probe, lane 121 module,
  the 121 review's appendix C). Not an in-tree duplicate today, but promote it next to
  `isSobolevDatum_unique` (`D01/ForceClass.lean:286`).
- **`exact?`/whnf-timeout caveat for the self-adjointness search.** A bare `exact? :
  IsSelfAdjoint T` from `IsIdempotentElem T` + `‖T‖ ≤ 1` dies with `(deterministic) timeout at whnf,
  maximum number of heartbeats (200000)` (`/tmp/rev121/neg.lean`) — the timeout must NOT be read as
  "the lemma might exist". Rewriting first via `IsIdempotentElem.isSelfAdjoint_iff_isStarNormal` and
  then `exact?` returns the honest `could not close the goal` (`/tmp/rev121/neg3.lean`). Route A is
  genuinely absent (confirms ATTEMPTS claim 1).
- **`A04/HighEnergy.lean:24` stale docstring** ("lane 053's instance in PR, not yet on integration")
  — it IS on integration (`Paper3/RealPositiveDensity.lean:27`). **Not edited here** (HighEnergy.lean
  is not this lane's file); flagged for the next SIMP pass, per the coordinator.
- **Bonus (finding 13): the full `energyIdentityHigh` assembles from in-tree lemmas** with this
  lane's `hpr`. Preserved as `research/A04/probes/energy_identity_high_probe.lean` (reviewer's
  `/tmp/rev121/assembly.lean`, compiled first try, standard axioms) with the lemma-per-slot recipe;
  consumer fits `fit_Rhigh`/`fit_chain` preserved as `research/A04/probes/fit_chain_probe.lean`.
