# ATTEMPTS — lane 073, D01, SL3 (+SL2): operator-valued L² Leray-complement multiplier

Module: `formalization/NSFormalization/Section4/D01/LerayMultiplier.lean`
(sorry-free; `#print axioms` standard, `research/D01/axioms_sl3.lean`, 21 declarations).

## Carrier / order-weight resolution (the key question)
- `Source/RealSobolev.lean`: `realSubspace (_s : ℝ)` **discards `s`** — it is
  `(⊥).comap (realSymmetry - id)` on `FourierData = Lp ℂ 2 volume`, independent of `s`.
  `RealSobolevHilbert s := realSubspace s`, so `RealVectorSobolev m = Product (Fin 3)(RealSobolevHilbert m)`
  is literally the SAME ℝ-Hilbert space for every `m` (lane 051 finding confirmed). Order/angular
  content lives only in `IsSobolevDatum`'s `angularRealization`, which the 0-homogeneous symbol does
  not touch. Consequence: a single operator serves every Sobolev order — no order weight to carry.
- Raw vector carrier: `R3L2Velocity = Lp R3C 2 volume`, `R3C = EuclideanSpace ℂ (Fin 3)`,
  `R3 = EuclideanSpace ℝ (Fin 3) = Space`. `Product (Fin 3) ℂ = EuclideanSpace ℂ (Fin 3) = R3C`
  (defeq), so `FiniteHilbertBochner.assemble 2 volume` / `coordinates 2 volume` is the bridge
  between the datum carrier (`PiLp 2` OF scalar `Lp`) and the raw carrier (`Lp` OF a `PiLp 2`,
  where the matrix acts pointwise).

## Template used (what worked)
- **Complex complement symbol**: defined fresh `complementSymbolComplex ξ := (ℂ ∙ r3FrequencyVectorComplex ξ).starProjection`,
  mirroring HeliCorgi `r3LeraySymbolComplex ξ = (ℂ∙ξ_C)ᗮ.starProjection`. All fibre algebra
  (apply, opNorm≤1, idempotent, kills-transverse, `P+(I−P)=I` via `Submodule.starProjection_orthogonal_val`)
  from the same `Submodule.starProjection_*` lemmas — exactly as the reviewer predicted.
- **Bundled CLM**: mirrored `R3LerayPointwiseL2.lean`'s pointwise action + `MemLp.of_le`, then
  BUNDLED (HeliCorgi leaves it a bare function): `→ₗ[ℂ]` (map_add/map_smul proved via a.e.
  + `Pi.add_apply`/`Pi.smul_apply` normalisation), `LinearMap.mkContinuous 1` with the norm bound
  `Lp.norm_le_norm_of_ae_le` (Mathlib LpSpace/Basic.lean:342). `restrictScalars ℝ` gives the `→L[ℝ]`
  form. `LinearMap.mkContinuous_norm_le` gives `‖·‖ ≤ 1`. a.e. action = `MemLp.coeFn_toLp`.
- **Reality (SL2)**: vector `realSymmetryVec = conjugationVec ∘ reflectionVec` on `R3L2Velocity`,
  with `conjR3C := LinearIsometryEquiv.piLpCongrRight 2 (fun _ => Complex.conjLIE)`. Pointwise symbol
  facts: even (`complementSymbolComplex_neg`), commutes with conjugation (`conjR3C_complementSymbolComplex`,
  via `inner_conjR3C : ⟪ξ_C, conjR3C v⟫ = conj⟪ξ_C, v⟫` + `Complex.conj_ofReal`). The commutation
  `realSymmetryVec ∘ lerayComplementL2 = lerayComplementL2 ∘ realSymmetryVec` mirrors lane 066's
  `realSymmetry_sobolevDirectionalDerivative` one-liner (`measurePreserving_neg.qmp.ae` transport).
- **q=2 isometry (reviewer's named work item) — BOTH directions delivered**: `coordinates_norm`
  (`‖coordinates b‖ = ‖b‖` into the `PiLp 2` datum carrier, via `L2.inner_def` + `PiLp.inner_apply`
  + `integral_finsetSum` Fubini + `norm_eq_sqrt_re_inner`) AND `assemble_norm` (its isometric
  inverse) plus the round trip `coordinates_assemble` (`coordinates ∘ assemble = id`). Also the
  reality intertwiner `coordinates_realSymmetryVec` (module `realSymmetryVec` ↔ scalar
  `Source.RealSobolev.realSymmetry`, componentwise). All generic in `ι/α/μ` where applicable.

## Failures / blockers

### Corrected (finding 1 of `REVIEW_SL3.md`): the "assemble whnf blow-up" claim was WRONG
The reviewer's five `/tmp` probes — each importing ONLY this module, no `set_option`, no edit to
`Source/` — proved `coordinates_assemble`, the `assemble` isometry (`assemble_norm`), the carrier
round trip, and the reality intertwiner in ~20 lines each at the concrete `Fin 3`/`ℂ`/`volume`
types and default heartbeats. I have now landed all of them **in this module** (`coordinates_assemble`,
`assemble_norm`, `coordinates_realSymmetryVec`); they build, elaborate silently, and are
standard-axiom.

**What actually happened** (not a heartbeat blow-up): (a) a **name-ambiguity error**
`Ambiguous term: insert` — `FiniteHilbertBochner.insert` clashes with `Insert.insert`; the fix is
one alias (`abbrev ins := @…insert`) or pinning the scalar `ins (H := ℂ)`. (b) A **wrong proof
structure**: my failing attempts either applied `Lp.ext` / `filter_upwards` first and then forced
`⇑(assemble h) t` (the coeFn at a point) to reduce, or used `unfold assemble` + `rw`/`refine .trans`
on the sum — routes that make the elaborator chase `insert := LinearMap.mkContinuous {…} 1 (…)`.
The **working** route keeps the `assemble` sum WHOLE at the coeFn level: prove
`(assemble μ h) t = ∑ i, ins i (h i t)` a.e. via `Lp.coeFn_finsetSum` + `ContinuousLinearMap.coeFn_compLpL`
+ `insert_apply` (the same shape as `assemble_coordinates`'s own proof), with a single clean
`change (∑ i, (ins (H := ℂ) i).compLpL 2 μ (h i)) t = _`. I likely misread the ambiguity error / a
slow first elaboration as being "stuck". No heartbeat bump is needed anywhere.

Struck-through wrong claim, kept per `CLAUDE.md` rule 4 as a negative example (a recorded negative
is only worth having if true — this one would have cost a follow-on lane an unnecessary edit to the
shared `Source/FiniteHilbertBochner.lean` and a wrong mental model of `Lp`/`compLpL` unification):
> ~~ANY manipulation of `FiniteHilbertBochner.assemble` from the importing module triggers a
> `whnf`/`isDefEq` heartbeat blow-up (times out even at 1,000,000 heartbeats — genuinely stuck).
> `coordinates_assemble` and the `assemble` isometry cannot be derived without touching `assemble`'s
> internals; the unblock requires new opaque-variable lemmas INSIDE `FiniteHilbertBochner.lean`.~~
> **Reason it is wrong:** the obstruction was a name-clash + a coeFn-too-early proof structure, not
> a defeq blow-up; both lemmas prove from the importing module in ~20 lines with no heartbeat bump
> and no `Source/` edit (reviewer probes B/C, now landed here).

### Remaining gap (the honest one): the datum-carrier operator `lerayComplement m`
`lerayComplement m : RealVectorSobolev m →L[ℝ] RealVectorSobolev m` is still NOT bundled. But it is
now a **short follow-on entirely inside `Section4/D01/`** (do NOT edit `Source/FiniteHilbertBochner.lean`):
1. Bundle `coordinatesL`/`assembleL` as `≃ₗᵢ[ℝ]` (or a CLM pair with the round trips
   `assemble_coordinates` upstream + `coordinates_assemble` here) — both are now isometries.
2. `lerayComplementDatum := coordinatesL ∘ lerayComplementL2 ∘ assembleL`, with `opNorm ≤ 1` by
   conjugation-by-isometry (not the `≤ |ι|` nine-scalar triangle bound).
3. `codRestrict` onto `RealVectorSobolev m = Product (Fin 3) (RealSobolevHilbert m)` via
   `coordinates_realSymmetryVec` (here) + `realSymmetryVec_lerayComplementL2_eq_self` (here) +
   `Source.RealSobolev.mem_realSubspace_iff`. `realSubspace` ignores its order argument, so one
   operator serves every `m`.
The nine-scalar `holderL` route (`ξᵢξⱼ/‖ξ‖²` + `ContinuousLinearMap.pi`) is NOT needed and only
reaches `opNorm ≤ |ι|`, not `≤ 1` (reviewer finding 1c); the vector/isometry route above is `≤ 1`.
