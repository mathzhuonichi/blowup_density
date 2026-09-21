# ATTEMPTS — lane 081, D01, SL3 final step: Leray-complement multiplier on the datum carrier

Module: `formalization/NSFormalization/Section4/D01/LerayDatum.lean` (sorry-free; `#print axioms`
standard for all 14 public declarations, `research/D01/axioms_leray_datum.lean`).
Builds on lane 073's `Section4/D01/LerayMultiplier.lean` (raw-carrier multiplier `lerayComplementL2`
and the `q = 2` `assemble`/`coordinates` isometry bridge, both already landed there).

## What was delivered

* **Item 1** — `lerayComplementAmbient : Product (Fin 3) (Lp ℂ 2 volume) →L[ℝ] …`,
  `= coordinates ∘ lerayComplementL2 ∘ assemble`, `‖·‖ ≤ 1`.
* **Item 2** — `realSymmetryVec_assemble` (the intertwiner) and
  `image_component_mem_realSubspace` (reality preservation, ambient form).
* **Item 3** — `lerayComplement (s : ℝ) : RealVectorSobolev s →L[ℝ] RealVectorSobolev s`,
  plus `lerayComplement_toAmbient` (it *is* the restriction of item 1).
* **Item 4** — `lerayComplement_opNorm_le_one`, `_idempotent`, `_ae`,
  `_eq_zero_of_transverse` (lane-079 transverse shape).

## Route chosen for item 3 (and why), and the "PiLp of submodules" question

The datum carrier is `RealVectorSobolev s = Product (Fin 3) (RealSobolevHilbert s)` — a
`PiLp 2` **of** the subtype `↥(realSubspace s)` — NOT a `Submodule` of the ambient
`Product (Fin 3) (Lp ℂ 2 volume)`.  So the natural `ContinuousLinearMap.codRestrict` (which needs
a `Submodule` of the codomain) has **no target object to restrict onto**; a codRestrict route would
first have to manufacture the submodule `⨅ i, (proj i ⁻¹' realSubspace s)` and an isometry between
that submodule and the `PiLp` of subtypes.  That detour is exactly the "awkward" the brief warned
about.

Chosen instead (the brief's endorsed alternative): **define `lerayComplement s` componentwise via
`LinearMap.mkContinuous`.**  `toFun h := WithLp.toLp 2 (fun i => ⟨ambient i-th coordinate, proof⟩)`
where the membership proof is `image_component_mem_realSubspace`.  `map_add'`/`map_smul'` reduce by
`PiLp.ext` + `Subtype.ext` to the ambient additivity/homogeneity of `assemble`/`coordinates`; the
`opNorm ≤ 1` bound is `mkContinuous 1` fed by `lcFunVec_norm_le`.

**Key simplification found (positive):** the subtype norm coincides *definitionally* with the coe
norm — `‖(x : FourierData)‖ = ‖x‖` holds by `rfl` for `x : RealSobolevHilbert s` (`exact?` even
offers `enorm_eq_iff_norm_eq.mp rfl`).  Hence the datum↔ambient norm bridge
`datumNorm_eq` is just `rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]; congr 1` — no
`Submodule.subtypeₗᵢ.norm_map`, no `Submodule.norm_coe` needed.  Likewise
`↑(a + b) = ↑a + ↑b` and `↑(c • a) = c • ↑a` on `RealSobolevHilbert s` are `rfl`, and
`(WithLp.toLp 2 g) i = g i` is `rfl`.

`lerayComplement_toAmbient` closes by `rw [lerayComplementAmbient_apply]; congr 1` — after the
rewrite the two `PiLp` bodies are defeq (`↑(lerayComplement s h i)` unfolds to the ambient
coordinate by `rfl`, and `WithLp.ofLp (WithLp.toLp 2 g) = g` definitionally), so `congr 1`
discharges it with no `funext`.

## Failed / discarded approaches (and why)

1. **`ContinuousLinearMap.codRestrict` at the `PiLp` level** — discarded before coding: there is no
   `Submodule` `p` with `↥p = RealVectorSobolev s`, so `codRestrict f p _` does not typecheck.
   Would require a synthetic `⨅`-submodule + an isometry to the `PiLp`-of-subtypes; strictly more
   work than the componentwise `mkContinuous`.

2. **Composition route `coordinatesL ∘ lerayComplementL2 ∘ assembleL` for item 3** — usable for
   item 1 (ambient), but for item 3 the inclusion/projection `PiLp 2 (subtypes) ↔ ambient` cannot
   be built from `PiLp.continuousLinearEquiv` alone: that equiv lands in the **sup-norm** plain
   product `∀ i, β i`, on which the middle `≤ 1` bound is lost, so the isometry lemmas
   (`PiLp.norm_eq_of_L2`) are needed regardless.  Given the subtype-norm defeq above, going
   componentwise directly is shorter.

3. **`ext` on `RealVectorSobolev s` equalities** — a bare `ext i` recurses through the subtype and
   then into `Lp`'s a.e. equality (`=ᵐ`), overshooting.  Fix: `PiLp.ext (fun i => Subtype.ext …)`
   controls the depth; then finish at the ambient `FourierData` level.

4. **Dropping `Pi.add_apply`/`Pi.smul_apply` from the ambient `map_add'`/`map_smul'` `simp only`** —
   in `lerayComplementAmbientLM` those args ARE needed to reduce `(coordinates a + coordinates b) i`
   (the goal is stated at a point `i` after `funext`); in `lcFunVec_add`/`lcFunVec_smul` they are
   NOT (the goal is already a bare `coordinates … i`), where the linter flags them unused.  Keep
   them only where the point-application is present.

## Exact Mathlib / upstream names used

* `WithLp`: `WithLp.toLp_ofLp`, `WithLp.ofLp_add`, `WithLp.ofLp_smul`, `WithLp.toLp_add`,
  `WithLp.toLp_smul`; `WithLp.ofLp (WithLp.toLp 2 g) = g` used definitionally.
* `PiLp`: `PiLp.norm_eq_of_L2`, `PiLp.ext`, `PiLp.inner_apply`, `PiLp.single_apply`.
* Subtype norm `‖(x : FourierData)‖ = ‖x‖`, submodule `coe_add`/`coe_smul`, and
  `(toLp 2 g) i = g i` — all hold by `rfl` (no dedicated lemma invoked).
* Bundling / norms: `LinearMap.mkContinuous`, `LinearMap.mkContinuous_norm_le`.
* Lp a.e. plumbing: `ContinuousLinearMap.coeFn_compLpL`, `Lp.coeFn_finsetSum`, `Lp.ext`,
  `ae_all_iff`, `Measure.measurePreserving_neg … .quasiMeasurePreserving.ae`.
* Inner product: `RCLike.inner_apply`, `Complex.conj_ofReal` (bridge to the `∑ⱼ ξⱼ·vⱼ` shape).
* Upstream (lane 073, `LerayMultiplier.lean`): `coordinates_ae`, `coordinates_norm`,
  `coordinates_assemble`, `assemble_norm`, `coordinates_realSymmetryVec`,
  `realSymmetryVec_lerayComplementL2_eq_self`, `realSymmetryVec_ae`, `conjR3C_apply`,
  `lerayComplementL2_ae`, `lerayComplementL2_idempotent`,
  `lerayComplementL2_eq_zero_of_transverse`, `lerayComplementL2_apply`, `norm_lerayComplementFun_le`.
* Upstream (`Source/FiniteHilbertBochner.lean`): `assemble`, `coordinates`, `insert_apply`,
  `assemble_coordinates`.
* Upstream (`Source/RealSobolev.lean`): `realSymmetry`, `realSymmetry_ae`, `realSubspace`,
  `RealSobolevHilbert`, `mem_realSubspace_iff`.

## Notes

* The order `s` is a phantom (`realSubspace` discards it); one operator serves every order, but the
  datum interface is indexed by `s` as required by the brief.
* Confirms the corrected `research/D01/ATTEMPTS_SL3.md` "Remaining gap": the follow-on was indeed a
  short lane entirely inside `Section4/D01/`, with **no** edit to `Source/FiniteHilbertBochner.lean`.
