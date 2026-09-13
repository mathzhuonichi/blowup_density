# ATTEMPTS — lane 117 (D01 / P2 = SL8 final assembly)

Module produced: `formalization/NSFormalization/Section4/D01/PressureJets.lean`
(namespace `NSFormalization.Section4.D01`).

## Outcome: the SL8_SPLIT.md / REVIEW_SL8_PREP.md §6 recipe went through verbatim.

The reviewer's end-to-end probe (`research/D01/probes/sl8_assembly_probe.lean`) was the recipe.
Turning it into the in-tree module required exactly the two documented substitutions and no new
analysis:

1. **`H108` hypothesis → merged lemma.**  The probe carried lane 108's corollary as a hypothesis
   `H108`.  Replaced by the in-tree `Leray.lerayComplement_zero_orderZeroDatum_eq_self`
   (`OrderZeroCurl.lean:510`, namespace `NSFormalization.Section4.D01.Leray`), applied directly in
   row i.6.  Unified with no `show`/coercion.

2. **Residual witness → exported lemma.**  The probe re-derived the `h = f−(u·∇)u+νΔu` slice as a
   local `smoothL2_residual`.  Replaced by lane 111's exported
   `MomentumSlice.smoothL2_momentumResidual_slice` (`MomentumSlice.lean:64`); `hres.memLp` feeds
   rows i.2/i.4/i.7 and `hres` itself (an `A05.SmoothL2`, defeq to `SmoothSquareIntegrableJets`)
   feeds `memHInfty_iff_smoothSquareIntegrableJets.mpr` in the bootstrap.

## Curl-free input for row i.6 — used lane 111's `partialDeriv_pressureGradient_symm`, not lane 106's.

Per the lane brief (D01 is upstream of A01 in the task DAG): `hcurl` is
`fun i j x => partialDeriv_pressureGradient_symm u ht i j x`
(`MomentumSlice.lean:188`, in-tree D01).  This keeps `PressureJets.lean` from importing
`A01/PressureGauge`, avoiding a layering inversion.  It unified with lane 108's `hcurl` binder on
the first compile — no need for the 106 fallback
(`A01.PressureGauge.hasSymmetricJacobian_pressureGradient … .2 x i j`), which the reviewer had
verified `rfl`-equal and which stays available if 111's shape ever regresses.

## Route details that the recipe warns are load-bearing (all held).

* Row i.2 genuinely needs `isSobolevDatum_unique` + `funext (temporalDerivative_slice_eq).symm`,
  **not** `rfl`: the two `MemLp` witnesses are for syntactically different functions
  (`fun x => temporalDerivative …` vs residual `−` `∇p`).
* Row ii.2's rewrite must go `← Leray.lerayComplement_lowerVectorL` **then** `hii1`.
* `lowerVectorL` is `NSFormalization.Section4.D01.lowerVectorL` (`HalfOrder.lean:103`), **not**
  `Leray.lowerVectorL`.  Written unqualified under `open` it resolves to the D01 one, which is the
  intended one; no compile cost here.

## No failed approaches.

`lake build NSFormalization.Section4.D01.PressureJets` succeeded on the first write; the only edit
after was trimming the module docstring / two section separators to reach the ≤120-line target.
All three declarations print exactly `[propext, Classical.choice, Quot.sound]`
(`research/D01/axioms_sl8_assembly.lean`).

---

## Post-review revision (lane-117 reviewer, `research/D01/REVIEW_SL8_ASSEMBLY.md`, ACCEPT-WITH-NOTES)

Reviewer finding 3 (medium): the order-`m` eq:Rpressure identity was proved inline in the main
theorem and thrown away.  Fixed here: exported the reviewer's appendix-B triple into
`PressureJets.lean` verbatim and made the main theorem consume it (the three pre-existing theorem
**statements** are byte-identical; only the main theorem's proof body changed):

* `isSobolevDatum_pressureGradient_lerayComplement` — for any order-`m` datum `Am` of the residual
  `h`, `IsSobolevDatum (m:ℝ) ∇p (Leray.lerayComplement (m:ℝ) Am)`.
* `exists_isSobolevDatum_pressureGradient_slice` — its `∃`-form (the `hP` slot A04's
  `momentum_datum` consumes).
* `pin_pressureGradient_datum` — any datum `P` a consumer holds for `∇p` is pinned to `(I−P)ₘ Am`
  by `isSobolevDatum_unique`.

### Reviewer MAINT / scope notes (recorded here; those other modules are NOT edited by this lane)

1. **(finding 5, MAINT)** `Pressure.pressureGradient_slice_smoothSquareIntegrableJets`
   (`D01/Pressure.lean:376`) is now dead and strictly weaker: its hypothesis
   `hut : SmoothSquareIntegrableJets (∂ₜu(t,·))` is exactly what
   `temporalDerivative_slice_smoothSquareIntegrableJets_of_memForceR` now proves.  Its only users are
   its own docstring and `research/D01/axioms_l9c.lean:33`.  `Pressure.lean` §3's "the single root
   gap" / "L9(c) stays open" docstring is now stale.  A SIMP/MAINT lane should retire it or re-derive
   it from the new corollary and refresh the docstring.
2. **(finding 6, MAINT)** Lane 111's `lerayComplement_orderZeroDatum_add` / `_sub`
   (`D01/OrderZeroAlgebra.lean:97,106`) are now dead code — the assembly uses `map_sub` on the CLM
   directly (`PressureJets.lean`).  Only user is `research/D01/axioms_sl8_prep.lean:10-11`, which
   would need updating if they are removed.
3. **(finding 4, scope)** What is proved at order 0 is eq:Rpressure in the residual spelling
   `f − (u·∇)u + νΔu`, not the manuscript's `f − ∇·(u⊗u)`.  Two deltas: `(u·∇)u` vs `∇·(u⊗u)` (the
   bridge `convectionDivergence_eq_advection` lives in `Section4.A01`, so using it here would invert
   the layering this lane preserves); and the extra `νΔu`, which `(I−P)` kills only because
   `div Δu = 0` — and the reviewer found **no in-tree `div Δu = 0` lemma**, so bridging to the
   manuscript's literal display is a real (small) missing step.  Immaterial to P2's regularity target.
4. **(finding 7 / §4.4, structural)** Rows i.2 and i.4 remain inlined as `have hi2` / `have hi4`
   inside `orderZeroDatum_pressureGradient_eq` (not exported).  `hi4` — `(I−P)₀ (datum⁰ ∂ₜu) = 0`,
   the order-0 transversality of `∂ₜu` — is a reusable fact now living only as a `have`.  Not
   exported by this revision (out of the requested scope); flagged for a follow-up if a consumer
   needs it.

### Other reviewer scope clarifications (info, no code change)

* "unconditional" in the docstring means "no `hut` hypothesis", not "no force hypothesis"
  (`hf : MemForceR f` is still required; `Pressure.lean:62-66`'s counterexample field `f ∉ F_R`).
* `orderZeroDatum_pressureGradient_eq` is **not** what A01's `pressure_recovery` needs (that is a
  pointwise `IsLerayComplement`, one level below the `RealVectorSobolev 0` datum carrier); the lead
  should not book A01 `pressure_recovery` as unblocked by this lane.
* A04 eq:Rhigh's `hP` input **is** unblocked by `exists_isSobolevDatum_pressureGradient_slice`; its
  `hpr` (pressure-drop `⟪G,P⟫ = 0`) is **not** and remains an A04 item (needs a self-adjointness
  lemma for `lerayComplement`, which the reviewer verified is not in tree).
* P2 contract registration route (reviewer §6): a **V3** of `D01.datum_lemmas`
  (`Contracts/V3/DatumLemmas.lean` + `Bindings.DatumLemmasV3` + `Tests.DatumLemmasV3`), three fields
  binding to the theorems above via `Bindings.uniqueness_toA02`.  That is a separate contract lane.
