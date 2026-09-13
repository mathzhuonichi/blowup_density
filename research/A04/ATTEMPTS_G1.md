# A04 unit G1 — attempts (lane 056)

Split-and-start lane. Goal: split eq:Rhigh into ≤ 8 sub-lemmas (`G1_SPLIT.md`)
and prove the S sub-steps. Do **not** attempt the L sub-lemmas.

## What was proved (all in `formalization/NSFormalization/Section4/A04/HighEnergy.lean`)

* `inner_energy_assembly` / `inner_energy_Rhigh` (SL8) — the pairing arithmetic
  from the datum-form momentum equation to eq:Rhigh's displayed RHS, on a
  **generic** real inner product space `E`.
* `outerSobolevNormAt_le` / `outerNormAt_le` (SL6) — the `ℝ≥0∞ → ℝ` transport of
  `A03.outerProductTame` to the real datum norms `sobolevNormAt`.

Axioms: all four are `[propext, Classical.choice, Quot.sound]` only
(`research/A04/axioms_g1.lean`). No `sorry`, no `axiom`, no `native_decide`.

## Design decisions and why

1. **Arithmetic lemmas are generic in `E`, not on `RealVectorSobolev m`.**
   Lane 053's `Paper3.realSobolevInnerProductSpace` (the `Inner ℝ` instance on the
   datum carrier) is in PR and is **not on `erenup/integration`** (grep of the
   worktree found only vendor Euler `InnerProductSpace ℝ` instances). Stating the
   assembly over any `[InnerProductSpace ℝ E]` sidesteps the missing instance,
   compiles today, and is reused verbatim by the L-lemma at `E = RealVectorSobolev m`.
   Mathlib's `real_inner_le_norm`, `inner_sub_right`, `inner_add_right`,
   `real_inner_smul_right` all apply generically.

2. **Tame bound is consumed via the *local* `A03.outerProductTame`, not the
   contract field.** `NSFormalization` cannot import `Contracts.*` (repo rule),
   so `TameProductAPI.outerProductTame` is unavailable inside `formalization/`.
   The binding `Bindings/TameProduct.lean:122` points the contract field at
   `NSFormalization.Section4.A03.outerProductTame` (`OuterTameProduct.lean:157`),
   and `tameProduct_sobolevENorm_eq` / `tameProduct_outerSobolevENorm_eq` confirm
   the contract mirrors the local defs by `rfl`. So the transport lemma imports
   `A03.OuterTameProduct` directly.

3. **`hnl` (nonlinear pairing) is an interface, not proved here.** eq:Rhigh's
   single-term nonlinear bound `C‖u‖_{H²}‖u‖_{H^m}‖∇u‖_{H^m}` does **not** come
   from `A03.smoothJets_advectionTame` (two terms) directly; it comes from the
   outer-product route `(u·∇)u = ∇·(u⊗u)`, H^m integration by parts
   `⟪G, ∇·(u⊗u)⟫ = −⟪∇-datum, u⊗u datum⟫`, Cauchy–Schwarz, then `outerProductTame`.
   The IBP identity is the L sub-lemma SL5; `inner_energy_assembly` takes
   `−⟪G, N⟫ ≤ NLbound` as a hypothesis so the S arithmetic is separated from it.

4. **Momentum equation carried as `Gt = ν•L − N − P + F` with the pressure
   `P` kept explicit** and dropped by the separate hypothesis `⟪G, P⟫ = 0`, so
   the solenoidality step (SL4, blocked on L9(c)) is a named interface rather
   than being silently folded away.

5. **eq:Rhigh, not eq:highcontinuation.** No Young's inequality here — the
   dissipation `ν grad²` is absorbed *exactly* (moved to the LHS via the
   Laplacian identity `⟪G,L⟫ = −grad²`). Young's absorption is unit **G2**.

## Approaches tried and outcome

* **Bounding `−⟪G,N⟫` inside the assembly via `‖G‖·‖N‖` and the advection tame
  bound** — rejected. `‖(u·∇)u‖_{H^m}` bounds to the *two-term* eq:Rproduct, not
  the single term of eq:Rhigh; the single term only appears through the outer
  IBP, whose CS pairs `∇u` (not `u`) with `u⊗u`. So the nonlinear factor is not
  `‖G‖·‖N‖`. Kept `−⟪G,N⟫ ≤ NLbound` abstract instead.

* **Transporting the tame bound with `ENNReal.toReal_le_toReal`** — its
  hypotheses are the two *≠ ⊤* facts of *both* sides; `ENNReal.toReal_mono`
  (needs only RHS ≠ ⊤) is shorter and the RHS finiteness is `ENNReal.mul_ne_top`
  of the (finite) factor norms and `ofReal_ne_top`. The LHS (outer norm)
  finiteness is then not even needed — it follows from the bound. Used
  `toReal_mono`.

* **`ring` after `simp only [inner_add_right, inner_sub_right, real_inner_smul_right,
  hlap, hpr]`** to normalise `⟪G, ν•L − N − P + F⟫` — worked first try; `⟪G,N⟫`,
  `⟪G,F⟫` are treated as opaque real atoms by `ring`. (Lean prints a generic
  "ring works in commutative rings" *hint* during the full lake build, but it is
  emitted by replayed upstream `Source/`/`Paper3/` modules, not by this file:
  `lake env lean` on `HighEnergy.lean` alone prints nothing.)

## Frontier left for follow-up lanes

**SL1 (D2) is closed here** (see "Review fixes" below), so it is no longer on
this list.  Remaining:

* **SL2** — momentum equation in datum form: `Gt = ν•L − N − P + F`. Now needs
  only SL1 (done) + `ClassicalSolutionR.momentum` (a field, not an A01 clause) +
  datum linearity, and `isSobolevDatum_smul` (companion to the existing
  `D01.isSobolevDatum_add`, currently absent) for the `ν•` term. `M`, not L.
* **SL3** — Laplacian identity on the **datum** carrier (decision recorded in
  `G1_SPLIT.md`); needs the datum-side order shift, open — `SmoothDatum.lean:388`
  is jet-side and its docstring flags U1b(ii) as untouched. Also needs a
  formalization def of `gradientSobolevNormAt` (only in `Spec.lean:190` today).
* **SL4** — pressure drop; depends on D01 **L9(c)** (`∇p` in the carrier at order
  `m`), being closed in another lane (055-D01-unit-l9c seen in worktrees).
* **SL5** — H^m integration by parts of `∇·(u⊗u)` on the datum carrier.
* **SL7 carrier link** — `⟪·,·⟫` ↔ `sobolevNormAt` on `RealVectorSobolev m`
  needs lane 053's inner-product instance on integration.

The "pin-the-representative" technique used in SL1 (turn a datum identity into a
pointwise identity of continuous bounded representatives, `A03.representative_ae`
+ `angularRealization_boundedRepresentative`) is expected to shorten SL2–SL4.

## Review fixes (ACCEPT-WITH-NOTES, `REVIEW_G1.md`)

* **MAJOR, finding 2 — SL1/D2 is not blocked and not A01's.** New module
  `formalization/NSFormalization/Section4/A04/TimeDerivative.lean` proves D2 in
  full, `sorry`-free, standard axioms: `d2_scalar` (scalar case, the reviewer's
  compiled proof lifted verbatim) and `timeDeriv_isSobolevDatum` (the **vector**
  statement, the deliverable). The route is the bounded representative
  `Paper3.angularBoundedRepresentative` (CLM, `2 ≤ m`) +
  `HasFDerivAt.comp_hasDerivAt` for the pointwise derivative, `representative_ae`
  + `Continuous.ae_eq_iff_eq` to pin it, `HasDerivAt.unique` on the imaginary
  part, `angularRealization_boundedRepresentative` back to `IsSobolevDatum`. The
  vector case is componentwise (`isSobolevDatum_iff` = `Iff.rfl`, `PiLp.proj`
  CLM) with existence straight from `velocity_smooth`. No difference quotients,
  no dominated convergence, no `isSobolevDatum_smul`, no A01 clause.
  - *Failed sub-approach:* assembling the vector `HasDerivAt` in `Space` from
    componentwise derivatives via `PiLp.continuousLinearEquiv` / `EuclideanSpace.equiv`
    hit a `PiLp`-vs-`WithLp` instance diamond and a non-defeq `symm_apply_apply`
    on the derivative value, so `simpa`/`exact` would not close it. Avoided
    entirely: existence comes from `velocity_smooth` (the honest vector deriv),
    and only the *scalar components* go through `PiLp.proj` (`comp_hasDerivAt`,
    which unifies fine) plus `HasDerivAt.deriv` to relate `(deriv vec t) i` to
    `deriv (component) t`.
  - `PiLp.proj` needed an explicit `(𝕜 := ℝ)`; `MemLp` of a component came from
    `ContinuousLinearMap.comp_memLp'` on `PiLp.proj`; `u` had to be pinned
    (`u := fun z => w.velocity z i`) in the `d2_scalar` call (higher-order
    unification would not infer it).
* **MINOR, finding 3 — SL6 `MemHmVector` sourcing.** `G1_SPLIT.md` SL6 corrected:
  the `MemLp` half of `MemHmVector` needs `velocity_smooth` (via
  `D01.contDiff_slice` + `D01.memLp_of_isSobolevDatum`), not `.sobolev` alone.
  Doc-only.
* **MINOR, finding 4 — `hlap` hardened.** `inner_energy_assembly` /
  `inner_energy_Rhigh` now take `hlap : ⟪G, L⟫ ≤ -grad²` (was `=`) with the extra
  `hν : 0 ≤ ν` (which `energyIdentityHigh`'s `0 < ν` supplies), so an SL3 that
  proves the datum-carrier order shift only as an inequality still feeds the
  assembly. The manuscript's exact identity is the special case.

## Commands
* `bash scripts/lean-install.sh` — OK (full build).
* `lake build NSFormalization.Section4.A04.HighEnergy` — OK (9889 jobs).
* `lake build NSFormalization.Section4.A04.TimeDerivative` — OK (9889 jobs).
* `lake env lean ../formalization/…/A04/{HighEnergy,TimeDerivative}.lean` — clean.
* `lake env lean ../research/A04/axioms_g1.lean` — all six lemmas
  (`inner_energy_assembly`, `inner_energy_Rhigh`, `outerSobolevNormAt_le`,
  `outerNormAt_le`, `d2_scalar`, `timeDeriv_isSobolevDatum`)
  `[propext, Classical.choice, Quot.sound]`.
* `make check` — see final message.
