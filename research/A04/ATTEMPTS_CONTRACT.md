# ATTEMPTS_CONTRACT — lane 133-A04-energy-high-contract

First registered A04 contract: `A04.energy_high_partial`
(`verification/Contracts/V1/EnergyHighPartial.lean`), the proved field
`energyIdentityHigh` (eq:Rhigh, `paper/sections/appendix-a-local-theory.tex:132-137`).

## Decisions

1. **Froze the tree form, not the blind `DifferentiableAt`→`deriv` form.**
   Following `research/A04/BLIND_RHIGH.md` §5.1: the tree statement
   (`∃ d, HasDerivAt (fun r => ‖u(r)‖²_{H^m}) d t ∧ …`) is (a) already proved
   (`Section4/A04/EnergyIdentityHigh.lean:145`, token-for-token the spec field
   `Spec.lean:424-434`), (b) more faithful (asserts the derivative, matching the
   manuscript's `d/dt`; gives a named constant), and (c) implies the blind form
   modulo A01 m1.  The blind form is **not provable in today's tree** — see
   negative example N1 — so freezing it would smuggle an A01 `L`-unit gap into the
   contract.

2. **`Chigh : ℕ → ℝ` + `Chigh_pos` are data fields (opaque).**  They are the
   Skolemization of the blind writers' `∃ C, (∀ m, 0 < C m) ∧ …`
   (`BLIND_RHIGH.md` §5.1).  The contract asserts only `0 < Chigh m`; it does NOT
   assert `Chigh = tame.Ctame`.  That identification holds by `rfl` in the binding
   (both are `A03.outerTameConst`) and is exported there as the bonus
   `energyHighPartial_Chigh_eq_Ctame` for unit G2's `Cgron` (`REVIEW_ENERGY_HIGH.md`
   finding 6).  Because it carries data, `EnergyHighPartialAPI` is a `Type` and the
   binding is a `def`, exactly as `C01.energy_absorption_partial`.

3. **Three spec-local defs restated verbatim, drift-guarded by `rfl` bridges**
   (`Bindings/EnergyHighPartial.lean`): `sobolevNormAt` (`Forcing.lean:74`),
   `gradientSobolevNormAt` (`LaplacianDatum.lean:86`), `HasSmoothSobolevPath`
   (`DerivNorm.lean:87`).  All three `rfl` bridges typecheck (verified — the lane-128
   reviewer's `/tmp/rev128/p5_hssp_bridge.lean` re-confirmed here by
   `research/A04/axioms_contract.lean`).  `ClassicalSolutionR` is the CLAUDE.md
   structure exception: crossed with `Bindings.uniqueness_toA02`, and the conclusion
   needs no adjustment because `(uniqueness_toA02 w).velocity = w.velocity` by `rfl`.

4. **`RealVectorSobolev` in the contract via `open`, not `import`.**  The contract
   imports only `Contracts.V1.{Data,TameProduct}` (+ Mathlib), satisfying even the
   strict import rule.  `HasSmoothSobolevPath` needs `RealVectorSobolev`, which is
   `NSFormalization.Paper3`'s; that namespace is transitively imported by
   `Contracts.V1.Data`, so `open NSFormalization.Paper3 (RealVectorSobolev)` brings
   the name into scope without an import (`Data.lean` and `TameProduct.lean` already
   `open` `NSFormalization.*` the same way).  `check_contracts.py` accepts it (23
   contracts, base compatibility checked).

5. **Added the fourth finiteness lemma** `gradientSobolevENorm_velocity_ne_top` in a
   new module `formalization/NSFormalization/Section4/A04/GradientFiniteness.lean`
   (existing modules must not be edited), credited to the lane-128 reviewer.  It
   closes the `⊤ ↦ 0` risk on eq:Rhigh's dissipation term and is cited in the
   contract's `.toReal` disclosure and re-exported at binding level as
   `energyHighPartial_gradientSobolevENorm_velocity_ne_top`.  Route (verified, all
   three ≤ standard axioms): `C01.velocity_slice_smoothL2` → `A03.SmoothL2.partialDeriv`
   per column → `D01.sobolevENorm_ne_top_of_contDiff_memLp` → `A03.columnsSobolevENorm_le_sum`
   + `ENNReal.sum_ne_top`.

## Negative examples (pasted error text)

**N1 — the blind form is not provable in the tree.**  `HasSmoothSobolevPath`
cannot be derived from `ClassicalSolutionR.sobolev`, which is what the blind
`DifferentiableAt`→`deriv` form would need (`BLIND_RHIGH.md` §3.3,
`/tmp/rev130/p4_gap.lean`):

```
theorem hssp_of_classicalSolution … (w : Data.ClassicalSolutionR ν a f T) :
    HasSmoothSobolevPath T w.velocity := by
  intro m
  obtain ⟨G, hGc, hGd⟩ := w.sobolev m
  exact ⟨G, hGd, hGc⟩
--> error: Application type mismatch: the argument hGc has type
      ContinuousOn G (Ico 0 T)
    but is expected to have type
      ContDiffOn ℝ ∞ G (Ico 0 T)
```

i.e. `sobolev` gives only a `ContinuousOn` datum path, `HasSmoothSobolevPath` wants
`ContDiffOn ℝ ∞`.  This is A01's `sobolev_smooth` (`research/A01/Spec.lean:180`, m1,
`L`, gap).  Hence the field is registered as **conditional** on `HasSmoothSobolevPath`
and this is disclosed as the contract's most important caveat.

**N2 — no zero-solution instantiation in `Tests`.**  The 128-review non-vacuity
witness (`/tmp/rev128/p4_vacuity.lean`) uses `zeroSol`, which is a `research/`
reconstruction, not a tree declaration.  Reconstructing it in a `Tests` module
(which is `warningAsError` and may not import `Formal.*`) is not cheap, so the
`Tests` file keeps the axiom check plus two shape `example`s instead.  Non-vacuity
of the hypothesis package (including a satisfiable `HasSmoothSobolevPath` on the
zero solution, and `d` forced to `0`) is already established by that 128 review.

## Building (no compilation failures encountered)

Every new module compiled on the first `lake build`/`lake env lean`, silent, with
only `propext / Classical.choice / Quot.sound`.  The `A05.SmoothL2` returned by
`velocity_slice_smoothL2` feeds `A03.SmoothL2.partialDeriv` (which asks
`A03.SmoothL2`) by defeq — the two `SmoothL2` defs are syntactically the same
`ContDiff ℝ ∞ ∧ ∀ n, MemLp …`.

## What a V2 would add (unit G2, not proved in tree on this branch)

* `regularizedNormDerivative` — eq:highcontinuation before the limit
  (`Spec.lean:437-465`, `appendix-a-local-theory.tex:139-145`, the `ζ`-regularized
  `(‖u‖_{H^m})'` bound);
* `highContinuationIntegral` — the integrated Grönwall form (`Spec.lean:494-510`)
  and the continuation criterion eq:criterion;
* the constant `Cgron` (`= (Chigh m)²/(4ν)`), which will consume the binding's
  `energyHighPartial_Chigh_eq_Ctame`.

When A01 m1 (`sobolev_smooth`) lands, the blind `DifferentiableAt`→`deriv` form
becomes a free 7-line consequence (`BLIND_RHIGH.md` §3.3 `tree_implies_A`); it does
not need a V2 of this contract.

## Load-bearing hypotheses of the registered field (copied from lane 128's `ATTEMPTS_ENERGY_HIGH.md`, per review finding 1)

The contract docstring and scope point here for the slack table; the source of truth is lane 128's record, reproduced verbatim:

| `0 < ν` | **yes** (not tight) | only as `le_of_lt hν` → `inner_energy_Rhigh`'s `hν : 0 ≤ ν`; mathematically `0 ≤ ν` suffices, kept `0 < ν` for spec fidelity |
| `a ∈ initialClassR` | **no** | unused on this route; carried in the spec-shaped theorem for fidelity only (matches `REVIEW_HPR.md` finding 13 / probe docstring) |
| `3 ≤ m` | **yes** (not tight) | only via `have hm2 : 2 ≤ m := by omega`; this route needs only `m ≥ 2`, kept `3 ≤ m` per manuscript `:129` |

Summary: `a ∈ initialClassR` is unused by the proof (kept for spec fidelity); `3 ≤ m` and `0 < ν` carry slack (the route needs `2 ≤ m`, `0 ≤ ν`) — V2 strengthening candidates, not changes to the frozen field.
