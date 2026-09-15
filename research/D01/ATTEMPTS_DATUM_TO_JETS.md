# D01 unit L2, the `⟹` direction: datum ⟹ square-integrable jets, and time slices

Lane 025, task **D01**.  Module:
`formalization/NSFormalization/Section4/D01/DatumToJets.lean`.

This is the converse of lane 020's `Section4/D01/SmoothDatum.lean` (jets ⟹ datum), plus the
time-slice extraction from `Contracts.V1.Data.ClassicalSolutionR`.  Together the two modules close
`research/D01/RECONCILIATION.md` unit **L2** in all three of its clauses, and they retire items
(1), (2) and (3) of `research/A03/REVIEW_CONTRACT.md` §6 and items 1–2 of
`research/A05/REVIEW_CONTRACT.md` "The datum-vs-jet gap".

---

## 1. Route chosen

The analytic content — *distributional derivative of an `L²`-datum realization = classical
derivative of the smooth field* — is already in tree, in
`formalization/NSFormalization/Source/FourierPhysicalJets.lean`, which was written for the
**cycles** Fourier convention.  `RECONCILIATION.md:153` already named it as the binding for this
direction; nothing in it had to be re-proved or generalized.

The three links added here are all bookkeeping:

1. **Angular ⟹ cycles.**  `Paper3.cyclesToAngular s : SobolevHilbert s ≃L[ℂ] Lp ℂ 2 volume`
   (`Paper3/AngularTameProduct.lean:11`) with
   `angularRealization_eq_cycles` (`:31`): the manuscript's angular datum and its cycles preimage
   realize the *same* tempered distribution.  Cost: `frequencyUnit ^ |s| = (2π)^{|s|}`
   (`cyclesToAngular_symm_norm_le`, `:20`).  This is the **only** place a `(2π)` enters.
2. **Order lowering.**  `Paper3.sobolevOrderLowering` (`Paper3/SobolevOrderLowering.lean:26`),
   contractive (`sobolevOrderLowering_norm_le`, `:39`) and realization-preserving
   (`sobolevRealization_orderLowering`, `:78`): an order-`m` datum gives an order-`j` datum for
   every `j ≤ m`.
3. **Pairing shape.**  `Contracts.V1.Data.IsSobolevDatum` (`Data.lean:160`) pairs against *every*
   Schwartz test; `FourierPhysicalJets.CompactRep` (`:14`) asks only for compactly supported ones,
   and `•` on `ℂ` is `*`.  One `simp only [smul_eq_mul]`.

Then `FourierPhysicalJets.physicalJetLp j` (`:159`) — a **bounded linear map**
`(Fin 3 → SobolevHilbert j) →L[ℝ] Lp (Space [×j]→L[ℝ] Space) 2 volume` — and
`physicalJetLp_ae` (`:159`) give both the qualitative `MemLp` and, because the map is bounded, the
quantitative bound for free.

Inside `FourierPhysicalJets` the real work is `compactRep_directional` (`:60`), which routes
through `Paper3.sobolevRealization_directionalDerivative`
(`Paper3/SobolevDirectionalDerivative.lean`) and
`Source.WeakClassicalDerivative.ae_eq_classical_derivative`.  **This module re-proves none of it.**

### The constant, and the `(2π)`

```
jetDatumConst j m   = (‖physicalJetLp j‖ + 1) * frequencyUnit ^ (m : ℝ)
jetSobolevConst m   = ∑ j ∈ Finset.range (m + 1), jetDatumConst j m
```

with `frequencyUnit = 2 * Real.pi` (`Source/FourierConvention.lean:15`).  So:

* **Yes, a `(2π)` appears**, as exactly one factor `(2π)^m` (`m` = the *datum* order, not the jet
  order), and nowhere else.  It is the ratio of the two Bessel symbols `(1+|ξ|²)^{m/2}` (angular,
  `01-introduction.tex:85-86`) and `(1+4π²|ξ|²)^{m/2}` (cycles), bounded by
  `Paper3.angularWeightSymbol_norm_le` (`Paper3/AngularSobolevCoordinates.lean:34`).
* `‖physicalJetLp j‖` is the operator norm of the finite-dimensional reassembly of the `3^j`
  coordinate words into a `j`-multilinear map on `R³`; it depends only on `j` and the dimension
  three, never on the field.  It is **not** computed — `appendix-a-local-theory.tex:10` and
  `appendix-b-embeddings.tex:109-110` both leave such constants free.
* The `+ 1` exists only so that `jetDatumConst_pos` is one line.  It is the reason the `⊤` branch
  of `jetSobolevENorm_le_sobolevENorm` cannot collapse `⊤` to `0`.  The honest bound is with
  `‖physicalJetLp j‖`; `norm_jetOfDatum_le` proves the `+1` version and the `nlinarith` step is the
  only place the slack is used.
* Order lowering costs nothing (contractive), and the real-subspace inclusion
  `RealSobolevHilbert s ↪ FourierData` is isometric, so `‖(A i : FourierData)‖ = ‖A i‖ ≤ ‖A‖`
  (`PiLp.norm_apply_le`) with constant one.

---

## 2. Exact hypotheses

Everything is stated on `z : Space → Space` (= `Contracts.V1.Data.SpatialField`, `Data.lean:99`).

| theorem | hypotheses | conclusion |
|---|---|---|
| `memLp_iteratedFDeriv_of_isSobolevDatum` | `j ≤ m`, `ContDiff ℝ ∞ z`, `IsSobolevDatum (m:ℝ) z A` | `MemLp (iteratedFDeriv ℝ j z) 2 volume` |
| `eLpNorm_iteratedFDeriv_le_of_isSobolevDatum` | same | `eLpNorm (iteratedFDeriv ℝ j z) 2 volume ≤ ofReal (jetDatumConst j m) * ‖A‖ₑ` |
| `memLp_of_isSobolevDatum` / `eLpNorm_le_of_isSobolevDatum` | same | `MemLp z 2 volume`, `eLpNorm z 2 volume ≤ ofReal (jetDatumConst 0 m) * ‖A‖ₑ` |
| `memHInfty_jets` | `ContDiff ℝ ∞ z`, `∀ m, ∃ A, IsSobolevDatum (m:ℝ) z A` | `∀ n, MemLp (iteratedFDeriv ℝ n z) 2 volume` |
| `memHInfty_iff_smoothSquareIntegrableJets` | — | `MemHInfty z ↔ SmoothSquareIntegrableJets z` |
| `exists_smoothL2Field_of_memHInfty` | as `memHInfty_jets` | `∃ B : EulerLpTranslation.SmoothL2Field Space, B.field = z` |
| `jetSobolevENorm_le_sobolevENorm` | `ContDiff ℝ ∞ z` **only** | `jetSobolevENorm m z ≤ ofReal (jetSobolevConst m) * sobolevENorm (m:ℝ) z` |
| `contDiff_slice` | `ContDiffOn ℝ ∞ v (Ico 0 T ×ˢ univ)`, `t ∈ Ico 0 T` | `ContDiff ℝ ∞ fun x => v (t,x)` |
| `smoothSquareIntegrableJets_slice` | the two `ClassicalSolutionR` fields, `t ∈ Ico 0 T` | `SmoothSquareIntegrableJets (v(t,·))` |
| `memHInfty_dirDeriv` | `MemHInfty z` | `MemHInfty (A05.dirDeriv i z)` |

Notes.

* **No** `HasCompactSupport`, **no** `MemLp _ 1`, no decay, no Schwartz representative anywhere.
* The datum order is an arbitrary `m : ℕ`; the jet order is any `j ≤ m`.  Real (half-integer,
  negative) orders are **not** covered on this side: `physicalJetLp` is indexed by `ℕ`, and a jet
  of fractional order has no meaning.  Lane 020's `⟸` direction does cover real orders.
* `jetSobolevENorm_le_sobolevENorm` needs only smoothness, because its `⊤` branch is genuine: if
  `z` has no order-`m` datum then `sobolevENorm (m:ℝ) z = ⊤` (empty `⨅` in `ℝ≥0∞`) and the
  constant is positive, so the right-hand side is `⊤`.  The `ENNReal.mul_iInf` step in the
  nonempty branch is what makes the bound hold against the *infimum* rather than against one
  chosen datum — which is what `research/A03/REVIEW_CONTRACT.md` §6(3) asks for.
* `smoothSquareIntegrableJets_slice` takes the `sobolev` field **without** its `ContinuousOn`
  conjunct: only `∀ t ∈ Ico 0 T, IsSobolevDatum (m:ℝ) (fun x => velocity (t,x)) (G t)` is used.
  A consumer supplies it as `fun m => (u.sobolev m).imp fun _ h => h.2`.
* The `t = 0` edge of goal 2 is handled by `ContDiffOn.comp` with the affine inclusion
  `x ↦ (t,x)` and `univ ⊆ (·)⁻¹' (Ico 0 T ×ˢ univ)`: the slab is one-sided in **time** but
  contains a full **spatial** neighbourhood, and `ContDiffOn.comp` transports the
  `ContDiffWithinAt` Taylor data along the inclusion onto a genuine neighbourhood of `x` in the
  slice, so `contDiffOn_univ` upgrades it to `ContDiff`.  No separate `t = 0` case is needed and
  no extension to negative times is used.

---

## 3. Which goals are done

| goal | status |
|---|---|
| 1. datum ⟹ jets, quantitative, for `j ≤ m` | **done** (`memLp_iteratedFDeriv_of_isSobolevDatum`, `eLpNorm_iteratedFDeriv_le_of_isSobolevDatum`) |
| 1. `MemHInfty z → ∀ n, MemLp (iteratedFDeriv ℝ n z) 2 volume` | **done** (`memHInfty_jets`), with the full `↔` (`memHInfty_iff_smoothSquareIntegrableJets`) and the `SmoothL2Field` clause (`exists_smoothL2Field_of_memHInfty`) — so unit L2 is closed in all three clauses of `RECONCILIATION.md:153` |
| 1. `jetSobolevENorm 2 z ≤ C · sobolevENorm 2 z` | **done** (`jetSobolevENorm_le_sobolevENorm`, at every order `m`) |
| 2. time-slice smoothness incl. `t = 0` | **done** (`contDiff_slice`, `contDiff_slice_scalar`) |
| 2. slice satisfies `SmoothSquareIntegrableJets` / `SmoothJetsUpTo 2` | **done** (`smoothSquareIntegrableJets_slice`, `smoothJetsUpTo_slice`) |
| 3. corollaries for consumers | **done** (`slice_jets_and_bound`, `slice_allOrderJets_and_bound`, `memHInfty_jetClasses`) |
| 3. pressure gradient | **partial**: `contDiff_pressureGradient_slice` only — see §6 |
| 3. reference solution / initial datum | **done** via `memHInfty_jetClasses` (`initialClassR.1`) and `smoothSquareIntegrableJets_slice` |
| bonus: A02 U1a's order-0-datum ⟹ `L²`-slice step | **done** (`memLp_of_isSobolevDatum`, `eLpNorm_le_of_isSobolevDatum`) |
| bonus: derivative closure | **done** (`smoothSquareIntegrableJets_dirDeriv`, `memHInfty_dirDeriv`) — closes `research/A03/Spec.lean:339` `memHInfty_partialDeriv` |

---

## 4. Definitional agreement with the contracts (scratch-checked)

`formalization/` may not import `Contracts.*` (`verification/lakefile.toml` requires
`../formalization`), so `SmoothSquareIntegrableJets`, `SmoothJetsUpTo` and `jetSobolevENorm` are
restated in the module, as `SmoothDatum.lean` already restates `IsSobolevDatum` and
`sobolevENorm`.  A scratch file `verification/Bindings/Scratch025.lean` (built with
`lake build Bindings.Scratch025` from `verification`, then **deleted**) checked every one of these
by `Iff.rfl` / `rfl`, with `D = NSFormalization.Section4.D01`,
`C = BlowupDensity.Contracts.V1.Data`, `G = BlowupDensity.Contracts.V1`,
`B = BlowupDensity.Contracts.V1.BoundedRep`:

```lean
example (v : C.SpatialField) : D.SmoothSquareIntegrableJets v ↔ G.SmoothSquareIntegrableJets v := Iff.rfl
example (v : C.SpatialField) : D.SmoothSquareIntegrableJets v ↔ B.SmoothSquareIntegrableJets v := Iff.rfl
example (m : ℕ) (v : C.SpatialField) : D.SmoothJetsUpTo m v ↔ B.SmoothJetsUpTo m v := Iff.rfl
example : D.jetSobolevENorm = B.jetSobolevENorm := rfl
example (s : ℝ) (z : C.SpatialField) (A : RealVectorSobolev s) :
    D.IsSobolevDatum s z A ↔ C.IsSobolevDatum s z A := Iff.rfl
example : D.sobolevENorm = C.sobolevENorm := rfl
example (i : Fin 3) (v : C.SpatialField) : A05.dirDeriv i v = G.partialDeriv i v := rfl
example (w : C.SpatialField) : A05.SmoothL2 w ↔ G.SmoothSquareIntegrableJets w := Iff.rfl
```

The same scratch checked the statements the consumers actually need, all elaborating with `exact`
against the real `ClassicalSolutionR` fields (`u.velocity_smooth`, `u.sobolev`, `u.pressure_smooth`):

```lean
-- datum form ⟹ both jet-form classes
example {z} (h : C.MemHInfty z) : G.SmoothSquareIntegrableJets z :=
  D.memHInfty_iff_smoothSquareIntegrableJets.mp h
example {z} : C.MemHInfty z ↔ G.SmoothSquareIntegrableJets z :=
  D.memHInfty_iff_smoothSquareIntegrableJets
example {z} (h : z ∈ C.initialClassR) : G.SmoothSquareIntegrableJets z :=
  D.memHInfty_iff_smoothSquareIntegrableJets.mp h.1
example {z} (h : C.MemHInfty z) (i : Fin 3) : C.MemHInfty (G.partialDeriv i z) :=
  D.memHInfty_dirDeriv h.1 h.2 i

-- the quantitative half, with `Data.sobolevENorm` on the right
example {z} (hz : ContDiff ℝ ∞ z) :
    B.jetSobolevENorm 2 z ≤ ENNReal.ofReal (D.jetSobolevConst 2) * C.sobolevENorm 2 z :=
  D.jetSobolevENorm_le_sobolevENorm 2 hz

-- slices of a classical solution
example (u : C.ClassicalSolutionR ν a f T) (ht : t ∈ Ico (0:ℝ) T) :
    G.SmoothSquareIntegrableJets fun x => u.velocity (t, x) :=
  D.smoothSquareIntegrableJets_slice u.velocity_smooth
    (fun m => (u.sobolev m).imp fun _ h => h.2) ht

-- the A03 → R42 edge, end to end
example (API : B.BoundedRepresentativeAPI) (u : C.ClassicalSolutionR ν a f T)
    (ht : t ∈ Ico (0:ℝ) T) :
    eLpNorm (fun x => u.velocity (t, x)) ⊤ volume
      ≤ ENNReal.ofReal API.Cinfty *
        (ENNReal.ofReal (D.jetSobolevConst 2) * C.sobolevENorm 2 fun x => u.velocity (t, x)) := ...

-- the A05 → R43/R44 edge, end to end
example (API : G.GradientL6API) (u : C.ClassicalSolutionR ν a f T) (ht : t ∈ Ico (0:ℝ) T) :
    eLpNorm (G.gradientTensor fun x => u.velocity (t, x)) 6 volume
      ≤ ENNReal.ofReal API.Csix * eLpNorm (G.laplacian fun x => u.velocity (t, x)) 2 volume :=
  API.gradientLSix _ (D.smoothSquareIntegrableJets_slice u.velocity_smooth
    (fun m => (u.sobolev m).imp fun _ h => h.2) ht)
```

Both edges elaborate.  `research/A05/REVIEW_CONTRACT.md:111` ("the blueprint edge `D01 --> A05`
does not yet discharge A05's consumers") and `research/A03/REVIEW_CONTRACT.md` §6 ("the
`A03 → R42` edge … is not walkable") are both now false.

As `research/D01/REVIEW_L2.md` §7 notes, these identities live only in a scratch; a
`verification/Bindings/` module would be the right place to commit them, and this lane is not
authorised to add one.

---

## 5. Rejected routes

1. **Multi-index Fourier from scratch** — `(1+|ξ|²)^{m/2} ẑ ∈ L²` ⟹ `ξ^α ẑ ∈ L²` for `|α| ≤ m`
   ⟹ `∂^α z ∈ L²` by Plancherel, then assemble the `3^j` words into `iteratedFDeriv`.  This is
   the mathematically direct route and is what `research/D01/ATTEMPTS_L2.md` and
   `research/A05/REVIEW_CONTRACT.md:104` both describe.  Rejected: it is precisely what
   `Source/FourierPhysicalJets.lean` already is — `coordinateWordLp` (`:83`) is the word assembly,
   `physicalJetLp` (`:159`) the tensor reassembly, `compactRep_directional` (`:60`) the
   Plancherel-plus-weak-equals-classical step — and re-deriving it would have duplicated
   `Euler.LpFiniteTensorReconstruction` as well.  The only reason it looked unavailable is that
   `FourierPhysicalJets` is in the cycles convention; one `cyclesToAngular` bridges that.
2. **Going through `Paper3.AngularSobolevClass.MemAngularSobolev` / the distributional
   `TemperedDistribution.MemSobolev` predicate.**  `range_sobolevRealization`
   (`SobolevHilbertModel.lean:116`) characterizes which distributions have a datum, but gives no
   *physical* function back; one still has to invert the Fourier transform and identify the result
   with `z` a.e.  That identification is `physicalLp_ae` (`FourierPhysicalJets.lean:31`), i.e. the
   chosen route with extra steps.
3. **Bessel-iterate inversion**, the mirror of lane 020: lane 020 pushes `z` forward through
   `(1 - (2π)^{-2}Δ)^m` (`Source.PhysicalBesselSobolev.besselField`); the converse would need that
   operator to be invertible on `L²` with the inverse mapping smooth fields to smooth fields.
   `research/D01/REVIEW_L2.md` §7 already records that invertibility "is not exposed".  Rejected.
4. **A cutoff/Fatou argument** (localize `z`, apply `realCompactSobolevTimeSlice`, pass to the
   limit).  This is the route `ATTEMPTS_L2.md` rejected for the other direction and it fails here
   for the same reason: the cutoff destroys the *datum* hypothesis (multiplying by a bump is a
   convolution on the Fourier side), so the hypothesis one is trying to use is the first casualty.
5. **Restating the time-slice goal on the `ClassicalSolutionR` structure itself.**  Rejected
   because `formalization/` cannot import `Contracts.V1.Data`, and re-spelling a 12-field
   structure to state two of its fields would be far more fragile than taking the two fields as
   hypotheses.  `smoothSquareIntegrableJets_slice` therefore takes
   `ContDiffOn ℝ ∞ v (Ico 0 T ×ˢ univ)` and the `sobolev` predicate directly; the scratch above
   confirms `u.velocity_smooth` and `(fun m => (u.sobolev m).imp fun _ h => h.2)` are accepted
   with no massaging.

---

## 6. Failed attempts and friction (all engineering, all fixed)

1. `‖physicalJetLp j‖` written as `norm_nonneg _` — elaborated the metavariable to the wrong
   normed group (`SeminormedAddGroup.toNorm` instead of `ContinuousLinearMap.hasOpNorm`).  Fixed
   by naming the argument: `norm_nonneg (physicalJetLp j)`.
2. `ENNReal.mul_iInf` does **not** take `a ≠ ⊤` at this pin; its hypothesis is
   `a = ∞ → ⨅ i, f i = 0 → ∃ i, f i = 0`.  Discharged with
   `fun h => absurd h ENNReal.ofReal_ne_top`.
3. `iInf_of_empty` needs an `IsEmpty` **instance**, not `¬ Nonempty`; `not_nonempty_iff.mp` and a
   `have` supplies it (a `haveI` there trips `linter.style.haveILetI`).
4. `ENNReal.mul_top`'s side goal simp-normalizes `ENNReal.ofReal c ≠ 0` to `0 < c`, so
   `(jetSobolevConst_pos m).ne'` is the wrong shape; `simpa using jetSobolevConst_pos m` is right.
5. `contDiff_finset_sum` does not exist; the lemma is `ContDiff.sum`
   (`Mathlib/Analysis/Calculus/ContDiff/Operations.lean:387`).
6. In the scratch, `abbrev D := NSFormalization.Section4.D01` does not abbreviate a **namespace**
   (Lean 4 has no namespace alias); every check had to be written with fully qualified names,
   which is also why `open`ing both `D` and `G` was not an option — `SmoothSquareIntegrableJets`
   is declared in both.
7. `mul_le_mul_left'` is not in scope for `ℝ≥0∞` at this pin; `gcongr` plus the hypothesis works.

No mathematical attempt failed: the route above was the first one tried after reading
`FourierPhysicalJets.lean`, and every step of it went through.

---

## 7. Remaining gaps, stated plainly

1. **No lower bound.**  Only `jetSobolevENorm m z ≤ C_m · sobolevENorm (m:ℝ) z` is proved.  The
   reverse, `sobolevENorm (m:ℝ) z ≤ C'_m · jetSobolevENorm m z`, is *not* here.  Lane 020 proves
   `sobolevENorm s z ≤ ‖smoothAngularDatum …‖ₑ` with the right-hand side a norm of **Bessel
   iterates**, not a jet sum (`REVIEW_L2.md` §7 second bullet); turning that into a jet sum needs
   `‖(iteratedBesselField m B).toLp‖ ≤ C_m ∑_{k ≤ 2m} ‖B.jetLp k‖`, which nothing in tree states.
   So the two norms are **not** shown equivalent, only one-sidedly comparable — which is the
   direction every consumer identified so far needs.
2. **Real orders on this side.**  `j` and `m` are natural numbers.  A fractional-order datum
   lowers to an integer-order one and the module then applies, but that composition is not stated.
3. **The pressure gradient has no jets.**  `ClassicalSolutionR.pressure_gradient`
   (`Data.lean:654`) asserts `∇p(t,·) ∈ L²` at order zero only, and the structure supplies no
   Sobolev datum for `p` or `∇p` at any order.  So `SmoothJetsUpTo 1 (∇p(t,·))` does **not**
   follow, and `A03.bounded_representative` cannot be applied to `∇p` from the class as specified.
   `contDiff_pressureGradient_slice` gives the smoothness half and nothing more.  Closing this
   needs either a stronger `ClassicalSolutionR` or unit **L9**(c) (`∇p = (I−P)(f − ∇·(u⊗u))`,
   itself blocked on the Leray projector, toolchain task U05).
4. **Time regularity of the jet path is untouched.**  Everything here is at a fixed `t`; the
   `ContinuousOn G (Ico 0 T)` conjunct of `ClassicalSolutionR.sobolev` is discarded.  A consumer
   needing `t ↦ ‖u(t,·)‖` measurable or continuous still needs units L4/L6;
   `FourierPhysicalJets.exists_smoothL2Field_path` (`:186`) is the obvious binding and is unused
   here.
5. **A02 unit U1b(i) and U1b(ii) remain open.**  The embedding `‖z‖_∞ ≤ C‖z‖_{H²}` on the angular
   carrier (= A01 unit **A1**) and the order shift `‖∇v‖_{H²} ≤ ‖v‖_{H³}` on the datum carrier are
   not touched.  What this module adds to U1 is that U1b(iii) can now start from
   `ClassicalSolutionR.sobolev` rather than from a jet carrier, and that U1a's "order-0 datum ⟹
   `L²` slice" step is now proved outright as `memLp_of_isSobolevDatum` /
   `eLpNorm_le_of_isSobolevDatum` (the `j = 0` case plus `norm_iteratedFDeriv_zero`); the rest of
   U1a — datum uniqueness (L1) and `ContinuousOn` of the datum path on compacts — is untouched.
6. **Unit L1 (datum uniqueness) is still open** and is not needed here: every statement is an
   inequality against `⨅`, so uniqueness of the datum never enters.
7. **The bindings are not committed.**  §4's identities were checked in a scratch that this lane
   deleted; `verification/Bindings/` is out of scope for lane 025.

---

## 8. Gates run

From the worktree root, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`, Lake from
`verification/`.

| gate | result |
|---|---|
| `lake build Contracts.V1.Data NSFormalization.Section4.D01.SmoothDatum Contracts.V1.GradientL6 Contracts.V1.BoundedRepresentative NSFormalization.Source.FourierPhysicalJets` | ok (9879 jobs) |
| `lake build NSFormalization.Section4.D01.DatumToJets` | ok, no warnings from this file |
| `make check` | exit 0 (`check_formalization_plan --check`, `check_contracts`, `test_contract_policy` 13 tests, `check_work_queue` 30 items) |
| `python3 experiments/build_changed_lean.py --base-ref erenup/integration --dry-run` | `Changed Lean modules: none` (the module is untracked, so the committed diff is empty) |
| `targets()` applied to the working tree, then built | `['NSFormalization.Section4.D01.DatumToJets']` → `lake build` ok |
| `#print axioms` on all 29 theorems (scratch, deleted) | every one exactly `[propext, Classical.choice, Quot.sound]` |

No `sorry`, no `axiom`, no `native_decide` in the module.
