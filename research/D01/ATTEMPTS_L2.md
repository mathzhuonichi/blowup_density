# D01 unit L2: `H^∞` jet form ⟹ angular Sobolev datum

Target: the `⟸` direction that `research/D01/RECONCILIATION.md` §3 row **L2** records as
open — "**Gap** in the `⟸` direction at non-compact data: only
`Paper3.realCompactSobolevTimeSlice` (`RealPositiveDensity.lean:54`) currently produces
data, and only for compact smooth input."  Two reviewers flagged it as a critical-path
risk for A02 (unit U1) and A03 (unit U2).  Neither of those units is *closed* by this
module; see §1a.

Deliverable: `formalization/NSFormalization/Section4/D01/SmoothDatum.lean`
(369 lines, no `sorry`, no `axiom`, no `native_decide`; every declaration's axiom set is
exactly `propext, Classical.choice, Quot.sound`).

---

## 1. What is proved

Write `z : Space → Space` for the physical field and take the hypotheses to be draft B's
jet form, which is exactly the field-for-field content of
`EulerLpTranslation.SmoothL2Field Space` (`vendor/NavierStokesAndEuler/Euler/LpSmoothField.lean:31`):

```
hz  : ContDiff ℝ ∞ z
hL2 : ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n z) 2 volume
```

| declaration | statement |
|---|---|
| `exists_isSobolevDatum_of_contDiff_memLp` (`:290`) | for **every real** `s`, `∃ A : RealVectorSobolev s, IsSobolevDatum s z A` |
| `memHInfty_of_contDiff_memLp` (`:299`) | `ContDiff ℝ ∞ z ∧ ∀ m : ℕ, ∃ A : RealVectorSobolev (m:ℝ), IsSobolevDatum (m:ℝ) z A`, i.e. `Contracts.V1.Data.MemHInfty z` |
| `sobolevENorm_ne_top_of_contDiff_memLp` (`:315`) | `sobolevENorm s z ≠ ⊤` at every real `s` |
| `smoothAngularDatum` (`:260`), `smoothAngularDatum_isSobolevDatum` (`:278`) | the explicit datum and its Schwartz pairing, not merely an existential |
| `angularRealization_smoothAngularDatum` (`:266`) | each component of the datum realizes `physicalDistribution (componentField i A)` |
| `norm_smoothAngularDatum_le` (`:332`), `sobolevENorm_le_norm_smoothAngularDatum` (`:349`) | `‖A‖ ≤ frequencyUnit^{\|s\|} · √(∑ᵢ ‖(1−(2π)^{-2}Δ)^m zᵢ‖₂²)` and `sobolevENorm s z ≤ ‖A‖ₑ` |
| `angularRealization_smoothAngularDatum_directional` (`:391`) | the **shape of A02 U1b(iii), on the jet carrier**: the datum of `∂_v z` realizes `∂_{v}` of the distribution realized by the datum of `z` |
| `exists_isSobolevDatum_fderiv` (`:400`) | `∂_v z` has a datum at every real order |

### 1a. What this does *not* close downstream

* **A03 unit U2 is unblocked, not closed.**  `research/A03/Spec.lean:324,330,339` state
  `memHInfty_memHm`, `memHInfty_component` and `memHInfty_partialDeriv` with
  `Contracts.V1.Data.MemHInfty z` as a **hypothesis**, i.e. in the *datum* form.  This
  module proves **jets ⟹ datum only**.  `memHInfty_partialDeriv`, for instance, needs
  datum ⟹ jets, then `∂_j`, then jets ⟹ datum; the first step is absent, so none of the
  three fields follows.  What is retired is the sizing risk of
  `research/A03/COMPARISON.md:210-221` — "if L2 stalls, U2 is an L" — because the
  non-compact datum producer now exists; the residual `⟹` direction is the one
  `RECONCILIATION.md:153` binds to `Source.FourierPhysicalJets.smoothL2FieldOfFourier`
  (`:169`) and `physicalJetLp_ae` (`:159`).
* **A02 unit U1 is not closed either.**  `research/A02/COMPARISON.md:163-164` splits U1
  into U1a (energy; needs D01 unit **L1** plus an order-0-datum ⟹ `L²`-slice lemma) and
  U1b, and U1b into three parts.  This module delivers **the shape of U1b(iii) only, and
  on the jet carrier**: the derivative is `SmoothL2Field.directionalField v`
  (`= fun x => fderiv ℝ z x v`), not the upstream `spatialDerivative u t x`
  (`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:59`), and it starts
  from a `SmoothL2Field`, not from `ClassicalSolutionR.sobolev`'s datum path
  (`Data.lean:643-645`) where U1b begins.  U1b(i) (the `H²` sup embedding on the angular
  carrier, = A01 unit **A1**) and U1b(ii) (the order shift `‖∇v‖_{H²} ≤ ‖v‖_{H³}` between
  two datum norms) are **untouched**: `norm_smoothAngularDatum_le` is a one-sided bound in
  the physical Bessel iterates, not a comparison of two datum norms.

`IsSobolevDatum` (`:237`) and `sobolevENorm` (`:306`) are **verbatim restatements** of
`verification/Contracts/V1/Data.lean:160` and `:189`.  They must be restated because the
`NSFormalization` package is a *dependency* of the `Contracts` library
(`verification/lakefile.toml` requires `../formalization`), so a module inside
`formalization/` cannot import `Contracts.V1.Data`.  The two are definitionally equal;
checked out of tree with

```lean
example (s : ℝ) (z : …SpatialField) (A : RealVectorSobolev s) :
    NSFormalization.Section4.D01.IsSobolevDatum s z A ↔
      BlowupDensity.Contracts.V1.Data.IsSobolevDatum s z A := Iff.rfl
example (s : ℝ) (z : …SpatialField) :
    NSFormalization.Section4.D01.sobolevENorm s z =
      BlowupDensity.Contracts.V1.Data.sobolevENorm s z := rfl
theorem contract_memHInfty … : BlowupDensity.Contracts.V1.Data.MemHInfty z :=
  NSFormalization.Section4.D01.memHInfty_of_contDiff_memLp hz hL2
```

all three accepted, `contract_memHInfty` and `contract_sobolevENorm_ne_top` with axioms
`[propext, Classical.choice, Quot.sound]`.  **Turning this into a committed binding needs
one module under `verification/Bindings/`, which this lane was not authorised to add.**

Strictly more than the task asked: the datum exists at every **real** order (half-integer
and negative included), not only at integer `m`, and with no compact-support hypothesis.

---

## 2. Route chosen, and why

**Chosen: reuse the existing cycles-convention integer-order construction, add reality,
add order lowering, transport to the angular normalization.**

The decisive discovery is that the hardest analytic step — physical `L²` jets ⟹ a
Fourier-side `L²` datum of integer order, without compact support and without an `L¹`
hypothesis — is *already in the tree*, in the cycles-frequency convention:

* `Source.PhysicalSobolevDistribution.physicalH0Datum` (`:42`) is `𝓕 A.toLp`, the order-0
  datum, through Mathlib's `L²` Fourier transform (`Lp.fourierTransformₗᵢ`), so no `L¹`
  premise ever appears;
* `Source.PhysicalBesselSobolev.evenSobolevDatum` (`:144`) raises this to every **even**
  order by iterating the *physical* Bessel operator `1 − (2π)^{-2}Δ` on the field
  (`besselField`, `:52`) and identifying it with `TemperedDistribution.besselPotential`;
* `Source.PhysicalIntegerSobolev.integerSobolevDatum` (`:14`) lowers `2n → n` with
  `Paper3.sobolevOrderLowering`, giving every integer order, and
  `vectorSobolevDatum_pairing` (`:54`) already states the Schwartz pairing
  componentwise — but with `sobolevRealization`, and in `VectorSobolevHilbert`, which is
  *not* the contract's `RealVectorSobolev` because it carries no reality constraint.

So the three genuinely missing pieces were:

1. **Reality.**  `RealVectorSobolev s = Product (Fin 3) (RealSobolevHilbert s)` and
   `RealSobolevHilbert s = Source.RealSobolev.realSubspace s`, the *closed subspace* of
   conjugate-reflection-symmetric data (`02-preliminaries.tex:72`).  Nothing in the tree
   proved that the datum of a real physical field is symmetric except by construction via
   `realProjectionTo` on compactly supported input.  Proved here along the construction:
   * `fourier_conjugation` (`:114`): `𝓕 (conjugation u) = realSymmetry (𝓕 u)` for **all**
     `u ∈ L²`, by `DenseRange.induction_on` from the Schwartz core, where it is
     `Source.RealSobolev.fourier_conjugate` (`RealSobolev.lean:61`) combined with
     `Paper3.frequencyRealSchwartz_toLp` (`AngularRealSobolev.lean:20`) and Mathlib's
     `SchwartzMap.toLp_fourier_eq`;
   * `IsRealField` (`:135`) — `∀ x, conj (A.field x) = A.field x` — is preserved by
     `addField`, `sumField`, `scaleField` with a real scalar, and (the only non-formal
     step) `directionalField`, because `conj` is an `ℝ`-CLM and `fderiv` commutes with
     post-composition by a CLM (`IsRealField.directional`, `:157`).  Hence by
     `laplacianField` and `besselField`, hence by `iteratedBesselField` (`:180`);
   * `realSymmetry_sobolevOrderLowering` (`:208`): order lowering is multiplication by the
     **real and even** symbol `(1+‖ξ‖²)^{(r−s)/2}`, so it commutes with conjugate
     reflection.  The a.e. argument is copied structurally from
     `Paper3.angularWeightEquiv_realSymmetry` (`AngularSobolevCoordinates.lean:239`).
2. **Arbitrary real order.**  `sobolevOrderLowering (m:ℝ) s hs` with `m = ⌈s⌉₊` and
   `Nat.le_ceil`, using `sobolevRealization_orderLowering`
   (`SobolevOrderLowering.lean:78`) to see that the physical distribution is unchanged.
   The integer case is the instance `s = m`, `hs = le_rfl`; the construction is written
   once, parameterised by `(m, s, hs : s ≤ m)`.
3. **Angular normalization.**  `Paper3.cyclesToAngularRealVector`
   (`AngularRealVectorBochner.lean:15`) and
   `angularRealization_cyclesToAngularReal` (`AngularRealSobolev.lean:89`).  This is the
   step `RECONCILIATION.md` §3 row L4 already names as the standard adaptation.

### Routes rejected

* **Schwartz density.**  Approximate `z` in `H^m` by Schwartz functions and pass the data
  to the limit.  Rejected: the contract's `IsSobolevDatum` is a *pointwise* Schwartz
  pairing with the given `z`, so a limit argument needs `L²` convergence of the physical
  approximants *and* an identification of the limiting pairing, i.e. it re-proves the
  existing `Paper3` density machinery in the wrong direction.  It also gives the datum only
  at the order used for the approximation, and would not produce an explicit datum.
* **Direct Fourier transform of the `L²` derivatives.**  Build the datum as
  `(1+|ξ|²)^{m/2} ẑ` from `𝓕 z` and Plancherel-type multi-index bookkeeping
  (`Real.fourierIntegral_fderiv` etc.).  Rejected: the bookkeeping is
  `∑_{|α|≤m} ‖∂^α z‖₂² ≍ ∫ (1+|ξ|²)^m |ẑ|²` with dimension-dependent binomial constants,
  and Mathlib at this pin has no multi-index Fourier–Sobolev equivalence.  The
  `besselField` route in `Source/PhysicalBesselSobolev.lean` is exactly the same idea done
  operator-wise instead of multi-index-wise, and it is already proved.
* **Distributional route via `TemperedDistribution.MemSobolev`.**  Show
  `MemSobolev m 2 (physicalDistribution zᵢ)` and use
  `Paper3.memAngularSobolev_iff_memSobolev` / `mem_range_angularRealization_iff`.  This is
  the same problem one level up: producing the `MemSobolev` witness *is* producing the
  datum.  It would also lose the explicit datum and the norm bound.
* **`Paper3.realCompactSobolevTimeSlice` plus cutoffs.**  Multiply `z` by a cutoff, use the
  compact-support construction, take a limit.  Rejected for the same reason as Schwartz
  density, plus it needs uniform `H^m` bounds on `χ_R z`, i.e. commutator estimates that do
  not exist in the tree.

### Failed attempts along the chosen route

1. **`realSymmetry` at the distribution level.**  First attempt was a general lemma
   `sobolevRealization s (realSymmetry h) ψ = conj (sobolevRealization s h (conjugateSchwartz ψ))`,
   from which reality would follow by `sobolevRealization_injective` for *any* datum whose
   realization is a real function.  Abandoned before formalising: it needs a
   conjugate-linear "conjugate distribution" operator, which is not bundled in Mathlib, and
   on the Schwartz core it still needs `𝓕⁻(conj ∘ g ∘ neg) = conj ∘ 𝓕⁻ g`, i.e. the same
   integral chase as `fourier_conjugate` but for `𝓕⁻` and through
   `sobolevWeightMultiplier`.  Proving reality *along* the construction (item 1 above) is
   strictly less work and reuses `fourier_conjugate`, which already exists.
2. **`open` scope errors.**  `addField`/`sumField`/`field_ext` live in
   `EulerLpTranslation.SmoothL2Field` and `EulerOrdinarySobolev`; with only
   `open EulerLpTranslation` they are unknown identifiers and `autoImplicit` turns them
   into sort variables, producing misleading "Function expected" errors.  Fixed by adding
   `open EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev`.
3. **`conjugation` not syntactically `compLpL`.**  `rw [ContinuousLinearMap.coeFn_compLpL …]`
   failed against a goal mentioning `conjugation A.toLp`, because `conjugation`
   (`RealSobolev.lean:22`) is a `def` and is not unfolded.  Fixed by extracting
   `conjugation_ae` (`:98`) once and using it everywhere.
4. **`private def basis`.**  `PhysicalBesselSobolev.laplacianField` is stated over a
   `private` orthonormal basis, so its body cannot be named from another module.  Worked
   around with `show IsRealField (sumField Finset.univ (fun i : Fin 3 => …
   (EuclideanSpace.basisFun (Fin 3) ℝ i) …))`, which is accepted up to `δ`-reduction.
5. Two deprecation warnings (`ContinuousLinearMap.coe_smul'`, `ContinuousLinearMap.smul_apply`)
   removed by switching to `smul_apply`; the module now builds warning-free.

---

## 3. Exact hypotheses, and why `H^∞` fields satisfy them

The theorems take `ContDiff ℝ ∞ z` together with `∀ n : ℕ, MemLp (iteratedFDeriv ℝ n z) 2 volume`
— nothing else.  No compact support, no `L¹`, no decay, no Schwartz representative.

* That pair is *precisely* the data of `EulerLpTranslation.SmoothL2Field Space`; the proofs
  construct `⟨z, hz, hL2⟩` and hand it to the existing machinery.
* It is draft B's spelling of `H^∞` in `RECONCILIATION.md` §3 row L2 and the `X_R` row of
  §1, so this closes exactly the implication that row asks for.
* For a field in every `H^m` in the *manuscript* sense, the implication in the other
  direction (`Data.lean`'s datum form ⟹ these jets in `L²`) is **not** proved here; see §4.

Two smaller hypotheses worth naming:

* `hs : s ≤ (m : ℝ)` in `smoothAngularDatum` — lowering is contractive only downwards
  (`sobolevOrderLowering` needs `r ≤ s`).  The public theorems instantiate `m = ⌈s⌉₊`.
* Order lowering is used twice (once inside `integerSobolevDatum`, once here); it is
  contractive, so the norm bound of `norm_smoothAngularDatum_le` is not degraded by it.

---

## 4. Remaining gaps, stated plainly

1. **No committed binding to `Contracts.V1.Data`.**  The definitional identity with
   `IsSobolevDatum`, `sobolevENorm` and `MemHInfty` is verified out of tree (§1) but not
   recorded in a compiled module, because this lane may only add files under
   `formalization/NSFormalization/Section4/D01/`.  The follow-up is a three-line
   `verification/Bindings/HInfty.lean`.
2. **Only the `⟸` direction of row L2.**  `MemHInfty a → ∀ n, MemLp (iteratedFDeriv ℝ n a) 2 volume`
   (the datum form implies the jet form, i.e. Sobolev embedding plus the identification of
   distributional and classical derivatives) is **not** proved.  This is what blocks A03
   U2 and A02 U1b from `ClassicalSolutionR`; A02 gets the derivative *identification*
   (`angularRealization_smoothAngularDatum_directional`), in the shape of U1b(iii) on the
   jet carrier, but not the converse regularity statement.
3. **The norm bound is in terms of Bessel iterates, not multi-indices.**
   `norm_smoothAngularDatum_le` gives
   `‖A‖ ≤ frequencyUnit^{|s|} · √(∑ᵢ ‖(1−(2π)^{-2}Δ)^m zᵢ‖₂²)`.
   The manuscript's `∑_{|α|≤m} ‖∂^α z‖₂` form needs, in addition,
   `‖(iteratedBesselField m B).toLp‖ ≤ C_m ∑_{k ≤ 2m} ‖B.jetLp k‖`, which is an induction
   over `besselField = id + c·laplacianField` using `toLp_mapField` and
   `norm_derivative_jetLp`; estimated at 40–60 lines and **not attempted** here.  The
   reverse inequality (a *lower* bound on the datum norm, i.e. the two-sided equivalence)
   is harder: it needs invertibility of the Bessel iterate on `L²`, which the current
   construction does not expose.
4. **No uniqueness statement.**  Uniqueness of the datum is `RECONCILIATION.md` unit L1
   (`angularRealization_injective`, `AngularFourierDilation.lean:203`); it is not restated
   here, so `sobolevENorm s z = ‖smoothAngularDatum … ‖ₑ` (equality rather than `≤`) is not
   proved.  With L1 it is immediate.
5. **No time-path version.**  `IsSobolevPath` / `MemForceR` (`Data.lean:174,544`) need the
   trajectory `t ↦ A t` to be `ContDiffOn` into `RealVectorSobolev m` and `MemLp` in time.
   `Source.PhysicalIntegerSobolev.continuous_vectorSobolevDatum` (`:61`) gives continuity of
   the cycles datum along a continuous jet path, and `cyclesToAngularRealVector` is a CLE,
   so the continuity half transports for free; smoothness in `t` and the `L¹ ∩ L²` time
   bounds are not touched.  That is unit L4/L6 work, not L2.
6. **`research/A02/` and `research/A03/` were absent at this lane's merge base
   (`09fcb90`)** and could not be read while the module was written; they **do exist on
   the integration tip** (`erenup/integration`).  They have since been read — via
   `git show erenup/integration:research/A02/COMPARISON.md` and
   `…:research/A03/{COMPARISON.md,Spec.lean}` — and the scope claims of §1a, of the module
   docstring and of the docstring of
   `angularRealization_smoothAngularDatum_directional` were corrected accordingly
   (reviewer findings 1 and 2 of `research/D01/REVIEW_L2.md`).  Findings 5, 6 and 7 were
   applied at the same time: the `angularRealization_injective` line number (`:203`), the
   rename `angularDatum → smoothAngularDatum` to stop shadowing
   `Paper3.angularDatum` (`AngularFourierDilation.lean:225`), and the qualification of the
   prior-art claim to *real angular vector* data.

Nothing in this module is conditional, admitted, or `sorry`-carrying: the gaps above are
statements that are *absent*, not statements that are assumed.

---

## 5. Commands run, and results

All from `verification/` after `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`.

| command | result |
|---|---|
| `bash scripts/lean-install.sh` | exit 0, `lake test` OK (`Contract BlowupDensity.Tests.checkedPacket: checked; standard logical axioms only`) |
| `lake build Contracts.V1.Data` | OK (built as part of the prerequisite build) |
| `lake build NSFormalization.Source.PhysicalIntegerSobolev NSFormalization.Paper3.AngularRealVectorBochner Contracts.V1.Data` | OK, 9873 jobs |
| `lake build NSFormalization.Section4.D01.SmoothDatum` | **OK**, 9871 jobs, no warning from the new file |
| `lake build` (default targets) | OK, 9346 jobs |
| `make check` | exit 0 (`check_formalization_plan --check`, `check_contracts`, `test_contract_policy` 13 tests, `check_work_queue` 30 items) |
| `python3 experiments/build_changed_lean.py --base-ref erenup/integration --dry-run` | `Changed Lean modules: none` (the file is untracked, so `git diff` sees nothing) |
| `targets(['formalization/NSFormalization/Section4/D01/SmoothDatum.lean'])` → `['NSFormalization.Section4.D01.SmoothDatum']`, then `lake build` of it | OK |
| `#print axioms` on all 29 new theorems (scratch file outside `formalization/`) | every one `[propext, Classical.choice, Quot.sound]` |
| `#print axioms contract_memHInfty`, `contract_sobolevENorm_ne_top` (scratch importing `Contracts.V1.Data`) | `[propext, Classical.choice, Quot.sound]` |

Failures encountered and fixed, in order: unknown identifiers `addField`/`sumField`/
`sumField_field`/`field_ext` (missing `open`); `rw` failure on `conjugation A.toLp`
(added `conjugation_ae`); `private` `basis` in `laplacianField` (used `show`); two
deprecated-lemma warnings.  No attempt was abandoned for a mathematical obstruction.

Note on `make check`: it reports `"source_hashes_match": false`.  That is **pre-existing
and unrelated** — the single mismatching file is `formalization/lakefile.toml`, changed by
the earlier HeliCorgi vendoring (`RECONCILIATION.md` §5, infrastructure note).  Only
`make snapshot` asserts on it; `make check` does not, and exits 0.
