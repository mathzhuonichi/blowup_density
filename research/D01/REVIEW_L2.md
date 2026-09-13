# Review of D01 unit L2 (lane 020) — `formalization/NSFormalization/Section4/D01/SmoothDatum.lean`

**Verdict: ACCEPT-WITH-NOTES.**  The module builds, is axiom-clean, is definitionally the
contract's own vocabulary, and closes exactly the `⟸` direction that `RECONCILIATION.md:153`
records as the L2 gap — at every real order, with no compact support and no `L¹`.  Every note is
a *docstring/record* overclaim about which downstream units it closes, plus two citation slips;
no mathematical defect, and no statement weaker than advertised.  Reviewed at `61db0b2` on
`erenup/020-D01-hm-datum` (merge-base `09fcb90`; integration is now `f1603c9`).  Nothing modified.

## 1. Gates

| gate | result |
|---|---|
| `cd verification && lake build NSFormalization.Section4.D01.SmoothDatum` | **exit 0**, 9871 jobs |
| warnings from the new file | **none** — 11 warnings + 1 `info`, all from *replayed* dependencies (`PhysicalBesselSobolev:134`, `PacketForceExtension:44`, `ViscosityPacket:34`, `RealSobolev:90`×3, `SpatiallyCompactTime:88`, `RealPositiveDensity:57,66,78,90`, `RealVectorPositiveDensity:29`) |
| `make check` | **exit 0** (plan, contracts, 13 policy tests, 30 work items) |
| `build_changed_lean.py --base-ref erenup/integration --dry-run` | `Changed Lean modules: NSFormalization.Section4.D01.SmoothDatum` — exactly one |
| same without `--dry-run` | **exit 0**, 9871 jobs |
| `grep -nE "sorry\|axiom\|admit\|native_decide\|unsafe"` | **zero matches**, not even in comments |
| size | 369 lines, **29 theorems**, **5 defs** |

## 2. Axioms

`/tmp` scratch importing the module, `#print axioms` on all 29 theorems (names harvested by grep, so
exhaustive), `lake env lean` from `verification/`.  **All 29 are exactly `[propext, Classical.choice,
Quot.sound]`.**  Scratch deleted.

## 3. Definitional agreement with `Contracts/V1/Data.lean`

One scratch importing both `Contracts.V1.Data` and the module; all six examples elaborate (exit 0, no
errors), confirming the worker's claims.  `D` = `NSFormalization.Section4.D01`, `C` =
`BlowupDensity.Contracts.V1.Data`:

```lean
example (s : ℝ) (z : Space → Space) (A : RealVectorSobolev s) :
    D.IsSobolevDatum s z A ↔ C.IsSobolevDatum s z A := Iff.rfl        -- ✓ (and `exact h` both ways)
example : D.sobolevENorm = C.sobolevENorm := rfl                      -- ✓ (function level)
example {z : Space → Space} (hz : ContDiff ℝ ∞ z)
    (hL2 : ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n z) 2 volume) :
    C.MemHInfty z := D.memHInfty_of_contDiff_memLp hz hL2              -- ✓
example {z : Space → Space} (hz : …) (hL2 : …) (s : ℝ) :
    C.sobolevENorm s z ≠ ⊤ := D.sobolevENorm_ne_top_of_contDiff_memLp hz hL2 s   -- ✓
example {z : Space → Space} (hz : …) (hL2 : …) (hdiv : C.IsSolenoidal z) :
    z ∈ C.initialClassR := ⟨D.memHInfty_of_contDiff_memLp hz hL2, hdiv⟩          -- ✓ (bonus)
```

`Data.lean:160` and `:189` are reproduced verbatim; `SpatialField` (`:99`) is an `abbrev` for
`Space → Space`, so there is no type mismatch.  The stated reason for restating rather than importing
(`verification/lakefile.toml` requires `../formalization`) is correct.

## 4. Statement fidelity — findings, ranked

1. **A03 unit U2 is not closed; only its hard half is unblocked.** (major, scope claim)
   `research/A03/Spec.lean:324,330,339` state `memHInfty_memHm`, `memHInfty_component`,
   `memHInfty_partialDeriv` all with `MemHInfty z` as **hypothesis** — the *datum* form.  The
   module proves jet ⟹ datum only; `memHInfty_partialDeriv` needs datum ⟹ jet, then `∂_j`, then
   jet ⟹ datum, and the first step is absent.  What the module does retire is the risk
   `research/A03/COMPARISON.md:210-221` names ("if L2 stalls, U2 is an L"): the non-compact datum
   producer now exists, and the residual `⟹` direction is the one `RECONCILIATION.md:153` already
   binds to `Source.FourierPhysicalJets.smoothL2FieldOfFourier` / `physicalJetLp_ae`.
2. **The `A02 unit U1` label on `angularRealization_angularDatum_directional` (`:350`)
   overclaims.** (major, scope claim)  `research/A02/COMPARISON.md:163-164` splits U1 into U1a
   (energy: needs D01 **L1** plus an order-0-datum ⟹ `L²`-slice lemma) and U1b, and U1b is
   three things: (i) `‖z‖_∞ ≤ C‖z‖_{H²}` on the angular carrier (= A01 unit **A1**, rated
   **L**); (ii) the order shift `‖∇v‖_{H²} ≤ ‖v‖_{H³}` on the angular datum carrier; (iii)
   identification of the *physical* `spatialDerivative u t x` with the derivative of that datum's
   realization.  The module delivers **(iii)'s shape only, on the jet carrier**:
   `SmoothL2Field.directionalField v` (= `fderiv ℝ z x v`) against `∂_{v}` of the angular
   realization — not upstream `spatialDerivative` (`vendor/…/NavierStokes/ProblemStatement.lean:59`),
   and not from `ClassicalSolutionR.sobolev`'s datum path (`Data.lean:643-645`), where U1b starts.
   (i) and (ii) are untouched: `norm_angularDatum_le` is a one-sided bound in Bessel iterates, not a
   comparison of two datum norms.  Should read "A02 unit U1b(iii), jet carrier".
3. **Hypotheses, order and constant are exactly as advertised.** (confirmed, no defect)
   `exists_isSobolevDatum_of_contDiff_memLp` (`:269`), `memHInfty_of_contDiff_memLp` (`:278`) and
   `sobolevENorm_ne_top_of_contDiff_memLp` (`:294`) take precisely `ContDiff ℝ ∞ z` and
   `∀ n : ℕ, MemLp (iteratedFDeriv ℝ n z) 2 volume` — field-for-field `SmoothL2Field`
   (`LpSmoothField.lean:31`).  **No** `HasCompactSupport`, **no** `MemLp _ 1`, no decay, no Schwartz
   representative.  Order is an unconstrained `s : ℝ`; `m = ⌈s⌉₊` with `Nat.le_ceil` covers negative
   `s` (`⌈s⌉₊ = 0`, `s ≤ 0`) and half-integers.  The constant of `norm_angularDatum_le` (`:311`) is
   exactly `frequencyUnit ^ |s| · √(∑ᵢ ‖(1−(2π)⁻²Δ)^m z_i‖₂²)`; every other link is contractive —
   `realProjectionTo_norm_le` (`RealPositiveDensity.lean:31`) ∘ `sobolevOrderLowering_norm_le`
   (`SobolevOrderLowering.lean:39`) ∘ `norm_integerSobolevDatum_le` (`PhysicalIntegerSobolev.lean:21`),
   then `cyclesToAngularRealVector_norm_le` (`AngularRealVectorBochner.lean:24`, rpow).
4. **Only half of `RECONCILIATION.md` L2.** (minor, correctly disclosed)  L2 asks for an `↔`
   *and* "either implies `∃ A : SmoothL2Field Space, A.field = a`"; the `⟹` half and the
   datum-form ⟹ `SmoothL2Field` half are absent.  `ATTEMPTS_L2.md` §4.2 says so plainly.
5. **Citation slip, `ATTEMPTS_L2.md` §4.4.** (minor)  `angularRealization_injective` is at
   `Paper3/AngularFourierDilation.lean:203`, not `:222` (`:222` is
   `angularFourierDistribution_schwartz_apply`); `RECONCILIATION.md` and A03 say `:203`.
6. **Name shadowing.** (minor)  The module defines `angularDatum` (`:239`) while
   `open NSFormalization.Paper3` brings `Paper3.angularDatum` (`AngularFourierDilation.lean:225`)
   into scope.  Type-directed overload resolution disambiguates today, so it builds; it is fragile,
   and A03 U1's reuse table names `Paper3.angularDatum`.  Consider `angularVectorDatum`.
7. **Docstring loose about prior art.** (minor)  "Before this module the only in-tree producer of
   data was `Paper3.realCompactSobolevTimeSlice`" holds only for *real angular vector* data;
   `Source.PhysicalIntegerSobolev.vectorSobolevDatum` (`:42`) already produced non-compact cycles data.

## 5. Reuse spot-check — every cited declaration resolves at file:line

`SmoothL2Field` `vendor/…/Euler/LpSmoothField.lean:31` (fields `field`, `smooth : ContDiff ℝ ∞ field`,
`integrable : ∀ n, MemLp (iteratedFDeriv ℝ n field) 2 volume` — exactly the theorems' hypothesis pair) ·
`Source/PhysicalSobolevDistribution.lean`: `physicalDistribution_apply` `:17`,
`physicalDistribution_directionalField` `:29` (`= ∂_{v} (physicalDistribution A)`, `LineDeriv` scope; proved
by integration by parts, a genuine distributional identity), `physicalH0Datum` `:42` ·
`Source/PhysicalBesselSobolev.lean`: `besselField` `:52`, `evenSobolevDatum` `:144` ·
`Source/PhysicalIntegerSobolev.lean`: `integerSobolevDatum` `:14`, `_realization` `:17`, `norm_…_le` `:21`,
`componentField` `:32`, `componentField_field` `:35`, `vectorSobolevDatum` `:42`, `vectorSobolevDatum_pairing`
`:54` · `Paper3/SobolevOrderLowering.lean`: `sobolevOrderLowering` `:26`, `_coeFn` `:31`, `_norm_le` `:39`,
`sobolevRealization_orderLowering` `:78` · `Paper3/AngularRealSobolev.lean`: `frequencyRealSchwartz` `:13`,
`_toLp` `:20`, `cyclesToAngularReal` `:67`, `_norm_le` `:80`, `angularRealization_cyclesToAngularReal` `:89` ·
`Source/RealSobolev.lean`: `realSymmetry_ae` `:28`, `conjugateSchwartz` `:53`, `fourier_conjugate` `:61`,
`mem_realSubspace_iff` `:123`, `realProjection_eq_self` `:131` · `Paper3/AngularRealVectorBochner.lean`:
`cyclesToAngularRealVector` `:15`, `_norm_le` `:24` · `Paper3/RealPositiveDensity.lean`: `realProjectionTo`
`:21`, `_norm_le` `:31`, `realCompactSobolevTimeSlice` `:54` · `Source/FourierConvention.lean`:
`frequencyUnit` `:15`, `frequencyUnit_pos` `:17`.  No fabricated reuse.

## 6. `ATTEMPTS_L2.md` — honest

Each rejected route fails for a reason that holds up: Schwartz density, the distributional `MemSobolev` route
and cutoffs on `realCompactSobolevTimeSlice` all reduce to "producing the witness *is* the problem", and the
direct multi-index Fourier route is correctly diagnosed as absent from Mathlib at this pin, with `besselField`
named as the operator-wise version already proved.  The five failed attempts are engineering failures,
labelled as such; §4 lists gaps without hedging.  Two rows are stale but superseded: §5's
`build_changed_lean.py → "none"` was correct while the file was untracked, and §4.6's "`research/A02/`,
`research/A03/` do not exist" held at the merge-base though both exist on `erenup/integration` (a rebase lets
finding 2 be fixed).  Defects: findings 5 and 2.

## 7. What L2 still lacks

* the `⟹` direction (datum form ⟹ `L²` jets), hence `MemHInfty a ↔ …` and `MemHInfty a → ∃ A :
  SmoothL2Field Space, A.field = a` — the blocker for A03 U2 and for A02 U1b from `ClassicalSolutionR`;
* a two-sided norm equivalence.  Only `sobolevENorm s z ≤ ‖A‖ₑ` is proved; equality needs unit **L1**
  (`angularRealization_injective`, `:203`), and the manuscript's `∑_{|α|≤m}‖∂^α z‖₂` form needs
  `‖(iteratedBesselField m B).toLp‖ ≤ C_m ∑_{k≤2m} ‖B.jetLp k‖` plus invertibility of the Bessel
  iterate on `L²` for the lower bound (not exposed);
* time paths: `IsSobolevPath` / `MemForceR` (`Data.lean:174,544`) need `ContDiffOn` in `t` into
  `RealVectorSobolev m` and `L¹ ∩ L²` time bounds.  Continuity transports free via
  `continuous_vectorSobolevDatum` (`PhysicalIntegerSobolev.lean:62`) + the CLE; the rest is L4/L6;
* a committed binding.  §3's identities live only in a scratch; a `verification/Bindings/` module
  (not authorised for this lane) should record them, and would also defuse finding 6.
