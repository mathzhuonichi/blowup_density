# ATTEMPTS — lane 141, A04 contract **V2** (`A04.energy_high_partial_v2`)

Lane kind: contract, version 2 of `A04.energy_high_partial`. Registers the
continuation constant `Cgron` and the two `ζ`-continuation fields
`regularizedNormDerivative` (unit **G2**, lane 135) and `highContinuationIntegral`
(unit **G2b**, lane 138), which V1 listed as "out of scope, not proved on this
branch". Built on `origin/erenup/integration` (lanes 133/135/138 present).

Files added (all built clean, standard three axioms):
`verification/Contracts/V2/EnergyHighPartial.lean`,
`verification/Bindings/EnergyHighPartialV2.lean`,
`verification/Tests/EnergyHighPartialV2.lean`,
`research/A04/axioms_contract_v2.lean`, `verification/contracts.json` entry,
`collaboration/work_items.json` id.

## Decisions

1. **Followed `REVIEW_G2B.md` §5 exactly.** `import Contracts.V1.EnergyHighPartial`
   only (V1 already imports `Contracts.V1.Data` + `Contracts.V1.TameProduct`, so the
   import policy `check_contracts.py` enforces is satisfied without touching the 009
   whitelist). `EnergyHighPartialV2API extends EnergyHighPartialAPI` adds four fields:
   `Cgron`, `Cgron_pos`, `regularizedNormDerivative`, `highContinuationIntegral`.

2. **One new restatement `MemL1Hm`, one new `rfl` bridge.** `Contracts/V1/Data.lean`
   has `forceSobolevENormL1` (`:231`) but **not** `MemL1Hm` (confirmed by grep). Restated
   verbatim from `Section4/A04/Forcing.lean:110`
   (`∀ m, forceSobolevENormL1 (m:ℝ) f ≠ ⊤`) using `Data.forceSobolevENormL1`, and bridged
   by `energyHighPartialV2_memL1Hm_eq : … = NSFormalization.Section4.A04.MemL1Hm := rfl`.
   The `rfl` holds because `Forcing.lean`'s `forceSobolevENorm` is field-for-field defeq
   to `Contracts.V1.Data`'s (the `Forcing.lean` module docstring states this, and the V1
   `sobolevNormAt_eq := rfl` bridge already exercises the same D01↔Data defeq chain). The
   contract's `forceSobolevENormL1` domain type `Data.SpaceTimeField` and the
   implementation's `A02.SpaceTimeField` are defeq (same as V1's `energyIdentityHigh`
   binding). Elaborated on the first try.

3. **`Cgron` opaque + `Cgron_pos`, value only in the binding.** Contract asserts only
   `0 < Cgron m ν` at `0 < ν`, mirroring V1's opaque `Chigh`. The value
   `(Chigh m)²/(4ν)` appears only as the binding `rfl` bonus
   `energyHighPartialV2_Cgron_eq (m ν) : energyHighPartialV2.Cgron m ν = Chigh m ^ 2 / (4 * ν)`
   (analogue of V1's `energyHighPartial_Chigh_eq_Ctame`). The manuscript displays no
   formula for `C_{m,ν}` — pinning it would over-specify (Rule 2 fidelity, `Spec.lean:350-353`).

4. **Two continuation fields bound through `uniqueness_toA02`**, exactly as V1's
   `energyIdentityHigh`: `A04.regularizedNormDerivative … (uniqueness_toA02 w) …` and
   `A04.highContinuationIntegral … (uniqueness_toA02 w) …`. The conclusions mention only
   `w.velocity`, and `(uniqueness_toA02 w).velocity = w.velocity` by `rfl`, so the field
   types match by defeq. `highContinuationIntegral`'s `MemL1Hm f` hypothesis is passed
   straight through: the contract's `MemL1Hm` and `A04.MemL1Hm` are defeq (bridge 2), so
   `hf1 : Contracts.V2…MemL1Hm f` inhabits the expected `A04.MemL1Hm f` slot with no cast.

5. **V1-projection guard is a `rfl` equality, stronger than A02's `maximalPartial_of_v2`.**
   `energyHighPartial_of_v2 : energyHighPartialV2.toEnergyHighPartialAPI = energyHighPartial := rfl`.
   Building the record as `{ energyHighPartial with … }` makes the inherited projection
   definitionally the frozen V1 witness `Bindings.energyHighPartial`, so V1's frozen test
   `Tests.EnergyHighPartial` keeps passing against the untouched witness, and this `rfl`
   rules out a V2 that silently drops or weakens a V1 field.

6. **Ten scope disclosures + the orphan disclosure** written into the module docstring
   and the `contracts.json` scope (opaque `Cgron`; `ν=0` junk so `0 < ν` cannot weaken;
   integrated = `ζ↓0` form; `IntervalIntegrable` asserted not assumed; `.toReal` covers
   only velocity/force slots here — V1's gradient-slot sentence deliberately **not**
   copied since no gradient norm appears; endpoints `0 ≤ t₀ ≤ t < T` with `t₀ = 0` in via
   continuity not `HasSmoothSobolevPath`; still conditional on `HasSmoothSobolevPath` =
   A01 m1; `MemL1Hm` redundant, derivable from `MemForceR` via `memL1Hm_of_memForceR`;
   `a ∈ initialClassR` slack; eq:criterion / Grönwall consequence / eq:mild / first-crossing
   out of scope). Plus: `regularizedNormDerivative` and `highContinuationIntegral` are
   **parallel** manuscript statements — the latter does **not** route through the former
   (it consumes `deriv_normSq_absorbed` + `sqrt_le_primitive_linear` directly), so
   `regularizedNormDerivative` is registered as an honest orphan (zero proof consumers),
   per `REVIEW_G2B.md` findings 2/4 and §5.4.

## Negative examples (pasted error text)

### N1 — the `uniqueness_toA02` transport is load-bearing
`research/A04/probes/v2_no_transport.lean` binds `regularizedNormDerivative` with the
bare Data solution `w` (no `uniqueness_toA02`):

```
error: Application type mismatch: The argument
  w
has type
  ClassicalSolutionR ν a f T
but is expected to have type
  NSFormalization.Section4.A02.ClassicalSolutionR ν a f T
in the application
  NSFormalization.Section4.A04.regularizedNormDerivative ν a f T hν ha hf w
```
(The same probe also reports `Unknown identifier … highContinuationIntegral` because it
imports only `HighContinuation`, not `HighContinuationIntegral` — an artefact of the
minimal probe, not the point; the transport mismatch above is.) Confirms the two
`ClassicalSolutionR` copies are distinct inductive types and the field-wise conversion is
required, as the CLAUDE.md structure exception says.

### N2 — the Young constant is exactly `(Chigh m)²/(4ν)`, not `/(2ν)`
`research/A04/probes/v2_wrong_cgron.lean` claims `Cgron m ν = Chigh m ^ 2 / (2 * ν)` by `rfl`:

```
error: Not a definitional equality: the left-hand side
  energyHighPartialV2.Cgron m ν
is not definitionally equal to the right-hand side
  NSFormalization.Section4.A04.Chigh m ^ 2 / (2 * ν)
```
Confirms the binding-level value bonus is a real check (the `4ν` denominator is the sharp
Young constant, 135-review §2(b) `young_constant_cannot_be_halved`), not a token I could
have mis-stated silently.

### N3 — the JSON re-dump `ensure_ascii` pitfall (engineering)
First edit of `verification/contracts.json` used `json.dump(..., indent=2)` (default
`ensure_ascii=True`), which escaped the non-ASCII in the **frozen** V1 scopes (`ν` →
`ν`, `R³` → `R³`, …), producing a 20-insertion / 8-deletion diff that rewrote
unrelated entries. `check_contracts.py` would not have failed (it compares only
`version`/`specification`/`test_module`/`declaration`/`enabled` per id, not scope bytes),
but it silently reformats frozen text. Fixed by restoring the pristine file and
re-dumping with `ensure_ascii=False`; the diff is now purely the one new entry (11
insertions). Lesson candidate for `logs/LESSONS.md`: editing the JSON registries in
Python must pass `ensure_ascii=False` or the frozen UTF-8 scopes get mangled.

## What a V3 would add

* **`eq:criterion` itself** — the continuation criterion `∫₀^S ‖u‖²_{H²} < ∞ ⇒` no
  breakdown at `S` (`appendix-a-local-theory.tex`, `Spec.lean` next field). Not proved.
* **The Grönwall consequence `higherOrderBound`** (`Spec.lean`,
  `appendix-a-local-theory.tex:146-147`): a single finite `H^m` bound on `[0,S)` for every
  order, consuming `highContinuationIntegral` through unit **G3** (`Gronwall.lean`, lane 041,
  already in tree) — the field R41/R42 actually need.
* **The uniform restart** (`Spec.lean`, `:147-152`), which is A02's `restart` cashed at the
  endpoint. Both of the last two are A04→R43/R44 hand-off fields, not yet assembled.

Once `eq:criterion` + `higherOrderBound` land, `regularizedNormDerivative`'s zero-consumer
status and the two dead Z1 derivative halves (`REVIEW_G2B.md` §5.4, 135-review finding 3)
should be re-judged in one MAINT pass, not deleted piecemeal.

## Review follow-up (REVIEW_CONTRACT_V2.md, applied by the lead as records only)

- Spec citation ranges: the G2 field cites its body (`Spec.lean:459-470`) while the G2b citation `:471-494` is the docstring, the body being `:494-510` — the intended reference is the field including its docstring in both cases; a docstring-only harmonisation is deferred (the file freezes on merge; the statements are byte-identical, verified 138/138 and 163/163 tokens against spec and tree).
- `probes/v2_no_transport.lean` tests only one of the two transported fields (missing import); the reviewer confirmed both transports are load-bearing — the probe is kept as is with this note.
- The `ensure_ascii` diff was 19/8 on reproduction (recorded as 20/8); substance identical.
- `axioms_contract_v2.lean` says "four" standard axioms where it means three (comment only).
- MAINT: `zeroSol` has now been rebuilt six times across reviews — land it once as `research/A04/probes/zero_solution.lean` (or a `Section4/A04/ZeroSolution.lean`); `regularizedNormDerivative` now has a contract-level consumer but still none in `formalization/` — decide with Z1's two derivative halves at V3.
