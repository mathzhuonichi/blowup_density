# A02 — registering `A02.uniqueness` (lane 057)

Record for the contract-registration lane: which theorems of the merged A02
modules were bundled into `verification/Contracts/V1/Uniqueness.lean`, which were
deliberately left out and why, how the structure conversion is done, and the
gates.  Positive and negative results both, per `CLAUDE.md` rule 4.  This lane
adds **no mathematics**: every field is `:= NSFormalization.Section4.A02.<thm>`
applied to solutions transported by the mechanical structure conversion.

Files produced: `verification/Contracts/V1/Uniqueness.lean` (spec,
`UniquenessAPI`), `verification/Bindings/Uniqueness.lean` (the `toA02` structure
conversion, three `rfl` bridges, two `rfl` `example`s, and the binding
`theorem uniqueness`), `verification/Tests/Uniqueness.lean` (`checkedUniqueness`
+ `checkAxioms`), and the `A02.uniqueness` entry of
`verification/contracts.json`.  No proof module was touched.

## 1. What is bundled — theorem → field

`A02` = `NSFormalization.Section4.A02`.  The two proved theorems are in
`Section4/A02/Uniqueness.lean` (lane 052; they rest on `Energy.lean` lane 033 and
`Bounds.lean` lane 049 through `Source.BoundedViscosityUniqueness`).

| theorem (file:line) | field | paper |
|---|---|---|
| `A02.velocity_unique` `Uniqueness.lean:120` | `velocity_unique` | `appendix-a-local-theory.tex:119-124` (energy estimate + Grönwall) |
| `A02.pressure_gauge` `Uniqueness.lean:244` | `pressure_gauge` | `02-preliminaries.tex:31`, `appendix-a-local-theory.tex:124` |

Both theorems are stated in `Section4/A02/Uniqueness.lean` with a docstring
"**Spec field `UniquenessAPI.velocity_unique`** (`research/A02/Spec.lean:267-272`),
verbatim" (resp. `:277-281`), so the field types below are copied token-for-token
from `research/A02/Spec.lean:263-281`.  The paper lines were re-read:
`appendix-a-local-theory.tex:119-120` is the display
`½(‖z‖₂²)' + ν‖∇z‖₂² ≤ ‖∇u₂‖_∞‖z‖₂²`, `:122-123` "the coefficient is bounded …
since `u₂ ∈ C_tH³`. Grönwall gives uniqueness", and `02-preliminaries.tex:31` is
"the scalar pressure is determined up to a function of time".

## 2. Left out, and why — the rest of `MaximalSolutionAPI`

`research/A02/Spec.lean` bundles `UniquenessAPI` (the two fields above) with a
much larger `MaximalSolutionAPI`.  Only the `UniquenessAPI` half has proved
modules today (`Energy`/`Bounds`/`Uniqueness`); the `Order.lean` and
`Restrict.lean` modules exist but their public deliverables are not yet the
`MaximalSolutionAPI` fields, and several fields (`exists_maximal`,
`maximal_unique`, `restart`, `insertion_lifespan_eq`) have no proof at all.  The
brief scopes this lane to `A02.uniqueness` only.  Explicitly **not** registered,
each owed by a later lane:

* the restated A01 interface — `horizon`, `localSolution`, `horizonLowerBound`
  (these become one `LocalTheoryAPI` field once A01 is registered);
* the order-theoretic characterizations of `maximalLifespanR` —
  `lifespan_le_iff`, `lifespan_le_iff_no_extension`, `lifespan_ge_of_forall_shorter`,
  `regularThrough_iff`, `referenceLifespan`, `horizon_le_lifespan`;
* patching and restriction — `patch`, `restrict`;
* the canonical pressure gauge — `pressure_normalization`;
* existence and uniqueness of the maximal solution — `IsMaximalSolution`,
  `exists_maximal`, `maximal_unique`;
* the quantitative restart — `restart`, `restart_datum`, `restart_force`;
* Theorem 4.2's identification — `lifespan_le_of_unbounded`,
  `insertion_lifespan_eq`.

Nothing registered asserts `eq:mild`, the continuation criterion `eq:criterion`
(A04's), or any smallness / common-horizon / compact-support / `p ∈ L²` side
condition.  The Grönwall coefficient's finiteness (`eq:Rproduct`'s
`‖z‖_∞ ≤ C‖z‖_{H²}`, the edge `A03 → A02` recorded in
`research/A02/COMPARISON.md` §5) is a **step of the discharging proof**, not a
field of this contract, exactly as the spec header says.

The narrowing to `F_R` (`Data.MemForceR`) instead of `prop:local`'s "smooth into
every `H^m`" class is deliberate and recorded in the spec header and in the
`contracts.json` scope: it is the class Section 4 quantifies over
(`F_c ⊆ F_rd ⊆ F_R`, `04-whole-space.tex:183-192`).  The initial class
`initialClassR` is `X_R` verbatim.

## 3. How the structure conversion is done

`ClassicalSolutionR` lives only in `Contracts/V1/Data.lean`.  The proof modules
cannot import `Contracts`, so `Section4/A02/SolutionClass.lean` restates the
class token-for-token; the two are **distinct inductive types**, so a `rfl`
bridge for the structure is impossible (`CLAUDE.md` structure exception).  Every
*field type* is definitionally the contract's, so `Bindings/Uniqueness.lean`
carries `uniqueness_toA02` — the field-by-field literal reusing the exact ten
projections of `research/A04/axioms_f1n1.lean` and `research/C01/axioms_u1u3.lean`:

```
velocity, pressure, horizon_pos, velocity_smooth, pressure_smooth,
initial, divergence, momentum, sobolev, pressure_gradient
```

The two `example`s `(uniqueness_toA02 w).velocity = w.velocity := rfl` and
`.pressure := rfl` commit that the projections reduce, so the field values
typecheck without a `show`.  Each `UniquenessAPI` field is then
`fun ν a f hν ha hf T₁ T₂ u₁ u₂ => A02.<thm> ν a f hν ha hf T₁ T₂ (uniqueness_toA02 u₁) (uniqueness_toA02 u₂)`
and elaborates by definitional unfolding alone — **no `by`, no `show`, no
`exact`-with-`show`** was needed:

* the hypotheses `ha : a ∈ Data.initialClassR`, `hf : Data.MemForceR f` are
  accepted where `A02.velocity_unique` expects the A02-local predicates, because
  those predicates are token-identical restatements (defeq by delta);
* the conclusion `(uniqueness_toA02 uᵢ).velocity`/`.pressure` reduces to
  `uᵢ.velocity`/`.pressure`, and `A02.PressureGaugeEquivOn` is defeq to
  `Data.PressureGaugeEquivOn`, so the field type is met.

The three defeqs the binding leans on are pinned as anti-drift `rfl` bridges in
`§0 Correspondence` (`uniqueness_initialClassR_eq`, `uniqueness_memForceR_eq`,
`uniqueness_pressureGaugeEquivOn_eq`), the same discipline as
`Bindings/TameProduct.lean` and `Bindings/DatumLemmas.lean`.  CI now fails if
either side of any of the three drifts.

## 4. One mechanical point: `UniquenessAPI` is a `Prop`

Both fields of `UniquenessAPI` are propositions, so the structure lands in
`Prop` (unlike `TameProductAPI`/`BoundedRepresentativeAPI`/`GradientL6API`, which
carry a data constant such as `C : ℝ` and are therefore in `Type`).  The
`linter.defProp` linter then requires `theorem`, not `def`, for a value of that
type — and `verification/Tests` is `warningAsError = true`, so a `def` there is a
hard error (`Definition checkedUniqueness is a proposition; use theorem instead`).
The binding `uniqueness` and the test `checkedUniqueness` are therefore both
`theorem`.  `TestSupport.checkAxioms` and `collectAxioms` operate on a theorem
name unchanged, so the axiom audit is identical.  This is the first all-`Prop`
registered contract; no existing Tests file needed this because every prior API
carries a data field.

## 5. Base drift: the `--base-ref origin/erenup/integration` gate

This worktree was cut at `185089b` ("Record lane 053 PR"), which is the
`merge-base` with `origin/erenup/integration` (`5ab13b1`).  Origin has since
advanced with a **new V2 DatumLemmas contract** —
`verification/Contracts/V2/DatumLemmas.lean`, `Bindings.DatumLemmasV2`,
`Tests.DatumLemmasV2`, registry id `D01.datum_lemmas_v2` — which this worktree
does not contain.  `check_contracts.py`'s `check_compatibility` iterates over
**every** `Contracts/*.lean` file present on the base ref and asserts it exists
unchanged in the tree, so it fails at
`AssertionError: Removed stable specification: verification/Contracts/V2/DatumLemmas.lean`
— a pre-existing consequence of the worktree being behind origin, **not** of any
file this lane adds (my only registry addition is `A02.uniqueness`; I remove and
change nothing frozen).  Resolving it is the lead's merge-time rebase step
(`CLAUDE.md`: "rebase 后重跑 tasks.py render"), which is outside this lane's
"no git write commands" scope.  The substantive compatibility of *this lane's*
delta is shown by `--base-ref HEAD` (base = the fork point `185089b`), which
passes with `base_compatibility_checked: true`.

## 6. Gates

All run in the worktree, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`,
lake from `verification/`.

| command | result |
|---|---|
| `cd verification && lake build Contracts.V1.Uniqueness Bindings.Uniqueness Tests.Uniqueness` | **exit 0**, `Build completed successfully (9947 jobs)`; the only log line naming a file of this lane is `Tests/Uniqueness.lean:16:0: Contract BlowupDensity.Tests.checkedUniqueness: checked; standard logical axioms only` |
| `make check` | **exit 0** — plan check, `check_contracts` (11 contracts), `test_contract_policy` (13 tests), `check_work_queue` (30 items) |
| `make test` | **exit 0**; every `checked...` line prints "standard logical axioms only", including `checkedUniqueness` |
| `make test-mutations` | **exit 0** — `implementation_refactor: accepted`, `admitted_proof` / `extra_axiom` / `weakened_hypothesis` all `rejected as required` |
| `python3 experiments/check_contracts.py` (no base) | **exit 0**, `registered_contracts: 11`, `A02.uniqueness` closure 1183 modules (includes `Tests.Uniqueness` and `NSFormalization.Section4.A02.Uniqueness`) |
| `python3 experiments/check_contracts.py --base-ref HEAD` | **exit 0**, `base_compatibility_checked: true`, 11 contracts — this lane's delta adds only `A02.uniqueness` |
| `python3 experiments/check_contracts.py --base-ref origin/erenup/integration` | **fails** on the pre-existing `Contracts/V2/DatumLemmas.lean` present on origin but absent from this behind-origin worktree; see §5.  Not caused by this lane. |
| `#print axioms` (scratch, deleted) | `Bindings.uniqueness`, `Tests.checkedUniqueness`, `A02.velocity_unique`, `A02.pressure_gauge` each `[propext, Classical.choice, Quot.sound]` |

No `maxHeartbeats` bump anywhere: the contract, binding and test all elaborate at
the default budget.  The binding's `uniqueness_toA02` and its three bridges are
default-transparency definitional unfoldings.
