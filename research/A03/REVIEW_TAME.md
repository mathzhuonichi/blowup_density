# Reviewer verdict — lane 026, `A03.tame_products`

**ACCEPT-WITH-NOTES.** Every gate passes, every axiom set is exactly the three standard
ones, and the registered clauses are faithful to Lemma A.1 in objects, norms, orders,
constant dependence and literalness of the products. Four documentation-level findings,
and six of the eight `maxHeartbeats` bumps are dead weight. Nothing blocks the merge.

## 1. Gates (`erenup/026-A03-tame-contract` @ `4ba526e`)

| gate | result |
|---|---|
| `make check` | pass (plan, contracts, policy 13 tests, work queue 30 items) |
| `make test` | pass; **7/7** registered contracts print `checked; standard logical axioms only` (Thresholds, Packet, Correction, GradientL6, BoundedRepresentative, Scaling, TameProduct); warm 2.1 s |
| `make test-mutations` | pass — `implementation_refactor: accepted`; `admitted_proof`, `extra_axiom`, `weakened_hypothesis` all `rejected as required` |
| `check_contracts.py --base-ref erenup/integration` | pass, `base_compatibility_checked: true`, `registered_contracts: 7`. **No merge-base fallback needed**: the `R42.insertion_family` drift on integration does not trip the gate. |
| `build_changed_lean.py --dry-run` | exactly the expected **7** modules: `Contracts.V1.TameProduct`, `Bindings.TameProduct`, `Tests.TameProduct`, and the four `Section4.A03.{RealAngular,Scalar,Vector,Outer}TameProduct` |
| same without `--dry-run` | pass, 9884 jobs, 2.1 s warm |

## 2. Axioms

Scratch module with `#print axioms` on `BlowupDensity.Tests.checkedTameProduct`,
`BlowupDensity.Bindings.tameProduct`, **all 66 theorems** of the four new modules
(RealAngularProduct 12, ScalarTameProduct 15, VectorTameProduct 25, OuterTameProduct 14)
and the 15 bridge theorems — **83 declarations**. All 83 print exactly `[propext,
Classical.choice, Quot.sound]`; no `sorryAx`, no extra axiom. Scratch deleted.

## 3. `maxHeartbeats` — eight sites, two of them real

Measured by elaborating per-site copies (bump commented out, or lowered), imports warm.

| site | value | theorem | needed above the 200 000 default? | requirement |
|---|---|---|---|---|
| `RealAngularProduct.lean:109` | 1 000 000 | `realSymmetry_angularProduct` | **yes** — `timeout at isDefEq` at `:115:33`, the `realSymmetry_sobolevProduct` rewrite | >250k, ≤300k → **~3.3× headroom** |
| `RealAngularProduct.lean:211` | 1 000 000 | `norm_mulDatum_le` | no | **unnecessary** |
| `ScalarTameProduct.lean:224` | 2 000 000 | `tameProductScalar` | **yes** — `timeout at isDefEq` at `:251:10`, `ENNReal.ofReal_add (by positivity) (by positivity)` | >800k, ≤1 000k → **~2× headroom** |
| `VectorTameProduct.lean:253` | 1 000 000 | `tameProductVector` | no | **unnecessary** |
| `VectorTameProduct.lean:305` | 1 000 000 | `algebraProductVector` | no | **unnecessary** |
| `OuterTameProduct.lean:149` | 1 000 000 | `outerProductTame` | no | **unnecessary** |
| `OuterTameProduct.lean:203` | 1 000 000 | `outerProductDifference` | no | **unnecessary** |
| `OuterTameProduct.lean:298` | 1 000 000 | `advectionTame` | no | **unnecessary** |

**Assessment.** The two live bumps are legitimate elaboration cost, not proof fragility:
Lean's own message is `(deterministic) timeout at isDefEq`, the cost is unification
through `SobolevHilbert s` (an `abbrev` for `Lp ℂ 2 volume`) along `cyclesToAngular`,
and both proofs are short structured `rw`/`calc` chains with no `simp` search or
`nlinarith` at the failing position. The six dead bumps are over-provisioning — harmless
today, but they suppress the signal if one of those proofs later starts costing several
times more.

**warningAsError / CI.** `warningAsError = true` is set only on the `Tests` lean_lib;
all eight sites are in `NSFormalization`, and `set_option maxHeartbeats` emits no
diagnostic in any case, so nothing exceeds what `verification/Tests` tolerates —
`Bindings/TameProduct.lean` and `Tests/TameProduct.lean` set none. Precedent exists at
both values (`Bindings/Correction.lean:130` is already 2 000 000; `formalization/`
already has an 8 000 000 site), though the lane contributes 8 of the 13 sites now in
`formalization/`. **Runtime is not at risk**: full from-source elaboration with warm
imports is 5.4 + 9.8 + 3.5 + 4.2 ≈ **23 s** for all four modules.

## 4. Self-contained definitions ↔ source ↔ bridge

Fourteen re-defined notions plus `Data.sobolevENorm`; **fifteen bridges, every one `:=
rfl`**. Nothing re-defined is left unbridged.

| contract notion | source it must match | bridge (`rfl`) |
|---|---|---|
| `IsScalarSobolevDatum` | `i`-component of `Data.IsSobolevDatum` (`Data.lean:160`); `01-introduction.tex:91,94` | `tameProduct_isScalarSobolevDatum_eq` |
| `scalarSobolevENorm` | `Data.sobolevENorm` (`:189`) with `Fin 3` → point | `tameProduct_scalarSobolevENorm_eq` |
| `MemHmScalar`, `MemHmVector` | `02-preliminaries.tex:29-30`; `MemLp _ 2` excludes the junk-`0` of `Data.lean:148-155` | `tameProduct_memHmScalar_eq`, `_memHmVector_eq` |
| (`Data.sobolevENorm` itself) | `Section4.D01.sobolevENorm` (`SmoothDatum.lean:306`) | `tameProduct_sobolevENorm_eq` |
| `SmoothJets` | `A03.SmoothL2` (`A03/SmoothJets.lean:60`) = vendor `EulerLpTranslation.SmoothL2Field` | `tameProduct_smoothJets_eq` |
| `lift`, `partialDeriv`, `advectionOf` | pinned upstream `spatialDerivative`/`coordinateVector`; `01-introduction.tex:83`, appendix `:50` | `_lift_eq`, `_partialDeriv_eq`, `_advectionOf_eq` |
| `outerColumn`, `diffField` | appendix `:17`, `:51-52` | `_outerColumn_eq`, `_diffField_eq` |
| `columnsSobolevENorm` + its 3 uses | `01-introduction.tex:103`, "sum the squared component norms" — the nine-entry Frobenius quantity | `_columnsSobolevENorm_eq`, `_outerSobolevENorm_eq`, `_outerDiffSobolevENorm_eq`, `_gradientSobolevENorm_eq` |

Every reused-source citation resolves exactly: `FourierTameProduct.lean:150`,
`CompleteTameProduct.lean:101,113,128`,
`AngularTameProduct.lean:14,20,39,51,61,70,76,141,146,174`,
`RealSobolev.lean:25,35,72,123`, `SmoothDatum.lean:208,237,306,309,315`,
`AngularFourierDilation.lean:203`, `AngularRealSobolev.lean:54`,
`A05/SmoothJets.lean:87,94`.

## 5. Fidelity to Lemma A.1 — findings, ranked

1. **Wrong provenance for the difference bound, three times.**
   `Contracts/V1/TameProduct.lean:21`, `:341` and `OuterTameProduct.lean:13` say the
   bound is "quantified at `paper/originals/local/paper_3_whole_space.tex:192`". Line
   192 is the Plancherel/Young step of the a-priori `H^m` bound. The only mention of the
   difference estimate in the originals is `:156` (identical to appendix `:51-52`) and
   it is **qualitative**: "factorizing `u⊗u−v⊗v` gives the corresponding difference
   estimate". No quantified inequality of that shape exists anywhere under `paper/`. The
   registered inequality is the correct, standard consequence of the factorization plus
   `eq:algebra` and the Lean proof derives it exactly that way — only the citation and
   the word "quantified" are wrong.
2. **`UnprovedTameProductObligations.memHInfty_advectionTame` is weaker than what it
   records.** `∃ Cadv, 0 < Cadv ∧ …` sits *inside* `∀ u v`, so the constant may depend
   on the fields — where `Spec.lean:564` uses the structure field `C m` and
   `appendix-a-local-theory.tex:10` fixes the constant to the order and the domain. The
   structure's docstring claims the gap is recorded "in the manuscript's own form and
   without weakening". The structure is never instantiated, so no registered strength is
   affected; the *recorded debt* is.
3. **"Every `MemHInfty` clause is collected" is not accurate.** `TameProduct.lean:51-57`
   and the `contracts.json` scope both say so. `research/A03/Spec.lean` has four —
   `memHInfty_memHm:324`, `memHInfty_component:330`, `memHInfty_partialDeriv:339`,
   `advectionTame:564` — and only two are collected. Both omissions are one-step
   corollaries of `memHInfty_memHm` with registered fields, and `ATTEMPTS_TAME.md:59-63`
   says so correctly; the log is more honest than the contract and the registry.
4. **`ATTEMPTS_TAME.md:200-205` over-attributes the heartbeat bumps**, listing all eight
   theorems as needing one. Six do not (§3).

Everything else checks out. Same objects and norms as the paper (`Data.sobolevENorm`
datum form throughout; `isSobolevDatum_iff` is `Iff.rfl`, so the scalar carrier really
is one component of the vector one; the tensor norm is `01-introduction.tex:103`'s
Frobenius quantity). Constants are all `ℕ → ℝ` structure fields quantified outside every
field — order-only, never support- or frequency-dependent; splitting `Cdiff` from `Calg`
is no weaker. Products are literal and pointwise (`a x * b x`, `a x • w x`, `(u x j) • v
x`, `u x - v x`); `advectionOf` is the classical directional derivative and
`advectionOf_eq` proves it equals `∑_j u_j ∂_j v`. `eq:algebra`, `eq:tame` and the
difference bound are **registered at `k ≥ 3`** as the manuscript states and **proved at
`k ≥ 2`** — conservative and stated in the docstrings. `outerProductTame` keeps its low
factor at order **two**, which is what makes `eq:Rhigh` (`:132-137`) an `H²` criterion;
`eq:Rhigh`'s Cauchy–Schwarz against `‖∇u‖_{H^m}`, the integration by parts and the
Grönwall go to A04, and `∇·(u⊗u) = (u·∇)u` to A01 unit E1 — both correctly deferred, not
asserted.

## 6. Mathematics spot-check

**`realSymmetry_sobolevProduct` / `angularProduct_mem_realSubspace` — sound.** Density
induction in each argument through `denseRange_weightedFourierLp`, valid because
`realSymmetry` is a CLM and `sobolevProduct` a continuous bilinear map, so both sides
are continuous and `isClosed_eq` applies. On the Schwartz core
`sobolevProduct_weightedFourierLp` makes the product literal pointwise multiplication
and `weightedFourierLp_conjugate` converts the Fourier-side conjugate reflection into
physical pointwise conjugation (`conjugateSchwartz_apply : conjugateSchwartz φ x = conj
(φ x)`), under which multiplication is a ring homomorphism; transport to the angular
normalization is `cyclesToAngular_realSymmetry` and its `symm` companion. `realSubspace`
is weight-independent and the Bessel weight is real and even, so reality of the weighted
datum is reality of `ẑ`. Exactly the conjugation symmetry of the Fourier data of a
product of real fields; no new Fourier analysis smuggled in.

**`ae_eq_of_schwartz_pairing` — right hypotheses.** Mathlib's
`ae_eq_of_integral_contDiff_smul_eq` wants `LocallyIntegrable f`, `LocallyIntegrable
f'`, and `∀ g : E → ℝ`, `ContDiff ℝ ⊤ g`, `HasCompactSupport g → ∫ g • f = ∫ g • f'`.
The wrapper supplies both local-integrability hypotheses and instantiates its stronger
Schwartz hypothesis at `Complex.ofRealCLM ∘ g` via `HasCompactSupport.toSchwartzMap`,
`Complex.real_smul` turning `•` into `*`. Assuming equality on *all* complex Schwartz
maps is more than the lemma needs and exactly what `IsSobolevDatum` provides, so nothing
is over-claimed. Local integrability of the physical side comes from `MemLp _ 2` via
`locallyIntegrable_ofReal` — the same hypothesis that rules out `Data.lean:148-155`'s
junk-`0` — and of the other side from continuity of `angularBoundedRepresentative`.

## 7. Registry, work queue, log

`contracts.json` has 7 entries and the `A03.tame_products` scope matches the registered
fields and names the exclusions (subject to finding 3). `work_items.json` lists
`A03.tame_products` under A03; `TASKS.md` and `tasks/A03.md` agree. Cards **regenerate
byte-identically** (`tasks.py render` in a sandbox copy produced no diff).
`UnprovedTameProductObligations` is never instantiated, appears in no test and is absent
from `contracts.json` — the isolation it claims is real. `ATTEMPTS_TAME.md` is accurate
apart from finding 4.

## 8. The unregistered fields

Three obligations. Lane 025 (`erenup/025-D01-datum-to-jets`, `8f5c0c1`, in PR) proves
`memHInfty_iff_smoothSquareIntegrableJets`, i.e. `Data.MemHInfty z ↔ SmoothJets z`. Once
merged it **closes two of the three**: `memHInfty_memHm` from the registered
`smoothJets_memHmVector`, `memHInfty_advectionTame` from the registered
`smoothJets_advectionTame`. It does **not** close `componentSobolevENorm`, the exact
identity `‖z‖²_{H^s} = ∑_i ‖z_i‖²_{H^s}` — a pure `ℝ≥0∞` identity through two datum
infima with a `⊤` case split, independent of D01 unit L2, and used by no registered
clause.
