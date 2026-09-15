# Review — lane 009, D01 reconciliation (`verification/Contracts/V1/Data.lean`)

Reviewer verdicts:

* **Definitions (`Data.lean`): ACCEPT-WITH-NOTES.** 56 `def`/`abbrev`/`structure`, no theorem,
  no `sorry`/`axiom`. Every declaration I checked against its cited paper line is faithful; the
  two draft blockers (REVIEW_A issue 1, REVIEW_B issue 1) and REVIEW_B issues 2–5 are all
  discharged. Four residual defects below, one of which (#1) is a re-introduction of the very
  lower-integral gap the reconciliation set out to close.
* **Policy change: ACCEPT the six-module allowlist; NARROW the `NavierStokes.` prefix.**
  The local allowlist is exactly six strings, matched by set membership, and enforcement is real
  end-to-end. The new vendor *prefix* is the loose part: it admits all 643 `NavierStokes.*`
  modules including the comparator machinery, where `Data.lean` needs exactly one.

---

## Part A — the policy change

**(1) Is the allowlist exactly six and nothing broader?** Yes.
`CONTRACT_CANONICAL_MODULES` (`experiments/check_contracts.py:26`) is a `frozenset` of six exact
module names tested with `in`, not by prefix. `contract_import_allowed` = prefix test **or** set
membership; the prefix tuple is the broad half.

**(2) Does the regression test enforce the boundary?** The predicate is correct, but
`ContractImportBoundary` (`experiments/test_contract_policy.py:23`) unit-tests
`contract_import_allowed` only — it never calls `check()`, so a refactor that stopped consulting
the predicate would not be caught. I therefore reproduced the boundary end-to-end in a throwaway
tree under `/tmp` (copy of `experiments/`, a minimal `verification/` + registry, one probe
contract):

| probe import in `verification/Contracts/V1/Probe.lean` | result |
|---|---|
| `NSFormalization.Paper3.RealAdmissibleForce` | **rejected**, `Implementation-dependent specification: …: ['NSFormalization.Paper3.RealAdmissibleForce']` |
| `NSFormalization.Paper3.GridGeometry` | accepted |
| `public import NSFormalization.Paper1.InsertionEnergy` | **rejected** (the `public import` form is covered) |
| two modules on one `import` line, second banned | **rejected** (multi-module lines are covered) |
| `NavierStokes.ComparatorTheorem` | **accepted** — see (5) |

**(3) What `Data.lean` actually uses from each of the six.** All six supply definition-level
conventions; none supplies a proof. Total added closure: 51 modules / 7161 LOC (35 local /
3795 LOC + 16 vendor); no `sorry`/`axiom`/`admit`/`native_decide` token anywhere in it (checked).

| module | declarations named in `Data.lean` | kind | inlinable? |
|---|---|---|---|
| `Source.FourierConvention` | `angularFourier` (`:309`) | `def`, 2 lines — the `(2π)^{-3/2}` convention | in isolation yes; but forks the convention away from `angularFourier_eq_integral`, and it is already in AngularFourierDilation's closure |
| `Paper3.AngularFourierDilation` | `angularRealization` (`:138`), `angularFourierDistribution` (`:266`) | `def` (CLM), convention — **construction is proof-carrying** | **No** — see (4) |
| `Source.RealSobolev` | `FourierData` (code); `RealSobolevHilbert`, `realSubspace` appear in prose only | `abbrev = Lp ℂ 2 volume`, 1 line | 1 line, but `realSubspace` itself is proof-carrying (`realSymmetry` CLM), and the module is already in the closure |
| `Paper3.RealVectorPositiveDensity` | `RealVectorSobolev` (15 uses) | `abbrev = PiLp 2 (Fin 3 → realSubspace s)` | **No** in substance — inherits `realSubspace`/`realSymmetry` |
| `Paper3.PositiveTemporalDensity` | `positiveTimeMeasure` (via `forceTimeMeasure`, `:103`) | `abbrev = volume.restrict (Ioi 0)`, 1 line | 1 line, no proofs; already in the closure, so removing it saves nothing |
| `Paper3.GridGeometry` | `CartesianGrid`, `CartesianGrid.cell` | `structure` + `def`, ~15 lines, no proof terms | **Yes** — 1 module, 111 lines, the only separable one; but `finite_grids_common_ball`/`finite_grids_common_interior`, which thm:Rgrid's proof needs, are stated against this structure |

**(4) Could they be inlined? `angularRealization` in particular.** No.
`angularRealization s = (angularCoordinateRealization s).comp angularFrequencyDilation.symm…`
(`AngularFourierDilation.lean:176`) is three lines, but `angularFrequencyDilation` (`:80`) is built
by `LinearEquiv.extendOfIsometry` whose final argument is the **proof**
`schwartzAngularDilation_norm_toLp`, and `angularCoordinateRealization`
(`AngularSobolevCoordinates.lean:131`) composes `sobolevRealization` with
`(angularWeightEquiv s).symm`, likewise proof-carrying. Reproducing it needs the 32-module /
3502-LOC / 241-theorem local closure of `AngularFourierDilation`. Inlining would put proofs in the
contract, which the design forbids. Only `GridGeometry` (and, in isolation, three one-liners
already in the closure) could be inlined.

**(5) Does `NavierStokes.` also admit `NavierStokesR3.` and `NavierStokes.Comparator`?**

* `NavierStokesR3.*` — **no**. The prefix carries a trailing dot, so
  `'NavierStokesR3.Foo'.startswith('NavierStokes.')` is `False`; and no such module exists
  (`NavierStokesR3` is only a Lean *namespace* inside `NavierStokes.R3.ProblemStatement`).
  `Data.lean:64` claiming the policy allows `NavierStokesR3.*` packages "freely" is wrong prose.
* `NavierStokes.Comparator*` — **yes**, and I confirmed a contract importing
  `NavierStokes.ComparatorTheorem` passes `check_contracts.py`. The registered-contract closure
  check bans `ComparatorChallenges.` but not this. Probably unintended: `Data.lean` needs exactly
  one vendor module, `NavierStokes.R3.ProblemStatement`, out of the 643 the prefix admits.
  (`NavierStokes.ComparatorBridge`/`ComparatorDefinitions` are already in its closure transitively.)

**Two further scope facts, not blockers.** (a) The allowlist governs **direct imports only**:
`Data.lean`'s closure includes `NSFormalization.Source.Insertion`, a module the new test names as
an example of what must be rejected. (b) Pre-existing and worth fixing while here: `Mathlib`,
`Lean`, `Init` have no trailing dot, so `MathlibExtras.X`, `LeanFoo.Bar`, `Initialize.X` all pass.

**Recommendation.** Merge as-is, then in a follow-up: replace the `NavierStokes.` prefix with the
explicit vendor entries actually needed, in the same frozenset style; state in the comment that
the list governs direct imports, not the closure; give `Mathlib`/`Lean`/`Init` trailing dots; and
add one end-to-end case to `test_contract_policy.py` that drives `check()` over a temp tree.

---

## Part B — ranked issues in the definitions

| # | Sev | Declaration (`Data.lean`) | Paper | What differs | One-line fix |
|---|---|---|---|---|---|
| 1 | moderate | `CompletedDense` `:600` | `04:219` prop:Renergy | the approximating datum path `D` carries no measurability, so `bochnerDatumENorm q s (D - b)` is `eLpNorm` of a possibly non-measurable function, i.e. a **lower** Lebesgue integral that can under-report the distance — exactly REVIEW_B issue 3, which `forceSobolevENorm` was rewritten to avoid | add `AEStronglyMeasurable D forceTimeMeasure` to the existential |
| 2 | moderate | coverage gap | `04:221,227` prop:Renergy; `04:85` prop:Rcritical1 | "dense in `L²(0,∞;Ḣ^{-1})`" and `‖g_ε−g‖_{L²_tḢ^{-1}}→0` are **not statable**: there is no homogeneous datum *path*, no vector homogeneous datum, and `CompletedDense` is hard-wired to `IsSobolevPath`. `RECONCILIATION` §4 item 5 justifies dropping the *physical-field* `L^q_tḢ^s` but not this | add `IsHomogeneousPath` + a homogeneous `CompletedDense`, or record the omission in §4 as an explicit R46/R43 blocker |
| 3 | minor | `energyEssSup` `:330`, `energyGradient` `:344`, `energyENorm` `:355` | `01-intro:143` eq:Enorm | `eLpNorm`/`∫⁻` are applied to slices of an arbitrary `SpaceTimeField` with no measurability hypothesis, so eq:REclose's *bound* can be met by a non-measurable field with a small lower integral. Contradicts the module docstring `:41-46` ("no lower Lebesgue integral of a function whose measurability is unavailable"). Also `energyENorm T z = 0` for `T ≤ 0` | restrict the docstring claim to the time norms, or add a measurability clause |
| 4 | minor | `IsSobolevDatum` `:136` ⇒ `sobolevENorm` `:155` | `01-intro:94` | the RHS `∫ x, ψ x * z x i` is a totalized Bochner integral: for a slice non-integrable against *every* Schwartz `ψ` the RHS is `0` for all `ψ`, so `A = 0` is a datum and `sobolevENorm s z = 0` — a junk `0`, not `⊤`. Documented in RECONCILIATION §4 residual risks and unreachable from `F_R`/`H^∞` (the `m = 0` clause excludes it), but it qualifies the docstring's "`⊤` off its space" | soften the docstring, or add a local-integrability side condition |
| 5 | minor | `IsSobolevPath` `:143`, `IsLebesgueSlicePath` `:208` | `01-intro:124` fn., `02-prelim:62` | a datum is demanded at **every** `t ≥ 0`; the paper identifies time slices a.e. Strictly stronger, so the norm fails safe to `⊤`; harmless on the smooth `F_R` but should be recorded | note the deviation, or quantify a.e. |
| 6 | minor | `IsHomogeneousDatum` `:263` docstring | `02-prelim:67`, `app-B:59-64` | says the `Integrable` clause "holds exactly on `-3/2 < s < 3/2`". It constrains only `s < 3/2`; for `s ≤ 0` the integrand is integrable by Cauchy–Schwarz at every `s`. The lower bound comes from injectivity/no-polynomial-ambiguity | reword |
| 7 | cosmetic | `breakdownSetRZero` `:564` | `04:11` thm:Rmain(ii) | cites `02-prelim:41` and writes `B^{R,0}_{ν,T}`; line 41 defines the **torus** `B^0_{ν,T}`. The whole-space zero case is `B^R_{ν,0,T}` | fix the citation |
| 8 | cosmetic | canonical-dependency table `:57`, `:64` | — | lists `RealSobolevHilbert` as used (prose only; code names only `FourierData`); claims `NavierStokesR3.*` is an allowed package prefix (it is not, and no such module exists) | correct both rows |
| 9 | cosmetic | `RECONCILIATION.md` §2 | — | "51 local modules / ~7.1 kLOC": the closure is 51 modules / 7161 LOC of which **35** (3795 LOC) are local, 16 vendor | correct the count |

### Confirmations requested

* **`MemForceR` (`:424`) requires smoothness of the field itself.** Yes:
  `ContDiffOn ℝ ∞ f futureDomain` with `futureDomain = Ici 0 ×ˢ univ`. REVIEW_A's blocker is closed.
  Not a strengthening of `02-prelim:17`: `C^∞([0,∞);H^∞)` already implies joint smoothness on
  `[0,∞)×R³` by Sobolev embedding; in Lean it is what pins the representative.
* **`CompletedDense` (`:600`) quantifies over the completion.** Yes — `∀ b, MemBochnerDatum q s b`
  (strong measurability + finite Bochner norm), not over all distributions. REVIEW_B issue 1 closed
  (but see issue 1 above for the other side of the quantifier).
* **`L^q_tH^s_x` (`forceSobolevENorm` `:191`).** Measurable-path form: `⨅` over
  `IsSobolevPath ∧ AEStronglyMeasurable` of `eLpNorm … positiveTimeMeasure`; empty `⨅` in `ℝ≥0∞`
  is `⊤`. No lower-integral gap and no junk `0` **at this level**; both qualifications live one
  layer down in `IsSobolevDatum` (issue 4). Since all admissible `G` agree a.e. on `Ioi 0`, the
  infimum is the honest norm.
* **`E_T` (`:355`) is `ℝ≥0∞` and not vacuous.** Yes — no `.toReal`; REVIEW_B issue 2 closed.
  Interval `Ioo 0 T`, no endpoint at `T` (`01-intro:150`); gradient is Frobenius via
  `WithLp 2 (Fin 3 → Space)`, not an operator norm. Caveats in issue 3.
* **One homogeneous realization for `-3/2 < s < 3/2`.** `IsHomogeneousDatum s G u` says
  `⟨û, φ⟩ = ∫ φ · ‖ξ‖^{-s} G`. At `s = -1` this is `ĥ = |ξ|G`, i.e. `|ξ|^{-1}ĥ = G ∈ L²` —
  literally `eq:homogeneous-realization` (`02-prelim:59-62`). At `s = a ∈ (0,3/2)` it is app-B's
  `v̂ = |ξ|^{-a}G` (`app-B:56-70`), and the `Integrable` clause is app-B's own displayed estimate
  (`2a < 3`). At `s ≥ 3/2` the clause fails for nonzero `G`, so the space collapses to `{0}`
  rather than becoming vacuously true — the right behaviour given `app-B:101`.
  `Ḣ^{3/2}`/`Ḣ^{1/2}` exist as *quantities*: `dotHThreeHalvesENorm` `:317`, `dotHHalfENorm` `:322`,
  both `homogeneousFourierENorm` (`01-intro:105`, `04:91`, `app-B:31,107`, `app-A:24`).
* **Classical solution (`:504`).** Pressure constrained only by `∇p ∈ L²` (`02-prelim:101`), no
  scalar `p ∈ L²`; gauge freedom carried by the set-parametric `PressureGaugeEquivOn` `:469`
  (`02-prelim:31`, and `04:320`'s spatially constant gauge as the constant-`c` case);
  smoothness on `Ico 0 T ×ˢ univ` and `momentum` on `Ioo 0 T`, i.e. one-sided at `t = 0`;
  `sobolev` is `ContinuousOn G (Ico 0 T)`, matching `C([0,S];H^m)` on compact subintervals
  (`02-prelim:29`).
* **`maximalLifespanR` `:537`, `breakdownSetIn` `:552`, `RelativelyDense` `:580`.** All match
  thm:Rmain (`04:8-13`): `s_q = 2/q - 3/2` (`criticalOrder` `:225`), relative `L^q(0,∞;H^s)`
  ε-density on the ambient class, one lifespan function shared by `F_R`/`F_c`/`F_rd`
  (STATEMENTS §9 item 12), `B^R = {f ∈ Y : T_max ≤ ofReal T}`. Not vacuously satisfiable: if the
  norm is `⊤` the predicate is *false*, so it fails closed pending unit L12.
* **`AgreesOnFuture` `:113`.** `∀ t ≥ 0, ∀ x, f = g` matches `02-prelim:22-24` (forces live on
  `[0,∞)`, may be nonzero at `0`), while norms integrate over `(0,∞)`. On `F_R` the two coincide by
  continuity, so it is the correct separating equivalence and does not strengthen `MemForceR`.
* **Grid `:617`.** `CartesianGrid` has `offset, width : Fin 3 → ℝ` with `width_pos`, and
  `cell k = {x | ∀ j, offset j + width j * k j ≤ x j < offset j + width j * (k j + 1)}` —
  per-axis widths, arbitrary offset, half-open cells, cells indexed by `Fin 3 → ℤ`. Matches
  `04:288-294`; `finite_grids_common_interior/_ball` supply what thm:Rgrid's proof needs.
  `cellAverage :625` is `|C|^{-1}∫_C z`; `gridObservation :634` has the full `Fin 3 → ℤ` codomain
  with coordinatewise equality (`04:293`).

### Coverage vs `STATEMENTS.md` §8

Every `⟪D01:…⟫`/`⟪G01:…⟫` entry is either defined or listed in `RECONCILIATION.md` §4 with a
reason I accept: `Λ`/`J` as operators (§4.1, used only inside quantities), Leray + `eq:projected`
(§4.2, no Section 4 *statement* needs it), `IsMaximalSolution`/mild/continuation (§4.3, needs
A01/A02/A04), `V`/`V'` (§4.4, the paper itself calls these documentation), Fréchet topology on
`H^∞` (§4.6), `faceSet` (§4.7, G01's), `normLp p` (§4.8), packet data and exponent arithmetic
(§4.9). The §8.2/§8.4 items reclassified as lemmas are genuinely properties, not definitions.
**The one gap I do not consider justified is issue 2** — `⟪D01:normLqDotHminus1 2⟫` at the level
prop:Renergy needs. Everything else checks out.

### Bookkeeping

`collaboration/tasks/D01.md` carries a complete Paper-to-Lean table (every `Data.lean` declaration
appears) and an Attempts section recording all nine rejected alternatives plus the policy change.
Leaving `Data.lean` unregistered **is** acceptable for a definitions-only contract: there is no
theorem to bind, `check_contracts.py` never requires a `Contracts/*` file to be registered, and
`check_compatibility` freezes it byte-for-byte from the next merge onward.

One consequence should be fixed, though (**moderate, infra**): `verification/lakefile.toml` sets
`defaultTargets = ["Tests"]`, so neither `make test` (3037 jobs, `Tests.Thresholds` only) nor a
bare `lake build` ever elaborates `Contracts.V1.Data`. Only `build_changed_lean --base-ref` does,
and only while the file is *changed*. After merge a Mathlib or vendor bump could break it with
every gate green. Fix: `defaultTargets = ["Tests", "Contracts"]`.

---

## Gate results

Run from the worktree root after `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`.

| command | result |
|---|---|
| `make check` | **PASS**, 8.3 s — plan check, `check_contracts` (1 registered contract), 9/9 policy tests, work queue consistent |
| `make test` | **PASS**, 1.1 s — `Contract BlowupDensity.Tests.checkedThresholds: checked; standard logical axioms only` (does not cover `Contracts.V1.Data`) |
| `python3 experiments/check_contracts.py --base-ref erenup/integration` | **PASS**, `base_compatibility_checked: true` |
| `python3 experiments/build_changed_lean.py --base-ref erenup/integration --dry-run` | **PASS** — `Changed Lean modules: Contracts.V1.Data` |
| `python3 experiments/build_changed_lean.py --base-ref erenup/integration` | **PASS**, 2.0 s wall (warm cache) — `Build completed successfully (8816 jobs)`; linter warnings only, all in pre-existing `NSFormalization` files |
| `cd verification && lake env lean Contracts/V1/Data.lean` | **exit 0, empty output**, 4.8 s |
| `grep -nE "sorry\|axiom\|admit\|native_decide\|unsafe\|^\s*(theorem\|lemma\|example\|instance)\b" verification/Contracts/V1/Data.lean` | one hit, line 21, inside the module docstring ("no `sorry`, no `axiom`"). No theorem-like declaration. 56 `def`/`abbrev`/`structure` |
| `python3 experiments/test_contract_policy.py -v` | **PASS**, 9 tests |
| `/tmp` throwaway negative/positive policy probes | as tabulated in Part A(2) |

**Base-ref caveat.** `erenup/integration` has advanced 12 commits past this lane's merge-base
(`89ee45c`), so `git diff erenup/integration..HEAD` also reports unrelated *deletions* (lane
004/008/010 files). The gates still pass because the only `verification/Contracts` file at base is
`Thresholds.lean`, byte-identical here. The lane should be merged forward before integration.
