# Lane 019 review — contract `A05.gradient_l6`

Read-only review of `erenup/019-A05-l6-contract` @ `fe9bdb8`, rebased on
`erenup/integration` @ `4ba9f2b`.

## Verdict

**Accept.** The registered clause is Lemma B.1's third derived estimate with the
paper's two sides and a universal constant, proved on standard axioms, honestly
scoped. The one substantive finding (issue 1) is a *recorded* gap, not a defect.

## Gates (WT root; `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`)

| gate | result |
|---|---|
| `make check` | pass, 8.3 s (`30 work items: … consistent`) |
| `make test` | pass, 2.1 s; **four** contracts each `checked; standard logical axioms only`: `checkedThresholds`, `checkedPacket`, `checkedGradientL6`, `checkedCorrection` |
| `make test-mutations` | pass, 8.6 s; `implementation_refactor: accepted`; `admitted_proof` / `extra_axiom` / `weakened_hypothesis` all `rejected as required` |
| `check_contracts.py --base-ref erenup/integration` | pass; `registered_contracts: 4`, `base_compatibility_checked: true`; `A05.gradient_l6` closure 60 modules |
| `build_changed_lean.py --base-ref … --dry-run` | exactly six: `Bindings.GradientL6`, `Contracts.V1.GradientL6`, `NSFormalization.Section4.A05.{GradientL6,HessianLaplacian,SmoothJets}`, `Tests.GradientL6` |
| `build_changed_lean.py --base-ref …` | `Build completed successfully (8824 jobs)`, 2.1 s |

Caveat: every Lean gate **replayed** from the warm cache. Lake traces are
content hashes, so replay does certify the committed sources, but nothing was
re-elaborated in this pass.

## Axioms

Scratch `/tmp/A05AxiomScratch.lean` (`import Tests.GradientL6` + the three new
modules), `lake env lean` from `WT/verification`, `#print axioms` on 32
declarations — `checkedGradientL6`, `Bindings.gradientL6`, the four `rfl`
bridges, and **every** theorem and def of the three modules. All 32 printed
exactly `depends on axioms: [propext, Classical.choice, Quot.sound]`. Deleted.

## Hygiene

Grepping the contract, binding, test and three modules for
`sorry|admit|axiom|native_decide|nolint|set_option|trust|stub|TODO|FIXME|XXX|
HACK|placeholder|assume|unsafe|partial|@[` hits only `Tests/GradientL6.lean`'s
standard `import TestSupport.Axioms` / `run_cmd TestSupport.checkAxioms` and one
prose "assumed". Grepping the same six for
`fourier|𝓕|angular|plancherel|frequency|normaliz`: **comments only**.

## Re-definition ↔ source ↔ bridge

| contract notion | source | bridge |
|---|---|---|
| `lift` | device of `Data.IsSolenoidal` (`Data.lean:504`) | none needed — spec-side only, absorbed into the three `rfl`s below |
| `partialDeriv j v` | `Data.spatialDerivative` + `coordinateVector` (`ProblemStatement.lean:39`), reused not copied | `partialDeriv_eq = dirDeriv j v` |
| `gradientTensor v` | `Data.spatialGradient` (`Data.lean:453`), reused not copied | `gradientTensor_eq = gradTensor v` |
| `laplacian v` | upstream `spatialLaplacian` (`ProblemStatement.lean:76`), reused not copied | `laplacian_eq = lap v` (load-bearing: `lap` is defined independently as `∑ᵢ∂ᵢ∂ᵢ`) |
| `SmoothSquareIntegrableJets` | vendor `SmoothL2Field` (`LpSmoothField.lean:31-34`), **genuinely re-written** | `smoothSquareIntegrableJets_eq = SmoothL2 v` — to the A05 module's copy, **not** to the vendor structure |

Every re-defined notion with an implementation counterpart is bridged; each
bridge is `rfl` and axiom-clean. Cited line numbers all check out.

## Fidelity to `appendix-b-embeddings.tex:32`

* **Left side.** Confirmed. `eLpNorm (gradientTensor v) 6 volume`; the pointwise norm is
  the `PiLp 2` assembly of three `Space`-valued columns, `(∑_{i,j}|∂_jv_i|²)^{1/2}`
  — the Frobenius quantity of `01-introduction.tex:103`, not an operator norm.
* **Right side.** Confirmed. `eLpNorm (laplacian v) 2 volume`, the pinned componentwise
  `∑ᵢ∂ᵢ∂ᵢu`, i.e. the `Δu` of `eq:RH1`.
* **Constant.** Confirmed. `Csix` is a *structure field*, quantified outside every field
  as `:109-110` requires; Mathlib's `eLpNormLESNormFDerivOfEqInnerConst`
  (`SobolevInequality.lean:453`) depends only on `E, μ, p`, so it is genuinely
  universal. `9 = 3·3` from the two crude `l²≤l¹` steps, `+1` for positivity.
* **Hessian–Laplacian.** Confirmed: an *equality*, `∑_{i,j}∫‖∂ᵢ∂ⱼv‖² = ∫‖Δv‖²`
  (= `‖D²v‖₂² = ‖Δv‖₂²`), proved rather than assumed.
* **Hypothesis class.** GAP: the smooth `H^∞` fields of `:34-37` satisfy the jet
  class mathematically, but **not yet formally in tree** — issue 1.
* Norms are `ℝ≥0∞`-valued with no `.toReal`, and the class forces a finite RHS,
  so the bound is never vacuous.

Worker claims:

1. *Fourier-free* — true where stated: no statement or proof step in the three
   modules, the binding or the contract mentions a Fourier transform, and the
   vendor input `smooth_eLpNorm_six_le` (cutoffs + Mathlib GNS + Fatou) has a
   7-module vendor import closure with no Fourier module. "Nowhere in the
   closure" is **not** literally true of the registered *import* closure: 60
   modules including `Source.Fourier*`, `Paper3.Angular*`,
   `R3.ComparisonFourierSetup`, `R3.CompactSchwartz` — all pulled by
   `Contracts.V1.Data`, the contract's only import, not by A05.
2. *Constant* — `9 * eLpNormLESNormFDerivOfEqInnerConst volume 2 + 1` confirmed
   verbatim at `GradientL6.lean:52-53`.
3. *Order-3 jets* — confirmed (the first integration by parts pairs
   `⟪∂ᵢ∂ᵢ∂ⱼv, ∂ⱼv⟫`). **It costs nothing for any Section 4 use**: the contract's
   hypothesis quantifies `∀ n`, so the extra order is invisible at the
   interface. It would matter only if the contract were later weakened to `H³`
   (and for `H²` the cutoff+Fatou route of `ATTEMPTS.md` §1.1 would be needed).

## The datum-vs-jet gap — what remains for R43/R44

`Data.MemHInfty a` (`Data.lean:495`) is `ContDiff ℝ ∞ a ∧ ∀ m : ℕ, ∃ A :
RealVectorSobolev m, IsSobolevDatum m a A` — the **datum** form, a Fourier-side
realization statement. The contract's hypothesis is the **jet** form,
`∀ n, MemLp (iteratedFDeriv ℝ n v) 2 volume`. Lane 020
(`erenup/020-D01-hm-datum`, `9bf6f58`, scoped "jets => datum only") proves
**jets ⇒ datum** — the direction a consumer does *not* need. Still missing:

1. **datum ⇒ jets**, the converse: from `MemHInfty v` obtain
   `∀ n, MemLp (iteratedFDeriv ℝ n v) 2 volume`. Fourier-side work
   (`IsSobolevDatum` ⇒ weak `L²` derivatives, weak = classical by smoothness,
   then a multilinear-norm comparison) — units U1–U3, which `ATTEMPTS.md` §1.1
   explicitly declined.
2. **A time-slice step.** R43/R44 apply the clause to `u(t,·)`; `ClassicalSolutionR`
   supplies `velocity_smooth : ContDiffOn ℝ ∞ velocity (Ico 0 T ×ˢ univ)` plus a
   *datum*-form `sobolev` field, so extracting `ContDiff ℝ ∞ (fun x => velocity
   (t,x))` for interior `t` is a small extra obligation on top of (1).

So the blueprint edge `D01 --> A05` does not yet discharge A05's consumers.

## Issues, ranked

1. **[medium; recorded, not a defect of this lane]** Unusable by R43/R44 until
   datum ⇒ jets exists. Disclosed in the `contracts.json` scope, the contract
   docstring `:36-42`, and `ATTEMPTS.md` §3.
2. **[low]** `SmoothSquareIntegrableJets` / `SmoothL2` are hand-copies of the
   vendor `SmoothL2Field` at two removes with no machine-checked bridge
   (impossible by `rfl`: `Prop` vs `structure`). Vendor drift is caught by
   nothing. Harmless today — nothing in the closure uses the vendor structure —
   but "field-for-field" rests on eyeballing.
3. **[low]** "No Fourier transform anywhere in the closure" overstates; the
   per-file claims are accurate, the import-closure claim is not.
4. **[cosmetic]** `ATTEMPTS.md` §6 predates the rebase: "three contracts" (now
   four) and `check_contracts.py --base-ref erenup/integration` "fails" (it now
   passes). Contract docstring `:16` says Prop 4.4 reuses the clause "verbatim"
   at `:171`; `:171` reuses it by reference to the `eq:RH1` absorption.
   `SmoothJets.lean:57` cites `LpSmoothField.lean:45-50` for
   `SmoothL2Field.derivative`, which is at `:49-54`.

## Not verified

* No cold rebuild — all Lean gates replayed from cache.
* No proof-term Fourier audit: Lean `v4.34.0-rc2` does not expose imported
  theorem bodies via `ConstantInfo.value?` (2160 of 4999 reachable constants
  returned none), so my traversal covered only types and defs. Fourier-freeness
  is verified at statement level plus by the Fourier-free 7-module vendor
  closure of `SmoothSobolevL6`.
* Vendor `smooth_eLpNorm_six_le` and Mathlib's GNS were read, not re-proved.

## Metadata

`contracts.json` scope reads "Lemma B.1's gradient-L⁶ clause only; not the
Ḣ^{1/2}/Ḣ^{3/2} embeddings…" as required. `work_items.json` A05 lists
`A05.gradient_l6`. Cards regenerate byte-identically: `git archive HEAD` → `/tmp/a05cards`,
`python3 experiments/tasks.py render`, `diff -ru` → no diff.
