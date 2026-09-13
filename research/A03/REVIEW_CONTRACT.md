# A03 contract review — `A03.bounded_representative` (V1)

Lane `023-A03-l2linf-contract`, HEAD `1f85c04`, rebased on `erenup/integration` (`4ba9f2b`). Read-only pass; nothing
committed was modified.

## Verdict: **ACCEPT-WITH-NOTES**

Every gate green, all eleven declarations on exactly the three standard axioms, hygiene grep empty, both re-defined
notions guarded by `rfl`, and the two clauses faithful to `appendix-a-local-theory.tex:12` with a genuinely
universal constant. Seven findings, two Medium; finding 1 is a latent *hard* build break at merge next to lane 019
and should be fixed first. Neither Medium affects the mathematics.

## 1. Gates (WT root; `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`)

| command | result |
|---|---|
| `make check` | exit 0, 8.5 s. `Explicit axiom/admission tokens, all copied sources: 11`; `registered_contracts: 4`; `test_contract_policy` `Ran 13 tests … OK`; `check_work_queue` `30 work items: … consistent.` Pre-existing on base and untouched here: `source_hashes_match: false`, the `Paper1/BoundaryCorollary.lean:90` `sorry` token. |
| `make test` | exit 0. Exactly four contract lines, each `checked; standard logical axioms only`: `checkedThresholds`, `checkedPacket`, `checkedCorrection`, `checkedBoundedRepresentative`. No `error`/`sorry`/`declaration uses`. |
| `make test-mutations` | exit 0, 8.5 s. `implementation_refactor: accepted`; `admitted_proof`/`extra_axiom`/`weakened_hypothesis` all `rejected as required`; `Mutation suite passed.` |
| `check_contracts.py --base-ref erenup/integration` | exit 0, `base_compatibility_checked: true`. Closures 5 / 534 / 597 / **59**; A03 is the leanest registered contract. |
| `build_changed_lean.py … --dry-run` | `Bindings.BoundedRepresentative, Contracts.V1.BoundedRepresentative, NSFormalization.Section4.A03.{BoundedRepresentative,SmoothJets}, Tests.BoundedRepresentative` — the expected five. |
| same, no `--dry-run` | exit 0, `Build completed successfully (8823 jobs)`, **2.0 s wall**, every job `Replayed`. **Warm cache; not a cold-build figure, and I did not produce one.** |
| `tasks.py render` in a `/tmp` `git archive` copy | exit 0; `diff -r` against `collaboration/` identical. Cards regenerate byte-for-byte. `contracts.json` and `work_items.json` A03 entries are the only registry changes. |

## 2. Axioms

Scratch `/tmp/a03_axioms_scratch.lean` importing `Tests.BoundedRepresentative`, run with `lake env lean` from
`WT/verification`, then deleted. **Eleven declarations, every one** `depends on axioms: [propext, Classical.choice,
Quot.sound]`, nothing else: `Tests.checkedBoundedRepresentative`; `Bindings.boundedRepresentative`,
`smoothSquareIntegrableJets_eq`, `jetSobolevENorm_eq`; `SmoothL2.contDiff`, `SmoothL2.jetMemLp`;
`boundedRepresentativeConst_pos`, `norm_le_tensorSobolevNorm`, `ofReal_tensorSobolevNorm`, `enorm_le_jetENorm`,
`eLpNormTop_le_jetENorm` — that is every theorem of both modules.

## 3. Hygiene

`grep -nE "sorry|axiom|admit|native_decide|unsafe|Admitted"` over contract, binding, test and the two modules:
**zero hits**, comments included. Case-insensitive (plus `todo|fixme|hack`) adds only `import TestSupport.Axioms`
and `run_cmd TestSupport.checkAxioms` in `Tests/`.

## 4. Re-definition ↔ source ↔ bridge

Contract imports `Contracts.V1.Data` only; `SpatialField` (`Data.lean:99`) and `Space` reused unchanged. Exactly two
notions re-defined, **both** guarded.

| contract notion | source, opened | bridge in `Bindings/BoundedRepresentative.lean` |
|---|---|---|
| `BoundedRep.SmoothSquareIntegrableJets` :115 | vendor `EulerLpTranslation.SmoothL2Field` `LpSmoothField.lean:31-34` (`field`/`smooth`/`integrable`), via `Section4.A03.SmoothL2` :51 | `smoothSquareIntegrableJets_eq` — **`rfl`** |
| `BoundedRep.jetSobolevENorm` :126 | `Section4.A03.jetENorm` :93, the `ℝ≥0∞` counterpart of vendor `tensorSobolevNorm` `EulerProof.lean:8091-8092` | `jetSobolevENorm_eq` — **`rfl`** |

Both bodies are verbatim lane 019's `Contracts.V1.SmoothSquareIntegrableJets`
(`019-A05-l6-contract/…/GradientL6.lean:106`) and `Section4.A05.SmoothL2`, as claimed; the vendor comparison is
field-for-field by eye (`Prop` vs `structure`, no `rfl` possible), so vendor drift is caught by nothing — correct today, and nothing in the closure uses the vendor structure.

**Namespace-clash test (run, not reasoned).** I compiled 019's `Contracts/V1/GradientL6.lean` into a temporary olean
root against this worktree's built closure and imported both contracts in one file.
`…Contracts.V1.SmoothSquareIntegrableJets` and `…Contracts.V1.BoundedRep.SmoothSquareIntegrableJets` **coexist
without error** and are definitionally equal (an `example … := rfl` between them typechecks) — the nested namespace
does its job. Residual: a module that `open`s *both* and writes the bare name gets `error: Ambiguous term`; nothing
in tree does.

## 5. Paper fidelity — findings, ranked

1. **[Medium] Latent hard collision with lane 019 — at the binding, not the contract.**
   `Bindings/BoundedRepresentative.lean:24` declares `BlowupDensity.Bindings.smoothSquareIntegrableJets_eq`; 019's
   `Bindings/GradientL6.lean:37` declares the **same full name**, same namespace, different module. Verified
   empirically: importing two such modules gives `import failed, environment already contains
   'BlowupDensity.Bindings.smoothSquareIntegrableJets_eq'`. Today no module imports both bindings (each
   `Tests/X.lean` imports one), so gates stay green after a merge; it becomes a hard error the first time an
   umbrella, a downstream test or a consumer binding pulls both. The lane avoided the *contract* clash and
   re-created one a layer down. Fix: rename this one, e.g. `boundedRep_smoothSquareIntegrableJets_eq`.
2. **[Medium] Hypothesis inflation, plus one false claim about it.** Contract `:51-52`: the class "is the weakest
   hypothesis the proof route uses — only the jets of order `0`, `1` and `2` enter." The second half is right, so
   the first is wrong: `norm_le_tensorSobolevNorm` (`:119-120`), proved in the same file, takes `ContDiff ℝ ∞ z ∧ ∀
   j ≤ 2, MemLp …`, as does the vendor input; the class demands `∀ n`. The registered clause is therefore strictly
   weaker than what this lane already proved, than the manuscript's (`v ∈ H²`, no smoothness), and than the accepted
   draft, which states it on `MemHmVector 2` with `sobolevENorm 2` (`research/A03/Spec.lean:383-402`). Costs Section
   4 nothing — every consumer field is `H^∞` — but it is not minimal.
3. **[Low] The right-hand side's provenance is cited one link short.** `:68-71` (and module `:51-53`) call the
   manuscript's `‖v‖_{H²}` "`(∑_{|α|≤2}‖∂^αv‖₂²)^{1/2}`", citing `01-introduction.tex:94,103` — but 94 is the
   Fourier-side *set* definition and 103 the vector/tensor summation convention; the manuscript **defines**
   `‖z‖_{H^s(R³)}² = ∫(1+|ξ|²)^s|ẑ|²` at `:85-86` on the angular transform of `:91`. The chain is jet ℓ¹ ↔
   multi-index ℓ² ↔ Fourier weight; only the first two links are written, and the conclusion survives (angular
   Plancherel is an isometry). Those two are correct: `max_w|T(e_w)| ≤ ‖T‖ ≤ ∑_w|T(e_w)|` (left since `‖e_{w_i}‖=1`;
   right is vendor `multilinear_norm_le_coordinate_sum`, `EulerProof.lean:6202`) and `‖a‖₂ ≤ ‖a‖₁ ≤ √3‖a‖₂` over
   three orders, every factor depending only on `3` and `2`. Relatedly, "both sides are physical-space quantities"
   (`:82-84`) holds of the *Lean* statements — all the file asserts — but not of the paper's right-hand side.
4. **[Low] `ATTEMPTS.md:83-85` "the two routes agree on the manuscript's constant" is one exact claim and one loose
   one.** Exact: `embeddingConstant 3 2 = ‖besselWeight 3 (-2)‖_{L²}` and `besselWeight 3 (-2) ξ = (1+‖ξ‖²)^{-1} =
   besselInverse ξ` (`BesselH2Fourier.lean:19`), so it is the same real as `besselConstant` (`:39`), the
   manuscript's `(∫⟨ξ⟩^{-4})^{1/2}` — confirmed by reading both definitions, but **no Lean lemma states it**. Loose:
   the *routes'* constants differ. `sobolevBoundedRepresentative2_norm_le`
   (`SobolevBoundedRepresentative.lean:24-25`) carries `besselConstant` alone; `smoothEmbeddingConstant` multiplies
   it by the localization artifact `unitBumpCoefficient 0 + (2π)^{-2}·3·unitBumpCoefficient 2`. And `:47`'s constant
   is that of `‖v̂‖₁ ≤ C‖v‖_{H²}`, one inversion factor short of the `C` in `‖v‖_∞ ≤ C‖v‖_{H²}`. Harmless: only
   `Cinfty_pos` is exported.
5. **[Low] `contracts.json` scope under-discloses vs its sibling.** Here: "Lemma A.1's H² ↪ L^∞
   bounded-representative clause in jet form; not the tame product estimates". 019's A05 entry adds "its equivalence
   with the datum form `Data.MemHInfty` is not asserted". Neither that gap nor the whole-space-only restriction
   (`lem:calculus` says "either domain") appears. Both are fully disclosed in the docstring and `ATTEMPTS.md`; only
   the JSON is thin.
6. **[Low] The uniqueness consumer needs one more unstated ingredient.** `:26-30` routes `‖∇u₂‖_∞` of
   `appendix-a-local-theory.tex:120-123` through `supNorm_le` on each `∂_ju₂` "and an order shift that this contract
   does not state". It also needs derivative-closure of the class; `Section4/A03/SmoothJets.lean:31-34` deliberately
   drops the A05 copy's closure lemmas. Not mentioned.
7. **[Trivial] Task attribution now self-contradictory.** `collaboration/tasks/A03.md:7` and
   `DEPENDENCY_GRAPH.md:218` say "The embedding clauses of shared Lemma A.1 are supplied by A05", and
   `research/A03/REVIEW.md` accepted "embeddings deferred to A05" — yet this is registered under A03.
   `STATEMENTS.md:261-262`, `:1120-1122` and `research/A03/Spec.lean:383` put it under A03, and A05's registered
   contract is Lemma **B.1**, so A03 is right; the card text was not updated.

**Checked and correct.** The constant is universal — a structure field quantified outside `z`, `ν` and every
solution, matching the bare unsubscripted `C` of `appendix-a-local-theory.tex:8-12`. Both left sides are right:
`eLpNormTop_le` is the literal `‖·‖_{L^∞(R³)}` that `⟪D01:normLinfty⟫` is pinned to (`STATEMENTS.md:261-262`,
`:348-350`) and carries `A03 → R42`; `supNorm_le` is strictly stronger and legitimate, a `SmoothL2` field being
continuous and so its own representative. Vendor input `smooth_pointwise_le_H2` (`EulerProof.lean:8237-8239`) has
exactly the stated hypotheses — `ContDiff ℝ ∞ f`, `∀ j ≤ 2, MemLp (iteratedFDeriv ℝ j f) 2 volume`, `∀ x`: **no
support assumption, everywhere-pointwise** — with codomain any `[NormedAddCommGroup F] [InnerProductSpace ℂ F]
[CompleteSpace F]` (`:7980`), i.e. a *complex* Hilbert space, which is exactly why a reduction is needed. The
reduction is sound: `complexify 3 : Domain 3 →ₗᵢ[ℝ] EuclideanSpace ℂ (Fin 3)` (`:5600`) is an ℝ-linear isometry;
`norm_map` moves the left side, `complexification_tensor_memLp` (`:8358`) the hypotheses,
`complexification_sobolevNorm` (`:8366`) the right side; `Space = Domain 3` is the same `abbrev`. `+1` on the
constant is sound (same device as A05), and no norm is routed through `.toReal` (`ofReal_tensorSobolevNorm` pays for
it with `MemLp`), so no bound is vacuous.

## 6. The gap statement — what an `R42`/`A02` consumer still needs

Consistent with `019-A05-l6-contract/research/A05/REVIEW_CONTRACT.md:93-113`. The datum-form clause (c) — `MemHInfty
z → eLpNorm z ⊤ volume ≤ ofReal Cinfty * Data.sobolevENorm 2 z` — is **unregistered**, and nothing shipped mentions
`sobolevENorm`, `IsSobolevDatum` or `MemHInfty`. A consumer holding `Data.MemHInfty` (`Data.lean:495`, the
Fourier-side datum form) needs three things this contract does not supply:

1. **datum ⇒ jets.** From `IsSobolevDatum m z A` get `∀ n, MemLp (iteratedFDeriv ℝ n z) 2 volume` — D01 unit **L2**,
   booked at `Data.lean:487-491`. Lane 020 proves only the converse (`memHInfty_of_contDiff_memLp`,
   `norm_angularDatum_le`), which composed with `sobolevENorm = ⨅ …` gives `sobolevENorm 2 z ≤ C·(jets)`, the wrong
   way round. `research/D01/REVIEW_L2.md` §4.1/§4.4 and `research/A03/COMPARISON.md:210-221` (rating it an **L**)
   agree.
2. **A time-slice extraction.** R42 applies the clause to `u(t,·)`; `ClassicalSolutionR` (`Data.lean:624`) gives
   `velocity_smooth : ContDiffOn ℝ ∞ velocity (Ico 0 T ×ˢ univ)` and a *datum*-form `sobolev` field, so obtaining
   `ContDiff ℝ ∞ (fun x => velocity (t,x))` on all of `Space` is an extra obligation (routine for interior `t`,
   one-sided at `t = 0`).
3. **The quantitative half**, if the consumer wants `Data.sobolevENorm 2` on the right rather than the jet norm:
   `jetSobolevENorm 2 z ≤ C'·sobolevENorm 2 z` for *every* datum of `z`, since `sobolevENorm` is an infimum — the
   same open direction plus angular Plancherel. This bites in practice: `04-whole-space.tex:53` supplies the
   extension's bound in `C_tH²`, the datum norm, not as a jet sum.

Until (1) and (2) exist, the `A03 → R42` edge `eLpNormTop_le` is meant to carry is not walkable. The missing input
is square-integrability of the jets, not smoothness: every Section 4 consumer identified so far already holds a
smooth field.
