# A05 review — `research/A05/Spec.lean` + `COMPARISON.md`

Reviewer: lane 014. Scope: Lean hygiene, fidelity to Lemma B.1 as Props 4.3/4.4
consume it, normalization, reuse claims, split sanity. No files modified.

## Verdict: ACCEPT-WITH-NOTES

Typechecks with zero diagnostics; no `sorry`/`axiom`/`admit`, no abstract `Prop`
placeholder. All 5 estimate and 9 identification fields say what the paper says;
all 6 uses of Lemma B.1 in Props 4.3/4.4 are covered. The `Λ`/`J`-as-relation
decision, the `(2π)^{-a}` finding and the criticism of `Data.lean:313-315` are all
correct. Everything below is documentation drift, one uncovered endpoint and
optimistic sizing — no field needs restating.

## Issues, ranked

| # | sev | field / place | what differs | one-line fix |
|---|---|---|---|---|
| 1 | med | `rieszPowerExists`/`rieszPowerNorm`/`derivativeCriticalL3`, all at `a = 3/2` | `homogeneousDatumUnique` is restricted to `s < 3/2`, so at the one order the paper is delicate about (`04-whole-space.tex:91` `z = ‖Λ^{3/2}u‖₂`) nothing in the contract says `dotHomogeneousENorm (3/2)` is attained. Split unit U1 also stops at `s < 3/2` and U3 at `a < 3/2`, so **no unit owns the `a = 3/2` endpoint** that U4/U8 consume. | extend `homogeneousDatumUnique` to `-3/2 < s ≤ 3/2` (uniqueness does hold there: `|ξ|^{-3/2}(G₁-G₂) ∈ L¹_loc` and vanishes as a distribution), and widen U1/U3 to match |
| 2 | med | `COMPARISON.md` §0 constants note | cites `research/section4/STATEMENTS.md:465` for "ν-freedom of `c, C₀, C₁` load-bearing for Thm 4.1's converse". Line 465 is the Appendix B completion sentence; the ν-freedom claim is at `STATEMENTS.md:434`, `:508`, `:1288`. | retarget to `:434,508,1288` |
| 3 | low-med | `Spec.lean:66-68` (header, "Why `Λ` appears as a relation") | claims `Paper3/HomogeneousRealization.lean:7` "records that `‖ξ‖` is not `HasTemperateGrowth`". Line 7 says only "A full `L² → 𝓢'` homogeneous multiplier is intentionally not introduced here" — no reason is given and `HasTemperateGrowth` does not occur in that file. Same overclaim in `COMPARISON.md` §4.1. | drop the attributed reason; cite the file for the absence only |
| 4 | low | `Spec.lean` appendix-b line refs | several drift: `:47-49` (cited for the smooth-`H^∞` class) is actually the `1/p_a` display — the text is at `:36-37` and `:71-72`; `:14` (`p_a`)→`:12`; `:17` ("finite constants")→`:12`, and `:17` is in fact the *torus* inequality while the torus half is cited as `:19-21` (the prose; the inequality is `:17`) — the two citations are effectively swapped; `:19` (`C_a`, eq:critical-embedding-pair)→`:14-15`; `:69-70`→`:71-72`; `:96`→`:97`; `:97-99`→`:100-101`; `:103` (Plancherel, `∑|ξ_j|²=|ξ|²`)→`:98-99`; `:11-49` (lemma)→`:11-38`. | one pass renumbering against the current `appendix-b-embeddings.tex` |
| 5 | low | `homogeneousDatumUnique` docstring | "Restricted to the manuscript's range `-3/2 < s < 3/2` (`02-preliminaries.tex:70`, `appendix-b-embeddings.tex:44`)". Neither line displays that range: `:70` says "separable Hilbert space with no polynomial ambiguity", `:44` says `0 < a < 3/2`. The range is an in-tree convention inherited from `Data.lean:328`. | cite `Data.lean:328` for the range, the paper lines for the content |
| 6 | low | `COMPARISON.md` §2.4 | cites `Source/RieszSingularMultiplier.lean:17` for `symbol a ξ = ‖ξ‖^{-a}`; that line is `def multiplier`. `symbol` is `Source/RieszFrequencyCutoffs.lean:13`. | retarget |
| 7 | low | `sameRealDistribution` | the two `IsHomogeneousVectorDatum` hypotheses are inert: the conclusion `U = V` follows from `IsSliceDistribution` alone (a tempered distribution is fixed by its Schwartz pairings, `Data.lean:291`). The field is therefore uniqueness of `IsSliceDistribution` dressed as a two-order statement. Harmless, and `COMPARISON.md` already identifies the real content correctly. | drop the two datum hypotheses, or keep and note they are decorative |
| 8 | low | `embeddingPair` at `a = 1` | never consumed inside the contract: `gradientLSix` is an independent, Fourier-free field with its own `Csix`, while the paper (`04-whole-space.tex:112`) derives `‖∇u‖₆ ≤ C‖Δu‖₂` *from* the `Ḣ¹→L⁶` case. Not wrong — the vendor route is better — but the paper's stated derivation is not the contract's. | note in the docstring that the `a=1` clause is kept for fidelity, not consumed |
| 9 | note | `criticalRepresentative`, `embeddingPair` | stated only for `MemHInfty` fields, whereas `DEPENDENCY_GRAPH.md:199` asks for the "full stated homogeneous completion". The narrowing is licensed by `appendix-b:34-37` and `STATEMENTS.md:467` ("Applied only to smooth `H^∞` fields") and the header declares it. | record the narrowing against the graph contract text |

## Fidelity: the 6 uses

| # | site | Spec route | ok |
|---|---|---|---|
| 1 | `04:93` `‖u‖₃ ≤ Cy` | `velocityCriticalL3` + `rieszPowerNorm (1/2)` | yes |
| 2 | `04:94` `‖∇u‖₃+‖Λu‖₃ ≤ Cz` | `derivativeCriticalL3` + `rieszPowerNorm (3/2)`, one constant as in the paper | yes (see issue 1) |
| 3 | `04:112` `‖∇u‖₆ ≤ C‖Δu‖₂` | `gradientLSix`, Plancherel folded in | yes |
| 4 | `04:155,171` `‖u‖₃ ≤ CY` | `velocityCriticalL3` ∘ `homogeneousLeSobolev (1/2)` | yes |
| 5 | `04:155` `‖∇u‖₃ ≤ CZ` | `derivativeCriticalL3` ∘ `dotThreeHalvesLeGradientSobolev` | yes (paper/`STATEMENTS:601` route via `‖∇u‖_{Ḣ^{1/2}}` differs but is equivalent) |
| 6 | `04:155` `‖Ju‖₃ ≤ C(Y²+Z²)^{1/2}` | `besselCriticalL3` + `IsBesselPower 1` | yes |

Fields (velocity / `gradientTensor` / `Λv` / `Jv`), norms and the `ℝ≥0∞`
fail-safe-to-`⊤` convention all match. `gradientTensor` is `Data.spatialGradient`
on the lift, so its pointwise norm is Frobenius (`01-introduction.tex:103`), not
an operator norm; `gradientTensor v x = toLp 2 (fun j => partialDeriv j v x)`
definitionally, so `tensorMemLp` is well-formed; `tensorSobolevENorm (1/2)` is `Z`. Constants are structure fields with every `∀` inside, hence
independent of the field, of `ν` and of `T`; neither `ν` nor `T` occurs in the
structure. Checked mathematically: `‖v‖_{Ḣ^{3/2}} ≤ ‖∇v‖_{H^{1/2}}` (via
`|ξ|³ ≤ |ξ|²⟨ξ⟩`) and `‖v‖_{Ḣ^a} ≤ ‖v‖_{H^a}` for `a ≥ 0`.

**Λ/J as relations: sufficient.** `‖Λu‖₃`, `‖Ju‖₃` are `L³` norms of the
transformed *field*, which no quantity built from `u` expresses; and `‖Λ^{3/2}u‖₂`
is only ever a quantity (`appendix-b:100-101` refuses `Ḣ^{3/2}` as a space and
asserts no `Ḣ^{3/2} ↪ L^∞`), so no total operator is possible. `rieszPowerExists`
/`rieszPowerNorm` (resp. Bessel) give existence, single-valuedness up to null sets
and the norm identification — exactly what 4.3/4.4 use. `AEStronglyMeasurable w`
inside the relation is right: without it `eLpNorm w 3` is a lower integral.

**`dotHomogeneousENorm`.** Mirrors `Data.sobolevENorm` (`:189`) with
`IsHomogeneousSliceDatum` (`:364`) for `IsSobolevDatum`; empty infimum `⊤`,
matching `eq:homogeneous-realization` (`02-preliminaries.tex:58-69`, the `s=-1`
display `Data.IsHomogeneousDatum` generalizes) and `appendix-b:55-70`. It agrees
with `Data.homogeneousVectorENorm` (`:349`) where both are defined, given datum
uniqueness (issue 1). The draft is **right** that `Data.homogeneousFourierENorm`
(`:407`) must not be used on general `H^∞` slices — `Data.lean`'s own caveat
(`:402-406`) — and `H^∞ ⊄ L¹` (a smooth `~|x|^{-2}` field), so the junk-`0`
failure is reachable, not hypothetical.

## Normalization

Confirmed. `angularFourier f ζ = (2π)^{-3/2}𝓕f(ζ/2π)`
(`FourierConvention.lean:15,23`), so with `ζ = 2πξ`,
`∫|ζ|^{2a}|f̂_ang|²dζ = (2π)^{2a}∫|ξ|^{2a}|𝓕f|²dξ`, i.e. `‖v‖_{Ḣ^a,paper} =
(2π)^a‖ |ξ|^a𝓕v‖₂`. The in-tree cycles constant must be
multiplied by **exactly `(2π)^{-a}`**; at `a=0` the factor is `1` (the right
consistency check), and `FourierConvention.lean:50` is the inhomogeneous analogue
in tree. `FractionalRealization.lean:11` states the layer is cycles, and `:96` has
the genuinely homogeneous `‖datum a h‖` on the right. The **L⁶ estimate escapes
the factor**: `gradientLSix` is discharged by the Fourier-free vendor bound, and
its residual `‖D²v‖₂ = ‖Δv‖₂` carries the same `(2π)²` on both sides. Separately,
`01-introduction.tex:111-116` and `appendix-b:49-51` are right that Tao's (A.11)
constant transfers to the *paper* with no factor — the `(2π)^{-a}` is purely a
paper↔tree matter, and `COMPARISON.md` §2.2/§2.3 draws that line correctly.

## Reuse table (spot-check)

| cited | claim | verdict |
|---|---|---|
| `vendor/.../R3/SmoothSobolevL6.lean:72` `smooth_eLpNorm_six_le` | hyps exactly `ContDiff ℝ 1 f` + `MemLp f 2 volume`, **no** support hypothesis, `ℝ≥0∞`-valued, `{E}` any real inner-product space (`:23`) | confirmed on all four counts; `E := WithLp 2 (Fin 3 → Space)` does instantiate |
| `Source/FractionalRealization.lean:78` `realization_toDistribution` | the `L^{p_a}` element *is* the original distribution | confirmed |
| `Source/FractionalRealization.lean:96` `realization_norm_le_datum` | RHS is the homogeneous `‖datum a h‖`, all `0<a<3/2` | confirmed |
| `Paper1/SchwartzCriticalEmbedding.lean:171` `criticalFieldLp_norm_le_datum` | RHS `‖criticalDatum φ‖ = ‖ |ξ|^{1/2}𝓕φ‖₂`, **homogeneous** (`:38-39`) | confirmed |
| `…:195` `criticalFieldLp_norm_le_weighted` | RHS `‖weightedFourierLp (1/2) φ‖`, **inhomogeneous** | confirmed — and `EXTERNAL_REUSE.md:36` does cite `:195`, so `COMPARISON.md`'s "the blueprint names the inhomogeneous one" is a real and useful catch |
| `Paper3/SobolevDirectionalDerivative.lean:54,120` | `SobolevHilbert s →L SobolevHilbert (s-1)`; `:120` realizes the actual distributional `∂_a`; `:10` carries an explicit `2π` | confirmed |
| `Source/AngularGradientIdentity.lean:45,81,92,107` | `:45` pointwise, hypothesis-free; `:81,:92,:107` all require `ContDiff ℝ ∞` **and** `HasCompactSupport` | confirmed |
| `Source/BesselFractionalData.lean:45` `datum` | contraction `SobolevHilbert a →L L²`, symbol `‖ξ‖^a⟨ξ⟩^{-a}`, needs `0 ≤ a` | confirmed |
| `Paper3/SobolevOrderLowering.lean:26,78` | contraction + realization preserved | confirmed |
| `SobolevHilbertModel.lean:21,89,122,130`; `RieszPotentialLp.lean:14,15`; `RieszFourierProfilePower.lean:10`; `AngularFourierDilation.lean:80,142,176,203`; `AngularSobolevClass.lean:22`; `SmoothL6Adapter.lean:34`; `FractionalRepresentative.lean:19`; `RealVectorPositiveDensity.lean:18,24`; `AngularRealVectorBochner.lean:64`; `RieszPotentialOperator.lean:97`; `RieszComplexPotential.lean:57`; `AngularSobolevCoordinates.lean:156`; `Data.lean:625,636` | all as described | confirmed |
| `Source/VectorForceNorms.lean:47` | exists, but it bounds a **time**-`L^q` norm of `vectorFourierSobolevNorm`, not a componentwise `MemLp` assembly for a `WithLp 2` tensor; weak support for `tensorMemLp` | over-cited; `COMPARISON.md` already calls the work "purely structural", which is right |
| `Source/RieszSingularMultiplier.lean:17` | `symbol` claimed; line is `def multiplier` | issue 6 |

Every `Data.lean` reference in `Spec.lean` (`:160,189,321,349,355,364,407,446,488,
497`) is exact.

## What `Data.lean` should change (report only)

**`Data.lean:312-315` is mathematically wrong and should be fixed.** It asserts
that for `s ≥ 3/2` the `Integrable` clause of `IsHomogeneousDatum` "fails for
every nonzero `G` and the space collapses to `{0}`". What fails at `s ≥ 3/2` is
only the *Cauchy–Schwarz sufficient bound* quoted just above it. Two
counterexamples: (a) any `G ∈ C_c^∞(R³∖{0})` makes `|ξ|^{-s}G` bounded with
compact support, hence integrable against every Schwartz test, at every `s`;
(b) for any `H^∞` field `v`, `G := |ξ|^{3/2}v̂ ∈ L²` (bounded near `0`, `v ∈ H²`
at infinity) and `|ξ|^{-3/2}G = v̂ ∈ L²`, so `φ·v̂ ∈ L¹`. What *is* true is that
at `s ≥ 3/2` the datum map is no longer **onto** `L²` — `G ~ r^{-3/2}(log 1/r)^{-1}`
near the origin is in `L²` with `|ξ|^{-3/2}G ∉ L¹_loc` — so there is no
completion and no isometric bijection, the honest reading of `appendix-b:100-101`.
Fix: keep Cauchy–Schwarz as an upper-range *sufficiency* remark, then say
surjectivity onto `L²` fails at `s ≥ 3/2` while the predicate stays satisfiable,
in particular on every `H^∞` field — which is what `04-whole-space.tex:91`'s
`z = ‖Λ^{3/2}u‖₂` needs. The A05 draft is correct on both halves.

Smaller: `Data.lean:415,420` (`dotHThreeHalvesENorm`, `dotHHalfENorm`) are
`homogeneousFourierENorm` yet are documented as `04-whole-space.tex:91`'s `z` and
`:85`'s `‖a‖_{Ḣ^{1/2}}` — both applied to `H^∞` fields (`ClassicalSolutionR`
slices, `X_R`), exactly the use `:405` forbids. Narrow those docstrings to the
`L¹∩L²` profile sites or point them at a datum-form norm (`COMPARISON.md` §5.5
makes the same observation).

## Split (10 units)

No unit is a research problem; the Riesz-kernel chain is complete through
`potentialOperator_norm_le` and nothing needs new maximal-function work. Sizes
are optimistic in four places:

* **U3 (S→M)**: not transcription — it must *construct* the order-`a` homogeneous
  datum and verify the `Integrable` clause for every Schwartz test, atop U1/U2.
* **U4 (M→L)**: covers `0 < a ≤ 3/2`, but its ingredients and prerequisites U1/U3
  all stop strictly below `3/2` (issue 1); the endpoint needs its own argument.
* **U7 (M→L)**: three conversions at once — scalar `ℂ` → real `Fin 3`, cycles →
  angular, `‖·.toLp p‖ : ℝ` → `eLpNorm · p : ℝ≥0∞` — plus the numeral bridge.
* **U9 (S→M)**: besides the vendor instantiation it needs `‖D²v‖₂ = ‖Δv‖₂` (a real
  Plancherel lemma, only *booked* in D01) and `MemLp (gradientTensor v) 2` from the
  *datum-form* `MemHInfty` — the jet-form equivalence `Data.lean:483-484` books as
  a separate unit L2 and that U9's ingredient list omits.
* **U10**: names `critical_inhomogeneous_identity` "with `HasCompactSupport`
  removed", which is not a removal — it is stated in `vectorAngularSobolevNorm`, a
  literal Fourier integral valid only on `L¹∩L²`, so on a general `H^∞` field it
  must be re-derived at the datum level. U10 does not need it: the weight
  inequalities it also lists (`|ξ|^{2a} ≤ ⟨ξ⟩^{2a}`, `|ξ|³ ≤ ⟨ξ⟩|ξ|²`) suffice,
  `dotThreeHalvesLeGradientSobolev` being an inequality, not the `Y²+Z²` identity.

U1/U2/U5/U6/U8 sizes are fair; the critical paths and "U9 first, Fourier-free, in
parallel" are sound, subject to the U9 caveat.

## Check log

* `. scripts/lean-env.sh; LEAN_NUM_THREADS=6; cd verification && lake env lean ../research/A05/Spec.lean` → **exit 0**, no stdout/stderr, ~2.9 s. Run twice, identical.
* Hygiene: `grep -nE '\b(sorry|axiom|admit|native_decide|unsafe)\b'` → one hit at `:11`, module-docstring prose only. No `theorem`/`lemma`/`example`/`instance`/`axiom` declarations; contents are 9 `def`s and 1 `structure` (14 propositional + 5 data fields).
* Read: `appendix-b-embeddings.tex` (full), `04-whole-space.tex:80-175`, `02-preliminaries.tex:1-80`, `01-introduction.tex:85-130`; `Contracts/V1/Data.lean:140-200,280-425,440-500,617-645`; the 20 cited reuse sites above; `DEPENDENCY_GRAPH.md:193-206`, `EXTERNAL_REUSE.md:36`, `collaboration/tasks/A05.md`, `research/D01/RECONCILIATION.md:180-200`, `research/section4/STATEMENTS.md:460-470,596-606`.
* No files modified; no git write commands run.
