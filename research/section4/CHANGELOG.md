# `research/section4/STATEMENTS.md` — changelog

## Version 2 (2026-09-13, after review) — lane 012, task **SPEC**

Input: `research/section4/REVIEW.md` (verdict ACCEPT-WITH-NOTES on version 1), which lists twelve
errors and gives partial verdicts on its items 1 and 7. Every fix below was checked against the
paper before it was made. No file outside `research/section4/` was touched; nothing under
`paper/`, `formalization/`, `verification/`, `collaboration/` or `vendor/` was edited, and the
DAG proposals are reproduced as proposals only.

Line columns: **v1** is the line in the reviewed version (the numbering `REVIEW.md` uses);
**v2** is the line in the file as it now stands. Paper paths are relative to `paper/sections/`.

---

### The twelve listed errors

| # | v1 | v2 | Change | Paper justification |
|---|---|---|---|---|
| 1 | 1027–1035 | 1125–1157 | §8.4 retitled "**one definition, three usages**" and rewritten: one object `Ḣ^s = {h ∈ S' : ĥ measurable, |ξ|^s ĥ ∈ L²}` for `−3/2 < s < 3/2`, plus three lemmas — (a) the Appendix-B identity, (b) smooth-compact finiteness at negative orders, (c) the `s = −1` instance. `Ḣ^{3/2}` kept as a quantity, with the note that the *norm* must still be defined. | `appendix-b-embeddings.tex:56–70` (the completion is that set), `:67–69` (annular density), `:44`,`:64` (range `0<a<3/2` exclusive), `:101–102` (no `Ḣ^{3/2}↪L^∞`); `02-preliminaries.tex:58–61` (`eq:homogeneous-realization`), `:66–69` and `appendix-b-embeddings.tex:58–65` (temperedness, twice); `04-whole-space.tex:70–72` (smooth-compact finiteness), `:91` (`z = ‖Λ^{3/2}u‖₂`) |
| 1 | 462–467 | 527–535 | §3(v) "Which homogeneous realization" rewritten: same object at `s = 1/2` and `s = −1`, only the attached lemma differs; `Ḣ^{3/2}` remains the one exception. | as above |
| 2 | 321–324 | 342, 361–363 | `Cconst : ℝ` moved to precede `energyRate` in `RInsertAPI` (field-order error). | `04-whole-space.tex:39–41` `eq:REclose` |
| 3 | 325 | 325, 364 | `RInsertAPI` gains `thresholds : ThresholdAPI`; `forceConvergence` now reads `s < thresholds.exponent q 0` instead of the hardcoded `2/q - 3/2`. | `04-whole-space.tex:42` and `:8` (`s_q = 2/q − 3/2`), routed through `verification/Contracts/V1/Thresholds.lean` per this ledger's own rule (v2 §0, lines 46–49) |
| 4 | 156 | 175–177 | Rider history window changed from `t ≤ T - ρ` to `t ≤ T - 2*ε^2`; the rider existential now binds `ε`. | `04-whole-space.tex:36` (`u_ε=v` for `0≤t≤T−2ε²`) — a window of the inserted family, unrelated to the force radius |
| 5 | 150–158 | 171–173 | Rider gains `⟪D01:limsupLeft⟫ T (fun t => ⟪D01:normLinfty⟫ (u t)) = ⊤`; the prose at v2:73–79 now spells out that "singularity exactly at `T`" is `Tmax = T` **and** unbounded speed. | `04-whole-space.tex:35`; `02-preliminaries.tex:47–48` ("unbounded speed at their terminal time"); `04-whole-space.tex:13` (the rider sentence) |
| 6 | 155 vs 308 | 174, 346 | `⟪D01:IsMaximalSolution⟫` fixed at **five** arguments `ν a f u p` in both places; §8.7 records the single arity. | `02-preliminaries.tex:28–36` — a classical solution carries a pressure; matches `⟪D01:IsClassicalSolution⟫ ν a g v π I` already used at v2:332 |
| 7 | 313, 319 | 353, 359 | `velSupport` and `pressureCompact` quantifiers changed from `∀ t, t < T` to `∀ t, 0 ≤ t → t < T`. | `04-whole-space.tex:36,38`; velocity norms run over `(0,T)` (`01-introduction.tex:140–141`) |
| 8 | 329–330 | 373–384 | The justification paragraph split: `pressureCompact` is proved inside 4.2's proof; `velDivFree` is **not**, and is now attributed to Lemma 3.4 and Prop. 3.3 via `04:23–27`, displayed only in Thm 3.6(iii). | `04-whole-space.tex:51` (compact `P_ε`), `:23–27` (torus lemmas reused on `R³`); `03-torus.tex:188` ("smooth, divergence-free field"), `:141` ("Incompressibility is preserved"), `:295` (Thm 3.6(iii)), `:332` ("Each summand of the velocity is divergence free"); consumers `04-whole-space.tex:306,308` |
| 9 | 364–365 | 423 | Citation for "imposes no endpoint value at `T`" corrected from `01-introduction.tex:151` to `:149–150`. Also corrected in §8.5 (v2:1170). | `01-introduction.tex:149–150` |
| 10 | 796–805 | 868–890 | `REnergyAPI` now carries `insertion : RInsertAPI` and `insertionData` as fields; `simultaneous` and `differenceOnly` are stated for that one family instead of `∀ ins : RInsertAPI`, restoring the `ν`/`T`/`a` guards. Explanatory paragraph rewritten. | `04-whole-space.tex:221` ("one may **simultaneously** arrange" — a choice, not a universal), `:271` ("the simultaneous convergence for the same family"), `:264–271` (the `L²_tḢ^{-1}` clause is proved here, not in Thm 4.2), `:42` ("the same family of inserted solutions") |
| 11 | 145–148 vs 656–661 | 160–164 | `RMainAPI.nonDensityZero` re-centred at `0`, dropping the existential centre, so it matches `RClassesAPI.nonDensityZero`. The §1(i) prose bullet (v2:88–90) updated to match. | `04-whole-space.tex:179` ("an open ball about zero disjoint from `B^R_{ν,0,T}`", "These nonempty **relative** open balls prove non-density") |
| 12 | 667–670 | 735–743 | §5(v) "Missing DAG edge `R42 → R45`" reworded as an **interface gap**: `R42` already reaches `R45` via `R41D → R41 → R45`; what is missing is a contract clause, fixed by a class-parametric `R41D` routed `R41D → R45`. | `04-whole-space.tex:38` (conclusion 5), `:7–14` (Thm 4.1's statement carries no support claim), `:198` (Cor 4.5's proof), `:177` (`R41D`'s two-case split); graph facts from `formalization/blueprint/DEPENDENCY_GRAPH.md` as quoted by `REVIEW.md:52–59` |
| 12 | 1172 | 1320–1329 | §9 item 17 retitled "DAG defects found while reading" and rewritten: one genuinely missing edge (`A03 → R42`), one interface gap, one graph/text discrepancy. | `04-whole-space.tex:53`, `appendix-a-local-theory.tex:9–13`, `04-whole-space.tex:262` |

### Item 1 (partial verdict) folded into the text

| v1 | v2 | Change | Paper justification |
|---|---|---|---|
| 24 | 34 | §0 table row "three distinct realizations" → "one definition `Ḣ^s`, `−3/2 < s < 3/2`, with three usages". | as row 1 above |
| 243–247 | 264–269 | §2(ii) `⟪D01:dotHsFinite s⟫` replaced by `⟪D01:dotHs s⟫` at `−3/2 < s < 0`, with the finiteness statement labelled a *lemma*. | `04-whole-space.tex:70–72` |
| 405–409 | 463–474 | §3(ii) Appendix-B bullet reworded as the identity lemma at `s = 1/2`; a separate bullet added for the `Ḣ^{3/2}` **quantity**, recording that the norm notation still occurs and must be defined. | `appendix-b-embeddings.tex:41–72`, `:31`, `:107`; `appendix-a-local-theory.tex:24`; `04-whole-space.tex:91` |
| 1001–1003 | 902–907 | §6(v) "Which homogeneous realization" reworded: one definition covers `s = −1` and `s = 1/2`; the care needed is a uniform temperedness proof on `|s| < 3/2`. | `02-preliminaries.tex:58`, `:66–69`; `appendix-b-embeddings.tex:56–70`, `:58–65` |

### Item 7 (partial verdict) — remaining skeleton defects

| v1 | v2 | Change | Paper justification |
|---|---|---|---|
| 310–311 | 348–351 | `RInsertAPI.blowup` restated in the paper's displayed form `limsup_{t↑T}‖u_ε(t)‖_∞ = ∞` instead of `¬ ⟪D01:BoundedNear⟫`. | `04-whole-space.tex:35` |
| 340 (risk note only) | 333, 393–395 | The hypothesis `T^ν_{max,R}(a,g) > T + δ`, previously only in a risk note, added as the field `referenceLifespan`; the risk note now points at it. | `04-whole-space.tex:32` ("Let `(v,π,g)` be **the** solution … regular through `T+δ`"), `02-preliminaries.tex:34–36` |
| 315 | 355 | `velDivFree` also guarded by `0 ≤ t` — an extension of listed error 7 for internal consistency (the reviewer listed only 313 and 319, but the three fields describe the same velocity difference). | `04-whole-space.tex:36,38`; `03-torus.tex:295`; §9.15 of this ledger |
| — | 368–371 | New paragraph after the skeleton stating why velocity fields carry `0 ≤ t` and force fields do not. | `04-whole-space.tex:76` ("including any part after `T`") — clarification **C3** |

### Consequential edits (not in the reviewer's list)

| v1 | v2 | Change | Reason |
|---|---|---|---|
| 1 | 1 | Header bumped to "version 2 (2026-09-13, after review)". | task |
| 16 | 18–26 | New preamble paragraph: what version 2 is, where the changelog lives, where the Lean names come from, and that the blueprint is not edited here. | task |
| 60–64 | 73–79 | §1(i) rider prose expanded with the `T − 2ε²` window and the two-part reading of "singularity exactly at `T`". | errors 4 and 5 |
| 74–75 | 88–90 | §1(i) non-density bullet re-centred at `0`. | error 11 |
| 270–274 | 297–309 | §2(iii) correction bullet annotated with `CorrectionAPI` field names, and a new sub-item 6 recording `corrected_background` and `perturbation_divergence_free` as I02's two extra exports. | task (use I02 field names); supports error 8 |
| 350–353 | 404–411 | §2(v) "Missing DAG edge to A03" expanded with the decisive paper line and the reviewer's reason for preferring the direct edge. | `04-whole-space.tex:53`; `appendix-a-local-theory.tex:9–13` |
| 855 | 1038 | `RGridAPI` gains `convergencesFamily : convergences.insertion = insertion`. | consequence of error 10 — R46 now owns the family, so R47 must pin it |
| 1114–1125 | 1265–1269 | §9 item 2 names the two fields that now thread the single family. | consequence of error 10 |
| 1002–1005 | 1090–1096 | §8 preamble explains the parenthesised Lean names and their provisional status. | task |
| 1007–1188 | 1089–1252 | §8.1–§8.10 annotated with the Lean names from `research/D01/DraftB.lean`, `research/I01/Spec.lean` (`PacketAPI`) and `research/I02/Spec.lean` (`CorrectionAPI`); three gaps recorded explicitly — no Bochner *space* object (§8.5), no maximal-solution predicate and no `limsupLeft` (§8.7), and DraftB's `criticalOrder`/`scalingExponent` duplicating `ThresholdAPI.exponent` (§8.10). | task |
| — | 1331–1355 | New closing section "DAG changes recommended", reproducing `REVIEW.md:179–199` verbatim. | task |

### Fixes not applied

None. All twelve listed errors were confirmed against the paper and applied.

### Notes for the next lane

* `verification/Contracts/V1/Packet.lean` does not exist on `erenup/integration`; the packet field
  names in §8.8 come from `research/I01/Spec.lean` (`PacketAPI`) and must be re-checked when the
  I01 contract lands.
* `research/D01/RECONCILIATION.md` is not present in this worktree, so the Lean names in §8 come
  from `research/D01/DraftB.lean` only. They are provisional until
  `verification/Contracts/V1/Data.lean` is registered.
* `⟪D01:limsupLeft⟫` is a new placeholder introduced by this revision (errors 5 and item 7); D01
  does not define it yet.
