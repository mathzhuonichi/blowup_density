# Review — lane 081, task D01, obligation P2, sub-lemma SL3 final step (+SL2)

Reviewed: `formalization/NSFormalization/Section4/D01/LerayDatum.lean`,
`research/D01/ATTEMPTS_LERAY_DATUM.md`, `research/D01/axioms_leray_datum.lean`
(commit `1c906f7`, 3 files, 459 lines, all additions — no existing module touched).
Context read: `Section4/D01/LerayMultiplier.lean` (lane 073), `Section4/D01/LeraySymbol.lean`,
`Source/RealSobolev.lean`, `Source/FiniteHilbertBochner.lean`,
`Paper3/RealVectorPositiveDensity.lean`, `Paper3/AngularFourierDilation.lean`,
`Section4/D01/SmoothDatum.lean` (`IsSobolevDatum`), `research/D01/{P2_SPLIT,REVIEW_SL3,ATTEMPTS_SL3}.md`,
`paper/sections/04-whole-space.tex` (eq:Rhigh, eq:Rpressure).
Read/build only; the reviewer wrote this file and nothing else. Reviewer probes live in
`/tmp/rev081/probe{1,2}.lean` (not committed).

## Verdict — **ACCEPT-WITH-NOTES**

Merge as is. Everything the brief asked for is delivered and is the statement it claims to be:
`lerayComplement s` really is `(I−P)` on `RealVectorSobolev s`, the a.e. action pins it uniquely,
the transverse hypothesis matches lane 079's output **token-for-token with no bridge**, and the
carrier/`codRestrict` analysis in ATTEMPTS is accurate. The notes below are all *follow-on*
work items (things SL5/SL8 will want exported), not defects in what was shipped.

## 1. Compiles — clean

| command | result |
|---|---|
| `cd verification && lake build NSFormalization.Section4.D01.LerayDatum` | `Build completed successfully (8845 jobs).` (only the known 52 HeliCorgi/vendor warnings) |
| `lake env lean ../formalization/NSFormalization/Section4/D01/LerayDatum.lean` | **0 bytes of output** — no `sorry`, no warning, no linter hit |
| `lake env lean ../research/D01/axioms_leray_datum.lean` | 14 declarations, **each** `[propext, Classical.choice, Quot.sound]` |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats'` | only the docstring sentence "No `sorry`, no `axiom`" and the `#print axioms` lines in the audit file — no occurrence in proof text |
| `make check` | exit 0 (`30 work items: ownership, contract registration and task cards consistent`) |
| `python3 experiments/build_changed_lean.py --base-ref erenup/integration` | exit 0 — this is CI's "changed modules outside the registered closure" step, i.e. **CI does compile the new module** even though nothing imports it yet |
| `git diff --stat erenup/integration...HEAD` | 3 files, +459, no frozen `Contracts/V1`, `Tests`, `paper/` or generated card touched |

## 2. Statement fidelity — the operator is pinned, and pinned correctly

**Is it `(I−P)`?** Yes. `lerayComplement_ae` (:295) is an *exact* a.e. identification of each
component with `(complementSymbolComplex ξ (assemble … ξ)) i`, and lane 073 defines
`complementSymbolComplex ξ = (ℂ ∙ MNS2.r3FrequencyVectorComplex ξ).starProjection`, i.e. the
projection onto the **longitudinal** line — the gradient part, which is what eq:Rpressure's
`∇p = (I−P)(f − ∇·(u⊗u))` needs. Orientation is right (it is not HeliCorgi's solenoidal `P`).

**Could a wrong implementation pass?** Taken individually, yes: the identity satisfies
`_idempotent` + `_opNorm_le_one`, the zero map satisfies `_idempotent` + `_opNorm_le_one` +
`_eq_zero_of_transverse`. What rules both out is `lerayComplement_ae` **alone**: an `Lp` element is
determined by its a.e. class, a `RealSobolevHilbert s` element by its `Lp` coercion, and a
`RealVectorSobolev s` element by its three components — so the delivered `_ae` determines
`lerayComplement s h` uniquely for every `h`. `_idempotent` and `_eq_zero_of_transverse` are
consistency corollaries, not the pin. There is **no** nontriviality lemma stated (see finding 2);
as a check I derived one from the delivered API (probe F, 4 lines):
`(∀ᵐ ξ, (h₁ ξ, h₂ ξ, h₃ ξ) ∈ ℂ ∙ ξ_ℂ) → lerayComplement s h = h` — the zero map does not satisfy
that, so the API really does force `(I−P)`.

**a.e. shape vs. the explicit tuple.** The RHS is the symbol applied to `(assemble … ) ξ`, not
literally to `(h₁ ξ, h₂ ξ, h₃ ξ)`. The two agree a.e. and I proved the explicit form from the
exported API (probe E) — but the bridge is *not* exported (finding 1).

**Transverse hypothesis vs lane 079 — verified token-for-token.** The delivered hypothesis is

```lean
(htr : ∀ᵐ ξ ∂(volume : Measure MNS2.R3),
    ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) * (((h j : FourierData)) ξ) = 0)
```

and it elaborates to (`pp.numericTypes`):

```
∀ᵐ (ξ : NavierStokes.ProblemStatement.Space), ∑ j, ↑(ξ.ofLp j) * ↑↑↑(h.ofLp j) ξ = (0 : ℂ)
```

Probe D fed lane 079's written shape verbatim (`A` in place of `h`) to
`lerayComplement_eq_zero_of_transverse` — it typechecks. So do the two plausible spelling
variants, `∑ j, (ξ j : ℂ) * …` (no intermediate `ℝ` ascription) and `∑ j, …` (no `: Fin 3`).
**No bridge lemma is needed**; `((ξ j : ℝ) : ℂ)` and `(ξ j : ℂ)` are the same term because
`ξ j : ℝ` already. Note also that `MNS2.R3` and `NavierStokes.ProblemStatement.Space` are the same
`EuclideanSpace ℝ (Fin 3)` with the same `volume`, so lane 079 may write either. If lane 079
instead hands over the inner-product form `inner ℂ ξ_ℂ (…) = 0`, the bridge is 3 lines via the
module's own `inner_r3FreqVec` (:307) — verified (probe G).

## 3. Consistency — the carrier claim, the restriction, the phantom

* **Carrier.** Confirmed by `rfl` (probe B):
  `RealVectorSobolev s = PiLp 2 (fun _ : Fin 3 => ↥(realSubspace s))`. `realSubspace` is a
  `ClosedSubmodule ℝ FourierData` (`Source/RealSobolev.lean:118`), so the carrier is a `PiLp` **of**
  subtypes, **not** `↥p` for a submodule `p` of the ambient `Product (Fin 3) (Lp ℂ 2 volume)`.
  `ContinuousLinearMap.codRestrict f p h : E →L[R] ↥p` therefore does not typecheck against this
  codomain — the ATTEMPTS objection is exactly right, and the componentwise `mkContinuous` route
  is the right call.
* **`lerayComplement_toAmbient` (:268)** states the restriction relation correctly: the image's
  coerced component tuple, read into the ambient `PiLp`, equals `lerayComplementAmbient` of the
  ambient inclusion of the input. (There is no *bundled* inclusion CLM — finding 6.)
* **Phantom index, used honestly and legitimately.** `realSubspace (_s : ℝ)` discards `s`
  (`realSubspace s = realSubspace t` and `RealVectorSobolev s = RealVectorSobolev t` by `rfl`,
  probe B), and both the module docstring and ATTEMPTS say so. This is not a fidelity loss for
  eq:Rhigh: in this model the order weight lives in the **realization** map
  `angularRealization s` (`Paper3/AngularFourierDilation.lean:176`, Bessel weight), not in the
  carrier norm, so the carrier's `L²` norm *is* the `Hˢ` norm of the underlying field, and one
  `s`-independent operator is correct precisely because the fibre symbol is `ℂ`-linear and
  `s`-free, hence commutes with the scalar weight. `lerayComplement_opNorm_le_one` is therefore
  the `‖(I−P)F‖_{Hˢ} ≤ ‖F‖_{Hˢ}` of the paper, in this model. (The remaining convention step is
  finding 4.)
* **Imports** are `Section4.D01.LerayMultiplier` + `Paper3.RealVectorPositiveDensity` only — both
  canonical, both already merged. This is a `formalization/` module, so the `Contracts/*` import
  policy does not apply; `post_lean.py` and `make check` are clean anyway. **No definition is
  restated**: the single local name is `private abbrev ins`, an alias for
  `FiniteHilbertBochner.insert` that dodges the clash with `Insert.insert`, mirroring upstream's
  own local alias.

## 4. ATTEMPTS honesty — verified, no overclaim

* Every declaration is at the line the brief lists: `realSymmetryVec_assemble` :84,
  `image_component_mem_realSubspace` :100, `lerayComplementAmbient` :152/`_apply` :163/
  `_opNorm_le_one` :169, `lerayComplement` :255, `_coe` :260, `_toAmbient` :268,
  `_opNorm_le_one` :277, `_idempotent` :281, `_ae` :295, `inner_r3FreqVec` :307,
  `_eq_zero_of_transverse` :316. Cited upstream lines check out too:
  `RealVectorSobolev` at `Paper3/RealVectorPositiveDensity.lean:15`, `realSubspace` at
  `Source/RealSobolev.lean:118`.
* The **"helpful defeqs" claim is true** — all four hold by `rfl` (probe C, all accepted):
  `‖(x : FourierData)‖ = ‖x‖` for `x : RealSobolevHilbert s`; `↑(a + b) = ↑a + ↑b`;
  `↑(c • a) = c • ↑a`; `(WithLp.toLp 2 g) i = g i`.
* The "discarded approaches" section is accurate: (1) the `codRestrict` non-typecheck is confirmed
  above; (2) `PiLp.continuousLinearEquiv` does land in the sup-norm plain product, so the `≤ 1`
  bound indeed needs `PiLp.norm_eq_of_L2` either way; (4) the `Pi.add_apply`/`Pi.smul_apply`
  asymmetry is consistent with the module elaborating with **zero** linter warnings.

## Findings

1. **(low, usability — `LerayDatum.lean:295`)** `lerayComplement_ae`'s RHS is the symbol at
   `(assemble … ) ξ`; the a.e. identification of `assemble`'s coeFn with the raw tuple is **not
   exported** (`assemble_ae` :58 is `private` and is stated via sums of `PiLp.single` insertions,
   not as the tuple). Every consumer will rebuild the same 6 lines. *Fix (follow-on lane, 6
   lines):* export
   `theorem assemble_vec_ae (s) (h) : ∀ᵐ ξ, (assemble 2 volume fun k => ↑(h k)) ξ = WithLp.toLp 2 (fun j => (h j : FourierData) ξ)`,
   proved by `ae_all_iff` + `coordinates_ae` + `coordinates_assemble` + `PiLp.ext` (probe 2 has it
   verbatim), and optionally restate `_ae` against it.
2. **(low, completeness)** No datum-level counterpart to upstream
   `lerayComplementL2_eq_self_of_longitudinal` (`LerayMultiplier.lean:257`). Nothing in the
   delivered set *asserts* nontriviality; the pin is carried entirely by `_ae` (which is enough —
   see §2). *Fix:* add `lerayComplement_eq_self_of_longitudinal` in the SL5 lane, where it is
   needed anyway; 4 lines on top of finding 1's helper (probe F).
3. **(informational)** Lane 079's transverse shape needs **no** bridge — confirmed by
   typechecking, including two spelling variants. Nothing to do.
4. **(medium, but for the *next* lane, not this one)** The convention step SL8 still has to take:
   the datum's frequency variable is the *normalized angular* one
   (`angularRealization s = angularCoordinateRealization s ∘ angularFrequencyDilation.symm`),
   while `complementSymbolComplex ξ` is HeliCorgi's symbol in the raw `ξ`. This is harmless only
   by 0-homogeneity — and the **complex** symbol has no homogeneity lemma: `LeraySymbol.lean:144`
   proves it for the real `complementSymbol`, and `LerayMultiplier.lean:309` supplies only
   `complementSymbolComplex_neg`. P2_SPLIT's step 7c ("the 0-homog matrix symbol commutes with the
   scalar order weight") will need `complementSymbolComplex (c • ξ) = complementSymbolComplex ξ`
   for `c > 0`. Flagged so the SL5/SL7 lane budgets it.
5. **(very low, duplication)** `assemble_ae` (:58) is a verbatim copy of the `hsum` block inside
   upstream `coordinates_assemble` (`LerayMultiplier.lean:445–460`). Acceptable at two copies; if a
   third appears, hoist it into `LerayMultiplier.lean` and have both call it.
6. **(low, ergonomics)** `lerayComplementAmbient` and `lerayComplement` are tied together only
   pointwise, through `lerayComplement_toAmbient`; there is no bundled inclusion
   `RealVectorSobolev s →L[ℝ] Product (Fin 3) (Lp ℂ 2 volume)`, so a consumer wanting
   operator-level algebra on the ambient side must build one. Deliberate and fine at this size —
   note it only so the next lane does not look for it.

## What SL8 (the eq:Rpressure assembly) now has, and what it still needs

**Has.** The `(I−P)` of eq:Rpressure now exists as a first-class object on exactly the carrier the
manuscript's datum interface uses: `lerayComplement s : RealVectorSobolev s →L[ℝ] RealVectorSobolev s`,
with the `Hˢ` contraction (`_opNorm_le_one`, which is eq:Rhigh's boundedness in this model),
idempotence, the exact a.e. fibre action, reality preservation built into the codomain (SL2 is
discharged, not deferred), the kill-solenoidal step in lane 079's exact shape, and the identity
saying it is the restriction of the ambient multiplier. SL3 and SL2 are closed.

**Still needs.** (i) The *transport* lemma nobody has yet: `IsSobolevDatum s z A →
IsSobolevDatum s ((I−P)z) (lerayComplement s A)` — i.e. `angularRealization s` intertwines
`lerayComplement` with the distributional `(I−P)`. That is where finding 4's 0-homogeneity of the
complex symbol and commutation with the Bessel weight get consumed (P2_SPLIT 7c). Without it the
operator acts on data but is not yet known to compute `∇p`. (ii) SL6 (the `iξⱼ` datum) and SL5
(`∇p` longitudinal via curl-freeness), which together supply the *hypothesis* of
`lerayComplement_eq_self_of_longitudinal` for `∇p` and of `_eq_zero_of_transverse` for `∂ₜu`;
(iii) SL7's order-0 Plancherel seed (`MemLp ⟹ IsSobolevDatum 0`), still unwired — nothing yet
manufactures the *first* datum; (iv) the final pin `representative_ae` + `DatumToJets` ⇒
`SmoothSquareIntegrableJets (∇p)`. SL8's blocker list in `P2_SPLIT.md` ("SL3–SL7") can be
narrowed to **SL5, SL6, SL7**.
