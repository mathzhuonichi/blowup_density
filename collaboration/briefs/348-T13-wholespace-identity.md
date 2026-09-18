# Lane 348-T13-wholespace-identity — T13 the whole-space Gagliardo identity `wholeSpace_identity` of `LocalizationAPI`: `IReal s f = cFrac s · ‖f‖²_{Ḣ^s(ℝ³)}` (and `IReal s f < ⊤`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/348-T13-wholespace-identity` (git branch `erenup/348-T13-wholespace-identity`,
based on lane 344's branch merged with `origin/erenup/integration-section3`: canonical modules `formalization/NSFormalization/Section3/T10/*.lean`,
`Section3/T13/Localization.lean` (vocabulary: `fractionalRadialKernel`, `cFrac`, `IReal`, `SupportedInBall`, …) and lane 344's
`Section3/T13/ConstantEndpoints.lean` (`constant_pos_finite`, the radial majorant `cFracRadial`, `interior_fundamentalCube`, …; reuse, do not
re-prove), plus Section 4's `Section4/D01/{HomogeneousNorm,HomogeneousWitness,OrderZeroDatum,...}.lean`; the proof target is the field
`wholeSpace_identity` of `research/T13/probes/api_on_canonical.lean:47-51`).
Read `CLAUDE.md` (hard rules), **`research/T13/RECONCILIATION.md`, `research/T13/COMPARISON.md` (esp. "Proof dependencies" item 2 — the
whole-space identity route), `research/T13/REPORT_344.md`, `research/T13/ATTEMPTS_CONSTANT_ENDPOINTS.md`**, `paper/sections/03-torus.tex:35-51`,
and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; no anonymous `local instance`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented.
  No edits to existing modules; new files only.
- **No named inputs, no placeholders, no goal repackaging** (this is a hard analytic unit): every declaration must be closed from
  Mathlib and the tree. If a sub-step cannot be closed, deliver everything else and state the residual as a concrete lemma statement with
  the exact error text in `ATTEMPTS`; a `def X : Prop := <goal>` or a hypothesis equal to the target will be discarded without review.
- Before claiming a lemma is "not in the tree", `grep -rn` `Section4/D01/*.lean` (`angularFourier`, `homogeneousFourierENorm`,
  `isHomogeneousSliceDatum_compact`, `enorm_of_isHomogeneousSliceDatum`, `isHomogeneousSliceDatum_unique`, `enorm_homogeneousVectorDatum`,
  Plancherel-type lemmas for `angularFourier`), `Section3/T13/*.lean`, `Section3/T10/*.lean`. Before citing a paper line, `sed -n` it.
  Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.

## Goal (verbatim, `research/T13/probes/api_on_canonical.lean:47-51`)
```
wholeSpace_identity :
  ∀ (s : ℝ), 0 < s → s < 1 → ∀ f : SpatialField,
    ContDiff ℝ ∞ f → HasCompactSupport f →
      IReal s f < ⊤ ∧ IReal s f = cFrac s * dotHomogeneousENorm s f ^ (2 : ℕ)
```
with `IReal s f = ∫⁻ h, ∫⁻ x, ofReal ‖f (x+h) − f x‖² · |h|^{-3-2s}`, `cFrac s = ∫⁻ h, ofReal ‖e^{i h₀} − 1‖² · |h|^{-3-2s}`
(`Section3/T13/Localization.lean:49-74`) and `dotHomogeneousENorm s f = ⨅ G realizing f, ‖G‖ₑ` (`Section4/D01/HomogeneousNorm.lean:26`).

Route (`03-torus.tex:40-51`, COMPARISON item 2): (1) **infimum bridge** — for smooth compactly supported `f` the canonical datum exists
(`isHomogeneousSliceDatum_compact`), its norm is `homogeneousFourierENorm s f` (`enorm_of_isHomogeneousSliceDatum` /
`enorm_homogeneousVectorDatum`; check exact names and statements), and data are unique (`isHomogeneousSliceDatum_unique`), so
`dotHomogeneousENorm s f = homogeneousFourierENorm s f = (∑ᵢ ∫⁻ ξ, ofReal (‖ξ‖^{2s} ‖angularFourier fᵢ ξ‖²))^{1/2}`. (2) **Plancherel per
component and per `h`**: `∫ |fᵢ(x+h) − fᵢ(x)|² dx = (normalisation) · ∫ |e^{i h·ξ} − 1|² |angularFourier fᵢ ξ|² dξ` — find the exact
normalisation of `angularFourier` in D01 (it may be `𝓕` of Mathlib composed with a scaling; the paper's `c_s` has no `2π`, and the
identity must come out with exactly `cFrac s`, so track the constant carefully; if D01 has a Plancherel lemma for `angularFourier` use it,
otherwise derive it from Mathlib's `Real.fourierIntegral`/`MeasureTheory.Lp` Plancherel on `EuclideanSpace ℝ (Fin 3)` for Schwartz
functions — `HasCompactSupport` + `ContDiff` gives a `SchwartzMap`). (3) **Tonelli** (`lintegral_lintegral_swap`, everything is
`ℝ≥0∞`-valued and measurable) to swap `h` and `ξ`. (4) **the inner integral**: `∫⁻ h, ofReal ‖e^{i h·ξ} − 1‖² · |h|^{-3-2s} = cFrac s · ‖ξ‖^{2s}`
for `ξ ≠ 0` by a rotation taking `ξ/‖ξ‖` to `e₀` (`LinearIsometryEquiv` on `EuclideanSpace`, measure preserving:
`LinearIsometryEquiv.measurePreserving`) and the dilation `h ↦ ‖ξ‖⁻¹ • h` (`MeasureTheory.Measure.addHaar_smul` /
`lintegral_comp_smul` with the factor `‖ξ‖^{-3}` cancelling against `|h|^{-3-2s}` scaling to leave `‖ξ‖^{2s}`); `ξ = 0` is null
(`D01.ae_ne_zero`). (5) finiteness from `constant_pos_finite` (344) and `homogeneousFourierENorm s f < ⊤` (from the datum's `‖G‖ₑ ≠ ⊤`).
Handle `ofReal`/`ENNReal.rpow` bookkeeping with care (`s < 1` and `0 < s` are only needed for finiteness of `cFrac`).

## Deliverables
1. New module `formalization/NSFormalization/Section3/T13/WholeSpaceIdentity.lean` (namespace `NSFormalization.Section3.T13`):
   the infimum bridge `dotHomogeneousENorm_eq_homogeneousFourierENorm` (smooth compactly supported `f`), the kernel scaling lemma
   `lintegral_kernel_smul` (`= cFrac s * ‖ξ‖^{2s}`), the Plancherel step, and `theorem wholeSpace_identity` with exactly the goal above.
2. Probe `research/T13/probes/wholespace_identity_closes.lean`: `example` closing the field verbatim by `exact wholeSpace_identity`, plus a
   non-vacuity instance (the `ContDiffBump` field of `research/T13/probes/constant_endpoints_closes.lean` is fine).
3. Records: `research/T13/ATTEMPTS_WHOLESPACE_IDENTITY.md`, conformance `research/T13/axioms_wholespace_identity.lean`, status line in
   `research/T13/COMPARISON.md`, report `research/T13/REPORT_348.md`.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T13.WholeSpaceIdentity` (0 errors), `lake env lean` on the
module (0 output), on the probe (only its `#print axioms` lines), on the axioms file; `make check` from the worktree root.

## Report
Commit on your branch; end with four parts (theorems with exact statements / files / gaps with exact error text / commands run and
results). Also write it to `research/T13/REPORT_348.md`.
