# Review — lane 062, task D01, obligation P2 (split-and-start)

Reviewed: `research/D01/P2_SPLIT.md`, `research/D01/ATTEMPTS_P2.md`,
`research/D01/axioms_p2.lean`, `formalization/NSFormalization/Section4/D01/LeraySymbol.lean`
(commit `df5cb31`).  Read/build only; the reviewer wrote this file and nothing else.

## Verdict — **ACCEPT-WITH-NOTES**

The Lean is accept-grade with no reservations: it builds clean, emits no diagnostics of
its own, all eleven declarations are standard-axiom, and every symbol lemma is the
statement it claims to be (independently re-checked against `ξ = 0`, `e₁`, `e₂` in a
scratch file, since deleted).

The **split document is not accept-grade as a plan**, and it is the plan, not the code,
that the next lane will act on.  Its two headline conclusions are both wrong:

* the designated crux **SL3 is not new infrastructure** — a coordinate-mixing,
  operator-valued `L²` multiplier built from *exactly this symbol* already exists in the
  vendored library this very module imports (`vendor/HeliCorgi/Formal/R3LerayPointwiseL2.lean`),
  and Mathlib's `ContinuousLinearMap.holderL` is not restricted to scalar symbols at all;
* the designated hard blocker **SL4β (= D01 unit L3) is not needed** — the closed
  solenoidal subspace can be bypassed entirely by the pointwise fibre fact, which is a
  one-line consequence of the lemmas this lane just proved.

Meanwhile the sub-lemma the chain actually stalls on is **not listed**: SL6's argument is
circular as written (findings 3–4).  These are `.md` defects, correctable by editing the
split; the merged Lean is unaffected.  Hence ACCEPT-WITH-NOTES rather than REJECT, with
findings 1–4 to be resolved **before** a follow-on lane starts building SL3.

---

## Part 1 — Build, axioms, hygiene (all pass)

All from `WT/verification` after `. ../scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, no `-j`,
one lake at a time.

| # | Command | Result |
|---|---------|--------|
| 1 | `bash scripts/lean-install.sh` | `== OK` (full replay, exit 0) |
| 2 | `lake build NSFormalization.Section4.D01.LeraySymbol` | exit 0, `Build completed successfully (8816 jobs)`. 13 warnings in the whole run, **none** from the new module (all from pre-existing `Source/RealSobolev.lean`, `Paper3/SpatiallyCompactTime.lean`, `Paper3/RealPositiveDensity.lean`, `Paper3/RealVectorPositiveDensity.lean`) |
| 3 | `lake env lean ../formalization/NSFormalization/Section4/D01/LeraySymbol.lean` (fresh elaboration, bypasses replay) | exit 0, **no output at all** — confirms zero warnings from the file, not merely a silent replay |
| 4 | `lake env lean ../research/D01/axioms_p2.lean` | exit 0; **11** `#print axioms` lines, every one `[propext, Classical.choice, Quot.sound]` |
| 5 | `grep -rE "sorry\|admit\|native_decide\|\baxiom\b\|maxHeartbeats\|set_option"` over the two new Lean files | one hit, `LeraySymbol.lean:35`, inside the module docstring (`"No `sorry`, no `axiom`; …"`). Nothing in code. |
| 6 | `make check` (from WT root) | exit 0 — `check_formalization_plan.py --check`, `check_contracts.py`, `test_contract_policy.py` (13 tests OK), `check_work_queue.py` (30 work items consistent) |

**Import closure (computed with a transitive-closure script over every `import` line in
`formalization/`, `verification/`, `vendor/HeliCorgi`, `vendor/NavierStokesAndEuler`):**

* `NSFormalization.Section4.D01.LeraySymbol` closure = 104 modules, containing exactly one
  HeliCorgi module: `Formal.R3LerayFrequencySymbol`.  The direct import is in
  `formalization/`, where it is allowed, and it is the second `Formal.*` consumer after
  `Section4/HeliCorgiPort.lean`.
* `Tests.*` closure = 987 modules. **`Formal.*`: NONE. `FormalPatched.*`: NONE.
  `…D01.LeraySymbol`: not present.**  No file under `verification/` contains
  `import Formal` or the string `LeraySymbol`.  The 52 upstream HeliCorgi warnings
  therefore cannot reach the `warningAsError = true` `Tests` library. ✔
* In fact nothing in the repo imports `LeraySymbol` except `research/D01/axioms_p2.lean`,
  which is not a library module.  (Informational, not a finding: like every other
  `Section4/*` module it is outside `NSFormalization.lean`'s root and outside both
  `defaultTargets`, so it is compiled by CI only through
  `experiments/build_changed_lean.py` on the PR that touches it — the same standing as
  `HeliCorgiPort.lean`.)

## Part 2 — The symbol lemmas (all correct)

`complementSymbol ξ := (ℝ ∙ ξ).starProjection` is the right object, and it is the mirror
image of the reused upstream definition.  `vendor/HeliCorgi/Formal/R3LerayFrequencySymbol.lean:18,28`
reads `r3SolenoidalFiber ξ := (ℝ ∙ ξ)ᗮ`, `r3LeraySymbol ξ := (r3SolenoidalFiber ξ).starProjection`,
so `leraySymbol_add_complementSymbol` **is** the orthogonal decomposition
`Space = (ℝ∙ξ)ᗮ ⊕ (ℝ∙ξ)`, not an accidental algebraic coincidence. ✔

Checked line by line:

* `complementSymbol_apply` — `(⟨ξ,v⟩/‖ξ‖²) • ξ` via `Submodule.starProjection_singleton`; this
  is `ξξᵀ/‖ξ‖²` as claimed. ✔
* `complementSymbol_idempotent`, `_apply_mem`, `_fixed_of_mem`, `_self` — mirror upstream's
  proofs exactly. ✔
* `norm_complementSymbol_le`, `complementSymbol_opNorm_le_one` — the pointwise and bundled
  forms, from `Submodule.norm_starProjection_apply_le` / `starProjection_norm_le`. ✔
* `complementSymbol_neg` — even. ✔  (See finding 5: the stronger and equally cheap fact is
  0-homogeneity, which is worth having.)
* Real-linearity ("real matrix entries") is carried by the type `_ →L[ℝ] _`, as the
  docstring says. ✔

**`ξ = 0`.** `(ℝ ∙ 0) = ⊥` and `Submodule.starProjection_bot` makes it the **zero map**;
I verified `complementSymbol (0 : Space) = 0` and `complementSymbol 0 v = 0` in Lean (the
latter also directly from `complementSymbol_apply`, where `‖0‖² = 0` and Lean's `x/0 = 0`
makes the scalar vanish).  It is consistent with upstream's `r3LeraySymbol_zero : … = id`,
and the sum identity still holds at the origin (`id v + 0 = v`).  **Convention verdict:
correct and harmless.**  `{0}` is Lebesgue-null in `Space`, so an `L²`/`Lᵖ` Fourier
multiplier does not see it; both conventions (`(I−P)(0) = 0` here, `P(0) = I` upstream)
define the same operator.  The choice is not neutral for *interpretation* though — it
assigns the whole zero mode to the solenoidal part and none to the gradient part — and
the module docstring does not say so.  **Recommend one sentence recording this** (a null
set, hence multiplier-irrelevant), since a reader of SL5 will hit "is `∇p`'s zero mode
longitudinal?" and deserve the answer up front.

**Independent sanity (scratch file, elaborated, exit 0, then deleted):**
`complementSymbol e₁ e₁ = e₁` ✔ (via `complementSymbol_self`);
`complementSymbol e₁ e₂ = 0` ✔ (from `_apply` + `inner_single_left`);
`complementSymbol e₁ e₂ ≠ e₂` ✔ (nontriviality — the symbol is genuinely not the identity);
`leraySymbol_add_complementSymbol` at `ξ = e₁` for arbitrary `v` ✔.

## Part 3 — The split: route assessment (the substance of this review)

### Finding 1 — **major** — SL3's blocker claim is false; the multiplier already exists upstream

`P2_SPLIT.md:78` and `:141-143` state: *"no coordinate-mixing/operator-valued multiplier
exists in tree; all present ones are scalar (`mul ℂ ℂ`) or diagonal … This is the missing
infrastructure"*, and grade SL3 **M (crux)**.

The *scoped* survey behind that is accurate — I re-ran it.  Every `holderL` in
`formalization/` is the scalar `(ContinuousLinearMap.mul ℂ ℂ)`
(`Paper3/SobolevOrderLowering.lean:28`, `Paper3/SobolevDirectionalDerivative.lean:56`,
`Paper3/AngularSobolevCoordinates.lean:59`, `Source/SingularMultiplier.lean:13,16`,
`Source/BesselFractionalData.lean:46`), and every `ContinuousLinearMap.pi`
(`Section4/D01/HalfOrder.lean:106`, `Paper3/AdmissibleForce.lean:19`,
`Source/FourierPhysicalJets.lean:117,132,157`) is diagonal.  `realProjectionTo`
(`Paper3/RealPositiveDensity.lean:31`) is scalar.  So `Paper3/*` and `Source/*` are as
described. ✔

The conclusion drawn from it is nevertheless wrong on two independent counts.

**(a) It exists in the vendored library this very module imports.**
`vendor/HeliCorgi/Formal/R3LerayPointwiseL2.lean` is a coordinate-mixing, operator-valued
`L²` multiplier built from precisely this symbol, in the `Formal` library roots (hence
compiled by this repo at this pin):

```
def r3LerayPointwiseAction (f : R3L2Velocity) : R3 → R3C := fun ξ => r3LeraySymbolComplex ξ (f ξ)
theorem aestronglyMeasurable_r3LerayPointwiseAction (f) : AEStronglyMeasurable (…) volume
theorem memLp_r3LerayPointwiseAction (f) : MemLp (r3LerayPointwiseAction f) 2 volume :=
  (Lp.memLp f).of_le (aestronglyMeasurable_… f) (ae_of_all _ fun ξ => norm_r3LeraySymbolComplex_le ξ (f ξ))
def r3LerayPointwiseL2 (f : R3L2Velocity) : R3L2Velocity := (memLp_… f).toLp (…)
theorem r3LerayPointwiseL2_ae (f) : r3LerayPointwiseL2 f =ᵐ[volume] fun ξ => r3LeraySymbolComplex ξ (f ξ)
```
That is the *entire* construction, ~60 lines, with **no** `holderL`, **no**
`ContinuousLinearMap.pi`, **no** nine scalar entries, and the norm-≤-1 bound falling out of
the fibrewise contraction via `MemLp.of_le`.  Alongside it, the whole complex fibre algebra
already exists (`R3LerayComplexFiberSymbol.lean`: `r3LeraySymbolComplex ξ : R3C →L[ℂ] R3C`
with `_apply`, `_idempotent`, `_fixed_of_mem`, `_mem`, `norm_…_le`), the divergence bridge
(`R3LerayComplexDivergenceBridge.lean`), the Fourier conjugation
(`R3LerayPointwiseProjectionIdentification.lean: fourier_r3LerayL2Operator_ae`), and the
complement itself (`R3HelmholtzPressure.lean:228 r3LerayComplementL2 = F − P F`, with
`fourier_r3LerayComplementL2_ae` giving its a.e. longitudinal symbol).  The split's own
inventory cites `fourier_r3LerayComplementL2_ae` (`:233`) — it saw the file and did not
recognise it as the SL3 template.

**(b) Mathlib's `holderL` was never scalar-only.**
`Mathlib/MeasureTheory/Function/Holder.lean:125` reads
`def holderL : Lp E p μ →L[𝕜] Lp F q μ →L[𝕜] Lp G r μ` for an **arbitrary** continuous
bilinear `B : E →L[𝕜] F →L[𝕜] G`, with `norm_holderL_le : ‖B.holderL …‖ ≤ ‖B‖`.  Taking
`E := R3C →L[ℝ] R3C` (the operator fibre), `F = G := R3C`, the evaluation bilinear map is
**literally `ContinuousLinearMap.id ℝ E`** (`E →L[ℝ] (F →L[ℝ] G)` *is* `E →L[ℝ] E`), whose
norm is ≤ 1 by `ContinuousLinearMap.norm_id_le`.  I verified in Lean (scratch, exit 0,
deleted) that all four pieces elaborate at this pin:

```lean
example : OpFib →L[ℝ] CVec →L[ℝ] CVec := ContinuousLinearMap.id ℝ OpFib            -- evaluation
example : ‖ContinuousLinearMap.id ℝ OpFib‖ ≤ 1 := ContinuousLinearMap.norm_id_le
example (S : Lp OpFib ⊤ volume) : Lp CVec 2 volume →L[ℝ] Lp CVec 2 volume :=
  (ContinuousLinearMap.id ℝ OpFib).holderL volume ⊤ 2 2 S                          -- the CLM
example (S) (f) : ‖… S f‖ ≤ ‖id‖ * ‖S‖ * ‖f‖ := (…).norm_holder_apply_apply_le S f -- opNorm ≤ 1
example (S) (f) : (… S f : Space → CVec) =ᵐ[volume] fun ξ => (S ξ) (f ξ)           -- a.e. action
  := (…).coeFn_holder S f
```
with `OpFib := CVec →L[ℝ] CVec`, `CVec := EuclideanSpace ℂ (Fin 3)`.  This yields the
bundled CLM, `opNorm ≤ 1`, and the a.e. pointwise action **in one step**, from a single
input: `MemLp (fun ξ => symbol ξ) ⊤ volume`.  Its bound half is this lane's
`complementSymbol_opNorm_le_one`; its measurability half is HeliCorgi's
`aestronglyMeasurable_r3LerayPointwiseAction` argument, already written for this symbol.

**(c) The proposed construction cannot deliver the stated conclusion.**  Independently of
(a) and (b): SL3 states `lerayComplementVectorL_opNorm_le : ‖lerayComplementVectorL m‖ ≤ 1`,
but the proposed route (nine scalar `holderL` entries `ξᵢξⱼ/‖ξ‖²`, assembled with
`ContinuousLinearMap.pi`) reaches that bound only through a triangle inequality over the
nine entries, giving `≤ 3` (or `≤ √3` with care), never `≤ 1`.  The constant `1` is a
*pointwise matrix* fact (`‖M(ξ)v‖ ≤ ‖v‖`) and survives only in the vector-valued picture,
where `‖QA‖² = ∫ ‖M(ξ)Â(ξ)‖² ≤ ∫ ‖Â(ξ)‖²`.  The componentwise route destroys exactly the
structure the stated bound needs.

**Fix.**  Rewrite SL3: drop the "missing infrastructure" claim and the nine-entry template;
name `R3LerayPointwiseL2.lean` as the worked template and `ContinuousLinearMap.holderL` with
`B = ContinuousLinearMap.id ℝ (R3C →L[ℝ] R3C)` as the construction; regrade **M → S/M**.
Also note (harmless but relevant) that if the split ever does want the entry symbols, `≤ C`
suffices downstream — `SmoothSquareIntegrableJets` is qualitative and no constant is
consumed by SL6–SL8.

Two further ingredients the split's inventory omits, both needed by the vector-valued route
and both already in tree:

* **`Source/FiniteHilbertBochner.lean:42,44`** — `assemble : (ι → Lp H q μ) → Lp (Product ι H) q μ`
  and `coordinates`, with `assemble_coordinates` (`:47`).  This is the bridge between
  `RealVectorSobolev m = Product (Fin 3) (RealSobolevHilbert m)` (a `PiLp 2` *of* `Lp` spaces)
  and `Lp (EuclideanSpace ℂ (Fin 3)) 2` (the `Lp` *of* a `PiLp 2`), which is where the
  pointwise matrix acts.  `Paper3/RealVectorPositiveDensity.lean` already uses it.  The
  one gap: it is not yet known to be an isometry at `q = 2` — only `approximation_bound`
  (`:64`) is proved.  That is the real (small) SL3 work item, and it is nowhere in the split.
* **the complex fibre algebra.**  The data are ℂ-valued, so the fibre algebra SL3 actually
  consumes is the **ℂ** one, not the ℝ one this lane proved.  Good news: it is exactly as
  cheap.  I verified (scratch, exit 0, deleted) that `(ℂ ∙ w).starProjection` on
  `EuclideanSpace ℂ (Fin 3)` reproduces `_apply`, `opNorm ≤ 1`, idempotence, kill-if-transverse
  and fix-if-longitudinal from the *same* `Submodule.starProjection_*` lemmas — and upstream
  has already written it (`r3LeraySymbolComplex`).  So no complexification machinery is
  needed anywhere; the ℝ module stays as the "real matrix entries / reality" statement.

### Finding 2 — **major** — SL4β (= D01 unit L3) is not needed for eq:Rpressure

`P2_SPLIT.md:79,86-87` grades SL4β **L** and calls it, with SL3, one of the "two
independent hard pieces" gating P2, via "pointwise-solenoidal `L²` field → *closed*
solenoidal subspace".

The closed subspace is only required if `P` is *defined* as the orthogonal projection onto
it (which is how HeliCorgi builds `r3LerayL2Operator`, `R3LerayL2Operator.lean:28`).  Route B
does not define it that way — it defines the operator by its **symbol**.  Once the operator
is a symbol multiplier, "`(I−P)` kills a solenoidal field" is a **pointwise fibre fact**, one
line from lemmas that now exist:

```lean
-- verified in Lean (scratch, deleted): no subspace, no completeness, no projection theory
example (w v : CVec) (h : inner ℂ w v = (0:ℂ)) : cSym w v = 0
example (w v : CVec) (h : v ∈ (ℂ ∙ w))        : cSym w v = v
```
and its `ℝ` shadows are `complementSymbol_apply` + `complementSymbol_fixed_of_mem`, both
proved in this lane.  Composed with SL3's a.e. action (`coeFn_holder` /
`r3LerayPointwiseL2_ae`), that is the whole of SL4β and SL5, at zero extra cost beyond SL3.
Upstream has already written both in this exact shape:
`R3LerayComplexDivergenceBridge.lean:23,54` —
`mem_r3ComplexSolenoidalFiber_iff_rawDivergencePointwise_eq_zero` and
`r3LeraySymbolComplex_fixed_iff_normalizedDivergencePointwise_eq_zero`.

**What genuinely remains** after deleting SL4β is one lemma, not two:

> the order-`m` datum of `∂ⱼ z` is `iξⱼ` times the order-`m` datum of `z` (angular convention).

From that single lemma, `div z = 0 ⟹ ⟪ξ, ẑ(ξ)⟫ = 0` a.e. (SL4β) **and** the longitudinality
of a gradient (SL5) both follow.  So the split's separate **L** and **M** blockers collapse
into one **M** lemma.

Two corollaries the split should record:

* **SL5 is stated against the wrong invariant.**  As written it derives longitudinality from
  `∇p̂(ξ) = iξ p̂(ξ)`, which presupposes a datum for `p` itself — and nothing in
  `ClassicalSolutionR` gives `p` any decay (`pressure_smooth` only).  The right invariant is
  **curl-freeness**: `∂ᵢ(∂ⱼp) = ∂ⱼ(∂ᵢp)` is Clairaut on the smooth pressure and needs no
  datum for `p`; on the Fourier side it is `ξᵢ ẑⱼ = ξⱼ ẑᵢ` a.e., i.e. `ẑ(ξ) ∈ ℂ ∙ ξ`, which is
  exactly the hypothesis of the fix-if-longitudinal lemma above.
* **the convention worry is empty.**  `complementSymbol` is 0-homogeneous (finding 5), so it
  commutes with `cyclesToAngular`'s dilation, and the radial Bessel weight is scalar and so
  commutes with any matrix symbol.  `P2_SPLIT.md:40-48` chose Route B specifically to "avoid
  the cycles↔angular … transports entirely at the operator level"; in fact the transport is
  *free*, so Route A and Route B build the same operator and either convention may be used.
  (Relatedly, `P2_SPLIT.md:40-42` calls `RealVectorSobolev m` "the angular weighted-Fourier
  datum space" and cites `Paper3/RealVectorPositiveDensity.lean:15`, whose own header says
  *"cycles-frequency Sobolev Hilbert model. Angular convention transport is a separate
  obligation."*  Both are defensible — the **type** is convention-neutral
  (`SobolevHilbert _s` and `realSubspace _s` both ignore their order argument, and
  `cyclesToAngularReal s` maps the real subspace to itself), and the angular reading comes
  from `IsSobolevDatum`'s use of `angularRealization`, not from that file.  The citation
  should be to `Contracts/V1/Data.lean:160` / `angularRealization`, not to `:15`.)

### Finding 3 — **major** — SL6's argument is circular; the real gate is not listed

`P2_SPLIT.md:182-188`: *"apply `lerayComplementVectorL m` to `h`'s order-m datum (exists
since `h ∈ H^∞`, SL0); SL4 + SL5 give `lerayComplementVectorL m (h-datum) = ∇p-datum`."*

To even *state* `A_h = A_{∂ₜu} + A_{∇p}` you need `∂ₜu(t,·)` and `∇p(t,·)` to already **have**
order-`m` data — which is the conclusion of SL6/SL8.  SL5 makes this explicit: its hypothesis
is `hA : IsSobolevDatum m (∇p) A`.  Nothing in SL1–SL5 manufactures the first datum, and lane
055 deliberately does not (`Section4/D01/Pressure.lean:362` proves only the *equivalence* of the
two sides, neither outright).  The repo says so itself at `Section4/D01/DatumToJets.lean:499-503`:
*"`pressure_gradient` gives `∇p(t,·) ∈ L²` at order zero only, and no field of the structure
gives a Sobolev datum for `p` or `∇p` at any positive order."*

So the chain has no non-circular entry point, and the split lists no sub-lemma for one.
The missing step is an **existence/identification** step: construct the candidate datum
`Q(A_h)` and show the *physical field it represents* is `∇p(t,·)` — the content of HeliCorgi's
Route A (`r3HelmholtzPressure_gradient`, `R3HelmholtzPressure.lean:259`), which the split
demotes to "cross-check only" (`:49-54`).  That demotion is the strategic error: Route A is
the only listed item that produces a field rather than transforming one.

**Recommended repair** (order-0 seed + free bootstrap; not prescriptive, but it closes):

1. **New SL (S/M, missing):** `MemLp z 2 volume` (+ `ContDiff`) ⟹ `∃ A, IsSobolevDatum 0 z A`.
   This is order-0 Plancherel.  Mathlib has the isometry (`MeasureTheory.Lp.fourierTransformₗᵢ`,
   used upstream in `R3HelmholtzPressure.lean`); the repo does not yet wire it to
   `IsSobolevDatum 0` — the existing constructor `exists_isSobolevDatum_of_contDiff_memLp`
   (`Section4/D01/SmoothDatum.lean:290`) demands **all** jets in `L²` via `SmoothL2Field`, so it
   cannot be used for this.
2. `ClassicalSolutionR.pressure_gradient` (`Section4/A02/SolutionClass.lean:137`) then gives
   `∇p(t,·)`'s **order-0** datum for free, and `∂ₜu(t,·) = h − ∇p` gets one by subtraction.
   At order 0 the SL4/SL5 argument is non-circular and yields `Q(A⁰_h) = A⁰_{∇p}`.
3. **Bootstrap to every order at no cost:** the matrix symbol commutes with the scalar order
   weight, so `angularRealization m ∘ Q = (Q on distributions) ∘ angularRealization m`
   independently of `m` (same shape as `sobolevRealization_orderLowering`,
   `Paper3/SobolevOrderLowering.lean:78`).  Hence `Q(A^m_h)` realizes the *same* distribution
   at every `m` as `Q(A⁰_h)` does at 0, namely `∇p(t,·)` — which is `IsSobolevDatum m (∇p) (Q A^m_h)`.

That turns SL6 from circular into two small steps, and makes the whole of P2 gated by
(new-SL order-0 Plancherel) + (derivative↔`iξⱼ` datum) + (SL3, now S/M) — none of them **L**.

### Finding 4 — **minor** — the cost table's bottom line

`P2_SPLIT.md:85-87` — *"P2 is gated by two independent hard pieces — SL3 … and SL4β = unit
L3 … Everything else is M assembly."*  By findings 1–3 this is wrong in all three clauses:
SL3 is S/M and largely written upstream, SL4β is not needed, and the "M assembly" hides the
one genuinely missing existence step.  Rewrite the paragraph and the `cost`/`blocker`
columns accordingly.  (SL4α, `div ∂ₜu = ∂ₜ div u = 0`, is correctly graded S/M and correctly
flagged as unproved in tree; that row stands.)

### Finding 5 — **low** — a cheap missing lemma: 0-homogeneity

`complementSymbol_neg` (even) is the `c = −1` case of the stronger fact
`complementSymbol (c • ξ) = complementSymbol ξ` for `c ≠ 0`, which is as cheap
(`Submodule.span_singleton_smul_eq`, then `rfl` on the definition).  It is worth having
because it is what makes the cycles↔angular dilation invisible to the symbol (finding 2's
second corollary), i.e. it retires a whole paragraph of the split's route justification.
Suggested addition to `LeraySymbol.lean`, not a defect in what is there.

### Finding 6 — **low** — the `ξ = 0` convention is undocumented

See Part 2.  One sentence in the module docstring: `(ℝ ∙ 0) = ⊥`, so `complementSymbol 0 = 0`
(matching upstream's `r3LeraySymbol_zero = id`); `{0}` is null, so the `Lᵖ` multiplier is
unaffected by the choice.

## Part 4 — Honesty spot-checks (both pass)

* **`unnecessarySimpa`** (`ATTEMPTS_P2.md:64-66`).  Reproduced: I re-elaborated the rejected
  form `simpa [complementSymbol] using Submodule.starProjection_apply_mem (ℝ ∙ ξ) v` in a
  scratch file and got `warning: try 'simp' instead of 'simpa'` at the expected position,
  exit 0.  The shipped replacement (`simp only [complementSymbol]; exact …`) is clean.  The
  record is accurate. ✔
* **`HeliCorgiPort.lean` exposes only raw declarations** (`P2_SPLIT.md:58-61`).  Read in full
  (49 lines): six `example := @MNS2.…` references
  (`r3EndpointSafeProjected_exists_localMildSolution`, `…_localMildSolution_equation`,
  `r3HelmholtzPressure`, `r3HelmholtzPressure_gradient`,
  `r3EndpointSafeProjectedMild_navierStokes`, `exists_…`), no `def`, no `theorem`, no mention
  of `RealVectorSobolev` or `angularFourier`.  The claim is accurate. ✔  (Pedantic: the split
  names only the two pressure declarations "and the operators via import"; the file also
  exposes four local-existence / NS-equation declarations.  The substance — no bridge — holds.)
* The two `lake build` results quoted in `ATTEMPTS_P2.md:79-86` (8763 / 8816 jobs, 11 standard
  axiom lines) match what I got. ✔
* The claim that the split "does **not** attempt the M/L pieces" is honoured: nothing in
  `LeraySymbol.lean` touches `RealVectorSobolev`, the Fourier transform, or `pressureGradient`. ✔

## Summary of required actions (document only; no Lean change is required to merge)

1. **F1** — rewrite SL3: `R3LerayPointwiseL2.lean` is the template; `holderL` with
   `B = ContinuousLinearMap.id ℝ (R3C →L[ℝ] R3C)` is the construction; add
   `FiniteHilbertBochner.assemble`/`coordinates` (and its missing `q = 2` isometry) and the
   ℂ fibre algebra to the inventory; regrade M → S/M.
2. **F2** — delete SL4β/unit-L3 from the critical path; replace SL4β and SL5 by the single
   "datum of `∂ⱼz` is `iξⱼ` times the datum of `z`" lemma; restate SL5 via curl-freeness.
3. **F3** — add the missing order-0 Plancherel datum sub-lemma and the order bootstrap; stop
   demoting Route A to "cross-check"; fix SL6's circular sketch.
4. **F4** — rewrite the "two hard pieces" bottom line and the cost/blocker columns.
5. **F5/F6** (optional, cheap) — add `complementSymbol` 0-homogeneity; document the `ξ = 0`
   convention.

## Commands run (exact)

```
cd WT && bash scripts/lean-install.sh                                    # == OK
. WT/scripts/lean-env.sh ; export LEAN_NUM_THREADS=6                     # from WT/verification
lake build NSFormalization.Section4.D01.LeraySymbol                      # exit 0, 8816 jobs
lake env lean ../formalization/NSFormalization/Section4/D01/LeraySymbol.lean   # exit 0, no output
lake env lean ../research/D01/axioms_p2.lean                             # exit 0, 11 x [propext, Classical.choice, Quot.sound]
grep -rE "sorry|admit|native_decide|\baxiom\b|maxHeartbeats|set_option" \
  formalization/NSFormalization/Section4/D01/LeraySymbol.lean research/D01/axioms_p2.lean
                                                                         # 1 hit, docstring only
cd WT && make check                                                      # exit 0
python3 <transitive import closure over formalization/, verification/, vendor/>
                                                                         # Tests closure 987 modules; Formal.* NONE; FormalPatched.* NONE
lake env lean /tmp/scratch_leray.lean                                    # exit 0 (xi=0, e1, e2 sanity) — deleted
lake env lean /tmp/route_test.lean                                       # exit 0 (operator-valued holderL route) — deleted
lake env lean /tmp/route_test2.lean                                      # exit 0 (C fibre algebra, SL4b/SL5 pointwise) — deleted
lake env lean /tmp/simpa_check.lean                                      # unnecessarySimpa warning reproduced — deleted
```

No git write commands were run; the worktree is unmodified apart from this file.
