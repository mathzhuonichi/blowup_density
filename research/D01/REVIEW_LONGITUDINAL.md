# Lane 089 review — D01 · P2 · SL5 (Fourier longitudinal form of a curl-free field's datum)

Reviewer ran the Lean in the lane worktree
`.claude/worktrees/089-D01-p2-sl5-longitudinal` (branch `erenup/089-D01-p2-sl5-longitudinal`,
commit `388c7fc`; diff = exactly the three files under review, 426 added lines, nothing else
touched).

## Verdict: **ACCEPT-WITH-NOTES**

All four gates are green, the five declarations carry only the standard three axioms, the
statements say what the paper says, and every one of the four snags recorded in
`ATTEMPTS_LONGITUDINAL.md` was reproduced verbatim by the reviewer.  The notes are about
**downstream consumability** (the order at which SL7b can call this, and where the
`SmoothL2Field` wrapper must come from), one **documentation inaccuracy** in the ATTEMPTS
"Exact statements SL7b/SL8 will consume" section, and ~52 lines **shared with lane 079** that a
SIMP lane should factor.  Nothing in the delivered Lean needs to change.

## 1. Commands and results

All from the lane worktree, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, `lake` from
`verification/` only, one lake process at a time.

| Command | Result |
|---|---|
| `bash scripts/lean-install.sh` | `== OK` (idempotent; replayed, nothing rebuilt) |
| `cd verification && lake build NSFormalization.Section4.D01.Longitudinal` | `Build completed successfully (9913 jobs).` — 2.1 s wall (replay); **no warning from this module** (all warnings in the log are the known vendored HeliCorgi / `Source` ones) |
| `cd verification && lake env lean ../formalization/NSFormalization/Section4/D01/Longitudinal.lean` | **silent**, exit 0 |
| `cd verification && lake env lean ../research/D01/axioms_longitudinal.lean` | 5 declarations, each `depends on axioms: [propext, Classical.choice, Quot.sound]` — `longitudinal_symm_of_curl_free`, `longitudinal_of_curl_free`, `Leray.mem_span_r3FreqVec_of_curl_free`, `Leray.lerayComplement_eq_self_of_longitudinal`, `Leray.lerayComplement_eq_self_of_curl_free` |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats' …/Longitudinal.lean` | one hit, line 43, inside the module docstring (`No `sorry`, no `axiom`…`).  No `set_option` anywhere in the file |
| `make check` (worktree root) | `EXIT=0`; contract policy 13/13, `30 work items: ownership, contract registration and task cards consistent` |

Reviewer scratches (all in `/tmp/rev089/`, none committed):
`clairaut.lean` (finding 3, compiles silent), `probe.lean` (findings 5–6, compiles silent),
`snags.lean` (finding 8), `mono.lean` (finding 7), `defeq.lean` (finding 2).

## 2. Findings

### 1. (OK) Statement fidelity — `hcurl` is the right invariant, and the conclusion is the strong one

`hcurl : ∀ (i j : Fin 3) (x : Space), partialDeriv i Z.field x j = partialDeriv j Z.field x i`
(`Longitudinal.lean:66`) unfolds to `∂ᵢ Z_j (x) = ∂ⱼ Z_i (x)` everywhere — symmetric Jacobian,
i.e. `curl Z = 0` in R³.  That is exactly the invariant `research/D01/P2_SPLIT.md:167-178` calls
for, and deliberately *not* a datum for `p` (which `ClassicalSolutionR` never supplies: it gives
only `pressure_smooth` and `pressure_gradient`, `Contracts/V1/Data.lean:634,647`).  The paper side
is `paper/sections/02-preliminaries.tex:90` `eq:Rpressure`, `∇p = (I−P)(f − ∇·(u⊗u)) =: G`; SL5 is
the consistency half, `(I−P)∇p = ∇p`, and that is what `lerayComplement_eq_self_of_curl_free`
states at the datum level.

Quantifier order in the conclusion is the strong one — `∀ᵐ ξ, ∀ i j, …` (one null set for all nine
pairs, via the two `ae_all_iff.2`), not `∀ i j, ∀ᵐ ξ, …`.  Lemma C's hypothesis
(`Longitudinal.lean:256`) is the same shape, so `lerayComplement_eq_self_of_curl_free` is a direct
application with no repackaging.  Good.

### 2. (OK) `Space` / `MNS2.R3` boundary is `rfl`

Lemma A produces `∀ᵐ ξ : Space ∂volume`, Lemma C consumes `∀ᵐ ξ ∂(volume : Measure MNS2.R3)`.
Reviewer checked `example : Space = MNS2.R3 := rfl` and
`example (ξ j) : (MNS2.r3FrequencyVectorComplex ξ) j = ((ξ j : ℝ) : ℂ) := rfl` — both silent.
The `rfl` at `Longitudinal.lean:247` (`hfr`) is therefore sound and matches
`LerayDatum.lean:310`'s identical `hfr`.

### 3. (NOTE, severity: low — downstream input, not a defect) The Clairaut step is **26 lines**, slightly over the 20 briefed, and needs no new infrastructure

Reviewer wrote it end-to-end in `/tmp/rev089/clairaut.lean`; it compiles silent.  Shape:

```lean
theorem pressureGradient_curl_free {p : PressureField} {t : ℝ}
    (hp : ContDiff ℝ ∞ (fun y : Space => p (t, y))) (i j : Fin 3) (x : Space) :
    partialDeriv i (fun y : Space => pressureGradient p t y) x j
      = partialDeriv j (fun y : Space => pressureGradient p t y) x i
```

Three steps, 21 lines of proof: (a) the component identity
`pressureGradient p t y k = dirDeriv k (p(t,·)) y` (`simp [pressureGradient, dirDeriv,
coordinateVector, Pi.single_apply, mul_ite]`); (b) differentiability of the gradient field via
`(differentiableAt_piLp 2).2` plus `ContDiff.fderiv_right` per component; (c) the coordinate of a
Fréchet derivative is the derivative of the coordinate
(`PiLp.hasStrictFDerivAt_apply … |>.hasFDerivAt.comp x …`), then
`A05.dirDeriv_comm` (`SmoothJets.lean:111`, which *is* `ContDiffAt.isSymmSndFDerivAt`, the
`DivergenceTime.lean:115` pattern) closes it.  `A03.partialDeriv_eq_dirDeriv`
(`OuterTameProduct.lean:269`) is `rfl`, so no translation cost.

The hypothesis comes straight from the contract: reviewer also verified the 6-line wrapper

```lean
theorem pressureGradient_curl_free' (hp : ContDiffOn ℝ ∞ p (Ico 0 T ×ˢ univ)) (ht : t ∈ Ico 0 T) …
  := pressureGradient_curl_free (D01.contDiff_slice_scalar hp ht) i j x
```

using `D01.contDiff_slice_scalar` (`DatumToJets.lean:378`).  So `ClassicalSolutionR.pressure_smooth`
→ `hcurl` is **≈ 26 lines + a 6-line wrapper, zero new lemmas**.  One mechanical note for the
consumer lane: `Longitudinal.lean` does **not** import `DatumToJets`, so whoever writes
`pressureGradient_curl_free` has to add that import (a `formalization/` module — no contract import
policy involved).

### 4. (NOTE, severity: medium — the main consumability finding) The order `(m:ℝ)+1` is **not** what SL7b's order-0 seed can use; Lemma C is, and lane 085 closes the gap

`lerayComplement_eq_self_of_curl_free` is pinned to `(m:ℝ)+1`, `m : ℕ`, because Lemma A routes
through SL6 `isSobolevDatum_partialDeriv` (`DerivativeDatum.lean:245`), which is stated only for
natural `m` with order `m+1 → m`.  The smallest reachable order is therefore **1**, not 0.  SL7b's
seed lives at order 0 (`P2_SPLIT.md:76`, "order-0 Plancherel seed … `lerayComplementVectorL 0
(A⁰_h) = A⁰_{∇p}`"), so it **cannot** call `lerayComplement_eq_self_of_curl_free` directly.

What it *can* call, exactly:

* **the order-agnostic one, this lane's real deliverable** —
  `NSFormalization.Section4.D01.Leray.lerayComplement_eq_self_of_longitudinal (0 : ℝ) A⁰ hlong
  : lerayComplement 0 A⁰ = A⁰`.  Lemma C is stated at **arbitrary real `s`** and takes no datum,
  so it is already the right shape; the only missing input is `hlong` at order 0.
* **the bridge down from order 1**, one line, using lane 085 (`LerayLowering.lean`, merged to
  integration at `2455c2c`; **not** in this lane's base — `git merge-base --is-ancestor 2455c2c
  HEAD` = NO, so the reviewer could not compile it here):

  ```lean
  -- s = (m:ℝ)+1, r = 0
  rw [Leray.lerayComplement_lowerVectorL s r hrs A,
      Leray.lerayComplement_eq_self_of_curl_free hcurl m hA]
  -- ⊢ lerayComplement r (lowerVectorL s r hrs A) = lowerVectorL s r hrs A
  ```

  and, on the datum side, `Leray.leray_datum_lower hrs hA htrans` (`LerayLowering.lean:229`).
  Chaining is legitimate because data are unique: `A03.IsSobolevDatum.unique`
  (`VectorTameProduct.lean:64`) identifies the order-0 Plancherel datum of `∇p` with
  `lowerVectorL 1 0 _ A¹` as soon as an order-1 datum `A¹` exists.

  Alternatively, a ~10-line lemma "longitudinality descends along `angularOrderLowering`" is
  available for free from 085's `angularOrderLowering_coeFn` — the lowering acts a.e. as the
  **scalar** multiplier `loweringMult s r ξ`, and `ξᵢ (c·Âⱼ) = ξⱼ (c·Âᵢ)` is immediate.

No change requested in this lane; this is the interface note SL7b needs.

### 5. (NOTE, severity: low) The `SmoothL2Field` wrapper must come from the **residual side**, not from `∇p`'s own regularity — `ATTEMPTS_LONGITUDINAL.md:102` is loose about this

Lemma A requires `Z : SmoothL2Field Space`, i.e. **all** jets of `Z.field` in `L²`
(`vendor/NavierStokesAndEuler/Euler/LpSmoothField.lean:31`).  For `Z.field = ∇p` that is precisely
`SmoothSquareIntegrableJets (∇p)`, which is SL8's *conclusion* (`P2_SPLIT.md` SL8).  Taking
`ATTEMPTS_LONGITUDINAL.md:102`'s phrase "`(Z := ∇p wrapper)`" literally would be circular.

The non-circular reading, which the reviewer believes is intended and which works: build `Z` from
the NS residual, `Z.field = fun x => f(t,x) − ∇·(u⊗u)(t,x) − ∂ₜu(t,x)` (a `SmoothL2Field` for
`H^∞` data, by the `A04/MomentumDatum.lean:98` ingredients `advection_slice_smoothL2`,
`laplacian_slice_smoothL2`, `forceSlice_smoothL2_of_memForceR`), which **equals `∇p` pointwise** by
the PDE; then `hcurl` for `Z.field` follows from finding 3 through that pointwise equality.  Worth
one corrected sentence in the ATTEMPTS file when the consumer lane lands (not a blocker; ATTEMPTS
is a non-generated research note).

### 6. (OK) Lemma A is not vacuous, and `hcurl` is load-bearing

Both probes in `/tmp/rev089/probe.lean` compile silent under `set_option autoImplicit false`.

* **Inhabitant.**  The zero field `Z0 : SmoothL2Field Space := ⟨0, contDiff_const, …⟩` satisfies
  `hcurl` (`simp [partialDeriv, spatialDerivative, A03.lift]`) and has an order-`(m:ℝ)+1` datum
  `smoothAngularDatum ⌈(m:ℝ)+1⌉₊ … Z0` by `smoothAngularDatum_isSobolevDatum`
  (`SmoothDatum.lean:277`, the `:290` `exists_isSobolevDatum_of_contDiff_memLp` route).  The
  hypotheses are jointly satisfiable, so the lemma is not vacuously true.
* **`hcurl` is load-bearing.**  Beyond the obvious (the proof uses `hcurl i j x` at
  `Longitudinal.lean:108`), the reviewer proved that an `hcurl`-free Lemma A is *absurd*: taking
  such a `bad` as a hypothesis and combining it with lane 079's
  `transverse_of_divergence_free` through Lemma C and `lerayComplement_eq_zero_of_transverse`
  derives `A = 0` for the datum of **every** divergence-free smooth `L²` field.  Four lines,
  compiles.  So the curl hypothesis cannot be dropped or weakened away.

### 7. (OK) Lemma B's `ξ = 0` handling is correct, and the coordinate extraction is right

`mem_span_r3FreqVec_of_curl_free` (`:235`) takes `hξ : ξ ≠ 0` — necessary, since at `ξ = 0` the
hypothesis `hv` is vacuous while `ℂ ∙ r3FrequencyVectorComplex 0 = ⊥`, so the statement would be
false there.  The extraction `∃ k, ξ k ≠ 0` is done by
`by_contra hcon; exact hξ (by ext k; simpa using not_exists.mp hcon k)` — correct in
`EuclideanSpace ℝ (Fin 3)`, where `ext` is the `PiLp` coordinate extensionality (all coordinates
zero ⇒ the vector is zero).  Lemma C supplies the null set inline,
`hne : ∀ᵐ ξ ∂volume, ξ ≠ 0 := by simp [ae_iff]` (`:262`), i.e. `volume {0} = 0` — correct for
Lebesgue measure on R³ and the same device 079/081 use.  Only `hv k j` is consumed, which is what
the a.e. hypothesis delivers.

### 8. (OK) Consistency with `LerayDatum` and 079

Imports are the canonical two (`Transverse`, `LerayDatum`); the module defines **no** `def` and
restates **no** definition (five theorems only), so there is nothing for the `rfl`-bridge rule to
guard.  Lemma C is a faithful mirror of `lerayComplement_eq_zero_of_transverse`
(`LerayDatum.lean:316`): the same `set b := assemble 2 volume …`, the same
`coordinates_ae`/`coordinates_assemble` `hall` block, and it exits through the **public**
`lerayComplement_coe` + `lerayComplementL2_eq_self_of_longitudinal`
(`LerayMultiplier.lean:257`).  It never touches `lerayComplementLM` / `lcFunVec` /
`lerayComplementAmbientLM` internals.  The `symm` + transport split is proportionate — see
finding 9.

### 9. (OK, by measurement) The two-theorem split is forced, not stylistic

Reviewer rebuilt the monolithic version (`/tmp/rev089/mono.lean`: Lemma A with the
cycles-convention heart inlined as a single `have`, `set_option maxHeartbeats 200000`, the repo
default) and got

```
/tmp/rev089/mono.lean:19:0: error: (deterministic) timeout at `whnf`,
  maximum number of heartbeats (200000) has been reached
```

in 6.2 s.  ATTEMPTS snag 1 is exactly right, and the split is the correct fix (no `maxHeartbeats`
bump in the committed module).

### 10. (NOTE, severity: low — SIMP lane, not a blocker) ~52 lines are shared verbatim with lane 079

Not duplication introduced carelessly — 079 is the acknowledged template — but a SIMP lane should
factor these out:

| Block | 089 | 079 | Note |
|---|---|---|---|
| `hXfield` | `:74-80` | `Transverse.lean:123-129` | 089's is the two-index `(a k)` generalization; 079's is the diagonal `(j j)`.  Same body. |
| `hreal_mixed` / `hreal` | `:82-95` | `Transverse.lean:130-144` | **089's `hreal_mixed` strictly subsumes 079's `hreal`** (079 = the `a = k` diagonal).  Promote `hreal_mixed` into `DerivativeDatum.lean` next to `isSobolevDatum_partialDeriv` and have 079 call its diagonal. |
| `hσ`, `hW`, `hAW`, `C`, `hCne` | `:141-158` | `Transverse.lean:191-207` | byte-identical: the `sobolevDirectionalSymbol` coordinate formula and the three non-vanishing facts.  A small "symbol algebra" section. |
| `hc0` / `κ` / `hMP` / `hfwd` | `:180-191` | `Transverse.lean:231-245` | byte-identical dilation-transport preamble.  A generic "an a.e. bilinear relation transports through `angularFrequencyDilation`" helper would kill both copies. |

Also already flagged by 079 itself: `angularFrequencyDilation_coeFn` (`Transverse.lean:66`) is a
`Paper3`-level fact awaiting promotion, and lane 085 has a second copy.  That is three copies now;
worth putting on the SIMP lane's list.

### 11. (OK) ATTEMPTS is honest

All three cited declarations open where claimed and say what is claimed:
`DerivativeDatum.lean:245` = `isSobolevDatum_partialDeriv` (order `m+1 → m`, `Z : SmoothL2Field`);
`LerayMultiplier.lean:257` = `lerayComplementL2_eq_self_of_longitudinal` (hypothesis
`∀ᵐ ξ, f ξ ∈ ℂ ∙ r3FrequencyVectorComplex ξ`); `SmoothDatum.lean:290` =
`exists_isSobolevDatum_of_contDiff_memLp`.  `LerayDatum.lean:316` =
`lerayComplement_eq_zero_of_transverse`, the mirror Lemma C follows.

The four recorded snags are all real, reproduced by the reviewer:

1. **monolithic 200000-heartbeat timeout** — reproduced verbatim, finding 9.
2. **`rw` on the un-β-reduced integrand** — reproduced.  After
   `refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))` the goal is literally
   `(fun x => ψ x * F x) x = (fun x => ψ x * G x) x` and `rw [hFG x]` fails with
   "Did not find an occurrence of the pattern".  `simp only` (which β-reduces) is the right fix.
3. **`Lp.coeFn_sub` gives function subtraction** — confirmed against Mathlib:
   `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean:201`,
   `theorem coeFn_sub (f g : Lp E p μ) : ⇑(f - g) =ᵐ[μ] f - g`.  The RHS is the `Pi` subtraction,
   hence the `Pi.sub_apply` at `Longitudinal.lean:139`.
4. **`push_neg` deprecated at this pin** — confirmed:
   ``warning: `push_neg` has been deprecated. Prefer using `push Not` instead.``  Since the lane's
   own gate is a **silent** `lake env lean`, avoiding it was necessary, and the `by_contra`
   replacement at `:238-240` is fine.

The "Commands run" section of ATTEMPTS matches what the reviewer observed (`Build completed
successfully (9913 jobs)`, silent `lake env lean`, five standard-axiom declarations,
`make check` `EXIT=0`).

## 3. What SL7b now has in hand, and what is still missing

SL7b is "eq:Rpressure at order 0, non-circular": from the order-0 Plancherel datum `A⁰_h` of the
residual `h = f − ∇·(u⊗u) − ∂ₜu`, show `lerayComplement 0 A⁰_h = A⁰_{∇p}` — i.e. that `(I−P)`
kills the solenoidal part (SL4, lane 079) and fixes the gradient part (SL5, this lane).  **In hand
after 089:** the whole gradient half at every order `(m:ℝ)+1`,
`Leray.lerayComplement_eq_self_of_curl_free hcurl m hA : lerayComplement ((m:ℝ)+1) A = A`, plus —
and this is the piece SL7b will actually call — the **order-agnostic** Lemma C
`Leray.lerayComplement_eq_self_of_longitudinal (s : ℝ) (h : RealVectorSobolev s) hlong :
lerayComplement s h = h`, which takes no datum and no `SmoothL2Field` and therefore works at
`s = 0` the moment a.e. longitudinality is available there; plus the reusable fibre fact
`Leray.mem_span_r3FreqVec_of_curl_free` for anyone who needs the line membership directly.  With
079 already supplying `lerayComplement_eq_zero_of_transverse ∘ transverse_of_divergence_free`, the
fibre content of eq:Rpressure is complete at orders `≥ 1`.

**Remaining inputs, with sizes.**  (i) `pressureGradient_curl_free`, the Clairaut `hcurl` — **≈ 26
lines + a 6-line contract wrapper**, fully verified by the reviewer, no new infrastructure, needs
only an added `import …D01.DatumToJets` (finding 3).  (ii) Getting from order `1` down to order
`0`: **1–2 lines** once lane 085 is in the base —
`rw [Leray.lerayComplement_lowerVectorL, Leray.lerayComplement_eq_self_of_curl_free …]`, with
`Leray.leray_datum_lower` for the datum bookkeeping and `A03.IsSobolevDatum.unique` to identify the
Plancherel order-0 datum with the lowering; alternatively a **~10-line** "longitudinality descends
along `angularOrderLowering`" lemma straight from 085's `angularOrderLowering_coeFn` (finding 4).
(iii) The genuinely new work SL7b still owns, unchanged by this lane: the **order-0 Plancherel
datum constructor** `exists_isSobolevDatum_zero_of_memLp` (`P2_SPLIT.md` 7a, S/M — the entry point
nothing else manufactures), the **`SmoothL2Field` wrapper for the residual side** assembled from
`A04/MomentumDatum.lean`'s slice lemmas (M, and the thing that makes the argument non-circular,
finding 5), and SL4α (`div ∂ₜu = 0`, S/M).  SL8's transport lemma
`IsSobolevDatum s z A → IsSobolevDatum s ((I−P)z) (lerayComplement s A)` is **not** delivered here
and is not implied by it — Lemma C is about a datum being *fixed*, not about `(I−P)` transporting
the datum property — so that remains M-sized and depends on 085's commutation.
