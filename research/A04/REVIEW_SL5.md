# Review — lane 095, task A04, sub-lemma SL5 (nonlinear IBP + Cauchy–Schwarz, split-and-start)

Reviewer: opus (lane-review, light & strict).  Commit under review: `203136d`
(`[095-A04] SL5 split: sub-lemma table; discrete Cauchy-Schwarz for sums of inner
products; summed real skew-adjointness`).  Worktree
`.claude/worktrees/095-A04-sl5-nonlinear`; read/build only, no repo file other than
this one was written, no git command other than `status`/`log`/`show`.

## Verdict

**ACCEPT-WITH-NOTES.**

The Lean is clean and the four delivered lemmas are faithful, unconditional and
non-vacuous.  The module builds, elaborates silently at the default heartbeat
budget, carries no `sorry`/`axiom`/`native_decide`/`maxHeartbeats`, all four
declarations are exactly `[propext, Classical.choice, Quot.sound]`, and `make check`
passes.  5e is not a Mathlib duplicate at this pin.  I did not merely read the two
load-bearing claims, I ran them:

* **5d is not a tautology.**  A sign-flipped copy of
  `sum_real_inner_angularDirectionalDerivative` fails to elaborate (the
  `Finset.sum_neg_distrib` rewrite has nothing to match), so the minus sign is
  load-bearing and 082's `real_inner_angularDirectionalDerivative` is genuinely
  consumed, not decorated with `simp`.
* **5e lands where 5h needs it.**  `sum_inner_le_sqrt_mul_sqrt` instantiates verbatim
  at `E := RealVectorSobolev (m:ℝ)`, `ι := Fin 3` (compiled), which is the exact shape
  of the last step of the assembly once both slots are at order `m`.

The notes are all in the accompanying research docs — which, for a *split*-and-start
lane, are the main deliverable.  One of them (F1) is substantive: the table's
blocker analysis is both mis-attributed and stale, and the row that records the
genuinely remaining analytic gap is **missing**.  Nothing requires changing a proved
statement; one stale sentence in the module docstring should be corrected.

---

## 1. Compiles — commands and results

All from the worktree, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, lake from
`verification/`, one lake process at a time.

| command | result |
|---|---|
| `bash scripts/lean-install.sh` | exit 0; its `lake test` ends `== OK`, every registered contract "checked; standard logical axioms only" |
| `lake build NSFormalization.Section4.A04.NonlinearPairing` | `Build completed successfully (9894 jobs).`  Only warning in the run is the pre-existing `SchwartzMap.smul_apply` deprecation in `Paper3/SobolevDirectionalDerivative.lean:103`, untouched by this lane |
| `lake env lean ../formalization/NSFormalization/Section4/A04/NonlinearPairing.lean` | **silent**, exit 0 |
| `lake env lean ../research/A04/axioms_sl5.lean` | 4 declarations, each `[propext, Classical.choice, Quot.sound]` — `sum_inner_le_sqrt_mul_sqrt`, `abs_sum_inner_le_sqrt_mul_sqrt`, `sum_real_inner_angularDirectionalDerivative`, `sum_real_inner_angularDirectionalDerivativeReal` |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats'` on the module | no hits.  In `research/A04/axioms_sl5.lean` only the four `#print axioms` lines and the header comment |
| `make check` | exit 0 (`13 tests OK`, `30 work items: ownership, contract registration and task cards consistent`) |
| mutation probe (stdin, no file written): 5d with the RHS minus dropped | **fails** — `rewrite failed: did not find -∑ …`.  Non-tautology confirmed |
| instantiation probe (stdin): 5e at `E := RealVectorSobolev m`, `ι := Fin 3` | compiles |

CI coverage: the module is outside the registered-contract closure, but
`.github/workflows/contracts.yml` runs `experiments/build_changed_lean.py --base-ref`
("Compile changed modules outside the registered test closure"), so it *is* built on
the PR.  No gap.

## 2. Statement fidelity

**(a) 5e is the right inequality for `hnl`. ✔**  The target is
`- ⟪G t, N⟫ ≤ gradientSobolevNormAt (m:ℝ) u t * (outerSobolevENorm (m:ℝ) (u t·) (u t·)).toReal`
(`HighEnergy.lean:101–110`, `hnl`).  Both factors are the **same** ℓ²-over-columns
assembly, verified in the tree:

* `outerSobolevENorm s u v = columnsSobolevENorm s (outerColumn u v)`
  (`A03/OuterTameProduct.lean:79`), and
  `columnsSobolevENorm s T = (∑ⱼ sobolevENorm s (T j) ^ 2) ^ (1/2)` (`:75`).  So it is
  the ℓ² (Frobenius) sum over the three columns `Wⱼ = uⱼ·u`, **not** a separate tensor
  norm — the table's answer to the open question is correct.
* `gradientSobolevENorm s v = columnsSobolevENorm s (fun j => partialDeriv j v)` (`:87`),
  `gradientSobolevNormAt s u t = (gradientSobolevENorm s (u t·)).toReal`
  (`LaplacianDatum.lean:87`).

So `√(∑ⱼ‖aⱼ‖²)·√(∑ⱼ‖bⱼ‖²)` is structurally the right RHS, with `aⱼ = Dⱼ(datum_{m+1} u)`
and `bⱼ = datum_m(Wⱼ)`, both read through `sobolevENorm_eq`
(`A03/VectorTameProduct.lean:71`, `sobolevENorm s z = ‖A‖ₑ`).

`.toReal`/`sqrt` handling in rows 5f/5g is **honest**: the ℝ≥0∞ `(∑ x²)^(1/2)` ↔ ℝ
`√(∑ (x.toReal)²)` bridge needs each column enorm `≠ ⊤`, and both rows say so
(5g explicitly names "5b (`Bⱼ` finite)").  The existing template
`gradientSobolevENorm_toReal_sq_eq_sum` (`LaplacianDatum.lean:96`) derives that
finiteness *from the datum* via `enorm_ne_top`, so it is free rather than assumed;
going from the squared identity to the `√` form is `Real.sqrt_sq ENNReal.toReal_nonneg`.
Correctly rated S.

**(b) 5d is stated at the orders SL5 needs. ✔**
`sum_real_inner_angularDirectionalDerivative (s : ℝ) (a : Space) (f g : Fin 3 → FourierData)`
is fully generic in `s` and lives on the ambient `Lp ℂ 2 volume` carrier, so the
order clash (`G` at `m`, the column data at `m+1`) simply does not arise — this is
exactly the shape 088's `inner_datum_laplacianDir` consumes inline.  The subtype form
`sum_real_inner_angularDirectionalDerivativeReal` is restricted to a **common order `s`**
in both slots, and that restriction is documented twice: in the module docstring
("on the datum-carrier subtype at a common order") and in `ATTEMPTS_SL5.md` design
decision 2, which explicitly rejects the subtype form as insufficient for SL5.  Good.

**(c) The table.**  Row 5a's reading of `advection` is **correct**:
`advection u t x = spatialDerivative u t x (u (t,x)) = fderiv ℝ (fun y => u(t,y)) x (u(t,x))`
(`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:62–64`) — the
**advection form** `(u·∇)u`, not the divergence form.  The divergence-form rewriting
`advection = ∑ⱼ ∂ⱼ(uⱼ • u)` is stated with the right derivative operator
(`partialDeriv j v x = fderiv ℝ v x (e_j)`, `OuterTameProduct.lean:59`, a *vector*-valued
derivative of the vector field `Wⱼ`) and the right side condition
(`spatialDivergence u t x = ∑ᵢ (spatialDerivative u t x eᵢ) i = 0`,
`ProblemStatement.lean:66–68`), plus `DifferentiableAt` — which is needed, since
`fderiv` returns `0` off the differentiability set.  I re-derived the route in
`ATTEMPTS_SL5.md`: `∂ⱼWⱼ = (∂ⱼuⱼ)u + uⱼ∂ⱼu`, summed gives `(div u)·u + (u·∇)u`.  Correct.

Sizes: see F1/F3 below and the corrected table in §5.

**(d) Vacuity. ✔**  All four lemmas are unconditional (no hypotheses beyond
typeclass arguments), so nothing can be satisfied vacuously; and 5d genuinely
consumes 082 — the mutation probe above shows the statement is false without the
sign, and the proof term is literally
`Finset.sum_congr rfl (fun i _ => real_inner_angularDirectionalDerivative s a (f i) (g i))`.

## 3. Consistency

* Imports: one line, `NSFormalization.Section4.A04.RealPairing`.  The module is under
  `formalization/`, not `Contracts/`, so the contract import policy does not apply; no
  contract is registered by this lane and `check_work_queue.py` is green.
* No definition is restated.  Everything (`FourierData`, `RealVectorSobolev`,
  `angularDirectionalDerivative(Real)`) is opened from the canonical modules.
* **Not a Mathlib duplicate.**  At this pin (`Mathlib/Analysis/…`), grep finds no
  `Finset.inner_mul_le_norm_mul_norm` and no `inner_mul_le_norm_mul_norm` at all;
  `Finset.sum_inner` (`InnerProductSpace/Basic.lean:157`) is `∑ ⟪fᵢ, x⟫ = ⟪∑ fᵢ, x⟫`,
  a different statement; `real_inner_le_norm` / `abs_real_inner_le_norm`
  (`Basic.lean:465,469`) are the scalar Cauchy–Schwarz, and
  `Real.sum_mul_le_sqrt_mul_sqrt` (`Analysis/Real/Sqrt.lean:500`) is the ℝ-valued
  discrete one.  The composite over inner products does not exist in Mathlib, and a
  tree-wide grep finds no local copy either (the four existing users of
  `Real.sum_mul_le_sqrt_mul_sqrt` — `Paper1/{FiniteWeightedPairing,PeriodicH2Embedding,
  PeriodicFiniteL3,PeriodicCriticalBridge}`, `C01/Trilinear.lean:113` — all inline it at
  norms, never at inner products).  5e is new and correctly generic.

## 4. Honesty of ATTEMPTS

Opened and confirmed:

* `outerSobolevENorm` is the ℓ² assembly over columns — ✔ (`OuterTameProduct.lean:75,79`).
* `advection` is the advection form `fderiv … x (u(t,x))` — ✔ (`ProblemStatement.lean:63`).
* `Real.sum_mul_le_sqrt_mul_sqrt` at `Analysis/Real/Sqrt.lean:500`, "the same lemma C01
  uses for `advection_norm_le`" — ✔ (`C01/Trilinear.lean:113`).
* `Finset.sum_neg_distrib` used at `Source/OrdinaryViscousStability.lean:42` and
  `Paper1/ConservativeForce.lean:66` — ✔ both.
* The `/--` on `open` parse error and the rejection of the subtype-only 5d are both
  plausible and consistent with the delivered code.

**Not confirmed:** there is **no note anywhere** (`SL5_SPLIT.md`, `ATTEMPTS_SL5.md`,
module docstring) that lane 088's `Section4/A04/LaplacianAssembly.lean` is absent from
this branch.  The file is indeed absent (`ls formalization/NSFormalization/Section4/A04/`
shows 12 modules, no `LaplacianAssembly.lean`); it landed on `erenup/integration` as
PR #94 after this worktree branched.  Instead of recording that, the docs assert that
SL3's order shift is "still open" — see F1.  (Minor: `ATTEMPTS_SL5.md` says
`Finset.sum_neg` "in tree is about `SignType`/sign sums"; the actual hit at this pin is
`SkewPolynomial.sum_neg`.  The conclusion — wrong lemma family — stands.)

---

## Findings

### F1 — **Medium/High** (documentation, but it is *this lane's* deliverable).  The 5f/5h blocker is mis-attributed, stale, and the row recording the real remaining gap is missing.

**Location:** `research/A04/SL5_SPLIT.md` row `5f.grad` and the "Remaining frontier"
paragraph; `formalization/.../A04/NonlinearPairing.lean:41–42` (module docstring,
"5f is gated on the SL3 datum-carrier order shift").

Three separate problems, in increasing order of importance.

**(i) Row 5f as *stated* has no order shift at all.**  The row states
`√(∑ⱼ ‖Dⱼ G'‖²) = gradientSobolevNormAt (m:ℝ) u t` **with `G' = datum_{m+1}(u)`**.  That is
literally `gradientSobolevENorm_toReal_sq_eq_datum_sum` (`LaplacianDatum.lean:130`,
already on this branch, predating 088) composed with `Real.sqrt_sq`.  Two lines, **S**,
no gate.  The order shift the row describes is a property of the **assembly (5h)** —
whether the skew-adjoint step *produces* `Dⱼ G'` or `Dⱼ G` — not of 5f.

**(ii) The SL3 gate is stale.**  PR #94 (lane 088, `LaplacianAssembly.lean`) closed SL3.
On `origin/erenup/integration` it supplies, all directly reusable by SL5:
`derivDatumStep n j`, `castOrder` / `isSobolevDatum_castOrder` / `cast_mid_order` /
`cast_top_order` (the ℕ-cast order transport), `coe_derivDatumStep`, `castOrder_coe`,
`norm_sq_derivDatumStep`, `isSobolevDatum_lowerVectorL` + `coe_lowerVectorL` (a datum
is the `angularOrderLowering` of a higher-order datum), `angularMid_comm` and
**`directionalDerivative_orderLowering_comm`** (`Dσ ∘ Λ_{s→r} = Λ_{(s-1)→(r-1)} ∘ Dσ'`),
plus `isSobolevDatum_laplacian` as a template for the 3-direction datum assembly.
Any sentence saying SL5 waits on SL3 must go.

**(iii) But PR #94 does *not* close SL5's order reconciliation, and the table has no row
for what does.**  Working the assembly through:

```
-⟪G,N⟫ = ∑ⱼ ∑ᵢ ⟪Dⱼ Gᵢ, (Bⱼ)ᵢ⟫        (5c rewrites N, then 5d.amb)
```
with `G = datum_m(u)` and `Bⱼ = datum_{m+1}(Wⱼ)` — the order `m+1` on the column side is
forced, because `isSobolevDatum_partialDeriv j n` only ever maps an order-`(n+1)` datum
to an order-`n` one.  The target needs `A' = datum_{m+1}(u)` on the left and
`Cⱼ = datum_m(Wⱼ)` on the right.  088 supplies the two identifications
`G = Λ_{m+1→m} A'` and `Cⱼ = Λ_{m+1→m} Bⱼ` (`isSobolevDatum_lowerVectorL` +
`isSobolevDatum_unique` + `coe_lowerVectorL`) and the commutation
`Dⱼ G = Λ_{m→m-1}(Dⱼ A')`.  What remains is

```
⟪Λ_{m→m-1}(Dⱼ A'ᵢ), Λ_{m+1→m+1}(Bⱼᵢ)⟫  =  ⟪Λ_{m→m}(Dⱼ A'ᵢ), Λ_{m+1→m}(Bⱼᵢ)⟫
                                        =  ⟪(Dⱼ A')ᵢ, (Cⱼ)ᵢ⟫
```

i.e. a **two-vector, two-source-order lowering transfer**
`⟪Λ_{s→r} v, Λ_{s'→t} w⟫ = ⟪Λ_{s→r'} v, Λ_{s'→t'} w⟫` whenever `r + t = r' + t'`.
082 has only the **single-vector** case: `inner_loweringMid_pairing`,
`inner_lowering_pairing_complex` and `real_inner_lowering_pairing`
(`A04/RealPairing.lean:168,199,218`) all take one `w`/`v` in both slots, which is what
SL3 needed (both slots descended from the same `Aᵢ`) and what SL5 does **not** have
(`u` on one side, `Wⱼ` on the other).  088 adds no two-vector version.
Half-transfer is genuinely required: the crude route `‖Λ_{m→m-1}(Dⱼ A')‖ ≤ ‖Dⱼ A'‖`
leaves `‖u⊗u‖_{H^{m+1}}` on the right, which is *weaker* than the target `‖u⊗u‖_{H^m}`
and does not feed SL6.

**Fix:** add a row (5i) for the two-vector transfer, mark it the critical path of SL5,
delete the SL3 gate from 5f, the frontier paragraph and the module docstring.  Sizing:
**S**.  The transfer is true for the same reason the single-vector one is —
`angularOrderLowering s r` is `U ∘ Mid ∘ U⁻¹` with a symbol that
`lowering_mid_symbol_eq` collapses to `sobolevBesselWeight (r-s) (frequencyUnit • ξ)`,
depending only on `r - s`, and `sobolevBesselWeight` is multiplicative — and the
existing proof of `inner_loweringMid_pairing` (`RealPairing.lean:168–197`, an
`integral_congr_ae` with `conjW` + two `show … from by ring` steps) never uses `v = w`
except in the literal `v ξ * conj (v ξ)`.  Generalizing it to `v ξ * conj (w ξ)` with
independent source orders is a mechanical edit of that one proof plus the two
transports above it.

### F2 — Low.  Row 5b is over-sized; its stated blocker belongs to 5c.

**Location:** `SL5_SPLIT.md` row `5b` ("**M**", "needs each `Wⱼ` wrapped as a
`SmoothL2Field`").

Datum **existence** is free from norm finiteness:
`A03.exists_sobolevDatum : sobolevENorm s z ≠ ⊤ → ∃ A, IsSobolevDatum s z A`
(`A03/VectorTameProduct.lean:77`, verified by `#check`).  And finiteness of
`sobolevENorm ((m+1:ℕ):ℝ) (outerColumn z z j)` is exactly what
`A03.tameProductVector (m+1) (by omega) (hu.component j) hu`
(`VectorTameProduct.lean:256`, verified by `#check`) bounds, with every factor on its
RHS finite under `MemHmVector (m+1) (u t·)` / `MemHmScalar (m+1)`.  So 5b is **S**.
The `SmoothL2Field` wrapping is a **5c** requirement — `isSobolevDatum_partialDeriv`
takes `{Z : SmoothL2Field Space}` — and should be recorded there, next to 088's
`Z.directionalField` repackaging trick, which is the pattern to copy.

### F3 — Low.  Row 5c's size drops; `isSobolevDatum_laplacian` is a line-by-line template.

**Location:** `SL5_SPLIT.md` row `5c` ("**M**").

088's `isSobolevDatum_laplacian` does the identical assembly with *two* derivative
steps (three directions, `isSobolevDatum_add` folded twice, `SchwartzPairable` from
`schwartzPairable_of_isSobolevDatum`, `Fin.sum_univ_three` reconciliation, then
`isSobolevDatum_unique` against the given `hN`).  5c is the one-step case.  **S–M**
once 5a and 5b are in hand.

### F4 — Low.  No record that 088 is off-branch.

**Location:** `ATTEMPTS_SL5.md` (whole file).

Per §4: the module is genuinely absent here, which is the correct explanation for why
the lane could not reuse it — but the reader is told instead that SL3 is open.  One
sentence naming PR #94 and the branch point would have prevented F1(ii).

### F5 — Low.  Citation line drift in `SL5_SPLIT.md`.

`outerColumn` is `A03/OuterTameProduct.lean:68`, not `:63`.  `gradientSobolevENorm` is
`A03/OuterTameProduct.lean:87`, not `:76`.  `realSobolev_inner_eq_ambient` is
`A04/RealPairing.lean:77`, not `:73`.  `real_inner_angularDirectionalDerivative` is
`:84`, not `:85`.  (`partialDeriv :59`, `outerSobolevENorm :79`,
`gradientSobolevNormAt LaplacianDatum:87`, `:96`, `:130`, `DerivativeDatum :134`, `:245`,
`C01/Trilinear :95`, `real_inner_angularDirectionalDerivativeReal :96` all check out.)

### F6 — Informational, not a blocker.  5d.amb overlaps three inline lines of 088.

`inner_datum_laplacianDir` (`LaplacianAssembly.lean`) does
`PiLp.inner_apply, ← Finset.sum_neg_distrib, Finset.sum_congr` inline rather than
calling a summed lemma.  5d.amb is that wrapper, so after both land 088 could be
shortened by it.  Nothing to change in this lane.

---

## 5. Corrected SL5 table (sizes after PR #94)

| # | statement | size (was) | status | inputs / blocker |
|---|---|---|---|---|
| 5a | div-free pointwise divergence form `advection u t x = ∑ⱼ partialDeriv j (outerColumn z z j) x`, hyps `DifferentiableAt ℝ z x` + `spatialDivergence u t x = 0` | **M** (M) | open | unchanged by #94.  `HasFDerivAt.smul` + `PiLp.proj` chain rule + `C01/Trilinear.lean:91–98` (`hadv`,`hbasis`,`hmap`) + `Fin.sum_univ_three`.  No upstream gap |
| 5b | `∃ Bⱼ, IsSobolevDatum ((m:ℝ)+1) Wⱼ Bⱼ` | **S** (M) | open | `A03.tameProductVector (m+1)` ⇒ enorm `≠ ⊤`, then `A03.exists_sobolevDatum`.  Needs `MemHmVector (m+1) (u t·)` from `velocity_smooth`.  **No `SmoothL2Field` needed here** (F2) |
| 5c | `N = ∑ⱼ derivDatumStep m j (castOrder … Bⱼ)` | **S–M** (M) | open | 5a + 5b; copy `isSobolevDatum_laplacian` with one step instead of two; `derivDatumStep`/`castOrder`/`isSobolevDatum_castOrder`/`isSobolevDatum_add`/`isSobolevDatum_unique` all from #94 + D01.  Needs each `Wⱼ` as a `SmoothL2Field` (F2) |
| 5d.amb | `∑ᵢ ⟪fᵢ, D gᵢ⟫ = -∑ᵢ ⟪D fᵢ, gᵢ⟫`, ambient | S | **DONE (095)** | — |
| 5d.sub | same on the subtype at a common order | S | **DONE (095)** | — |
| 5e | `∑ⱼ ⟪aⱼ,bⱼ⟫ ≤ √(∑‖aⱼ‖²)·√(∑‖bⱼ‖²)` (+ `\|·\|` form), generic | S | **DONE (095)** | — |
| **5i** | **two-vector lowering transfer** `⟪Λ_{s→r} v, Λ_{s'→t} w⟫ = ⟪Λ_{s→r'} v, Λ_{s'→t'} w⟫` for `r+t = r'+t'` (mid / complex / real layers) | **S** (**new — not in the lane's table**) | open | generalize `inner_loweringMid_pairing` (`RealPairing.lean:168`) from one vector to two and from one source order to two; transport with `angularOrderLowering_eq_dilation_mid` + `inner_map_map`, real part via `real_inner_eq_re_complex`.  **This is SL5's only genuinely new analytic content** (F1 iii) |
| 5f.grad | `√(∑ⱼ ‖Dⱼ A'‖²) = gradientSobolevNormAt (m:ℝ) u t`, `A' = datum_{m+1}(u)` | **S** (S–M, "gated on SL3") | open | `gradientSobolevENorm_toReal_sq_eq_datum_sum` (`LaplacianDatum.lean:130`) + `Real.sqrt_sq`.  **No gate** (F1 i,ii) |
| 5g.outer | `√(∑ⱼ ‖Cⱼ‖²) = (outerSobolevENorm (m:ℝ) z z).toReal`, `Cⱼ = datum_m(Wⱼ)` | S–M | open | 5b at order `m` (same route, `tameProductVector m`) + the `.toReal` ℓ² arithmetic of `gradientSobolevENorm_toReal_sq_eq_sum` (`LaplacianDatum.lean:96`) with `outerColumn` for `partialDeriv` |
| 5h | assembly: `inner_sum` → 5d.amb → **5i** → 5e at `E = RealVectorSobolev m` → 5f/5g | **M** (M) | open | 5c, 5i, 5f, 5g; `G = Λ_{m+1→m}A'`, `Cⱼ = Λ_{m+1→m}Bⱼ` (`isSobolevDatum_lowerVectorL`+`isSobolevDatum_unique`+`coe_lowerVectorL`, #94) and `Dⱼ G = Λ_{m→m-1}(Dⱼ A')` (`directionalDerivative_orderLowering_comm`, #94).  Use `abs_sum_inner_le_sqrt_mul_sqrt` so the sign need not be tracked |

Overall SL5 stays **L**, but the critical path is now short and concrete: 5i → 5a → 5b/5c → 5f/5g → 5h.

## 6. Recommended next SL5 sub-lane

**Row 5i — the two-vector lowering transfer.**  It is the only remaining item with
genuine analytic content, it is **S**, it is on the critical path of 5h, and it is
independent of 5a/5b/5c so it can run in parallel with them.

Deliverable, in `Section4/A04/RealPairing.lean`'s idiom (new module or an added
section; the three layers mirror `:168 / :199 / :218`):

```
theorem inner_loweringMid_transfer (s s' r t r' t' : ℝ) (h : r + t = r' + t')
    (hrs : r ≤ s) (hts : t ≤ s') (hrs' : r' ≤ s) (hts' : t' ≤ s')
    (v w : Lp ℂ 2 (volume : Measure Space)) :
    ⟪angularOrderLoweringMid s r hrs v, angularOrderLoweringMid s' t hts w⟫_ℂ
      = ⟪angularOrderLoweringMid s r' hrs' v, angularOrderLoweringMid s' t' hts' w⟫_ℂ
-- then `…_transfer_complex` (transport across `angularFrequencyDilation`) and
-- `real_inner_lowering_transfer` (real part, via `real_inner_eq_re_complex`).
```

What it needs: `angularOrderLoweringMid_coeFn`, `lowering_mid_symbol_eq` (both 076/082),
`sobolevBesselWeight_mul` for `b_{r-s}·b_{t-s'} = b_{r'-s}·b_{t'-s'}` under `h`, the real
`conjW` step already in `inner_loweringMid_pairing`, and
`angularOrderLowering_eq_dilation_mid` + `LinearIsometryEquiv.inner_map_map` for the
transport.  The existing single-vector proof is the template; note 082's usage warning
about `rw` on a dependent order index (use `simp only [show … from by ring]`).

The sub-lane should also, in passing, apply the doc corrections F1–F5 to
`SL5_SPLIT.md` and the one stale sentence at `NonlinearPairing.lean:41–42`.

## 7. Merge

No blocker.  Merge as is; the corrections above are documentation and belong either
to a fixup commit on this lane or to the 5i sub-lane's first commit.
