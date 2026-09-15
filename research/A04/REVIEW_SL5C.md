# Review — lane 105, A04 unit G1, SL5 row 5c (`Section4/A04/NonlinearDatum.lean`)

Reviewer: opus reviewer for lane 105.  Date 2026-09-13.  Commit under review `3b04945`
(branch `erenup/105-A04-sl5c-column-data`, base `erenup/integration`).

## Verdict

**ACCEPT-WITH-NOTES.**  All four gates pass (build clean, module silent, five declarations on the
standard three axioms, `make check` green).  The statements are the paper's and are pinned the right
way (uniqueness, not choice).  The datum route in Part 1 is sound and **not** circular.  The three
notes below are all cosmetic / informational; none blocks the merge and none requires a code change
before merging.

Bonus result of check 2(d): **the whole of row 5h type-checks on top of this lane**, no `sorry`, in
~75 lines.  The full text is reproduced in §5 — the 5h lane can start from it.

## 1. Gates (commands and results)

All from the lane worktree `/data_8T/ping/blowup_density/.claude/worktrees/105-A04-sl5c-column-data`,
after `bash scripts/lean-install.sh` (exit 0, ends `== OK`), `. scripts/lean-env.sh`,
`export LEAN_NUM_THREADS=6`, lake from `verification/`.

| command | result |
|---|---|
| `lake build NSFormalization.Section4.A04.NonlinearDatum` | final line `Build completed successfully (9901 jobs).`  Only replayed upstream warnings (`Source/ViscosityPacket.lean:34` unused simp arg, `Paper3/SobolevDirectionalDerivative.lean:103` `SchwartzMap.smul_apply` deprecation) — both pre-existing, neither in this lane's files |
| `lake env lean ../formalization/NSFormalization/Section4/A04/NonlinearDatum.lean` | **printed nothing**, `EXIT=0` |
| `lake env lean ../research/A04/axioms_sl5c.lean` | 5 declarations, each `depends on axioms: [propext, Classical.choice, Quot.sound]`, `EXIT=0`.  Matches the transcript pasted in the file verbatim |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats' …/NonlinearDatum.lean` | no match (`rc=1`); same for `research/A04/axioms_sl5c.lean` (the `#print axioms` lines are the only `axiom` substring and live in `axioms_sl5c.lean`'s command names, which the grep of the module does not see) |
| `make check` | `EXIT=0`; `check_formalization_plan.py --check` clean, `test_contract_policy.py` 13 tests OK, `check_work_queue.py` "30 work items: ownership, contract registration and task cards consistent" |

Diff scope: 4 files, `+318/−8` — `Section4/A04/NonlinearDatum.lean` (new, 199 lines),
`research/A04/ATTEMPTS_SL5C.md`, `research/A04/axioms_sl5c.lean`, `research/A04/SL5_SPLIT.md` (rows 5c
and the frontier paragraph).  No registry file touched, no `Contracts/V1` or `Tests` touched.
A04 is already claimed by `erenup` from lanes 088/095/100/102, so the absence of a separate claim
commit is correct here.

## 2. Statement fidelity

### (a) `outerColumn_smoothL2` (:93) — the datum route is sound and non-circular

Hypothesis is `MemHInfty z` **alone**, which is literally
`ContDiff ℝ ∞ z ∧ ∀ m : ℕ, ∃ A, IsSobolevDatum (m:ℝ) z A`
(`Section4/A02/SolutionClass.lean:88`, the verbatim `Contracts.V1.Data.MemHInfty`).  Chain, read end
to end:

1. `hSL2 : A03.SmoothL2 z := ⟨hH.1, memHInfty_jets hH.1 hH.2⟩`.
   `D01.memHInfty_jets` (`Section4/D01/DatumToJets.lean:287`) has exactly the shape claimed:
   `ContDiff ℝ ∞ z → (∀ m : ℕ, ∃ A, IsSobolevDatum (m:ℝ) z A) → ∀ n : ℕ, MemLp (iteratedFDeriv ℝ n z) 2 volume`.
   `A03.SmoothL2` (`Section4/A03/SmoothJets.lean:60`) is `ContDiff ℝ ∞ · ∧ ∀ n, MemLp (iteratedFDeriv ℝ n ·) 2 volume`,
   so the anonymous constructor is right.
2. `A03.SmoothL2.memHmVector` (`Section4/A03/VectorTameProduct.lean:346`) turns that into
   `MemHmVector k z` for **every** `k` — its own proof is `⟨h.memLp, D01.sobolevENorm_ne_top_of_contDiff_memLp h.1 h.2 _⟩`,
   i.e. from `z`'s jets, nothing about the column.
3. `A04.exists_outerColumn_datum (max n 2) (le_max_right n 2) (memHmVector …) j`
   (`Section4/A04/NonlinearColumns.lean:70`) needs `2 ≤ m` and `MemHmVector m z`; its internal route is
   `A03.outerProductTame` / `le_columnsSobolevENorm` ⇒ `sobolevENorm (outerColumn z z j) ≠ ⊤` ⇒
   `A03.exists_sobolevDatum`.  **The column's data come from the tame product bound on `z`, never
   from the column's own jets** — this is the point at which circularity would have appeared, and it
   does not.
4. Orders `0,1` (below the row-5b threshold `2 ≤ m`) are reached by lowering from `max n 2` with
   `A04.isSobolevDatum_lowerVectorL` (`LaplacianAssembly.lean:219`) at `hle : (n:ℝ) ≤ ((max n 2 : ℕ):ℝ)`.
   Using the uniform `max n 2` for all `n` (rather than a `n < 2` case split) is correct because
   lowering from `k` to `k` is the identity direction, and it keeps the proof one branch.
5. `memHInfty_jets hcontdiff hdata` then gives the column's jets, and
   `A05.SmoothL2` (`Section4/A05/SmoothJets.lean:44`) has the same body, so
   `⟨hcontdiff, memHInfty_jets hcontdiff hdata⟩` is the conclusion directly.

Smoothness of the column: `outerColumn u v j = fun x => (u x j) • v x`
(`Section4/A03/OuterTameProduct.lean:68`), so `(contDiff_euclidean.mp hzc) j |>.smul hzc` is exactly
right — the coordinate projection `x ↦ z x j` is smooth, and `ContDiff.smul` against `z`.

Verdict on (a): **sound**.  It is also genuinely cheaper than REVIEW_SL5A F3's anticipated Leibniz
jet expansion, and it needs no `L^∞` factor.  Minimal hypothesis (`MemHInfty z`, not
`SmoothL2 z + MemHInfty z`) is the right call.

### (b) `isSobolevDatum_advection_sum` (:133) — the datum object, and where the rewrite lands

The datum is spelled `∑ j : Fin 3, derivDatumStep m j (B j)` with `derivDatumStep` **the one 088
defines** (`Section4/A04/LaplacianAssembly.lean:95`,
`WithLp.toLp 2 fun i => angularDirectionalDerivativeReal ((n:ℝ)+1) (coordinateVector j) (B i)`),
imported transitively (`NonlinearDatum` → `NonlinearColumns` → `LaplacianAssembly`).  No local copy,
no `castOrder` wrapper on the `Bⱼ` side.  Consequence for 5h: 088's `norm_sq_derivDatumStep` (:275),
`coe_derivDatumStep` (:240) and `directionalDerivative_orderLowering_comm` (:202) apply to this term
with no bridging — confirmed by actually running them in §5.

The per-column step is `isSobolevDatum_partialDeriv (Z := outerColumnField hH j) j m (hB j)`, and
`D01.isSobolevDatum_partialDeriv` (`Section4/D01/DerivativeDatum.lean:245`) outputs exactly
`WithLp.toLp 2 fun i => angularDirectionalDerivativeReal ((m:ℝ)+1) (coordinateVector j) (A i)`, i.e.
`derivDatumStep m j (B j)` by `rfl` — the `have key j : … (derivDatumStep m j (B j))` ascription is
legitimate defeq, not a coincidence.

**Where the rewrite happens.**  Line 173 is
`rw [advection_eq_sum_partialDeriv_outerColumn hdiff hdiv, Fin.sum_univ_three]`.
The first rewrite replaces the **field** `(fun x => advection u t x)` by
`fun x => ∑ j, partialDeriv j (outerColumn … j) x` (lane 100's identity is an identity of `Space`
fields, `AdvectionDivergence.lean:76`).  The second, `Fin.sum_univ_three`, cannot fire on the field
sum — that sum sits under `fun x =>` and depends on the bound `x`, so `rw`'s motive would not
typecheck — so it necessarily lands on the **datum** sum, re-associating
`∑ j, derivDatumStep m j (B j)` into `d₀ + d₁ + d₂`.  That is a re-association of the *same* term, not
a substitution of a different datum.  The field side is reconciled separately and explicitly by
`hfield` (:164–171, `funext x; rw [Fin.sum_univ_three]; rfl`) applied to `h012`.  So: **the lane-100
rewrite is on the field; the datum is never changed, only re-associated.**  Correct.

Folding uses `D01.isSobolevDatum_add` (`ForceClass.lean:261`, the `SchwartzPairable` version, as in
088) with pairability from `schwartzPairable_of_isSobolevDatum (Nat.cast_nonneg m)` and continuity of
each `∂ⱼWⱼ` from `((outerColumnField hH j).directionalField (coordinateVector j)).smooth.continuous`
— the identical pattern to 088's `isSobolevDatum_laplacian` (:151-153).

Note the lemma is stated for **all** `m : ℕ` (no `2 ≤ m`), strictly more general than the SL5 regime.
Good.

### (c) `advection_slice_datum_eq` (:183) — hypothesis shape and pinning

`hN : IsSobolevDatum (m : ℝ) (fun x => advection w.velocity t x) N` is **character-for-character**
`momentum_datum`'s `hN` (`Section4/A04/MomentumDatum.lean:177`).  `N` is an implicit variable
constrained only by `hN`; the conclusion `N = ∑ j, derivDatumStep m j (B j)` is closed by
`exact isSobolevDatum_unique hN hmain` (:197), where
`D01.isSobolevDatum_unique` (`ForceClass.lean:286`) proves `A = B` from two data of the same field via
`angularRealization_injective`.  **No `Classical.choice` on `N`, no `∃`-elimination.**  A wrong
implementation cannot satisfy this: the only way to inhabit the conclusion is to be the datum, and
data are unique.  The three axioms in the audit confirm nothing exotic slipped in.

Hypothesis discharge is honest: `C01.velocity_slice_memHInfty w ht` (`Section4/C01/VelocityJets.lean:77`),
`D01.contDiff_slice w.velocity_smooth ht` (`DatumToJets.lean:366`) for differentiability, and
`w.divergence t ht` for solenoidality.

Paper anchor: `paper/sections/appendix-a-local-theory.tex:132` eq:Rhigh — this row produces the `N`
that enters the `−⟪G,N⟫` term of that estimate.  Nothing in the Lean statements over- or under-claims
relative to it.

### (d) 5h closes — see §5

## 3. Consistency

* Imports are the three canonical in-tree modules (`A04.NonlinearColumns`, `A04.AdvectionDivergence`,
  `C01.VelocityJets`).  No `Contracts.*` involvement, so the contract import policy does not apply;
  `check_contracts.py` via `make check` is green anyway.
* **No restated definitions.**  `outerColumn`/`partialDeriv` are A03's, `derivDatumStep`/
  `isSobolevDatum_lowerVectorL`/`castOrder` are 088's, `lowerVectorL` is `D01/HalfOrder.lean:103`,
  `SmoothL2Field` is the vendor's (`vendor/NavierStokesAndEuler/Euler/LpSmoothField.lean:31`, fields
  `field`/`smooth`/`integrable` — the constructor at :113-114 matches).
* `outerColumnField` is the only new `def`, as expected, with the `rfl` bridge `outerColumnField_field`
  (`@[simp]`).  Correct discipline.
* **No second copy of 088's template.**  There is deliberately no `advectionDatum` definition mirroring
  `laplacianDatum`; the sum is inlined.  That is the better choice — 088's `norm_sq_derivDatumStep`
  and `coe_derivDatumStep` then apply to `derivDatumStep m j (B j)` directly (verified in §5), with no
  unfolding step for 5h.

## 4. Honesty of `ATTEMPTS_SL5C.md`

Opened all three cited declarations and checked the negative claim.

* `A02/SolutionClass.lean:88` `MemHInfty` — **correct line, correct body.**
* `A03/VectorTameProduct.lean:346` `SmoothL2.memHmVector` — **correct line, correct statement.**
* `D01.memHInfty_jets` — cited as `DatumToJets.lean:298` in both `ATTEMPTS_SL5C.md` and the module
  header (:33).  The actual declaration is at **`DatumToJets.lean:287`**; 298 is inside
  `memHInfty_iff_smoothSquareIntegrableJets`.  See finding N3.
* The key negative claim — *"no reusable `smooth bounded scalar × SmoothL2 ∈ SmoothL2` closure exists
  in the tree"* — **verified**:
  * `vendor/NavierStokesAndEuler/Euler/LpSmoothFieldAlgebra.lean` (153 lines) contains only
    `jetPostcompose` (:20), `mapField` (:24, postcompose by a **continuous linear** map), `addField`
    (:47), `zeroField` (:72), `directionalField` (:94) and continuity lemmas.  No multiplicative or
    `smul`-by-a-function closure at all.
  * `Section4/A05/SmoothJets.lean` closure API is `fderiv` (:60), `clm` (:68, again a CLM), `dir`
    (:94).  Its only `smul` occurrence is `MemLp.const_smul … (‖L‖ : ℝ)` inside `clm` — a **constant**,
    not a function factor.
  * `Section4/A03/SmoothJets.lean` has no closure lemma beyond `SmoothL2.upTo`.
  * grep for `SmoothL2.*smul` / `smul.*SmoothL2` over `A03/` and `A05/` returns nothing.
  So the F3 route really would have needed new analysis, and the datum route really did avoid it.
  The claim is honest, not a shortcut excuse.
* The two "failed / rejected" entries (the `set z := …` abandonment, the redundant `SmoothL2 z`
  hypothesis) are consistent with the final code: the module does spell `fun y => u (t, y)` out
  everywhere, and `isSobolevDatum_advection_sum` does take only `MemHInfty`.
* The recorded command transcript matches mine except the job count (`9900` vs my `9901`) — an
  incremental-build artefact, not a discrepancy.

## 5. Findings

| # | severity | location | finding | fix |
|---|---|---|---|---|
| **N1** | low (non-blocking) | `NonlinearDatum.lean:138` | `hdiff : ∀ x, DifferentiableAt ℝ (fun y => u (t,y)) x` is **redundant**: `hH : MemHInfty (fun x => u (t,x))` already carries `ContDiff ℝ ∞`, from which `hdiff` follows.  The corollary at :192-196 therefore derives the same smoothness twice (once as `hcd` via `contDiff_slice`, once inside `hH`). | Optional, in a later lane: drop `hdiff` and use `fun x => (hH.1.differentiable (by simp)).differentiableAt` internally; `advection_slice_datum_eq` then loses its `hcd` line.  Do **not** hold the merge for this — the extra hypothesis makes the lemma no harder to apply. |
| **N2** | cosmetic | `NonlinearDatum.lean:113-114` | `outerColumnField` calls `outerColumn_smoothL2 hH j` twice (once per structure field). | Harmless (a `Prop`, so proof-irrelevant); mention only.  A `let h := outerColumn_smoothL2 hH j` would read better. |
| **N3** | low (citation drift) | `NonlinearDatum.lean:33` and `ATTEMPTS_SL5C.md` ("`DatumToJets.lean:298`") | `memHInfty_jets` is at `DatumToJets.lean:287`, not 298. | One-character-class fix whenever the file is next touched; not worth a rebuild on its own. |
| **N4** | informational | `NonlinearDatum.lean:185` vs `MomentumDatum.lean:174` (`Ioo`) | `advection_slice_datum_eq` takes `ht : t ∈ Ico (0:ℝ) T`; `momentum_datum` supplies `ht : t ∈ Ioo (0:ℝ) T`. | The 5h lane inserts `⟨le_of_lt ht.1, ht.2⟩`.  Already accounted for in the §6 brief. |

No finding of substance.  Nothing to fix before merge.

## 6. Brief for the 5h lane

**Target** (`hnl` of `A04.inner_energy_assembly`, `Section4/A04/HighEnergy.lean:106`, at
`NLbound = gradientSobolevNormAt (m:ℝ) u t * (outerSobolevENorm (m:ℝ) z z).toReal`):

```
- ⟪G, N⟫ ≤ gradientSobolevNormAt (m:ℝ) u t
            * (outerSobolevENorm (m:ℝ) (fun y => u (t,y)) (fun y => u (t,y))).toReal
```

**Inputs, with file:line.**

| role | declaration | location |
|---|---|---|
| 5c, the datum identification | `advection_slice_datum_eq` / `isSobolevDatum_advection_sum` | `Section4/A04/NonlinearDatum.lean:183` / `:133` |
| 5b, the order-`(m+1)` column data | `exists_outerColumn_datum_succ` | `Section4/A04/NonlinearColumns.lean:89` |
| 5d.amb, skew-adjointness (per component) | `real_inner_angularDirectionalDerivative` | `Section4/A04/RealPairing.lean:84` (`NSFormalization.Paper3`) |
| 5d.amb, summed form | `sum_real_inner_angularDirectionalDerivative` | `Section4/A04/NonlinearPairing.lean:163` |
| 5e, discrete Cauchy–Schwarz | `sum_inner_le_sqrt_mul_sqrt` (and `abs_…`) | `Section4/A04/NonlinearPairing.lean:130` / `:143` |
| 5i, two-vector lowering transfer | `real_inner_lowering_transfer` | `Section4/A04/NonlinearPairing.lean:108` (`NSFormalization.Paper3`) |
| 5f.grad, slice form | `sqrt_sum_norm_sq_derivDatumStep_eq_slice` | `Section4/A04/NonlinearColumns.lean:120` |
| 5g.outer | `sqrt_sum_norm_sq_columnData_eq` | `Section4/A04/NonlinearColumns.lean:166` |
| `Λ` past `D` | `directionalDerivative_orderLowering_comm` | `Section4/A04/LaplacianAssembly.lean:202` |
| `Λ_{s→s} = id` | `angularOrderLowering_self` | `Section4/A04/RealPairing.lean:157` (`NSFormalization.Paper3`) |
| datum lowering + its coercion | `isSobolevDatum_lowerVectorL`, `coe_lowerVectorL` | `Section4/A04/LaplacianAssembly.lean:219` / `:227` |
| `derivDatumStep` coercion | `coe_derivDatumStep` | `Section4/A04/LaplacianAssembly.lean:240` |
| subtype ↔ ambient inner product | `realSobolev_inner_eq_ambient` | `Section4/A04/RealPairing.lean:77` (`NSFormalization.Paper3`) |
| uniqueness | `isSobolevDatum_unique` | `Section4/D01/ForceClass.lean:286` |
| `lowerVectorL` | — | `Section4/D01/HalfOrder.lean:103` |

Namespaces to open (they are **not** all in `A04`): `NSFormalization.Paper3` carries
`real_inner_angularDirectionalDerivative`, `real_inner_lowering_transfer`,
`angularOrderLowering_self`, `realSobolev_inner_eq_ambient`, `RealVectorSobolev`,
`angularDirectionalDerivative`, `angularOrderLowering`; `NSFormalization.Source.RealSobolev` carries
`RealSobolevHilbert` and `FourierData`; `directionalDerivative_orderLowering_comm`,
`coe_derivDatumStep`, `coe_lowerVectorL`, `derivDatumStep` are in `NSFormalization.Section4.A04`.
(Each of these cost me a failed elaboration; the list is exact.)

**Order reconciliations.**  Three, and only three:

1. `G = lowerVectorL ((m:ℝ)+1) (m:ℝ) _ A'` — `isSobolevDatum_unique hG (isSobolevDatum_lowerVectorL … hA')`,
   then componentwise on the ambient carrier by `coe_lowerVectorL`.
2. `Cⱼ := lowerVectorL ((m:ℝ)+1) (m:ℝ) _ (Bⱼ)` is the order-`m` column datum — `isSobolevDatum_lowerVectorL … (hB j)`.
3. `Dⱼ (Λ_{m+1→m} A'ᵢ) = Λ_{m→m−1} (Dⱼ A'ᵢ)` — `directionalDerivative_orderLowering_comm` at
   `σ = σ' = s = (m:ℝ)+1`, `r = (m:ℝ)`; then `real_inner_lowering_transfer` at
   `(s,s',r,t,r',t') = ((m:ℝ)+1−1, (m:ℝ)+1, (m:ℝ)−1, (m:ℝ)+1, (m:ℝ), (m:ℝ))`, whose side condition
   `r + t = r' + t'` is `(m−1)+(m+1) = m+m`, closed by `ring`.  The `(m:ℝ)+1−1 = (m:ℝ)` normalisation
   needs an explicit `simp only [show (m:ℝ)+1−1 = (m:ℝ) from by ring] at htr ⊢`.

**Verified skeleton.**  The following compiles as written — `lake env lean /tmp/sl5h/full.lean`
printed nothing, exit 0, no `sorry`, no `maxHeartbeats` bump.  Sizes: 16 / 11 / 32 lines.

```lean
theorem inner_component_advection (m : ℕ) (e : Space)
    (Gi A'i Bi : Lp ℂ 2 (volume : Measure Space))
    (hG : Gi = angularOrderLowering ((m : ℝ) + 1) (m : ℝ) (by linarith) A'i) :
    (inner ℝ Gi (angularDirectionalDerivative ((m : ℝ) + 1) e Bi) : ℝ)
      = - (inner ℝ (angularDirectionalDerivative ((m : ℝ) + 1) e A'i)
            (angularOrderLowering ((m : ℝ) + 1) (m : ℝ) (by linarith) Bi) : ℝ) := by
  rw [real_inner_angularDirectionalDerivative ((m : ℝ) + 1) e Gi Bi]
  congr 1
  rw [hG, directionalDerivative_orderLowering_comm ((m : ℝ) + 1) ((m : ℝ) + 1) ((m : ℝ) + 1)
    (m : ℝ) e (by linarith) (by linarith) A'i]
  have htr := real_inner_lowering_transfer ((m : ℝ) + 1 - 1) ((m : ℝ) + 1) ((m : ℝ) - 1)
    ((m : ℝ) + 1) (m : ℝ) (m : ℝ) (by ring) (by linarith) (le_refl _) (by linarith) (by linarith)
    (angularDirectionalDerivative ((m : ℝ) + 1) e A'i) Bi
  rw [angularOrderLowering_self] at htr
  simp only [show (m : ℝ) + 1 - 1 = (m : ℝ) from by ring] at htr ⊢
  rw [angularOrderLowering_self] at htr
  exact htr

theorem inner_datum_advectionDir (m : ℕ) (j : Fin 3)
    {G : RealVectorSobolev (m : ℝ)} {A' B : RealVectorSobolev ((m : ℝ) + 1)}
    (hGA' : ∀ i, ((G i : RealSobolevHilbert (m : ℝ)) : Lp ℂ 2 (volume : Measure Space))
      = angularOrderLowering ((m : ℝ) + 1) (m : ℝ) (by linarith)
          ((A' i : Lp ℂ 2 (volume : Measure Space)))) :
    (inner ℝ G (derivDatumStep m j B) : ℝ)
      = - (inner ℝ (derivDatumStep m j A')
            (lowerVectorL ((m : ℝ) + 1) (m : ℝ) (by linarith) B) : ℝ) := by
  rw [PiLp.inner_apply, PiLp.inner_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [realSobolev_inner_eq_ambient, realSobolev_inner_eq_ambient, coe_derivDatumStep,
    coe_derivDatumStep, coe_lowerVectorL, hGA']
  exact inner_component_advection m (coordinateVector j) _ _ _ rfl

theorem sl5h_full {u : SpaceTimeField} {t : ℝ} (m : ℕ)
    (hsl : NSFormalization.Section4.A05.SmoothL2 (fun x => u (t, x)))
    {G : RealVectorSobolev (m : ℝ)} {A' : RealVectorSobolev ((m : ℝ) + 1)}
    (hG : IsSobolevDatum (m : ℝ) (fun x => u (t, x)) G)
    (hA' : IsSobolevDatum ((m : ℝ) + 1) (fun x => u (t, x)) A')
    {B : Fin 3 → RealVectorSobolev ((m : ℝ) + 1)}
    (hB : ∀ j, IsSobolevDatum ((m : ℝ) + 1)
      (outerColumn (fun y => u (t, y)) (fun y => u (t, y)) j) (B j))
    {N : RealVectorSobolev (m : ℝ)}
    (hN : N = ∑ j : Fin 3, derivDatumStep m j (B j)) :
    - (inner ℝ G N : ℝ)
      ≤ gradientSobolevNormAt (m : ℝ) u t
        * (outerSobolevENorm (m : ℝ) (fun y => u (t, y)) (fun y => u (t, y))).toReal := by
  have hle : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
  set C : Fin 3 → RealVectorSobolev (m : ℝ) :=
    fun j => lowerVectorL ((m : ℝ) + 1) (m : ℝ) hle (B j) with hCdef
  have hC : ∀ j, IsSobolevDatum (m : ℝ)
      (outerColumn (fun y => u (t, y)) (fun y => u (t, y)) j) (C j) :=
    fun j => isSobolevDatum_lowerVectorL ((m : ℝ) + 1) (m : ℝ) hle (hB j)
  have hGeq : G = lowerVectorL ((m : ℝ) + 1) (m : ℝ) hle A' :=
    isSobolevDatum_unique hG (isSobolevDatum_lowerVectorL ((m : ℝ) + 1) (m : ℝ) hle hA')
  have hGA' : ∀ i, ((G i : RealSobolevHilbert (m : ℝ)) : Lp ℂ 2 (volume : Measure Space))
      = angularOrderLowering ((m : ℝ) + 1) (m : ℝ) hle
          ((A' i : Lp ℂ 2 (volume : Measure Space))) := by
    intro i; rw [hGeq, coe_lowerVectorL]
  have hIBP : - (inner ℝ G N : ℝ)
      = ∑ j : Fin 3, (inner ℝ (derivDatumStep m j A') (C j) : ℝ) := by
    rw [hN, inner_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [inner_datum_advectionDir m j hGA', neg_neg]
  calc - (inner ℝ G N : ℝ)
      = ∑ j : Fin 3, (inner ℝ (derivDatumStep m j A') (C j) : ℝ) := hIBP
    _ ≤ Real.sqrt (∑ j : Fin 3, ‖derivDatumStep m j A'‖ ^ 2)
          * Real.sqrt (∑ j : Fin 3, ‖C j‖ ^ 2) :=
        sum_inner_le_sqrt_mul_sqrt Finset.univ _ _
    _ = gradientSobolevNormAt (m : ℝ) u t
          * (outerSobolevENorm (m : ℝ) (fun y => u (t, y)) (fun y => u (t, y))).toReal := by
        rw [sqrt_sum_norm_sq_derivDatumStep_eq_slice m hsl hA',
          sqrt_sum_norm_sq_columnData_eq m hC]
```

**Remaining goals for the 5h lane after pasting the above.**  The mathematics is done; what is left
is packaging, and it is small:

1. A `ClassicalSolutionR` slice corollary of `sl5h_full` — supply `hsl` from
   `C01.velocity_slice_smoothL2 w ht`, `hG`/`hA'` from the caller's datum path, `hB` from
   `exists_outerColumn_datum_succ` (needs `MemHmVector (m+1)` of the slice, available from
   `velocity_slice_smoothL2` + `A03.SmoothL2.memHmVector`), and `hN` from
   `advection_slice_datum_eq w m ht hN hB`.  Insert `⟨le_of_lt ht.1, ht.2⟩` for the `Ioo → Ico`
   conversion (finding N4).  **≈ 15 lines.**
2. Feeding it into `inner_energy_assembly` as `hnl`, alongside 088's `hlap`
   (`inner_datum_laplacian_le'`) and the pressure `hpr`.  **≈ 15 lines**, plus whatever the `hpr`
   (D01 obligation P2) status allows — that is the genuine remaining blocker of G1, not 5h.

Overall 5h: **S, not M** — ~75 lines of already-verified core plus ~30 of packaging.  The SL5_SPLIT
size estimate **M** can be revised down once this is pasted in.  `sqrt_sum_norm_sq_derivDatumStep_eq_slice`
and `sqrt_sum_norm_sq_columnData_eq` both applied first try; the only two places that fought back were
the `(m:ℝ)+1−1` normalisation and the namespace of the five `Paper3` lemmas, both solved above.

## 7. Recommendation

Merge as is.  Fold N1–N3 into whatever lane next touches `NonlinearDatum.lean` (most naturally the
5h lane, which will be editing the neighbourhood anyway).  The 5h lane should be briefed with §6 and
told that the analytic core already type-checks.
