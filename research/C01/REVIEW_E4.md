# REVIEW — lane 150-C01-e4-assembly (row E4 + row `energyIdentity`)

Reviewer run 2026-09-14 (relaunch after the router-429 kill of the first reviewer), worktree
`.claude/worktrees/150-C01-e4-assembly`, branch `erenup/150-C01-e4-assembly`, HEAD `6c2de7f`
(unchanged).  Read-only: no Lean edited, no git state touched.  Probes reused from the killed
run: `research/C01/probes/rev150_{defeq,gap,mutation}.lean` (all three re-run here).  Probes
new: `research/C01/probes/rev150b_{gradientsq,hardened,ioo}.lean`.

## Verdict: **ACCEPT-WITH-NOTES**

Both target statements are token-equivalent to `REVIEW_E4B.md` §4's prescription, all five
declarations carry exactly the standard three axioms, the module emits **zero** warnings of its
own, the `energyIdentity_classical_unconditional` value is character-for-character
`energyIdentity_classical`'s conclusion and is the paper's energy identity, five mutations break
(three by script, two by a hardened `HasDerivAt.unique` consequence), and one further mutation
(`Ioo`→`Ico`) confirms the interior guard is load-bearing.  Four notes, none blocking; two are
citation line numbers, one is a paper-label mislabel, one is the strictly-nicer statement the
gap probe shows is already reachable inside `formalization/`.

---

## 1. What the lane claims

Row **E4** of `research/C01/ENERGY_SPLIT.md` and, through it, the row `energyIdentity` payoff:

* `energyDerivative_hasDerivAt` — on a window `[c,S] ⊂ (0,T)` of a classical solution
  `w : ClassicalSolutionR ν a f T` with `hf : MemForceR f`, the `L²` energy of the velocity,
  re-indexed by the `+c` shift and clamped to `[0,S]`, is differentiable at every interior
  `r ∈ Ioo 0 (S−c)` with derivative `2⟪u(r+c,·), ∂ₜu(r+c,·)⟫_{L²}` — the exact `hd` slot of
  `energyIdentity_classical` (`MomentumCarrierB.lean:254-258`).
* `energyIdentity_classical_unconditional` — the raw-integral energy identity as a genuine
  `HasDerivAt` at **every** interior time, no side hypothesis beyond `w`, `hf`, `t ∈ Ioo 0 T`.
* Supporting: `wordEnergy_zero`, `wordInner_sum_zero` (the vendor's `s = 0` word bridges, which
  do not exist upstream), `velocity_hasDerivAt_time` (the unconditional pointwise `hd` seed).

## 2. What is in Lean

`formalization/NSFormalization/Section4/C01/EnergyDerivative.lean`, 210 lines, namespace
`NSFormalization.Section4.C01`, **5** declarations (`:42`, `:48`, `:57`, `:80`, `:154`), two
imports (`…C01.PressureJetPath`, `Euler.OrdinaryWordTime`).  No `sorry/admit/axiom/
native_decide/maxHeartbeats`, and — unlike lane 148 — **no `set_option` at all** (grep, §6).

### 2.1 Item 1 — `energyDerivative_hasDerivAt` is token-equivalent to the prescription — PASS

`REVIEW_E4B.md` §4's code block vs `EnergyDerivative.lean:80-97`: identical binder list in
identical order (`(w) (hf) (hc : 0 < c) (hcS : c ≤ S) (hST : S < T) {r : ℝ}
(hr : r ∈ Ioo (0:ℝ) (S − c))`), identical function
`fun ρ : ℝ => ‖(velocityField w hST ⟨(projIcc (0:ℝ) (S−c) _ ρ).1 + c, _⟩).toLp‖ ^ 2`, identical
value `2 * ⟪(velocitySliceField w (Ioo_subset_Ico_self (mem_Ioo_of_mem_Icc hc hST _))).toLp,
(temporalSliceField w hf (mem_Ioo_of_mem_Icc hc hST _)).toLp⟫`, identical point `r`.  Three
cosmetic differences, none a change of statement:

* the `0 ≤ S − c` slot is `sub_nonneg.mpr hcS` where §4 wrote `(by linarith)` — a `Prop`,
  proof-irrelevant;
* the two `r + c ∈ Icc c S` memberships are spelled `show r + c ∈ Icc c S from ⟨…,…⟩` where §4
  wrote `⟨by linarith, by linarith⟩` — same `Prop`;
* `⟪…⟫_ℝ` → `⟪…⟫`.  Verified this is not a weakening: `research/C01/probes/rev150_defeq.lean:20-21`
  prints `fun X Y => ⟪X.toLp, Y.toLp⟫ : SmoothL2Field Space → SmoothL2Field Space → ℝ`, i.e. the
  scoped `RealInnerProductSpace` `⟪·,·⟫` is `inner ℝ`, which is what both the vendor value and
  `energyIdentity_classical`'s `hd` use.  (`ATTEMPTS_E4.md:102-104` records that `⟪…⟫_ℝ` simply
  is not a notation here.)

**Vendor call.**  `Euler/OrdinaryWordTime.lean:69-75` is the `variable` block
`(T) (hT : 0 ≤ T) (A B : Icc 0 T → SmoothL2Field Space) (hA) (hB) (hd)`, pulled into
`wordEnergy_hasDerivWithinAt (s : ℕ) (t : Icc 0 T)` at **`:87`** by `include hA hB hd in` at
`:86`.  The lane's call (`:135`) `wordEnergy_hasDerivWithinAt (S − c) hT' A B hA hB hd 0
⟨r, hr.1.le, hr.2.le⟩` matches that order exactly.  Each clause:

* `hA` (`:113-114`) = `(velocityField_jetLp_continuous w hST n).comp hιvel`, with
  `velocityField_jetLp_continuous` at `Evolution.lean:164` (signature `(u) (hST : S < T) (n : ℕ)`,
  conclusion `Continuous (fun t : Icc 0 S => (velocityField u hST t).jetLp n)`) and
  `hιvel : Continuous ιvel`, `ιvel : Icc 0 (S−c) → Icc 0 S`, `ρ ↦ ⟨ρ.1 + c, _⟩`.  ✅
* `hB` (`:115-116`) = `(temporalSlicePath_jetLp_continuous w hf hc hST n).comp hσ`.  Lane 148's
  theorem is at `PressureJetPath.lean:286-291` and its binders really are `(w) (hf) (hc : 0 < c)
  (hST : S < T) (n)` — the `hcS` that review 148 N1 called inert **was** dropped before merge, so
  the lane's call site is correct.  ✅
* `hd` (`:118-133`) has the vendor's exact shape `∀ t (ht : t ∈ Ioo 0 (S−c)) x, HasDerivAt
  (fun ρ => (A (projIcc 0 (S−c) hT' ρ)).field x) ((B ⟨t, ht.1.le, ht.2.le⟩).field x) t`.  Its
  three sub-steps are the ones §4 item 3 prescribed: `velocity_hasDerivAt_time w htc x` at
  `t + c ∈ Ioo 0 T` (`htc` needs `0 < c` and `S < T`, both used); the `+c` chain rule
  `(hasDerivAt_id t).add_const c` fed through **`HasDerivAt.scomp`** (not `.comp` — the velocity
  is `Space`-valued; `ATTEMPTS_E4.md:86-100` records the two failed `comp`/instance-diamond
  attempts, both re-checkable); `rw [one_smul]`; then `congr_of_eventuallyEq` on
  `isOpen_Ioo.mem_nhds ht` undoing the `projIcc` clamp by `projIcc_of_mem`.  ✅
* the `s = 0` collapse `simp only [Nat.zero_add, wordEnergy_zero, wordInner_sum_zero]` and
  `hderiv.hasDerivAt (Icc_mem_nhds hr.1 hr.2)`.  ✅

**Item 6's `rfl` identification — verified by probe, and it holds at the whole-record level.**
`research/C01/probes/rev150_defeq.lean` examples (A) and (B) (exit 0):

```lean
velocityField w hST ⟨r + c, _⟩ = velocitySliceField w (Ioo_subset_Ico_self (mem_Ioo_of_mem_Icc hc hST _)) := rfl
(velocityField w hST ⟨r + c, _⟩).toLp = (velocitySliceField w _).toLp := rfl
```

so no `jetLp_congr`/`Lp.ext` bridge is hidden in the final `exact`; the lane's ATTEMPTS claim is
honest.  Probe (D) additionally checks the *function* is the intended one:
`(velocityField w hST ⟨(projIcc 0 (S−c) _ ρ).1 + c, _⟩).field = fun x => w.velocity (ρ + c, x)`
at interior `ρ` — i.e. the statement really is `ρ ↦ ‖u(ρ+c,·)‖²_{L²}`, not a clamped impostor.

### 2.2 Item 2 — `wordEnergy_zero` / `wordInner_sum_zero` — PASS, and the vendor really lacks them

`grep -rn 'wordEnergy_zero' vendor/NavierStokesAndEuler/` → **no hits**; `OrdinarySmoothWords.lean`
carries only `wordEnergy` (`:94-95`), `wordEnergy_nonneg`, `norm_toLp_sq_le_wordEnergy`,
`wordBound_sqrt`.  Review 148's N3 stands.  Both lane lemmas are real proofs, not restatements:

* `wordEnergy 0 A = ‖A.toLp‖ ^ 2` (`:42-44`) — `wordEnergy s A = ∑ n ∈ range (s+1), ∑ w : Fin n → Fin 3,
  ‖(wordField A w).toLp‖^2` (`OrdinarySmoothWords.lean:94-95`), so at `s = 0` the outer sum is the
  singleton `range 1` and the inner index is `Fin 0 → Fin 3`, a singleton type; `wordField_zero`
  (`:35-36`, `rfl`) collapses the summand.  `simp [wordEnergy, wordField_zero]` closes it.
* `wordInner_sum_zero` (`:48-51`) — the same collapse on the vendor's *value*.  The lane's
  `Nat.zero_add` prepend in the `simp only` at `:136` is genuinely needed (`ATTEMPTS_E4.md:106-109`):
  the vendor value is over `range (0+1)`, not `range 1`.
* Name hygiene: `grep -rn 'wordEnergy_zero|wordInner_sum_zero' formalization/ vendor/` outside this
  module → **no hits**, so the LESSONS-109 `Ambiguous term` hazard (a name living in both an
  `open`ed vendor namespace and the local one) does not arise.

### 2.3 Item 3 — `velocity_hasDerivAt_time` — PASS, unconditional, interior handled correctly

`:57-68`.  `ClassicalSolutionR.velocity_smooth : ContDiffOn ℝ ∞ velocity (Ico 0 T ×ˢ univ)`
(`A02/SolutionClass.lean:122`) is the *only* input; no `2 ≤ m`, no `ContDiffOn G`.  The block is a
verbatim re-proof of the `hvelx` inside `A04.timeDeriv_isSobolevDatum`
(`Section4/A04/TimeDerivative.lean:**194-205**`, the theorem itself at `:181`, carrying
`hm : 2 ≤ m` at `:183` and `hGc : ContDiffOn ℝ ∞ G (Ico 0 T)` at `:186` — neither available from
`ClassicalSolutionR`, whose `sobolev` field gives only `ContinuousOn G`), so review 148's N4 is
correctly discharged rather than worked around.

Interior handling is right and load-bearing: `hcd.differentiableOn` is evaluated at
`Ioo_subset_Ico_self hs` (lands in `Ico`), and the upgrade to `DifferentiableAt` uses
`Ico_mem_nhds hs.1 hs.2`, which needs the **strict** `0 < s`.  `t = 0` is therefore genuinely
excluded, as it must be (one-sided smoothness at `0` gives no two-sided derivative).

`temporalDerivative` resolves uniquely: `grep -rn 'def temporalDerivative' formalization/ vendor/`
→ exactly one hit, `vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:55`
(`fderiv ℝ (fun s => u (s,x)) t 1`); no `alias`/`abbrev` anywhere; and
`#check @temporalDerivative` under `set_option pp.fullNames true`
(`rev150_defeq.lean:17-18`) prints the single `NavierStokes.ProblemStatement.temporalDerivative`.
LESSONS-109 clear.  Probe (E) also confirms `temporalDerivative w.velocity s x =
deriv (fun ρ => w.velocity (ρ,x)) s` is `rfl`, which is why the lane's `exact` closes with the
`temporalDerivative` spelling while `.hasDerivAt` produced the `deriv` one.

### 2.4 Item 4 — `energyIdentity_classical_unconditional` — PASS on all three counts

`:154-208`.  Window `c := t/2`, `S := (t+T)/2` (so `S − c = T/2` and `r + c = t` at
`r := t − t/2`); `hg.comp t ((hasDerivAt_id t).sub_const (t/2))` transports the point; the value's
slice times are moved by `field_ext` on a plain field equation (`EulerOrdinarySobolev.field_ext`,
`OrdinarySmoothWords.lean:25`, legitimate because `SmoothL2Field`'s other two fields are `Prop`s),
avoiding a dependent-motive rewrite.

**(a) The `projIcc` is the identity near `t`, so this is the derivative of the real energy.**
The final `congr_of_eventuallyEq` (`:196-208`) works on `Ioo (t/2) ((t+T)/2) ∈ 𝓝 t` (nonempty
around `t` because `0 < t < T`), where both `projIcc`s reduce by `projIcc_of_mem`.  Decisively,
`research/C01/probes/rev150_gap.lean` (exit 0, 0 bytes) upgrades the statement to the **globally
correct** function with no clamp at all:

```lean
theorem rev150_energyIdentity_l2Sq (w) (hf) {t} (ht : t ∈ Ioo (0:ℝ) T) :
    HasDerivAt (fun s : ℝ => l2Sq (slice w.velocity s))
      (-2 * ν * (∫ x, ∑ i : Fin 3, ‖fderiv ℝ (slice w.velocity t) x (coordinateVector i)‖ ^ 2)
        + 2 * (∫ x, (inner ℝ (slice w.velocity t x) (slice f t x) : ℝ))) t
```

proved from the lane's theorem by `congr_of_eventuallyEq` + `projIcc_of_mem` +
`Vocabulary.norm_toLp_sq_eq_l2Sq` in 8 lines.  So the clamp is cosmetic, not a hedge.

**(b) The value is exactly `energyIdentity_classical`'s conclusion.**  Character-for-character
identical to `MomentumCarrierB.lean:258-261`; and the lane does not merely *restate* it, it feeds
`energyIdentity_classical w hf ht (d := 2 * ⟪…⟫) rfl` at `:191-193` — the `rfl` pins `d` to the
E4 value, so the `hd` slot cannot be satisfied by anything weaker (cf. `REVIEW_E3E4.md:183-184`,
"`hd` is not an escape hatch").

**(c) Mathematically this is the paper's energy identity.**  The paper displays the identity at
`paper/sections/02-preliminaries.tex:136-139`,
`½(‖U(t)‖₂²)' + ν‖∇U(t)‖₂² = ⟨F(t),U(t)⟩`, i.e. `(‖u‖₂²)' = −2ν‖∇u‖₂² + 2⟨u,f⟩`; `04-whole-space.tex:117`
invokes it ("The separate ordinary energy identity, with regularized norm division") as the input
to eq:RL2 at `:118-119`.  The lane's value is exactly that, with `‖∇u‖₂²` in the **Frobenius**
reading the paper intends: `fderiv ℝ u x (axis i) ∈ Space`, so
`∑ᵢ ‖fderiv ℝ u x (axis i)‖² = ∑ᵢⱼ |∂ᵢuⱼ(x)|²`, integrated — the same quantity
`Contracts/V1/Data.lean:448-454` documents as "deliberately *not* the operator norm".

**Is `PiLp.norm_sq_eq_of_L2` the only step to the contract's `gradientSq`?  Yes** — checked on
the `verification` side with the real `Contracts.V1` objects, `research/C01/probes/rev150b_gradientsq.lean`
(exit 0, 0 bytes):

```lean
theorem gradientTensor_normSq (z : SpatialField) (x : Space) :
    ‖gradientTensor z x‖ ^ 2 = ∑ i : Fin 3, ‖fderiv ℝ z x (coordinateVector i)‖ ^ 2 := by
  rw [gradientTensor, spatialGradient, PiLp.norm_sq_eq_of_L2]; rfl
theorem gradientSq_eq_raw (z : SpatialField) :
    (∫ x, ‖gradientTensor z x‖ ^ 2) = ∫ x, ∑ i : Fin 3, ‖fderiv ℝ z x (coordinateVector i)‖ ^ 2 :=
  integral_congr_ae (Filter.Eventually.of_forall (gradientTensor_normSq z))
```

The trailing `rfl` absorbs `spatialDerivative (lift z) 0 x = fderiv ℝ z x` and
`gradientTensor = spatialGradient ∘ lift`; `axis i = coordinateVector i` is `rfl`
(`rev150_defeq.lean:40`).  This confirms `REVIEW_E3E4.md:205-220` and `REVIEW_E2.md` §2.

### 2.5 Consistency with siblings and records — PASS

`ENERGY_SPLIT.md`'s two edited rows (E4, `energyIdentity`) describe exactly what landed, including
the honest residue ("the single `gradientSq`/`pairing` vocabulary step … a `verification` Bindings
lane, not a `formalization` proof").  `ATTEMPTS_E4.md`'s five failed approaches are specific enough
to be checkable and none is a face-saving paraphrase; the `Nat.zero_add` and `scomp` entries are
corroborated by the module's own code.  No declaration duplicates a sibling; the five new names are
tree-unique.

## 3. Notes (none blocking)

### N1 (low, citation) — the module's vendor line number is off by 7

`EnergyDerivative.lean:14` cites `EulerOrdinarySobolev.wordEnergy_hasDerivWithinAt` as
`Euler/OrdinaryWordTime.lean:80`.  Line 80 is inside the *previous* theorem
(`ordinaryWord_hasDerivWithinAt`, `:78-84`); `wordEnergy_hasDerivWithinAt` is at **`:87`** (with its
`variable` block at `:69-75` and `include` at `:86`).  LESSONS 09-14 ("论文/vendor 行号引用会代代相传"):
*one-line fix:* `:80` → `:87` at `EnergyDerivative.lean:14`.

### N2 (low, citation) — the ATTEMPTS pointer to the `hvelx` block is off by 3

`ATTEMPTS_E4.md:37` cites `TimeDerivative.lean:197-206`; the block is `:194-205` (the theorem opens
at `:181`).  *One-line fix:* `197-206` → `194-205`.

### N3 (low, paper label) — "eq:RL2" names the wrong display

`EnergyDerivative.lean:24` ("the raw-integral form of `eq:RL2`") and `:139` ("**Row `energyIdentity`
(eq:RL2), the raw-integral form**") attach the label `eq:RL2` to the *identity*.  `eq:RL2`
(`04-whole-space.tex:118-119`) is `‖u(t)‖₂ ≤ ‖a‖₂ + ∫₀ᵗ‖f‖₂` — the **consequence**, which is the
separate spec row `l2Bound` (`Spec.lean:383`).  The identity is `04-whole-space.tex:117` prose +
the display at `02-preliminaries.tex:136-139`, which is precisely how `Spec.lean:331-334` cites it.
*One-line fix:* in both docstrings write "row `energyIdentity` (`04-whole-space.tex:117`,
display at `02-preliminaries.tex:136-139`)" and keep `eq:RL2` for `l2Bound`.

### N4 (low, strictly nicer statement, already verified to compile)

`rev150_gap.lean`'s `rev150_energyIdentity_l2Sq` (quoted in §2.4(a)) is the clamp-free statement in
the spec's own `l2Sq`/`slice` vocabulary, and it needs only **one extra import**
(`NSFormalization.Section4.C01.ForceSlices`, where `slice`/`l2Sq` live; `Vocabulary` — hence
`norm_toLp_sq_eq_l2Sq` — is *already* in `EnergyDerivative`'s closure via
`PressureJetPath → JetPaths → MomentumCarrierB → Vocabulary`).  Exporting it from
`formalization/` would make the C01 V2 Bindings a pure assembly instead of carrying an 8-line
analytic argument.  Not demanded now; §4 folds it into the V2 plan.

## 4. Gaps — the exact C01 V2 contract plan

Nothing mathematical is missing for the `energyIdentity` row: the identity is proved,
unconditionally, at every interior time.  What remains is **registration**, and it is a
`verification`-side lane.  `contracts.json`'s `C01.energy_absorption_partial` scope string names
`energyIdentity`, `energyDifferentialBound`, `l2Bound` explicitly as *NOT included*, so V1 cannot be
amended — a V2 is required.  Concretely, following the `A04.energy_high_partial_v2` /
`B02.homogeneous_partial_v2` shape:

1. **`formalization/` prerequisite (≈10 lines, optional but recommended — N4).** Export
   `rev150_energyIdentity_l2Sq` from a C01 module (either add
   `import NSFormalization.Section4.C01.ForceSlices` to `EnergyDerivative.lean`, or a 30-line
   `Section4/C01/EnergySpec.lean` importing `EnergyDerivative` + `ForceSlices`).  Also add
   `def pairing (w z : SpatialField) : ℝ := ∫ x : Space, (inner ℝ (w x) (z x) : ℝ)` next to
   `ForceSlices.lean:83`'s `l2Sq`, token-for-token from `Spec.lean:196`, so that the V2 binding can
   carry a `rfl` bridge for it (there is currently **no** local `pairing` in `formalization/`,
   only the raw integrand).
2. **Contract**: `verification/Contracts/V2/EnergyAbsorptionPartial.lean`, structure
   `EnergyAbsorptionPartialV2API`, re-stating V1's six fields verbatim plus the two new spec-local
   defs (`gradientSq z := ∫ x, ‖gradientTensor z x‖^2` — `Spec.lean:185`; `pairing` — `Spec.lean:196`)
   and the new field `energyIdentity` copied token-for-token from `Spec.lean:344-350`.  Imports stay
   `Contracts.V1.{Data,GradientL6}` only (import policy unchanged).
3. **Bindings**: `verification/Bindings/EnergyAbsorptionPartialV2.lean`.
   * reuse `Bindings.uniqueness_toA02` to move `Contracts.V1.Data.ClassicalSolutionR →
     A02.ClassicalSolutionR` field-by-field (a `rfl` bridge for the structure is impossible — the
     `CLAUDE.md` structure exception; `Bindings/Uniqueness.lean:63`);
   * `rfl` bridges: `slice`, `l2Sq`, `l2Norm`, `laplacianSq`, `criticalL3`, `advectionWork`
     (copy V1's `energyAbsorptionPartial_*_eq`, `Bindings/EnergyAbsorptionPartial.lean:58-80`), plus
     the **new** `pairing` bridge from step 1;
   * the **one non-`rfl` bridge**: `gradientSq`, discharged by exactly
     `rev150b_gradientsq.lean`'s two lemmas (`PiLp.norm_sq_eq_of_L2` + `rfl`, then
     `integral_congr_ae`).  Verified compiling in this review; it is the whole of the
     `formalization → contract` vocabulary debt;
   * the field itself = `C01.energyIdentity_classical_unconditional` composed with the LHS bridge of
     step 1 (or, if step 1 is skipped, with `norm_toLp_sq_eq_l2Sq` + a `congr_of_eventuallyEq` for
     the `projIcc`, i.e. `rev150_gap.lean`'s 8 lines inlined into the binding).  The contract's extra
     hypotheses `0 < ν` and `a ∈ initialClassR` are simply unused — the lane's theorem is stronger.
4. **Tests**: `verification/Tests/EnergyAbsorptionPartialV2.lean`, mirroring
   `Tests/EnergyAbsorptionPartial.lean` (`def checkedEnergyAbsorptionPartialV2 : …V2API :=
   Bindings.energyAbsorptionPartialV2` + `run_cmd TestSupport.checkAxioms`).  Remember the
   `warningAsError = true` rule: no `Formal.*` import may reach `Tests/`.
5. **Registry**: `contracts.json` id `C01.energy_absorption_partial_v2`, `version: 2`,
   `parent_task: C01`; write the JSON with `ensure_ascii=False, indent=2` (LESSONS 141) and confirm
   `git diff --stat verification/contracts.json` shows **only** additions.  Gate: `scripts/gates.sh`
   incl. `make test-mutations` and `check_contracts.py --base-ref origin/erenup/integration`.

**Answer to the explicit question:** does `s ↦ ‖(velocityField …).toLp‖²` need one more `rfl` to
`l2Sq (slice u s)`?  **No — it needs one more non-`rfl` step.**  `‖A.toLp‖² = ∫ x, ‖A.field x‖²` is
`Vocabulary.norm_toLp_sq_eq_l2Sq` (`Vocabulary.lean:107-109`, proved from `real_inner_self_eq_norm_sq`
+ `field_inner`), *not* definitional; on top of it the `projIcc` clamp needs a
`HasDerivAt.congr_of_eventuallyEq`.  The `pairing` side, by contrast, **is** `rfl`
(`REVIEW_E3E4.md:206-208`, re-confirmed by `rev150_gap.lean` elaborating the value unchanged).

`energyDifferentialBound` (`Spec.lean:364`) and `l2Bound` (`:383`) are now unblocked and can ride
the same V2 (the former is `HasDerivAt.unique` + `real_inner_le_norm` + `norm_toLp_sq_eq_l2Sq`,
review 136 finding 8; the latter needs the `Paper1.sqrt_energy_le_primitive` generalization).

## 5. Commands and results

All from the lane worktree after `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, `lake` only from
`verification/`, one `lake` at a time.

| command | result |
|---|---|
| `lake build NSFormalization.Section4.C01.EnergyDerivative` | **exit 0**, `Build completed successfully (10302 jobs)`; 37 `warning:` lines, **0** matching `Section4` or `EnergyDerivative` |
| `lake env lean ../formalization/NSFormalization/Section4/C01/EnergyDerivative.lean` | **exit 0**, output **0 bytes** |
| `lake env lean ../research/C01/axioms_e4.lean` | **exit 0**; **5/5** `#print axioms` = `[propext, Classical.choice, Quot.sound]`; both `A04.zeroSol` `example`s elaborate silently |
| `grep -nE 'sorry\|admit\|native_decide\|maxHeartbeats\|set_option\|^ *axiom ' EnergyDerivative.lean axioms_e4.lean e4_probe2.lean` | **no output (exit 1)** — note this grep includes `set_option`: there is none |
| `make check` | **exit 0** — plan check (only the known `Paper1/BoundaryCorollary.lean:90` `sorry`), `check_contracts.py` 24 contracts, `test_contract_policy.py` `Ran 13 tests … OK`, `check_work_queue.py` `30 work items: … consistent` |
| `git diff --stat origin/erenup/integration...HEAD` | 5 files, 490 insertions, 2 deletions; **no `verification/` file touched**, so no `scripts/gates.sh` mutation run is owed |
| `python3 experiments/build_changed_lean.py --base-ref origin/erenup/integration --dry-run` | `Changed Lean modules: NSFormalization.Section4.C01.EnergyDerivative` — CI will compile the module (the `research/` axioms file is, as always, outside CI) |
| `lake env lean ../research/C01/probes/e4_probe2.lean` (the lane's own) | **exit 0**, 0 bytes |
| `lake env lean ../research/C01/probes/rev150_defeq.lean` | **exit 0**; (A)(B) item-6 `rfl` **hold**, (C) `axis = coordinateVector` `rfl`, (D) the function is `ρ ↦ ‖u(ρ+c,·)‖²`, (E) `temporalDerivative = deriv` `rfl`; `temporalDerivative` resolves to a single full name; 2 `unusedVariables` warnings from the probe's own `hcS`, none from the module |
| `lake env lean ../research/C01/probes/rev150_gap.lean` | **exit 0**, 0 bytes — the clamp-free `l2Sq`/`slice` form follows in 8 lines |
| `lake env lean ../research/C01/probes/rev150b_gradientsq.lean` | **exit 0**, 0 bytes — `gradientSq` bridge is `PiLp.norm_sq_eq_of_L2` + `rfl` + `integral_congr_ae` |
| `lake env lean ../research/C01/probes/rev150b_hardened.lean` | **exit 0**, 0 bytes — both hardened consequences derive |
| `lake env lean ../research/C01/probes/rev150_mutation.lean` | **exit 1**, three errors, one per mutation (below) |
| `lake env lean ../research/C01/probes/rev150b_ioo.lean` | **exit 1**, one error (below) |

### Negative checks

Five substantive mutations, none of the "drop an argument and re-apply" kind that LESSONS
2026-09-14 warns about (every binder of both theorems occurs in its *statement*, so the
`autoImplicit` false-negative trap cannot fire here either).

**M1 — factor `2` dropped from row E4's value**, lane's proof script verbatim
(`rev150_mutation.lean:20-72`):

```
rev150_mutation.lean:72:2: error: Type mismatch
  HasDerivWithinAt.hasDerivAt hderiv (Icc_mem_nhds hr.left hr.right)
has type
  HasDerivAt (fun r => ‖(A (projIcc 0 (S - c) hT' r)).toLp‖ ^ 2) (2 * ⟪(A ⟨r, ⋯⟩).toLp, (B ⟨r, ⋯⟩).toLp⟫) r
but is expected to have type
  HasDerivAt (fun ρ => ‖(velocityField w hST ⟨↑(projIcc 0 (S - c) ⋯ ρ) + c, ⋯⟩).toLp‖ ^ 2)
    ⟪(velocitySliceField w ⋯).toLp, (temporalSliceField w hf ⋯).toLp⟫ r
```

**M3 — `temporalSliceField` replaced by `forceSliceField` in the pairing** (`:75-127`):

```
rev150_mutation.lean:127:2: error: Type mismatch … has type
  … (2 * ⟪(A ⟨r, ⋯⟩).toLp, (B ⟨r, ⋯⟩).toLp⟫) r
but is expected to have type
  … (2 * ⟪(velocitySliceField w ⋯).toLp, (forceSliceField hf ⋯).toLp⟫) r
```

**M2 — viscous sign flipped in the unconditional identity** (`:130-180`):

```
rev150_mutation.lean:168:2: error: Type mismatch
  HasDerivAt.congr_of_eventuallyEq hcomp ?m.1047
has type   HasDerivAt ?m.1044 ((-2 * ν * ∫ x, ∑ i, ‖(fderiv ℝ (velocitySliceField w ⋯).field x) (axis i)‖ ^ 2) + 2 * ∫ x, ⟪…⟫) t
but is expected to have type
           HasDerivAt (fun s => ‖(velocityField w ⋯ (projIcc 0 ((t + T) / 2) ⋯ s)).toLp‖ ^ 2)
             ((2 * ν * ∫ x, ∑ i, ‖(fderiv ℝ (velocitySliceField w ⋯).field x) (axis i)‖ ^ 2) + 2 * ∫ x, ⟪…⟫) t
```

**H1/H2 — hardened**: instead of relying on the lane's script no longer elaborating, take each
mutated statement as a *hypothesis* and combine it with the lane's theorem via `HasDerivAt.unique`
(`rev150b_hardened.lean`, both **compile**, which is the point):

* `H1_dropTwo_forces_zero` — the factor-2-free value would force
  `⟪u(t,·), ∂ₜu(t,·)⟫_{L²} = 0` at every interior time of **every** classical solution;
* `H2_signFlip_forces_zero_dissipation` — the sign-flipped identity would force
  `ν · ∫ ∑ᵢ‖∂ᵢu(t,·)‖² = 0`, i.e. for `ν > 0` every classical solution would have vanishing
  gradient.

So the two mutations are genuinely different mathematics, not notational variants.

**M4 — `Ioo` widened to `Ico` in row E4's interior guard** (`rev150b_ioo.lean`, lane's script
verbatim, the only change being `hr : r ∈ Ico (0:ℝ) (S − c)`):

```
rev150b_ioo.lean:72:40: error: Application type mismatch: The argument
  hr.left
has type   0 ≤ r
but is expected to have type   0 < r
in the application   Icc_mem_nhds hr.left
```

The strict left endpoint is load-bearing.  (It is a *window* artifact, not a restriction on the
PDE: `energyIdentity_classical_unconditional` picks `c = t/2` so that **every** `t ∈ Ioo 0 T` is an
interior point of its own window — which is exactly why the second theorem quantifies over all
interior times with no window in the statement.)

**Non-vacuity.**  `research/C01/axioms_e4.lean:36-43` instantiates both theorems on
`A04.zeroSol 1 2` over the **non-degenerate** window `[1/2,1] ⊂ (0,2)` at `r = 1/4` and at the
interior time `1 ∈ (0,2)`; both elaborate.  Lane 148's N2 (a one-point `Icc 1 1` index) is **not**
repeated — and in row E4 it could not be, since `hr : r ∈ Ioo 0 (S − c)` itself forces `c < S`.
`A04.zeroSol` (`Section4/A04/ZeroSolution.lean:91`) is the **only** ground `ClassicalSolutionR`
witness in the tree (`ClassicalSolutionR.{restrict,congr,normalizePressure}`,
`A02/Restrict.lean:60,175,247`, all consume an existing solution), so no nonzero witness is
available; on `zeroSol` both sides are `0`, which is why M1/M3 (true for `zeroSol`, false in
general) are the checks that carry the content here.
