# REVIEW — lane 129-SIMP-D01-orderzero (simplifier + tester pass over the five D01 P2-chain modules)

Reviewer: opus (read-only on `/data_8T/ping/blowup_density`; all work in the worktree
`.claude/worktrees/129-SIMP-D01-orderzero`, branch `erenup/129-SIMP-D01-orderzero`,
single commit `cfbf60d` on merge-base `e592585`).  Probes in `/tmp/rev129/` (ephemeral — every
cited error text and the full counterexample source is pasted below, per LESSONS 2026-09-14).

## Verdict: **ACCEPT-WITH-NOTES**

The code change is safe, minimal and better-verified than the lane claims: **all 64 declarations of
the five modules have byte-identical *elaborated* types** (`pp.fullNames`) before and after, so the
lane-109/111 "bare name silently re-resolves after an `open` is removed" failure mode is ruled out,
not merely argued.  Every gate is green, including `make test-mutations`, which the lane did not run.

The notes are all on the **tester half**, not the code: one of the six negative blocks
(`P2_drop_hf`) produces **no evidence at all**, and the ATTEMPTS record asserts that a genuine
falsification of the `hdiv`-free transverse statement is "not feasible in a SIMP lane" — which is
**false**: I proved it in ~35 lines on top of the lane's own `gradBump` witness, using only
already-merged lemmas.  See findings 3–5; the machine-checked counterexample is pasted in §6 so it
can be lifted into `research/D01/negative_simp_p2.lean` verbatim.

---

## 1. Diff discipline and signatures — PASS

```
$ git diff e592585 HEAD --stat
 .../Section4/D01/OrderZeroAlgebra.lean   |   2 +-
 .../Section4/D01/OrderZeroCurl.lean      |  27 +--
 .../Section4/D01/OrderZeroSymbol.lean    |   5 +-
 .../Section4/D01/PressureJets.lean       |   4 +-
 research/D01/ATTEMPTS_SIMP.md            | 201 ++++++++
 research/D01/negative_simp_p2.lean       | 260 ++++++++++
 research/D01/negative_simp_p2_fail.lean  |  86 ++++
 7 files changed, 558 insertions(+), 27 deletions(-)
```

`git diff e592585 HEAD -- formalization/` is **117 lines total** and contains exactly:

* 8 deleted / 2 rewritten `open` / `open scoped` lines (`OrderZeroSymbol` ×3, `OrderZeroCurl` ×4,
  `OrderZeroAlgebra` ×1 rewrite, `PressureJets` ×2);
* one docstring line in `PressureJets.lean:11` (`02-preliminaries.tex:76-81` → `:89-94`);
* the `fourier_antisym` proof body (two `rw [show … from by …]` blocks → one `have hpull`, −6 lines).

`MomentumSlice.lean` is untouched.  Line counts reproduce the claim exactly:

| module | base | HEAD |
|---|---|---|
| OrderZeroSymbol | 494 | 491 |
| OrderZeroCurl | 517 | 506 |
| OrderZeroAlgebra | 112 | 112 |
| PressureJets | 156 | 154 |
| MomentumSlice | 201 | 201 |
| **total** | **1480** | **1464** |

**Citation check (LESSONS 2026-09-14, "论文行号引用会代代相传"):**
`grep -n 'label{eq:Rpressure}' paper/sections/*.tex` → `02-preliminaries.tex:90`; the block
"`The right side has zero mean. On $\R^3$ we require`" … "`parallel to $\xi$. Hence …`" spans
**89–94**.  The old `:76-81` is the `eq:projected` display.  **The fix is correct.**

**Signature-line diff:** 65 declaration head lines in each version, identical modulo line numbers
(`diff` empty).

**Elaborated-type diff (the real check).**  I generated `#check @<fullname>` for **all 64
declarations** of the five modules (namespaces `…D01.Cut`, `…D01`, `…D01.Leray` resolved by position)
under `set_option pp.fullNames true` + `pp.numericTypes true`, and ran the identical probe on the
lane worktree and on the root checkout (whose five D01 files are sha256-identical to the merge-base):

```
$ cd <WT>/verification && lake env lean /tmp/rev129/allchecks_head.lean > all_head.txt   # exit 0, 453 lines
$ cd /data_8T/ping/blowup_density/verification && lake env lean /tmp/rev129/allchecks_base.lean > all_base.txt  # exit 0, 453 lines
$ diff all_base.txt all_head.txt
ALL 64 ELABORATED TYPES IDENTICAL
```

The six main exports named in the brief are included and print with the same full names on both
sides; in particular `pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR` still takes
`NSFormalization.Section4.D01.MemForceR` (**not** `A02.MemForceR`) — the pre-existing lane-111
shadowing, unchanged by this lane.  `#print axioms` of all six: `[propext, Classical.choice,
Quot.sound]`.

## 2. Compiles / gates — PASS

All commands from `<WT>/verification` after `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, one lake
at a time.

| command | result |
|---|---|
| `lake build` of the 5 D01 modules | `Build completed successfully (9933 jobs)`, 0 errors, **no own-line warning on any D01 file** |
| `lake env lean` on each of the 5 files | each **exit 0, 0 bytes of output** |
| `lake build NSFormalization.Section4.A04.PressureDrop` | exit 0, `Build completed successfully (9939 jobs)` |
| `lake build NSFormalization.Section4.A04.EnergyIdentityHigh` | **exit 1 — file does not exist in this worktree** (see finding 1) |
| `lake build Tests.DatumLemmasV3` | exit 0, `Contract BlowupDensity.Tests.checkedDatumLemmasV3: checked; standard logical axioms only` |
| `lake env lean ../research/D01/axioms_order_zero.lean` | exit 0, 21 decls, all `[propext, Classical.choice, Quot.sound]` |
| `lake env lean ../research/D01/axioms_order_zero_curl.lean` | exit 0, 14 decls (incl. the re-proved `fourier_antisym`), all standard |
| `lake env lean ../research/D01/axioms_sl8_prep.lean` | exit 0, 13 decls, all standard |
| `lake env lean ../research/D01/axioms_sl8_assembly.lean` | exit 0, 6 decls, all standard |
| `make check` | exit 0 (`13 tests OK`; `30 work items: ownership, contract registration and task cards consistent.`) |
| `make test` | exit 0, **22** × `checked; standard logical axioms only` |
| `make test-mutations` | exit 0 — `implementation_refactor: accepted / admitted_proof: rejected as required / extra_axiom: rejected as required / weakened_hypothesis: rejected as required / Mutation suite passed.` |

No `sorry` / `admit` / `axiom` / `native_decide` anywhere in the two new research files; neither is in
a lake glob, so `negative_simp_p2_fail.lean` (which must fail) cannot break CI.

## 3. Findings

### Finding 1 — INFO: the lane is one commit behind integration; `A04/EnergyIdentityHigh` checked separately

`A04/EnergyIdentityHigh.lean` (lane 124, merged in `a016bf6`) does not exist at the lane's merge-base,
so the brief's build target failed with
`error: no such file or directory (error code: 2)  file: …/Section4/A04/EnergyIdentityHigh.lean`.
I checked the downstream consumer anyway by elaborating **integration's** copy against the **lane's**
D01 modules:

```
$ git show origin/erenup/integration:formalization/.../A04/EnergyIdentityHigh.lean > /tmp/rev129/EnergyIdentityHigh.lean
$ cd <WT>/verification && lake env lean /tmp/rev129/EnergyIdentityHigh.lean
EXIT=0   (0 bytes of output)
```

So the merge is safe on that axis.  (Structurally it must be: a top-level `open` is file-local and
does not propagate to importers; the only cross-file risk was the exports' types, ruled out in §1.)
Rebase onto `origin/erenup/integration` before merging and re-run `scripts/gates.sh`.

### Finding 2 — PASS: the `fourier_antisym` dedup is semantics-preserving

The two removed `rw [show … from by apply integral_congr_ae; filter_upwards with ξ; …]` blocks
differed only by the `p ↔ q` swap; the replacement `have hpull : ∀ d c : Fin 3, …` has the same body
with `(d, c)` for `(p, q)`, and the finisher is `rw [integral_sub …, hpull p q, hpull q p, hpp,
sub_self]`.  Evidence: the statement's elaborated type is in the 64-way identical diff of §1;
`#print axioms NSFormalization.Section4.D01.fourier_antisym` →
`[propext, Classical.choice, Quot.sound]`; `axioms_order_zero_curl.lean` and both downstream
consumers (`orderZeroDatum_longitudinal_of_curl_free`,
`Leray.lerayComplement_zero_orderZeroDatum_eq_self`) rebuild green.

### Finding 3 — MEDIUM: `P2_drop_hf` is an empty negative check (should be relabelled)

`negative_simp_p2_fail.lean:81-84`.  The statement (lines 81–83) is
`SmoothSquareIntegrableJets (fun x => pressureGradient u.pressure t x)` — **it contains no `hf` and
elaborates fine**.  The block's only error is

```
../research/D01/negative_simp_p2_fail.lean:84:76: error(lean.unknownIdentifier): Unknown identifier `hf`
```

at **line 84, the proof term** `by exact pressureGradient_slice_…_of_memForceR u hf ht`.  That error
is produced by *any* undefined name; the block demonstrates nothing whatsoever about `hf` being
load-bearing — it is a strictly weaker version of the anti-pattern LESSONS 2026-09-14 warns about
("负向检查不能只用「省略参数再 apply 原定理」").  The hypothesis *is* genuinely load-bearing (the
paper-level counterexample at `D01/Pressure.lean:62-66` — citation verified — makes the
`hf`-free statement false), but this file supplies no evidence for it.  **Ask for the label to be
changed to "no evidence produced; necessity known only from `Pressure.lean:62-66` prose"**, or for
the block to be replaced by an honest `#check`-level note.  (By contrast `add_drop_hw` and
`pressureGradient_eq_drop_hf` *do* error inside the statement — `65:27`, `65:68`, `75:61` — so their
STRUCTURAL label is correct and earned.)

### Finding 4 — MEDIUM: the "not feasible in a SIMP lane" claim is false — `hdiv` IS falsifiable, and I did it

`ATTEMPTS_SIMP.md` (lane-129 section, "Honest labelling of the ROUTE checks") says a full
counterexample for the transverse lemma "requires computing a Fourier transform (e.g. showing
`datum⁰(∇bump)` is longitudinal-not-transverse), which is **not feasible in a SIMP lane** and was not
attempted".  No Fourier computation is needed.  Using only **already-merged** lemmas and the lane's
own `gradBump`, in ~35 lines and under 25 minutes:

1. `Leray.lerayComplement_eq_zero_of_transverse 0 _ ⟨transverse⟩` (`D01/LerayDatum.lean:316`) gives
   `lerayComplement 0 (orderZeroDatum gradBump_mem) = 0`;
2. lane 108's `Leray.lerayComplement_zero_orderZeroDatum_eq_self` (curl-free, already proved for
   `gradBump` by the lane) gives `lerayComplement 0 (orderZeroDatum gradBump_mem) = orderZeroDatum …`;
3. hence `orderZeroDatum gradBump_mem = 0`, so by `isSobolevDatum_orderZeroDatum` the field pairs to
   zero against every Schwartz test; testing against its own components (Schwartz, since `∇bump` is
   smooth with compact support) gives `∫ (∂ᵢbump)² = 0`, so `∂ᵢbump ≡ 0` by continuity —
   contradicting the lane's own `gradBump_ne_zero`.

Result (`/tmp/rev129/counter.lean`, pasted in §6):

```
$ cd <WT>/verification && lake env lean /tmp/rev129/counter.lean
EXIT=0
'Rev129.transverse_without_hdiv_is_false' depends on axioms: [propext, Classical.choice, Quot.sound]
```

So `transverse_drop_hdiv` is **not** merely "not provable by the established route": the
`hdiv`-free statement is **provably false**, and `hdiv` is load-bearing in the strong sense.
Recommendation: move the §6 snippet into `research/D01/negative_simp_p2.lean` (it compiles as-is
appended after `gradBump_ne_zero`) and downgrade the ROUTE row for `hdiv` to a STRUCTURAL-strength
**FALSIFIED** row.

The same route kills the other two `hcurl` rows once someone builds a nonzero divergence-free
compactly-supported witness — `w := curl(bump·e₀) = (0, ∂₂φ, −∂₁φ)` is divergence-free by Clairaut
(`partialDeriv_gradient_eq_sndFDeriv` + `ContDiffAt.isSymmSndFDerivAt`, exactly as `gradBump_curl`),
and `w ≠ 0` because `∂₁φ ≡ 0` would force `φ(0) = φ(3·e₁)`, i.e. `1 = 0`.  Then:
transverse (proved lemma) + longitudinal (the `hcurl`-free claim) ⇒ `lerayComplement 0 = 0` **and**
`= self` ⇒ datum `= 0` ⇒ `w = 0`.  Estimated 40–60 lines; **not** done here (out of time-box).

**Which hypotheses are now proven load-bearing:**

| export | hypothesis | status after this review |
|---|---|---|
| `orderZeroDatum_transverse_of_divergence_free` | `hdiv` | **FALSIFIED without it** (machine-checked, §6) |
| `orderZeroDatum_add` | `hw` | STRUCTURAL (appears in conclusion) — earned |
| `orderZeroDatum_pressureGradient_eq` | `hf` | STRUCTURAL (appears in conclusion) — earned |
| `orderZeroDatum_longitudinal_of_curl_free` | `hcurl` | ROUTE only; falsifiable by the recipe above |
| `lerayComplement_zero_orderZeroDatum_eq_self` | `hcurl` | ROUTE only; falsifiable by the recipe above |
| `pressureGradient_slice_…_of_memForceR` | `hf` | **no evidence** (finding 3) |

### Finding 5 — LOW: MAINT item 1 names a destination that would create an import cycle

`ATTEMPTS_SIMP.md` MAINT #1 proposes promoting **four** `OrderZeroCurl` units to
`Paper3/AngularFourierDilation.lean` "as lane 109 did".  Only one of them can go there:

* `fderiv_zc_eq'` (`:61`, docstring `:59`) and `cs_ibp` (`:68`, docstring `:67`) are stated in terms
  of `Cut.zc`, `Cut.hasFDeriv_zc`, `Cut.zc_smooth`, `Cut.Pj` and `A03.partialDeriv` — all
  `Section4.*`.  `physical_weighted_pairing_zero` (`:148`) and `fourier_lineDeriv_apply` (`:330`)
  likewise depend on `Cut.*` / `D01.componentLp`.
* `Paper3/AngularFourierDilation.lean` imports only `Paper3.AngularSobolevCoordinates` + Mathlib, and
  `Section4.D01.*` imports Paper3.  Moving any `Cut`-dependent unit into Paper3 makes
  **Paper3 → Section4 → Paper3**, an import cycle.
* Only `longitudinal_of_longitudinal_symm` (`:435`, stated purely for `g : Fin 3 → FourierData`) is
  Paper3-level and can follow `transverse_of_transverse_symm` (already at
  `Paper3/AngularFourierDilation.lean:297`).

Ambiguity risk for that one move is **low** provided the lane-109 alias pattern is reused verbatim
(`Section4/D01/OrderZeroSymbol.lean:476-480`: `alias transverse_of_transverse_symm :=
NSFormalization.Paper3.transverse_of_transverse_symm`) — the enclosing-namespace alias wins over the
file's `open NSFormalization.Paper3`, which is why `OrderZeroSymbol.lean:491` still compiles.  A
half-move (Paper3 copy, **no** alias, both namespaces `open`ed) is what produced 109's
`Ambiguous term`.  The shared `Cut`/IBP machinery needs a **new module under `Section4/D01/`**, not
Paper3 — please amend MAINT #1 before a future lane acts on it.

### Finding 6 — INFO: the other MAINT items check out

| MAINT | claim | verified |
|---|---|---|
| #2 | `lerayComplement_orderZeroDatum_add/_sub` are dead | yes — `grep -rn` over `formalization research verification` finds them only in their own docstring (`OrderZeroAlgebra.lean:28`) and `research/D01/axioms_sl8_prep.lean:10-11` |
| #3 | `pressureGradient_apply` duplicated | yes — `A01/PressureGauge.lean:84` and `D01/MomentumSlice.lean:127`, different namespaces, no clash |
| #5 | transverse argument duplicated | yes — `PressureJets.lean:70-77` and `A04/PressureDrop.lean:194-196` both run `lerayComplement_eq_zero_of_transverse 0 _ (orderZeroDatum_transverse_of_divergence_free …)` |
| #6 | `MemForceR` shadowing | yes — `#check` with `pp.fullNames` prints `NSFormalization.Section4.D01.MemForceR` despite `open …A02 (… MemForceR)`; pre-existing, harmless, correctly left alone |
| opens | `frequencyUnit` unused in `OrderZeroSymbol`, used in `OrderZeroCurl` | yes — base `OrderZeroSymbol` has the token **only** on its own `open` line (`:347`); `OrderZeroCurl` uses it at HEAD `:441`+ (= base `:449`, as cited), and that open was kept |
| opens | `partialDeriv` unused in `PressureJets` | yes — only inside theorem *names* (`:76`, `:82`); `MomentumSlice` has bare uses (`:119`), open kept |

### Finding 7 — NIT: three small inaccuracies in `ATTEMPTS_SIMP.md`

1. "**exit 1 (as required), 6 errors**" — Lean emits **9** error messages (3 `Type mismatch` + 6
   `Unknown identifier`, because `hw` appears 3× and `hf` 3×).  Six *blocks*, nine errors.
2. "`make test-mutations` / `scripts/gates.sh` … was not run here" — I ran it: **passes**.  Worth
   updating so the lead does not treat it as an open item.
3. "`Build completed successfully (10017 jobs)`" — I measure 9933 / 9939 / 10011 / 10123 depending on
   the target set; harmless, but the quoted number is not reproducible as written.

## 4. Quality of the tester — summary judgement

* **Positive file (`negative_simp_p2.lean`)**: **good**.  Exit 0, 12 `#print axioms` all standard.
  The `∇bump` development is real work (compact support from `ContDiffBump.zero_of_le_dist`,
  curl-freeness from the module's own `partialDeriv_gradient_eq_sndFDeriv`, and a genuine
  `gradBump ≠ 0` via `is_const_of_fderiv_eq_zero` + `bump 0 = 1`, `bump (3·e₀) = 0`), and it is what
  made finding 4 possible.  `const_not_jets` is a real "the conclusion has content" check.
  `zeroSol`/`memForceR_zero` are honest about being the only reachable classical-solution witness.
* **Must-fail file (`negative_simp_p2_fail.lean`)**: **mixed**.  2 STRUCTURAL blocks are sound; 3
  ROUTE blocks are signature artefacts (correctly labelled, but one of them — `hdiv` — is now
  known falsifiable, finding 4); 1 block (`P2_drop_hf`) is evidence-free (finding 3).
* The honesty framing in the ATTEMPTS is, on balance, **adequate but over-pessimistic in one place
  and over-generous in another** — hence ACCEPT-WITH-NOTES rather than ACCEPT.

## 5. Requested before/after merge

Blocking: **none**.  Requested (cheap, worker can do in one pass, or a follow-up SIMP lane):

1. Paste the §6 counterexample into `research/D01/negative_simp_p2.lean` and change the `hdiv` row
   from ROUTE to FALSIFIED; delete the "not feasible in a SIMP lane" sentence.
2. Relabel `P2_drop_hf` per finding 3.
3. Amend MAINT #1 per finding 5 (destination module; cycle risk).
4. Fix the three nits of finding 7.
5. Rebase onto `origin/erenup/integration` (finding 1) and re-run `scripts/gates.sh` before merge.

## 6. The machine-checked counterexample (append after `gradBump_ne_zero` in `negative_simp_p2.lean`)

Verified with `cd <WT>/verification && lake env lean /tmp/rev129/counter.lean` → **exit 0**,
`'Rev129.transverse_without_hdiv_is_false' depends on axioms: [propext, Classical.choice, Quot.sound]`.
(Needs `open NSFormalization.Source.RealSobolev (FourierData)` and the lane's `gradBump`,
`gradBump_smooth`, `gradBump_cs`, `gradBump_mem`, `gradBump_curl`, `gradBump_ne_zero` in scope.)

```lean
/-- The `hdiv`-free transverse statement, quantified exactly as `transverse_drop_hdiv`. -/
def TransverseNoDiv : Prop :=
  ∀ {z : Space → Space} (hz : MemLp z 2 volume), ContDiff ℝ ∞ z →
    ∀ᵐ ξ : Space ∂volume,
      ∑ j : Fin 3, ((ξ j : ℝ) : ℂ) * ((orderZeroDatum hz j : FourierData) ξ) = 0

/-- Step 1: the hypothetical statement collapses the datum of `∇bump` to zero. -/
theorem datum_gradBump_zero (H : TransverseNoDiv) :
    orderZeroDatum gradBump_mem = 0 := by
  have h1 : Leray.lerayComplement 0 (orderZeroDatum gradBump_mem) = 0 :=
    Leray.lerayComplement_eq_zero_of_transverse 0 (orderZeroDatum gradBump_mem)
      (H gradBump_mem gradBump_smooth)
  have h2 : Leray.lerayComplement 0 (orderZeroDatum gradBump_mem) = orderZeroDatum gradBump_mem :=
    Leray.lerayComplement_zero_orderZeroDatum_eq_self gradBump_mem gradBump_smooth gradBump_curl
  rw [h2] at h1; exact h1

/-! ## Step 2: a zero order-0 datum forces the field to vanish, contradicting `gradBump ≠ 0`. -/

noncomputable def gi (i : Fin 3) : Space → ℝ := fun x => (gradBump x).ofLp i

theorem gi_smooth (i : Fin 3) : ContDiff ℝ ∞ (gi i) :=
  ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff).comp gradBump_smooth

theorem gi_cs (i : Fin 3) : HasCompactSupport (gi i) :=
  gradBump_cs.comp_left (g := fun v : Space => v.ofLp i) (by simp)

noncomputable def psi (i : Fin 3) : SchwartzMap Space ℂ :=
  (gi_cs i |>.comp_left (g := fun r : ℝ => ((r : ℝ) : ℂ)) (by simp)).toSchwartzMap
    (by exact (Complex.ofRealCLM.contDiff).comp (gi_smooth i))

theorem psi_apply (i : Fin 3) (x : Space) : psi i x = ((gi i x : ℝ) : ℂ) := rfl

/-- Step 2. -/
theorem gradBump_eq_zero_of_datum_zero (h0 : orderZeroDatum gradBump_mem = 0) : False := by
  have hds := isSobolevDatum_orderZeroDatum gradBump_mem
  rw [h0] at hds
  have hzero : ∀ i : Fin 3, ∫ x : Space, (psi i) x * ((gradBump x).ofLp i : ℝ) = 0 := by
    intro i
    have := hds i (psi i)
    simpa using this.symm
  have hsq : ∀ i : Fin 3, (fun x : Space => gi i x * gi i x) =ᵐ[volume] 0 := by
    intro i
    have hint : Integrable (fun x : Space => gi i x * gi i x) volume :=
      ((gi_smooth i).continuous.mul (gi_smooth i).continuous).integrable_of_hasCompactSupport
        ((gi_cs i).mul_right)
    have hre : ∫ x : Space, gi i x * gi i x = 0 := by
      have h1 := hzero i
      simp only [psi_apply] at h1
      have h2 : ∫ x : Space, (((gi i x * gi i x : ℝ)) : ℂ) = 0 := by
        rw [← h1]
        refine integral_congr_ae ?_
        filter_upwards with x
        simp only [gi]; push_cast; ring
      rw [integral_complex_ofReal] at h2
      exact_mod_cast h2
    exact (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg _) hint).mp hre
  have hgi : ∀ (i : Fin 3) (x : Space), gi i x = 0 := by
    intro i
    have hfun : gi i = (fun _ : Space => (0 : ℝ)) := by
      refine ((gi_smooth i).continuous.ae_eq_iff_eq volume
        (continuous_const : Continuous fun _ : Space => (0 : ℝ))).mp ?_
      filter_upwards [hsq i] with x hx
      have hx' : gi i x * gi i x = 0 := by simpa using hx
      exact mul_self_eq_zero.mp hx'
    intro x; exact congrFun hfun x
  apply gradBump_ne_zero
  funext x
  apply (WithLp.equiv 2 (Fin 3 -> Real)).injective
  ext i
  show (gradBump x).ofLp i = (0 : Space).ofLp i
  have h := hgi i x
  simp only [gi] at h
  simpa using h

/-- The full counterexample: the `hdiv`-free transverse statement is FALSE. -/
theorem transverse_without_hdiv_is_false : ¬ TransverseNoDiv := fun H =>
  gradBump_eq_zero_of_datum_zero (datum_gradBump_zero H)

#print axioms transverse_without_hdiv_is_false
```
