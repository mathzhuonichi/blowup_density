# Review — lane 137-A01-a3-force-cap (row A3-L1·f, the forcing integral cap)

Reviewer run 2026-09-14. Worktree `.claude/worktrees/137-A01-a3-force-cap`,
branch `erenup/137-A01-a3-force-cap`, one commit `ac7cfd9` on merge-base `d34d669`.
Probes in `/tmp/rev137/` (ephemeral; every error text quoted below is verbatim).

## Verdict: **ACCEPT-WITH-NOTES**

The mathematics is correct, the statements match `gronwall_bddAbove_Ico`'s slot on the
nose, the `MemForceR` L¹ claim is **faithful to the paper** (finding 1), and both
recorded failures reproduce verbatim. Five notes, none blocking; two of them
(findings 2, 3) correct claims in the records rather than the Lean.

---

## 1. Compiles / axioms / hygiene — PASS

```
$ . scripts/lean-env.sh && cd verification && LEAN_NUM_THREADS=6 \
    lake build NSFormalization.Section4.A01.ForceCap
EXIT=0
Build completed successfully (9885 jobs).
```
(the only warnings in the log are pre-existing `Replayed` warnings from
`Source/PhysicalBesselSobolev`, `Source/PacketForceExtension`, `Source/ViscosityPacket`,
`Paper3/SobolevDirectionalDerivative`; none from the new file)

```
$ lake env lean ../formalization/NSFormalization/Section4/A01/ForceCap.lean
EXIT=0        # 0 bytes of output — silent

$ lake env lean ../research/A01/axioms_a3_force.lean
EXIT=0
'NSFormalization.Section4.A01.sobolevNormAt_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.forceCap' … [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.intervalIntegral_le_forceSobolevENormL1' … [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.intervalIntegral_le_forceSobolevENormL1_of_memForceR' … [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.forceCap_L1' … [propext, Classical.choice, Quot.sound]
'memForceR_zero' … 'nonvac_forceCap' … 'nonvac_L1cap' … 'nonvac_forceCap_L1' … [propext, Classical.choice, Quot.sound]
```
9/9 declarations standard-3.

```
$ make check
EXIT=0    …  13 tests OK; "30 work items: ownership, contract registration and task cards consistent."

$ grep -nE 'sorry|admit|axiom|native_decide|maxHeartbeats|set_option' \
    formalization/NSFormalization/Section4/A01/ForceCap.lean research/A01/axioms_a3_force.lean
(no match, exit 1)
```
Diff touches exactly 4 files (1 new `.lean` in `formalization/`, 3 in `research/`); no
`Contracts/`, `Bindings/`, `Tests/` or `paper/` file is touched, so `make test`'s closure is
unaffected.

## 2. Statement fidelity

### Finding 1 (severity: **none — confirmation**, but worth recording project-wide)
**The `MemForceR` L¹_t claim is TRUE and the Lean is NOT stronger than the paper.**

`paper/sections/02-preliminaries.tex:17-21` (`grep -n 'label{eq:Rclasses}'` → `:17`, the
`\begin{equation}` line; the display is `:18-21`):

```tex
\begin{equation}\label{eq:Rclasses}
 \mathcal F_{\R}=\left\{f\in C^\infty([0,\infty);H^\infty):
 \norm{f}_{L^1_tH^m_x}+\norm{f}_{L^2_tH^m_x}<\infty
 \text{ for every integer }m\ge0\right\}.
\end{equation}
```

`formalization/NSFormalization/Section4/D01/ForceClass.lean:174-180` (verbatim restatement of
the frozen `Contracts/V1/Data.lean:544`):

```lean
def MemForceR (f : VelocityField) : Prop :=
  ContDiffOn ℝ ∞ f futureDomain ∧
    ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      IsSobolevPath (m : ℝ) f G ∧ ContDiffOn ℝ ∞ G futureTimes ∧
      MemLp G 1 forceTimeMeasure ∧ MemLp G 2 forceTimeMeasure
```

So `F_R` is **not** "only continuity into `H^∞`": the finiteness of `‖f‖_{L¹_tH^m}` *and*
`‖f‖_{L²_tH^m}` at every integer order is part of the manuscript's own definition, and the
Lean carries exactly those two clauses (`forceTimeMeasure = volume.restrict (Ioi 0)`, the
`(0,∞)` of `01-introduction.tex:140`). The lane's headline claim — that the
manuscript-literal `L¹_t H^m` cap is a *theorem* rather than an extra hypothesis — is
correct, and there is **no fidelity finding against the frozen `Data.lean`**.

### `#check` of every export (`set_option pp.fullNames true`, `/tmp/rev137/checks.lean`)
All five compile; abbreviated:

```
forceCap : ∀ {f}, D01.MemForceR f → ∀ (m : ℕ) {T₀ : ℝ}, 0 < T₀ →
  ∃ Bbnd, ContinuousOn (fun s => A04.sobolevNormAt ↑m f s) (Set.Ico 0 T₀) ∧
    (∀ t ∈ Set.Ico 0 T₀, 0 ≤ A04.sobolevNormAt ↑m f t) ∧
     ∀ t ∈ Set.Ico 0 T₀, ∫ s in 0..t, A04.sobolevNormAt ↑m f s ≤ Bbnd
gronwall_bddAbove_Ico : … ContinuousOn b (Set.Ico 0 T₀) → (∀ t ∈ Set.Ico 0 T₀, 0 ≤ b t) →
     … → (∀ t ∈ Set.Ico 0 T₀, ∫ s in 0..t, b s ≤ Bbnd) → …
```

(b) **Shape fits, and `Bbnd` is `t`-free.** The `∃ Bbnd` binder sits *outside* the `∀ t`, so
the cap is one constant for the whole `Ico 0 T₀`, exactly as `gronwall_bddAbove_Ico`'s
`{Bbnd : ℝ}` demands. `hb`/`hbnn`/`hbbnd` are matched token-for-token with
`b := fun s => sobolevNormAt ↑m f s`; the module's closing `example` composes them in one
line and compiles.

Also verified by probe: `A02.MemForceR = D01.MemForceR` is `rfl`, so the `A04` lemmas
(stated over `A02.MemForceR`) accept this module's `D01.MemForceR` hypothesis without a
bridge (consistent with `logs/LESSONS.md` 2026-09-14, lane 111).

### Finding 2 (severity: **low**, records only) — `hfin` is *not* load-bearing in the lemma as stated
`intervalIntegral_le_forceSobolevENormL1` takes **both** `hf : MemForceR f` and
`hfin : forceSobolevENormL1 ↑m f ≠ ⊤`. But `hf` already implies `hfin`
(`A04.memL1Hm_of_memForceR`), so `hfin` is a provably redundant argument:

```
$ lake env lean /tmp/rev137/redundant.lean          # EXIT=0
'hfin_redundant' depends on axioms: [propext, Classical.choice, Quot.sound]   -- hfin from hf
'no_hfin_needed' depends on axioms: [propext, Classical.choice, Quot.sound]   -- statement minus hfin, proved
```

The docstring ("The finiteness hypothesis is essential … without it the inequality would read
`∫ ‖f‖ ≤ 0`, which fails for a nonzero force") and the same sentence in
`ATTEMPTS_A3_FORCE.md` and the `A3_SPLIT.md` row are therefore **inaccurate for this lemma**.
They are true about a *different*, hypothetical statement — the inequality with `hf` dropped
as well. Two sub-points for the record:

* The `⊤ ↦ 0` trap is real in the abstract: a nonzero time-independent `g(x)` has
  `∫₀^∞‖g‖_{H^m} = ∞`, so `forceSobolevENormL1 = ⊤`, RHS `= 0`, LHS `= t·‖g‖_{H^m} > 0`.
  Such a `g` is **not** in `F_R`, which is exactly why `hfin` cannot be violated here.
* The dual totalization trap **also** applies on the left: a field with *no* datum path at all
  has `sobolevENorm = ⊤`, hence `sobolevNormAt = ⊤.toReal = 0`, so both sides collapse to `0`
  and the inequality is vacuously true — the counterexample above needs a force that *has*
  slice data but is not `L¹` in time. Neither point changes the Lean; both should replace the
  "genuinely load-bearing" sentence.

*Recommended*: keep `intervalIntegral_le_forceSobolevENormL1` as is (an honest conditional
form useful if `MemForceR` is ever weakened), but reword the three records to
"`hfin` is *derivable* from `hf` here; the conditional form is kept so the argument is
visible, and because the `⊤ ↦ 0` collapse would make the unconditional-in-`f` statement
false".

### Finding 3 (severity: **low**) — non-vacuity is stronger than the lane claims
`ATTEMPTS_A3_FORCE.md` concludes "non-vacuity is on the **zero force**". The zero force is a
degenerate witness: both sides of the L¹ cap are `0`. A genuinely **nonzero** `MemForceR`
witness is constructible in ~40 lines from what is already in the tree, via
`D01.memForceR_of_memForceCompact` and Mathlib's `ContDiffBump` — built and audited this
review (`/tmp/rev137/nonzero.lean`, `EXIT=0`):

```
'Fbump_ne_zero'            depends on axioms: [propext, Classical.choice, Quot.sound]
'memForceR_Fbump'          depends on axioms: [propext, Classical.choice, Quot.sound]
'nonvac_forceCap_nonzero'  depends on axioms: [propext, Classical.choice, Quot.sound]
'nonvac_L1_nonzero'        depends on axioms: [propext, Classical.choice, Quot.sound]
```

Shape: `Fbump (t,x) := (tb t * xb x) • e₀` with `tb : ContDiffBump (2:ℝ) := ⟨1/2,1,_,_⟩`
(time bump supported in `[1,3] ⊂ (0,∞)`) and `xb : ContDiffBump (0 : Space)`;
`HasCompactSupport` by `HasCompactSupport.intro` on `closedBall 2 1 ×ˢ closedBall 0 1`;
`tsupport ⊆ positiveTimeDomain` by `closure_minimal` into that closed box; `Fbump (2,0) ≠ 0`
by `ContDiffBump.one_of_mem_closedBall`. Two pin-specific gotchas worth a LESSON line:
`ContDiffBump.contDiff`'s `n` is `ℕ∞`, so `(n := ∞)` fails with
`Application type mismatch: the argument ∞ has type ℕ∞ω but is expected to have type ℕ∞`;
write `(n := (⊤ : ℕ∞))`, which *is* `∞` after the
`scoped[ContDiff] notation3 "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)` coercion.

This does not require a change to the lane, but the zero-force-only sentence in
`ATTEMPTS_A3_FORCE.md` should be softened, and the bump construction is worth promoting to
`research/A01/probes/` or to D01 as `memForceR_bump` — it is the first nonzero closed
`F_R` term in the project and every future non-vacuity audit wants it.

### Finding 4 (severity: cosmetic) — `hT₀ : 0 < T₀` is removable
It is used only to orient `Set.uIcc_of_le` in the integrability step; for `T₀ ≤ 0` the set
`Ico 0 T₀` is empty and the bundle holds with `Bbnd := 0`. The hypothesis-free version
compiles in 5 extra lines (`/tmp/rev137/nohT0.lean`, `EXIT=0`, standard 3 axioms). Not worth
a re-roll on its own; fold in if the module is touched again.

## 3. Consistency

* **Imports**: `A01.Propagation` (→ `A04.Gronwall`) and `A04.Continuity` (→ `A04.Forcing`).
  No new package edge, no `A04 → A01` reverse edge.
* **`sobolevNormAt_nonneg` is new**: `grep -rn 'sobolevNormAt_nonneg' formalization verification
  research` returns only this lane's files. The *same fact about `sobolevNormAt`* is however
  already written inline elsewhere — `A04/HighContinuation.lean:207`
  (`have hnnn : 0 ≤ sobolevNormAt (m : ℝ) w.velocity t := ENNReal.toReal_nonneg`) and, in
  lane 138, `A04/HighContinuationIntegral.lean:104` — with the `gradientSobolevNormAt` twin at
  `A04/EnergyIdentityHigh.lean:115`. (The other `ENNReal.toReal_nonneg` hits in `Section4/`
  — `A02/Order.lean:107`, `I02/Mixed.lean:61`, `R42/BlowupEssSup.lean:113`,
  `A04/NonlinearColumns.lean:{111,164}` — are generic, not about `sobolevNormAt`.)
  **MAINT item**: make `sobolevNormAt_nonneg` the single name (it belongs in
  `A04/Forcing.lean` next to the `def`, together with a `gradientSobolevNormAt_nonneg`) and
  rewrite those call sites.
* **No duplication with `A04/Forcing.lean`**: `grep -rn 'forceSobolevENormL1' formalization`
  finds only the `def`/`abbrev` sites, `MemL1Hm`, `memL1Hm_of_memForceR`, and
  `D01/HalfOrder.lean`'s `forceSobolevENormL1_half_ne_top`. There is **no** pre-existing
  "interval integral ≤ L¹ enorm" lemma anywhere; this lane's Step-1 `ℝ≥0∞` argument is new.
* **Finding 5 (severity: note) — placement.** The module is entirely about the *force*:
  `sobolevNormAt_nonneg`, `intervalIntegral_le_forceSobolevENormL1(_of_memForceR)` name no
  A01 object and belong beside their inputs in `A04/Forcing.lean` / `A04/Continuity.lean`.
  Only `forceCap`, `forceCap_L1` and the `example` are A01-flavoured (they are shaped by
  `gronwall_bddAbove_Ico`). Leaving the whole thing in A01 is defensible because the *bundle*
  is the deliverable; record it as a MAINT split candidate rather than re-rolling now.
* **Finding 6 (severity: note) — CI coverage.** Like `A01/Propagation.lean`, `ForceCap.lean`
  is imported by no `Contracts/` or `Bindings/` module, so `make test`'s closure never
  compiles it; only `experiments/build_changed_lean.py` (and the lead's explicit
  `Section4` sweep) covers it. Unchanged from lane 122's F1.

## 4. Honesty of `ATTEMPTS_A3_FORCE.md` — both failures reproduce verbatim

**Failure 1** (`/tmp/rev137/fail1.lean`, `EXIT=1`):
```
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  sobolevNormAt (↑m) f s
in the target expression
  (fun s => ENNReal.ofReal (sobolevNormAt (↑m) f s)) s = (fun s => ‖G s‖ₑ) s
```
— exactly the recorded text, and the context shows the recorded diagnosis
("the term shown was the un-beta-reduced lambda application") is right.
**Correction to the attribution**: the `set g := …` is a **red herring**. Re-running the same
probe with the `set` line deleted (`/tmp/rev137/fail1b.lean`) gives the *identical* error —
the cause is `setLIntegral_congr_fun`'s un-beta-reduced pointwise goal alone. The ATTEMPTS
heading ("`set g` + `rw` beta issue") should drop the `set`; the body's explanation stands,
and the `show …` fix is the right one.

**Failure 2** (`/tmp/rev137/fail2.lean`, `EXIT=1`):
```
error(lean.unknownIdentifier): Unknown identifier `hasCompactSupport_zero`
```
Confirmed: no such lemma at this Mathlib pin.

---

## 5. For the lead — which A3 rows are ready now

With **A3-L1·f** (this lane) and **A2b-a/a′** (126, 134) closed, and with A04's
`energyIdentityHigh` (121/128, `hpr` discharged), `Cgron`/`young_absorption_high`/
`regularizedNormDerivative` (135 = G2, merged) and `highContinuationIntegral`
(138 = G2b, in review) on the table, the A3 picture changes materially.

**In order:**

1. **A3-M1 — no longer an A01 row. Gate lifted; work already done in A04.**
   The Young absorption is `A04.young_high_real` / `A04.young_absorption_high`
   (`A04/HighContinuation.lean:91,111`), and it *fixes* the constant
   `Cgron m ν = (Chigh m)²/(4ν)` (`:73`, with `Cgron_pos` at `:77`). A01 consumes; delete
   the row or mark it "= A04 G2, DONE (135)".

2. **A3-M2 — gate lifted the moment 138 merges; then it is glue, size S.**
   `A04.highContinuationIntegral` (lane 138, `A04/HighContinuationIntegral.lean:85`) is
   *already* the `hstep` that `gronwall_bddAbove_Ico` consumes, at `t₀ := 0`:
   ```lean
   sobolevNormAt ↑m w.velocity t ≤ sobolevNormAt ↑m w.velocity t₀ +
     ∫ s in t₀..t, (Cgron m ν * sobolevNormAt 2 w.velocity s ^ 2 *
                      sobolevNormAt ↑m w.velocity s + sobolevNormAt ↑m f s)
   ```
   i.e. `y t ≤ y 0 + ∫₀ᵗ (Cgron·k·y + b)` with `y := sobolevNormAt ↑m w.velocity`,
   `k := sobolevNormAt 2 w.velocity ^ 2`, `b := sobolevNormAt ↑m f` — the same parse, no
   adapter. **Recommended next A01 lane (S)**: `Section4/A01/Horizon.lean` instantiating
   `gronwall_bddAbove_Ico` on a `ClassicalSolutionR`. After 137 + 138 its hypothesis list is
   discharged as follows:
   | slot | supplied by | status |
   |---|---|---|
   | `hCgron : 0 ≤ Cgron` | `A04.Cgron_pos m ν hν |>.le` (135) | ready |
   | `hy0 : 0 ≤ y 0` | `A01.sobolevNormAt_nonneg` (**this lane**) | ready |
   | `hy`, `hk` continuity | `A04.continuousOn_sobolevNormAt_velocity` (`Continuity.lean:105`) | ready |
   | `hknn` | `sq_nonneg` | ready |
   | `hb`, `hbnn`, `hbbnd` | `A01.forceCap` (**this lane**) | ready |
   | `hstep` | `A04.highContinuationIntegral` at `t₀ = 0` (138) | ready once 138 merges |
   | `hkbnd : ∫₀ᵗ‖u‖²_{H²} ≤ Kbnd` | **A3-L1·k** | **the only hole** |
   So after 138, **`Kbnd` is the single missing input** to the per-order uniform bound.

3. **A3-L2 (`horizon := S`) — ready now, size S, no dependencies.**
   Dissolved by 134's `forced_global_of_bound_unconditional`: the a-priori bound hands the
   whole prescribed `[0,S]`, so `horizon` is a definition plus a one-line lemma, not a choice
   over `exists_local`'s `∃ T`. Nothing in it waits on A04 or C1b. Good filler lane.

4. **A3-L1·k (the order-2 cap) — gate only *half* lifted; still M, still blocked.**
   Precise statement wanted (unchanged from `A3_SPLIT.md:70`): a **one-directional** comparison
   `sobolevNormAt 2 (⇑(U t)) ≤ c · ‖u t‖_{SobolevSpace 1 (q+1)}` with `c` independent of `t`,
   turning `exists_local`'s single quantitative clause `‖u‖ ≤ ‖u₀‖+1` into
   `Kbnd := c²·(‖u₀‖+1)²·T₀` (`∫₀ᵗ k ≤ t·sup k`). It is **not** a C1b norm identity (119's F7).
   What it needs, given 132:
   * **From the finite-order constructor**: `D01.exists_isSobolevDatum_of_memLp_derivs`
     (`D01/FiniteOrderConstructor.lean:269`) now takes `HasWeakDerivsL2 z m` to
     `∃ A : RealVectorSobolev ↑m, IsSobolevDatum ↑m z A`. So **C1b-m-D is closed on the D01
     side** (132, merged as #137). The **residual obligation is row `D-euler-pairing`**: the
     Euler side must supply `HasWeakDerivsL2 (⇑(U t)) 2`, i.e. `MemLp (⇑(U t)) 2` plus the
     order-≤2 *Schwartz-pairing* form of the weak derivatives of `⇑(U t)`
     (integration by parts against test functions). Until that lands, A3-L1·k cannot even name
     the order-2 datum, and — the totalization trap — a cap stated without it would be
     **vacuously true** (`sobolevENorm = ⊤ ⇒ sobolevNormAt = ⊤.toReal = 0`).
   * **`orderZeroDatumCLM` does not generalize.** `A01/DatumPathContinuity.lean:103` bundles
     the order-**0** datum as a genuine `EulerMeanSolenoidal.L2 →L[ℝ] RealVectorSobolev 0`, and
     its operator norm is exactly the `c` that an order-0 cap would need for free. There is no
     order-2 analogue: per `C1B_SPLIT.md:131`, *lowering* is a CLM but *raising* is
     multiplication by `(1+‖ξ‖²)^{1/2}`, unbounded on `L²`, so 125/132's constructor hands over
     **no bounded operator to take a norm of**. The constant `c` at order 2 must come from a
     hand-made bound (Plancherel-with-constants between the Euler `SobolevSpace 1 (q+1)` norm
     and the D01 order-2 datum norm), not from bundling. Size stays **M**, and it is the last
     blocker on the whole A3 chain.

5. **A3-Tm / A2b-c / H1 / T1** — unchanged by this lane. A3-Tm still needs the shared-`T₀`
   existence statement (F8); H1 still has only `exists_uniform_restart_time` as a candidate.

**Suggested order:** A3-L2 (S, ready) → the `gronwall_bddAbove_Ico` instantiation lane once
138 merges (S, ready modulo `Kbnd`) → `D-euler-pairing` (the Euler-side Schwartz pairing,
M — it unblocks A3-L1·k, C1b-c8-m and hence C1b) → A3-L1·k.
