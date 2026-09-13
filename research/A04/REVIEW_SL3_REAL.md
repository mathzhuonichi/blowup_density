# Review — lane 082, task A04, sub-lemma SL3 step 3a (real-carrier pairing identities)

Reviewer: opus (lane-review, light & strict).  Commit under review: `7f43e65`
(`[082-A04] SL3 step 3a: real-carrier skew-adjointness, lowering pairing, and
lowering-symbol order independence`).  Worktree
`.claude/worktrees/082-A04-sl3-real-pairing`; read/build only, no repo file other
than this one was written, no git command other than `status`/`log`/`show`/`diff`.

## Verdict

**ACCEPT-WITH-NOTES.**

The Lean is sound and the three delivered lemma families are faithful.  The module
builds, elaborates with **zero** warnings at the default heartbeat budget, is
`sorry`/`axiom`/`native_decide`-free, all 11 declarations depend only on
`[propext, Classical.choice, Quot.sound]`, and `make check` passes.

The two questions that actually mattered I ran rather than argued:

* **The real inner product is the right one.**  `#synth` confirms the carrier chain
  `PiLp.innerProductSpace → realSobolevInnerProductSpace → L2.innerProductSpace (𝕜 = ℝ)`,
  and I closed the *whole* chain from `RealVectorSobolev m` down to
  `∑ⱼ re ⟪·,·⟫_ℂ` using only this lane's two bridges.  Lane 076's F2 obstacle is
  genuinely removed.
* **The special case step 3b needs really comes out.**  I proved
  `⟪lowerDatum (m+1) (m-1) A, A⟫_ℝ = ‖lowerDatum (m+1) m A‖²` — the reconciliation
  verbatim — in 4 lines from `real_inner_lowering_pairing` + `angularOrderLowering_self`.

Notes: one real usability hazard in the shape of Lemma 2 (F1), and four gaps in the
step-3b brief (F2–F5), all documentation.  Nothing requires changing a proved
statement; nothing blocks the merge.

---

## Findings

### F1 — Medium (usability, not soundness).  Lemma 2's midpoint `(r + t) / 2` cannot be `rw`-normalized: the order is a dependent argument.

**Location:** `formalization/NSFormalization/Section4/A04/RealPairing.lean:214`
(`real_inner_lowering_pairing`), RHS `‖angularOrderLowering s ((r + t) / 2) hms w‖ ^ 2`.

`angularOrderLowering s r hrs` takes the order `r : ℝ` *and* a proof `hrs : r ≤ s`
that mentions it.  So after `have h := real_inner_lowering_pairing (m+1) (m-1) (m+1) …`,
the natural next step

```
rw [show (m - 1 + (m + 1)) / 2 = m from by ring] at h
```

**fails** with `motive is not type correct` (verified, probe B; full error kept in
`/tmp/rev082/probeB.lean` output).  The working form is `simp only`, which has a
strategy for proof-valued dependencies:

```
simp only [show (m - 1 + (m + 1)) / 2 = m from by ring] at h
```

This is not recorded anywhere — not in the module docstring, not in
`ATTEMPTS_SL3_REAL.md` §"Failed / adjusted approaches", not in the step-3b brief —
and it is the *first* thing the 3b worker will hit, since every use of Lemma 2 has to
normalize the midpoint.

**Fix (pick one, documentation-only is enough):**
(a) add one line to `ATTEMPTS_SL3_REAL.md` §"Failed / adjusted approaches" and one to
the brief: *"the midpoint is syntactic; normalize it with `simp only [show …]`, not
`rw` — `rw` fails with a non-type-correct motive"*; or
(b) if a V2 of the lemma is ever written, state it as
`{mid : ℝ} (hmid : r + t = 2 * mid) … ‖angularOrderLowering s mid hms w‖ ^ 2`,
which removes the hazard at the source.  Not worth reopening this lane for.

### F2 — Medium.  The step-3b brief omits `gradientSobolevENorm_toReal_sq_eq_datum_sum` — the thing being reconciled *to*.

**Location:** `research/A04/ATTEMPTS_SL3_REAL.md` §"Brief for step 3b", items 1–5.

The brief explains how to produce `⟪datum_{m-1} v, datum_{m+1} v⟫ = ‖datum_m v‖²`
but never names the right-hand side of the dissipation identity that this is aimed at:
`A04.gradientSobolevENorm_toReal_sq_eq_datum_sum`
(`formalization/NSFormalization/Section4/A04/LaplacianDatum.lean:130`), which delivers
`grad² = ∑ⱼ ‖D_j (datum_{m+1} u)‖²`.  Lane 076's `ATTEMPTS_SL3_PAIRING.md` does name it,
so a worker reading both files recovers it — but the task brief for 3a asked this file
to be self-contained, and as written a 3b worker briefed only by it does not know what
the target is.

**Fix:** add it as item 6 with the file:line above.

### F3 — Medium.  The step-3b brief omits `isSobolevDatum_add`, one of the two assembly inputs.

**Location:** same section, item 5.

The Laplacian datum assembly `datum_m(Δu) = ∑ⱼ D_j (D_j (datum_{m+2} u))` needs
`isSobolevDatum_partialDeriv` **twice** *plus datum additivity over the three
directions*.  The brief names the former (see F4) and not the latter.  In tree at
`Section4/D01/ForceClass.lean:261` (`D01.isSobolevDatum_add`, the `RealVectorSobolev`
form — this is the one wanted) and `Section4/A03/VectorTameProduct.lean:180`
(`A03.isSobolevDatum_add`, with an `hs : 2 ≤ s` side condition).

**Fix:** name `D01.isSobolevDatum_add` (`ForceClass.lean:261`) in item 5.

### F4 — Low.  Three citations in the brief carry no `file:line`.

**Location:** `ATTEMPTS_SL3_REAL.md:112` and `:122`.

* `isSobolevDatum_partialDeriv` (:122) → `Section4/D01/DerivativeDatum.lean:245`.
* `A04.inner_energy_assembly` (:112) → `Section4/A04/HighEnergy.lean:103`.
* (Everything else in the brief *is* cited with file:line, and every such citation I
  opened is correct — see the positive record below.)

### F5 — Low.  The brief drops the scalar↔vector datum bridge that item 5 needs to typecheck.

**Location:** same section, item 5.

`A03.lowerDatum` is a **scalar** map `RealSobolevHilbert s → RealSobolevHilbert r`,
while `D01.isSobolevDatum_unique` is a **vector** statement about
`RealVectorSobolev s`.  Getting from "`datum_{m+1} v` lowers to a datum at order
`m-1`" to "`datum_{m-1} v` *is* that lowering" therefore goes through the
componentwise bridge `A03.isSobolevDatum_iff`
(`Section4/A03/VectorTameProduct.lean:54`) and the scalar lowering fact
`A03.IsScalarSobolevDatum.lower` (`Section4/A03/ScalarTameProduct.lean:114`).
Lane 076's ATTEMPTS listed both; this brief lists neither.

Related and also unflagged (**Low**): `isSobolevDatum_partialDeriv` is indexed by
`m : ℕ` with orders `(m:ℝ)+1 → (m:ℝ)`.  To reach the order-`m-1` datum of `∂ⱼu` — the
left slot of the reconciliation — it must be instantiated at `m-1 : ℕ`, which needs
`1 ≤ m` and a `Nat.cast_sub` step to see `((m-1 : ℕ) : ℝ) + 1 = (m : ℝ)`.  Worth one
sentence so 3b does not discover it mid-proof.

### F6 — Info.  076's `inner_angularOrderLowering` is bypassed by this lane.

Lane 076 delivered self-adjointness of the full lowering operator and its review (F1)
called it "a *required* input" for step 3.  This lane does not use it: Lemma 2 is
re-derived directly from `angularOrderLoweringMid_coeFn` + the symbol algebra.  That is
the **right** call — deriving the pairing from self-adjointness would need a composition
law `Λ_{s→r} ∘ Λ_{s→t} = Λ_{s→mid} ∘ Λ_{s→mid}` that is not in tree — but it means
076's step-2 deliverable is now unused by the SL3 route, and neither the ATTEMPTS nor
the module docstring says so.  No action needed; recorded so the next reader does not
re-derive the question.

### F7 — Info (cosmetic).  Redundant import.

`RealPairing.lean:2` imports `NSFormalization.Section4.D01.DerivativeDatum`, which is
already reached transitively (`LaplacianPairing → LaplacianDatum → DerivativeDatum`).
Harmless, and arguably documents a direct dependency (`angularDirectionalDerivativeReal`
is used from it).  Leave it.

### F8 — Info.  Namespace vs directory: acceptable.

The module lives in `Section4/A04/` and opens `namespace NSFormalization.Paper3`.
This matches the immediate precedent — lane 076's `Section4/A04/LaplacianPairing.lean`
does exactly the same, as does `Section4/D01/DerivativeDatum.lean`, which is where
`Paper3.angularDirectionalDerivative` itself is defined.  Changing it to
`Section4.A04` here would *break* the convention and split the `Paper3` symbol
namespace across the SL3 route.  **Keep `NSFormalization.Paper3`.**  (Same call as
076's review F6; flagged only because a `Paper3/`-directory grep will not find these.)

### F9 — Info.  The task brief's line numbers for this module are stale.

Actual: `real_inner_eq_re_complex` :66, `realSobolev_inner_eq_ambient` :77,
`real_inner_angularDirectionalDerivative` :84,
`real_inner_angularDirectionalDerivativeReal` :96, `lowering_mid_symbol_eq` :114,
`lowering_mid_symbol_order_indep` :138, `angularOrderLoweringMid_self` :148,
`angularOrderLowering_self` :157, `inner_loweringMid_pairing` :168,
`inner_lowering_pairing_complex` :199, `real_inner_lowering_pairing` :214.
(11 declarations, not the 10 the brief lists — `angularOrderLoweringMid_self` is the
extra one, and it is used by `angularOrderLowering_self`.)

---

## Positive record (what passed)

### Check 1 — compiles, clean, standard axioms

All five gates pass; see §Commands.  Notably the module elaborates to **empty
output**: no warnings, no `set_option`, no raised heartbeat.

### Check 2a — the real inner product is the same instance `RealVectorSobolev` uses

Probe A (`/tmp/rev082/probeA.lean`, not committed) resolved the instance chain:

```
#synth InnerProductSpace ℝ (Lp ℂ 2 volume)        -->  L2.innerProductSpace
#synth Inner ℝ (Lp ℂ 2 volume)                    -->  L2.instInnerSubtypeAEEqFunMem…
#synth InnerProductSpace ℝ (RealSobolevHilbert 1) -->  realSobolevInnerProductSpace 1
#synth InnerProductSpace ℝ (RealVectorSobolev 1)  -->  PiLp.innerProductSpace …
```

and then three `example`s, all of which **elaborated**:

* `(inner ℝ x y : ℝ) = ∫ ξ, (inner ℝ (x ξ) (y ξ) : ℝ) := MeasureTheory.L2.inner_def x y`
  — so the LHS of `real_inner_eq_re_complex` is literally `L2.innerProductSpace` at
  `𝕜 = ℝ`, the instance the ambient carrier uses, not `Inner.rclikeToReal ℂ`;
* the **full chain**, closed with this lane's two bridges only:
  ```
  example (m : ℝ) (x y : RealVectorSobolev m) :
      (inner ℝ x y : ℝ) = ∑ j : Fin 3, RCLike.re (inner ℂ (x j : FourierData) (y j : FourierData)) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [realSobolev_inner_eq_ambient, real_inner_eq_re_complex]
  ```
* `‖x‖ = ‖(x : FourierData)‖ := rfl` for `x : RealSobolevHilbert m` — the norm bridge
  the ATTEMPTS claims is `rfl`, confirmed.

So `realSobolev_inner_eq_ambient` does connect the subtype inner to exactly the ambient
`L2` one, it genuinely is `rfl` (`Submodule.innerProductSpace` inherits the ambient
inner on coercions), and lane 076's F2 gap is closed as claimed.  Note the subtype
`realSubspace s` ignores its order argument (`RealSobolev.lean:118`), so
`RealSobolevHilbert (m-1)` and `RealSobolevHilbert (m+1)` are defeq — which is why the
cross-order pairings below typecheck at all.

### Check 2b — the step-3b special case comes out exactly

Probe B3 (`/tmp/rev082/probeB3.lean`) — **elaborates, no errors**:

```
example (m : ℝ) (h1 : m - 1 ≤ m + 1) (h3 : m ≤ m + 1) (A : RealSobolevHilbert (m + 1)) :
    (inner ℝ (lowerDatum (m + 1) (m - 1) h1 A) A : ℝ) = ‖lowerDatum (m + 1) m h3 A‖ ^ 2 := by
  have h := real_inner_lowering_pairing (m + 1) (m - 1) (m + 1) h1 le_rfl (by linarith) (A : FourierData)
  rw [angularOrderLowering_self] at h
  simp only [show (m - 1 + (m + 1)) / 2 = m from by ring] at h
  exact h
```

That is the reconciliation `⟪datum_{m-1} v, datum_{m+1} v⟫ = ‖datum_m v‖²` verbatim, at
`s = m+1`, `r = m-1`, `t = m+1`, midpoint `m`, already in the `A03.lowerDatum` subtype
face step 3b will meet — `A03.coe_lowerDatum` and the subtype norm/inner bridges are all
`rfl`, so `exact h` closes it with no glue.  `angularOrderLowering_self` does collapse
the `t = s` slot as advertised.  The only friction is F1.

### Check 2c — the sign, the midpoint, the dilation and the `re` are all load-bearing

Probe C (`/tmp/rev082/probeC.lean`): five deliberately-false variants, each fed either
the identical proof script or the delivered lemma as a term.  **All five fail**; the
positive control passes.

| probe | false statement | result |
|---|---|---|
| C1 | symmetric sign `⟪f, D g⟫_ℝ = ⟪D f, g⟫_ℝ`, Lemma 1's own script | `error: unsolved goals` |
| C2 | same, discharged by `real_inner_angularDirectionalDerivative` | `error: Type mismatch` |
| C3 | Lemma 2 with midpoint `r` instead of `(r+t)/2`, own script | `error: unsolved goals` |
| C4 | closed form `sobolevBesselWeight (r-s) ξ` (undilated) | `error: Type mismatch` |
| C5 | bridge with `RCLike.im` instead of `re` | `error: Type mismatch` |
| C6 | the **true** Lemma 1 (control) | elaborates |

So no wrong sign convention is making Lemma 1 true for the wrong reason, the midpoint is
not an artefact, and the `frequencyUnit •` inside the closed form is doing real work.
Non-vacuity: `angularOrderLowering_self` exhibits the family as the identity at `r = s`,
so the operators are not secretly zero.

### Check 2d — the closed form is consistent with the definitions

Opened both: `sobolevBesselWeight a ξ = ((1 + ‖ξ‖²)^(a/2) : ℝ)`
(`Paper3/SobolevHilbertModel.lean:24`) and
`angularWeightSymbol a ξ = W_a (c•ξ) * W_{-a} ξ` with `c = frequencyUnit`
(`Paper3/AngularSobolevCoordinates.lean:13`); both unfoldings confirmed by `rfl`
(probe D).  Hand-derivation:

```
W_r(cξ)·W_{-r}(ξ) · W_{r-s}(ξ) · W_{-s}(cξ)·W_s(ξ)
  = [W_r(cξ)·W_{-s}(cξ)] · [W_{-r}(ξ)·W_{r-s}(ξ)·W_s(ξ)]
  = W_{r-s}(cξ) · W_0(ξ) = W_{r-s}(cξ)             ✓
```

matching `lowering_mid_symbol_eq` exactly.  Its LHS is character-for-character the
symbol of `angularOrderLoweringMid_coeFn` (`LaplacianPairing.lean:139`), so the lemma is
about the right operator — confirmed by a probe deriving
`(angularOrderLoweringMid s r hrs y) =ᵐ fun ξ => W_{r-s}(c•ξ) * y ξ` from the two.  The
degenerate case `r = s` gives `1`, and `lowering_mid_symbol_order_indep` follows because
the closed form sees only `r - s`.  The pairing exponent arithmetic is right:
`(r-s) + (t-s) = 2·((r+t)/2 - s)`.

### Check 3 — consistency

* Imports: two, both canonical `NSFormalization` modules (F7 on redundancy).  This is a
  `formalization/` module, not `Contracts/*`, so the contract import policy does not
  apply; `check_contracts.py` passes inside `make check` anyway.
* **No `def` at all** — the module is 11 theorems.  Nothing is restated; every symbol and
  operator (`angularWeightSymbol`, `sobolevBesselWeight`, `frequencyUnit`,
  `angularOrderLowering(Mid)`, `angularDirectionalDerivative(Real)`,
  `angularFrequencyDilation`) is used from upstream.
* No duplication of 076: a grep finds no prior `angularOrderLowering_self` /
  `sobolevOrderLowering_self` / `orderLowering_refl`, and `inner_loweringMid_pairing`
  (a *pairing* at two orders) is a different statement from 076's
  `inner_angularOrderLoweringMid` (self-adjointness at one order).  See F6.
* Commit touches exactly three files (module + ATTEMPTS + axiom scratch), no
  `Contracts/`, no `Tests/`, no generated file.

### Check 4 — honesty of the ATTEMPTS

* **"Mathlib has no `LinearIsometryEquiv.restrictScalars`" — CONFIRMED** in this rev.
  `grep -c restrictScalars Mathlib/Analysis/Normed/Operator/LinearIsometry.lean` → `0`.
  A library-wide grep for `restrictScalars` intersected with `LinearIsometry` returns
  exactly three hits, all docstrings of the form "`X.restrictScalars` as a
  `LinearIsometry`" for `ContinuousAlternatingMap`
  (`Analysis/Normed/Module/Alternating/Basic.lean:360`), `ContinuousMultilinearMap`
  (`.../Multilinear/Basic.lean:646`) and `ContinuousLinearMap`
  (`Analysis/Normed/Operator/Basic.lean:439`).  None produces a `≃ₗᵢ[ℝ]`, so
  `inner_map_map` is genuinely unavailable for the real inner product.  Route A really
  is blocked; Route B is the right call.
* Cited declarations opened at their cited lines — all correct:
  `D01.isSobolevDatum_unique` `ForceClass.lean:286` ✓,
  `A03.lowerDatum` `RealAngularProduct.lean:140` ✓, `A03.coe_lowerDatum` `:144` ✓,
  `Paper3.realSobolevInnerProductSpace` `RealPositiveDensity.lean:27` ✓,
  `RealVectorSobolev` `RealVectorPositiveDensity.lean:15` ✓,
  `angularDirectionalDerivativeReal(_coe)` `DerivativeDatum.lean:134/141` ✓,
  `weight_product_order_indep` `:192` ✓, `mid_symbol_order_independent` `:207` ✓.
* The negative record is real and useful: the blocked Route A, the
  `sobolevBesselWeight_mul` **rewrite-ordering** hazard (`-r + (r-s)` must be normalized
  by an interleaved `show … from by ring` before the next factor matches — the same
  buffer-order trap as in `weight_product_order_indep`), and the ill-typed single-subtype
  skew-adjointness (resolved at the shared ambient carrier).  The choice of Lemma 3 form
  (a) over the commutation (b) is argued honestly, and the recipe for (b) is recorded
  rather than silently dropped.
* Both `rfl` claims in the ATTEMPTS (`realSobolev_inner_eq_ambient`, the norm bridge)
  are true — verified, not taken on trust.
* Gaps in the step-3b brief: F2 (`gradientSobolevENorm_toReal_sq_eq_datum_sum` missing),
  F3 (`isSobolevDatum_add` missing), F4 (two citations without file:line), F5 (the
  scalar↔vector datum bridge and the `ℕ`-index wrinkle).

---

## Commands and results

Run inside `.claude/worktrees/082-A04-sl3-real-pairing`, after
`bash scripts/lean-install.sh` (idempotent, ended `== OK`), `. scripts/lean-env.sh`,
`export LEAN_NUM_THREADS=6`; `lake` only from `verification/`, one process at a time.

1. `cd verification && lake build NSFormalization.Section4.A04.RealPairing`
   → **`Build completed successfully (9893 jobs).`**, exit 0.  Warnings are all replayed
   pre-existing upstream ones (`Source/ViscosityPacket.lean:34` unused simp arg,
   `Paper3/SobolevDirectionalDerivative.lean:103` `SchwartzMap.smul_apply` deprecation) —
   none from this module.
2. `cd verification && lake env lean ../formalization/NSFormalization/Section4/A04/RealPairing.lean`
   → **empty output**, exit 0.
3. `cd verification && lake env lean ../research/A04/axioms_sl3_real.lean`
   → **11** declarations, each exactly `[propext, Classical.choice, Quot.sound]`:
   `real_inner_eq_re_complex`, `realSobolev_inner_eq_ambient`,
   `real_inner_angularDirectionalDerivative`, `real_inner_angularDirectionalDerivativeReal`,
   `lowering_mid_symbol_eq`, `lowering_mid_symbol_order_indep`,
   `angularOrderLoweringMid_self`, `angularOrderLowering_self`,
   `inner_loweringMid_pairing`, `inner_lowering_pairing_complex`,
   `real_inner_lowering_pairing`.
4. `grep -nE 'sorry|admit|axiom|native_decide|maxHeartbeats|set_option' …/RealPairing.lean`
   → no match (exit 1).  Same grep over `research/A04/axioms_sl3_real.lean` → no match.
5. `make check` → **exit 0** (architecture/plan check, contract import policy,
   `test_contract_policy` 13/13, `check_work_queue`: "30 work items: ownership, contract
   registration and task cards consistent").
6. `git show --stat 7f43e65` → 3 files, +370, nothing under `Contracts/` or `Tests/`.
7. Reviewer probes, written to `/tmp/rev082/` only:
   * **A** — instance `#synth` chain + the full `RealVectorSobolev → ∑ re ⟪·,·⟫_ℂ`
     reduction + the `rfl` norm bridge → all elaborate (check 2a).
   * **B / B2 / B3** — the `r = s-2, t = s` and `m-1 / m+1` instantiations, ambient and
     `A03.lowerDatum` faces.  `rw` on the midpoint **fails** (F1); `simp only` **works**;
     B3 closes the reconciliation with `exact h` (check 2b).
   * **C** — five false variants, all rejected; positive control accepted (check 2c).
   * **D** — `angularWeightSymbol` / `sobolevBesselWeight` unfoldings by `rfl`, the
     closed form transported onto `angularOrderLoweringMid_coeFn`, the `r = s`
     degeneration → all elaborate (check 2d).

---

## Is step 3b ready, and how big?

**Ready.**  After this lane nothing analytic is missing: every input step 3b needs now
exists in tree, and I have working skeletons for the two places a worker would expect
trouble (probe A for the `PiLp`/subtype descent, probe B3 for the reconciliation — four
lines each).  The route is fully determined:

1. assemble `datum_m(Δu) = ∑ⱼ D_j (D_j (datum_{m+2} u))` from `isSobolevDatum_partialDeriv`
   (`DerivativeDatum.lean:245`, twice) + `D01.isSobolevDatum_add` (`ForceClass.lean:261`);
2. fire real skew-adjointness (this lane :84 / :96) to move one `D_j` across, giving
   `-∑ⱼ ⟪D_j datum_m u, D_j datum_{m+2} u⟫`;
3. rewrite both slots as data of `∂ⱼu` (`isSobolevDatum_partialDeriv` + uniqueness
   `ForceClass.lean:286`, through `A03.isSobolevDatum_iff` / `IsScalarSobolevDatum.lower`),
   landing on orders `m-1` and `m+1`;
4. apply Lemma 2 at `s = m+1, r = m-1, t = m+1` with `angularOrderLowering_self` — probe B3
   is the finished four-line proof — to reach `∑ⱼ ‖datum_m(∂ⱼu)‖²`;
5. match against `gradientSobolevENorm_toReal_sq_eq_datum_sum` (`LaplacianDatum.lean:130`)
   and weaken `=` to `≤` for `inner_energy_assembly` (`HighEnergy.lean:103`, `0 ≤ ν`).

**Size: M**, and the residual cost is bookkeeping, not mathematics — the three things that
will eat the time are (i) the F1 dependent-rewrite hazard at every use of Lemma 2,
(ii) the `ℕ`-vs-`ℝ` order casting (`isSobolevDatum_partialDeriv` is `ℕ`-indexed, so the
`m-1` slot needs `1 ≤ m` and `Nat.cast_sub`), and (iii) the `PiLp 2` `Fin 3` descent,
which probe A shows is three lines.  Folding F1–F5 into the ATTEMPTS before opening the
3b lane would remove essentially all of the discovery cost.
