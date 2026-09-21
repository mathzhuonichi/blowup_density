# Review — lane 088, task A04, sub-lemma SL3 step 3b (Laplacian datum + dissipation identity)

Reviewer: opus (lane-review, light & strict).  Commit under review: `7a25d85`
(`[088-A04] SL3 step 3b: the Laplacian datum and the dissipation identity
⟪G, datum Δu⟫ = -‖∇u‖²_{H^m}, delivering hlap`).  Worktree
`.claude/worktrees/088-A04-sl3-assembly`; read/build only, no repo file other than this
one was written, no git command other than `status` / `log` / `show --stat`.

## Verdict

**ACCEPT-WITH-NOTES.**

The Lean is sound and the two delivered statements are faithful to `eq:Rhigh`'s dissipation
term.  The module builds, elaborates with zero warnings at the default heartbeat budget, is
`sorry` / `axiom` / `native_decide` / `set_option`-free, all **20** declarations depend only on
`[propext, Classical.choice, Quot.sound]`, and `make check` passes.

Three things mattered and I ran them rather than argued them.

* **The `hlap` really is consumable.**  I compiled the *complete* A04-route instantiation of
  `A04.inner_energy_assembly` — `hmom` from `momentum_datum` (SL2), `hlap` from this lane's
  `inner_datum_laplacian_le` with `L` identified by Part 1 — on a real `ClassicalSolutionR`.
  It closes.  But **not** token for token: it needs ~5 lines of glue, and the naive one-shot
  `exact inner_datum_laplacian_le …` into the `gradientSobolevNormAt` goal **blows the 200000
  heartbeat budget at `isDefEq`**.  Finding 1, with the compiled recipe.
* **The sign is load-bearing.**  I re-ran the `inner_datum_laplacian` proof script verbatim
  against the `+` right-hand side: it fails with a sign type mismatch.  The `-` is produced by
  `Paper3.real_inner_angularDirectionalDerivative` (skew-adjointness) and cannot be dodged.
* **Nothing is vacuous.**  Every hypothesis of the three headline theorems is inhabited for an
  arbitrary `SmoothL2Field Space` (`D01/SmoothDatum.lean:290`
  `exists_isSobolevDatum_of_contDiff_memLp`), and my instantiation builds them from an actual
  solution slice.  Combined with `D01.isSobolevDatum_unique`, `isSobolevDatum_laplacian` pins
  `laplacianDatum m A` **uniquely** — a wrong implementation cannot satisfy it.

The notes are one usability gap (finding 1), one duplicated definition (finding 2), one
inaccurate sentence in the negative record (finding 3) and two cosmetics.

## Findings

### 1. MINOR (usability, blocking nothing) — `hlap` does not match token for token; the naive application times out

*Location:* `LaplacianAssembly.lean:324` `inner_datum_laplacian_le` vs the consumer
`HighEnergy.lean:101` `inner_energy_assembly` field `hlap : ⟪G, L⟫ ≤ - grad ^ 2`.

Two mismatches, both real:

* `L`.  `momentum_datum` (`MomentumDatum.lean:167`) hands the assembly an *arbitrary* datum
  `L` of `fun x => spatialLaplacian w.velocity t x`; `inner_datum_laplacian_le` only speaks
  about `laplacianDatum m A`.  The bridge is `isSobolevDatum_unique hL (isSobolevDatum_laplacian m hA)`
  — and the field-level defeq
  `spatialLaplacian w.velocity t ≡ spatialLaplacian (A03.lift Z.field) 0` **does** hold and is
  cheap (compiled).  Good.
* `grad`.  The lemma's right-hand side is `(A03.gradientSobolevENorm (m:ℝ) Z.field).toReal ^ 2`;
  the assembly's is `gradientSobolevNormAt (m:ℝ) w.velocity t ^ 2`
  (`LaplacianDatum.lean:~100`).  The two **are** `rfl` once `Z.field := fun x => w.velocity (t,x)`,
  but that `rfl` must be *stated* as a `have`.  Leaving it to unification inside `exact` makes
  the elaborator unfold `gradientSobolevENorm → columnsSobolevENorm → sobolevENorm` (an `⨅` over
  a subtype of data) and it dies:

  ```
  error: (deterministic) timeout at `isDefEq`, maximum number of heartbeats (200000)
  ```

  This is the *same* hazard the lane already recorded for Part 1 — it simply also bites on the
  consumer side, which the lane did not test.

The `Z : SmoothL2Field` wrapper of the slice **is** available:
`C01.velocity_slice_memHInfty_and_smoothL2 w ht |>.2 : A05.SmoothL2 (fun x => u.velocity (t,x))`
(`C01/VelocityJets.lean:65`) and `A05.SmoothL2` (`A05/SmoothJets.lean:44`) is exactly the two
fields of `EulerLpTranslation.SmoothL2Field`, so `⟨fun x => w.velocity (t,x), hsl.1, hsl.2⟩`
type-checks directly.

*Compiled glue (verbatim, exit 0):*

```lean
have htIco : t ∈ Ico (0 : ℝ) T := ⟨ht.1.le, ht.2⟩
have hsl := (C01.velocity_slice_memHInfty_and_smoothL2 w htIco).2
let Z : SmoothL2Field Space := ⟨fun x => w.velocity (t, x), hsl.1, hsl.2⟩
obtain ⟨A, hA⟩   := exists_isSobolevDatum_of_contDiff_memLp Z.smooth Z.integrable ((m : ℝ) + 2)
obtain ⟨A', hA'⟩ := exists_isSobolevDatum_of_contDiff_memLp Z.smooth Z.integrable ((m : ℝ) + 1)
have hGt  : IsSobolevDatum (m : ℝ) Z.field (G t) := hGd t htIco
have hLeq : L = laplacianDatum m A :=
  isSobolevDatum_unique hL (isSobolevDatum_laplacian (Z := Z) m hA)
have hstep : (inner ℝ (G t) (laplacianDatum m A) : ℝ)
    ≤ - (A03.gradientSobolevENorm (m : ℝ) Z.field).toReal ^ 2 :=
  inner_datum_laplacian_le m hGt hA' hA
have hg : gradientSobolevNormAt (m : ℝ) w.velocity t
    = (A03.gradientSobolevENorm (m : ℝ) Z.field).toReal := rfl
have hlap : ⟪G t, L⟫ ≤ - gradientSobolevNormAt (m : ℝ) w.velocity t ^ 2 := by
  rw [hLeq, hg]; exact hstep
exact inner_energy_assembly hν hd
  (momentum_datum w hf hm hGd hGc ht hL hN hP hF) hlap hpr hnl hGn hFn
```

Note the two `have`s (`hstep`, `hg`) are what keep it inside the heartbeat budget; inlining
either one reproduces the timeout.

*Suggested fix (small, for the G1 assembly lane rather than a re-roll of 088):* add a
`sobolevNormAt`-shaped corollary next to `inner_datum_laplacian_le`, e.g.

```lean
theorem inner_datum_laplacian_le_normAt {u : SpaceTimeField} {t : ℝ} {Z : SmoothL2Field Space}
    (hZ : Z.field = fun x => u (t, x)) … :
    (inner ℝ G (laplacianDatum m A) : ℝ) ≤ - gradientSobolevNormAt (m : ℝ) u t ^ 2
```

and record the timeout in `ATTEMPTS_SL3_ASSEMBLY.md` so the next worker does not rediscover it.

### 2. MINOR (duplication) — `vectorLowerDatum` already exists as `D01.lowerVectorL`

*Location:* `LaplacianAssembly.lean:209` `vectorLowerDatum`, `:214` `isSobolevDatum_vectorLower`.

`D01/HalfOrder.lean:103` already defines `lowerVectorL (s r : ℝ) (hrs) : RealVectorSobolev s →L[ℝ]
RealVectorSobolev r` with `lowerVectorL_apply … = lowerDatum s r hrs (A i) := rfl` (:112).  I
verified the new `def` is the same map:

```lean
example (s r : ℝ) (hrs : r ≤ s) (A : RealVectorSobolev s) :
    vectorLowerDatum s r hrs A = lowerVectorL s r hrs A := rfl   -- compiles
```

Likewise `isSobolevDatum_vectorLower` is exactly the three-line pointwise core already inlined
in `D01.isSobolevPath_lower` (`HalfOrder.lean:120-127`).

Mitigating: `LaplacianAssembly` does not import `D01.HalfOrder` today (its chain is
`RealPairing → LaplacianPairing → LaplacianDatum → HighEnergy` plus `D01.DerivativeDatum` and
three A03 modules), so this was not a knowing re-statement.  Still, "don't restate what the
tree already has" is the house rule.  *Fix (cheap, follow-up MAINT or the SL5 lane):* import
`D01.HalfOrder`, delete `vectorLowerDatum`, keep `coe_vectorLowerDatum` re-pointed at
`lowerVectorL`; or, if the import is unwelcome, add the one-line `rfl` bridge and a docstring
pointer.  Not blocking — nothing is unsound, and the duplicate is definitionally the original.

### 3. MINOR (honesty of the record) — one over-claimed `rfl` in `ATTEMPTS_SL3_ASSEMBLY.md`

*Location:* `research/A04/ATTEMPTS_SL3_ASSEMBLY.md:87-91`, the bullet
"`(m:ℝ)+1-1 ≟ (m:ℝ)` and `RealSobolevHilbert ((m:ℝ)+1-1) = RealSobolevHilbert (m:ℝ)`. These
*are* `rfl`".

The **first** conjunct is false.  As a real-number equation it is not `rfl`:

```
example (m : ℕ) : ((m : ℝ) + 1 - 1) = (m : ℝ) := rfl
-- error: Type mismatch … expected ↑m + 1 - 1 = ↑m
```

The **second** conjunct is true and is the one that matters: the *type* equality holds by `rfl`
because `Source.RealSobolev.realSubspace (_s : ℝ)` (`RealSobolev.lean:119`) **ignores its order
argument** — the carrier is the same closed real subspace of `FourierData` at every order.  That
is why `isSobolevDatum_partialDeriv`'s output (living at `RealSobolevHilbert ((m:ℝ)+1-1)`)
type-checks where `RealSobolevHilbert (m:ℝ)` is wanted.  The substance of the note is right; the
sentence should be corrected to say "the *type* equality is `rfl`; the real-number equality is
not".

### 4. COSMETIC — implicit reliance on a transitive import

`inner_datum_laplacian_le` uses `gradientSobolevENorm_toReal_sq_eq_datum_sum` from
`A04/LaplacianDatum.lean:130`, which is reached only transitively
(`RealPairing → LaplacianPairing → LaplacianDatum`).  An explicit
`import NSFormalization.Section4.A04.LaplacianDatum` would document the dependency.  No defect.

### 5. NOTE (for readers, not a defect) — what "order" means on this carrier

`RealVectorSobolev s = Product (Fin 3) (realSubspace s)` and `realSubspace` discards `s`, so the
norm on the datum carrier is the **ambient `FourierData` norm at every order**.  The Sobolev
order lives entirely in (i) *which* element is the datum of a given field (`IsSobolevDatum`,
which is unique) and (ii) the symbol multipliers `angularDirectionalDerivative` /
`angularOrderLowering`.  Three consequences, all fine but worth stating once:

* `isSobolevDatum_castOrder` (:76, `subst h; exact hA`) and `castOrder` (:82, `h ▸ A`) are a
  **genuine transport along a propositional equality of reals**, not an `unsafe`/`cast` hack; and
  because the target types are in fact identical, the transport is harmless.  `castOrder_coe`
  (:227, `subst h; rfl`) discharges it wherever it appears.  Checked.
* `angularMid_comm`'s `ring` step really is trivial *as multiplication operators*; the analytic
  content is `lowering_mid_symbol_eq` (gap `r - s` invariant under the `-1` shift) and
  `mid_symbol_order_independent`.  The module docstring (:41-44) says exactly this.  Honest.
* `‖G‖ = ‖u‖_{H^m}` holds *because* `G` is the order-`m` datum (`Continuity.sobolevNormAt_eq`,
  `:85`), not because the space knows its own order.

## What I checked, positively

**Statement fidelity (a) — `spatialLaplacian_lift_eq_datumSum` is a genuine `rfl`.**
`NavierStokes.ProblemStatement.spatialLaplacian u t x = ∑ i, fderiv ℝ (fun y => spatialDerivative u t y eᵢ) x eᵢ`
(`ProblemStatement.lean:76`) and `A03.partialDeriv j v = fun x => spatialDerivative (lift v) 0 x eⱼ`
(`A03/OuterTameProduct.lean:59`) with `lift v = fun z => v z.2`.  Both sides of :115 unfold to
`∑ j, fderiv ℝ (fun y => fderiv ℝ Z.field y eⱼ) x eⱼ`.  Confirmed by elaboration.  It is the
right operator: the paper's `Δu` in eq:Rhigh is the componentwise Euclidean Laplacian, and
`momentum_datum`'s `hL` uses the very same `spatialLaplacian w.velocity t`.

**(b) — `isSobolevDatum_laplacian` is stated in the tree's vocabulary.**  `IsSobolevDatum` is
`NSFormalization.Section4.D01`'s (`SmoothDatum.lean:237`, the one `momentum_datum` and
`timeDeriv_isSobolevDatum` use — verified by the compiling instantiation), `Z.field` is the
vendor `EulerLpTranslation.SmoothL2Field` projection
(`vendor/…/Euler/LpSmoothField.lean:31`), and `laplacianDatum` is a new `def` (legitimate new
object).  No local mirror of either.

**(c) — the inner product is the one the consumer uses.**  `inner_energy_assembly` at
`E = RealVectorSobolev (m:ℝ)` resolves `⟪·,·⟫` to the same `inner ℝ` instance the lemma's
`(inner ℝ G (laplacianDatum m A) : ℝ)` uses: my instantiation `rw`s one into the other with no
conversion step.  The internal move to the ambient carrier is `Paper3.realSobolev_inner_eq_ambient`
(`RealPairing.lean:77`, `rfl`).

**(d) — sign and orientation.**  The chain is
`real_inner_angularDirectionalDerivative` (`RealPairing.lean:84`,
`⟪f, D_a g⟫_ℝ = -⟪D_a f, g⟫_ℝ`) → `congr 1` → `directionalDerivative_orderLowering_comm` twice →
`real_inner_lowering_pairing` (`RealPairing.lean:218`, `⟪Λ_{s→r}w, Λ_{s→t}w⟫ = ‖Λ_{s→(r+t)/2}w‖²`,
non-negative) with `s = m+1, r = m-1, t = m+1` and `angularOrderLowering_self`, midpoint
`((m-1)+(m+1))/2 = m`, i.e. `‖Λ_{m+1→m} v‖² = ‖(D_j A')ᵢ‖²`.  So the `-` comes from
skew-adjointness and only from there.  **Adversarial test:** the identical proof script with
`+ ∑ⱼ ‖D_j A'‖²` fails —

```
error: Type mismatch … has type ⟪G, …⟫_ℝ = -‖derivDatumStep m j A'‖ ^ 2
  but is expected to have type ⟪G, …⟫_ℝ = ‖derivDatumStep m j A'‖ ^ 2
```

The orientation matches the manuscript: `appendix-a-local-theory.tex:134` carries
`+ν‖∇u‖²_{H^m}` on the **left** of eq:Rhigh, i.e. `⟪u, Δu⟫_{H^m} = -‖∇u‖²_{H^m}`.  The
right-hand side is the paper's quantity: `A03.gradientSobolevENorm` is `rfl`-equal to the
registered `Contracts.V1.TameProduct.gradientSobolevENorm`
(`Bindings/TameProduct.lean:89-91`), and `gradientSobolevENorm_toReal_sq_eq_datum_sum`
(`LaplacianDatum.lean:130`) ties it to `∑ⱼ ‖D_j A'‖²` with the *same* `derivDatumStep` term
(`inner_datum_laplacian_le` closes on `rfl`).

**(e) — non-vacuity.**  `D01.exists_isSobolevDatum_of_contDiff_memLp` (`SmoothDatum.lean:290`)
gives every `SmoothL2Field Space` a datum at **every real order**, so `hA`, `hA'`, `hG` are all
inhabited; my instantiation produces them from `C01.velocity_slice_smoothL2` on a genuine
`ClassicalSolutionR`.  And `D01.isSobolevDatum_unique` (`ForceClass.lean:286`) makes the datum
unique, so `isSobolevDatum_laplacian` is a *characterisation*, not a weak existence claim.

**Consistency.**  Imports are canonical local modules only (`A04.RealPairing`,
`D01.DerivativeDatum`, `A03.{Vector,Scalar}TameProduct`, `A03.RealAngularProduct`); no
`Contracts.*`, no HeliCorgi `Formal.*`.  `angularDirectionalMid` / `angularOrderLoweringMid` are
**used**, not re-defined — the only `def`s of those are 076's `LaplacianPairing.lean:53,131`
(grep over `formalization/`).  `laplacianDatum`, `derivDatumStep`, `castOrder` are genuinely new
objects.  The one duplicate is finding 2.  `directionalDerivative_orderLowering_comm` is exactly
route **(b)** that 082 examined and declined — `ATTEMPTS_SL3_REAL.md:94-110` says "the
commutation (b) is only the *alternative* route … recipe recorded, not built", and names
`mid_symbol_order_independent` × `lowering_mid_symbol_order_indep` as the recipe.  088 built it
from `mid_symbol_order_independent` + `lowering_mid_symbol_eq`, i.e. the recorded recipe with the
closed-form symbol lemma in place of the order-independence corollary.  Consistent; no conflict
with 085's `lerayComplement_lowerVectorL` (different operator, different module).

**Honesty of ATTEMPTS.**  Declaration count **20**, matching the 20 `#print axioms` lines
(checked by grep; the list is `isSobolevDatum_castOrder, castOrder, derivDatumStep,
cast_top_order, cast_mid_order, laplacianDatum, spatialLaplacian_lift_eq_datumSum,
isSobolevDatum_laplacian, angularMid_comm, directionalDerivative_orderLowering_comm,
vectorLowerDatum, isSobolevDatum_vectorLower, coe_vectorLowerDatum, castOrder_coe,
coe_derivDatumStep, inner_component_reconcile, norm_sq_derivDatumStep, inner_datum_laplacianDir,
inner_datum_laplacian, inner_datum_laplacian_le`).  Negative examples spot-checked:

* *"clean-order application → `isDefEq` TIMEOUT"* — **reproduced.**  Feeding a clean
  `(m:ℝ)+2` datum to `isSobolevDatum_partialDeriv j (m+1)` dies at
  `(deterministic) timeout at isDefEq, 200000 heartbeats`.  And `(((m+1:ℕ):ℝ)+1) = (m:ℝ)+2`
  is indeed **not** `rfl` (type mismatch), as claimed.  I hit the identical failure mode
  independently on the consumer side (finding 1).
* *"`rw` on the dependent midpoint index → motive is not type correct"* — consistent with
  `ATTEMPTS_SL3_REAL.md` F1 and with `real_inner_lowering_pairing`'s own usage note
  (`RealPairing.lean:214-217`), which prescribes `simp only [show … from by ring]`.  The code
  does that (:263-264).
* *"commutation route chosen over uniqueness to avoid `m ≥ 1`"* — coherent and I believe it:
  the uniqueness route would have to identify `D_j Gᵢ` as an order-`(m-1)` datum through the
  **ℕ-indexed** `isSobolevDatum_partialDeriv`, which has no ℕ-order `m-1` when `m = 0`.  The
  commutation is stated on arbitrary reals and works for all `m : ℕ`.
* The one inaccurate bullet is finding 3.

## Commands and results

All from the worktree, `. scripts/lean-env.sh`, `LEAN_NUM_THREADS=6`, lake run only from
`verification/`, one process at a time.

| command | result |
|---|---|
| `lake build NSFormalization.Section4.A04.LaplacianAssembly` | `Build completed successfully (9894 jobs).` exit 0; only replayed pre-existing upstream warnings (`Paper3/RealPositiveDensity`, `Source/PacketForceExtension` `if_pos`, `Source/ViscosityPacket` unused simp arg, `Paper3/SobolevDirectionalDerivative` `SchwartzMap.smul_apply` deprecation) — **none from this file** |
| `lake env lean ../formalization/NSFormalization/Section4/A04/LaplacianAssembly.lean` | **empty output**, exit 0 |
| `lake env lean ../research/A04/axioms_sl3_assembly.lean` | 20 declarations, each `[propext, Classical.choice, Quot.sound]`, exit 0 |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats\|set_option' …/LaplacianAssembly.lean` | no match |
| `make check` | exit **0** (architecture JSON, 13 contract-policy tests OK, `30 work items: ownership, contract registration and task cards consistent.`) |
| `/tmp` scratch: full `inner_energy_assembly` instantiation with `hlap := inner_datum_laplacian_le …` and `hmom := momentum_datum …` | **exit 0** with the glue of finding 1; **exit 1, `isDefEq` timeout** without it |
| `/tmp` scratch: `L = laplacianDatum m A` by `isSobolevDatum_unique` against `isSobolevDatum_laplacian` on a `ClassicalSolutionR` slice | exit 0 (the `spatialLaplacian w.velocity t` ↔ `spatialLaplacian (lift Z.field) 0` defeq holds) |
| `/tmp` scratch: `gradientSobolevNormAt (m:ℝ) w.velocity t = (gradientSobolevENorm (m:ℝ) Z.field).toReal := rfl` | exit 0 |
| `/tmp` scratch: `inner_datum_laplacian` proof script with `+` RHS | exit 1, sign type mismatch (finding: sign is load-bearing) |
| `/tmp` scratch: `vectorLowerDatum s r hrs A = lowerVectorL s r hrs A := rfl` | exit 0 (finding 2) |
| `/tmp` scratch: `((m:ℝ)+1-1) = (m:ℝ) := rfl` / `RealSobolevHilbert ((m:ℝ)+1-1) = RealSobolevHilbert (m:ℝ) := rfl` | **fails** / **succeeds** (finding 3) |
| `/tmp` scratch: `isSobolevDatum_partialDeriv 0 (m+1) hA` with clean `(m:ℝ)+2` hypothesis | exit 1, `isDefEq` timeout (recorded negative example reproduced) |

## Where the eq:Rhigh assembly (A04 unit G1) now stands

The split is `research/A04/G1_SPLIT.md`; the target is `Spec.lean` `energyIdentityHigh` =
`appendix-a-local-theory.tex:132-137` eq:Rhigh.

| # | what it is | status after 088 |
|---|---|---|
| SL0 | D1: `d = 2⟪G t, deriv G t⟫`, `sobolevNormAt = ‖G·‖` | **DONE** — `A04/DerivNorm.lean:141` `exists_hasDerivAt_sobolevNormAt_sq` |
| SL1 | D2: `deriv G t` is the datum of `∂ₜu(t,·)` | **DONE** — `A04/TimeDerivative.lean` `timeDeriv_isSobolevDatum` |
| SL2 | momentum equation in datum form `Gt = ν•L − N − P + F` | **DONE** — `A04/MomentumDatum.lean:167` `momentum_datum` (`hP` still an explicit hypothesis) |
| **SL3** | Laplacian datum + `⟪G, datum Δu⟫ = −‖∇u‖²_{H^m}` → `hlap` | **DONE, this lane** — steps 1–2 (076 `LaplacianPairing`), 3a (082 `RealPairing`), 3b (088 `LaplacianAssembly`): `isSobolevDatum_laplacian`, `inner_datum_laplacian`, `inner_datum_laplacian_le` |
| SL4 | pressure drop `⟪G, P⟫ = 0` (solenoidality) | **OPEN, blocked.**  Needs D01 **P2** (`∇p` datum at order `m`, the Leray route) which is itself not assembled: per `NEXT_SESSION.md`, P2 still has SL3 (081, `lerayComplement` on the datum carrier), SL4 (079, merged) and the P2 SL8 assembly outstanding.  Note P2 only *produces* `P`; SL4 additionally needs the **pairing** `⟪G, P⟫ = 0`, i.e. transversality of the order-`m` `∇p` datum against the solenoidal velocity datum — a new carrier lemma, not a corollary of P2's existence statement |
| SL5 | nonlinear IBP + Cauchy–Schwarz: `−⟪G, N⟫ ≤ ‖∇u‖_{H^m}·‖u⊗u‖_{H^m}` | **OPEN, L, unblocked.**  Per `ATTEMPTS_G1.md` §3: eq:Rhigh's *single-term* bound does **not** come from `A03.smoothJets_advectionTame` (two terms); it comes from `(u·∇)u = ∇·(u⊗u)`, the `H^m` integration by parts `⟪G, datum ∇·(u⊗u)⟫ = −⟪(D-datum of) G, datum (u⊗u)⟫`, then Cauchy–Schwarz, then SL6 |
| SL6 | outer tame transport to reals | **DONE** — `HighEnergy.lean` `outerSobolevNormAt_le` / `outerNormAt_le` |
| SL7 | force CS + norm identifications | **DONE** — generic CS inside SL8; `A04/Continuity.lean:85` `sobolevNormAt_eq` gives `‖G t‖ = sobolevNormAt` and `‖F‖ = sobolevNormAt f t` |
| SL8 | assembly to eq:Rhigh's RHS | **DONE** — `HighEnergy.lean:101` `inner_energy_assembly` / `inner_energy_Rhigh` |

So G1 is **6 of 8 closed** (SL0–SL3, SL6–SL8); the only mathematics left is **SL5** and **SL4**,
and SL4 is not startable until D01 P2 assembles.

**The next A04 lane should be SL5** — the `H^m` integration by parts of `∇·(u⊗u)` on the datum
carrier.  It is the last unblocked piece of eq:Rhigh, it is the largest remaining one, and this
lane hands it most of its tools: the IBP *is* `Paper3.real_inner_angularDirectionalDerivative`
(082) moved onto the outer-product datum, and `derivDatumStep` / `coe_derivDatumStep` /
`norm_sq_derivDatumStep` (088) are exactly the `∑ⱼ D_j` bookkeeping it needs on the `∇` side,
with `A03.outerColumn` / `outerSobolevENorm` on the other.  The `isDefEq` hazard of finding 1
will recur there (the same `sobolevENorm` infimum sits under `outerSobolevENorm`), so the lane
brief should tell the worker to state every order/norm bridge as an explicit `have … := rfl`.

Two small follow-ups to fold into that lane (or a MAINT lane), not worth a lane of their own:
findings 1 (a `sobolevNormAt`-shaped `hlap` corollary + the timeout recorded) and 2
(drop `vectorLowerDatum` in favour of `D01.lowerVectorL`).
