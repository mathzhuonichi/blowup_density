# Review — lane 065, task A04, sub-lemma SL2 (`Section4/A04/MomentumDatum.lean`)

Reviewer: opus, 2026-09-13. Worktree `.claude/worktrees/065-A04-sl2-momentum`
(read/build only; nothing but this file written).

## Verdict: **ACCEPT-WITH-NOTES**

The statement is exactly `research/A04/G1_SPLIT.md`'s SL2, the signs match the
vendor residual, the proof is kernel-checked on the standard three axioms, it
composes with SL8 (`inner_energy_assembly`) by direct term application with no
glue, and all gates pass. Every finding below is advisory; none blocks merge.

---

## 1. Builds and gates

| command (from the worktree) | result |
|---|---|
| `bash scripts/lean-install.sh` | `== OK` |
| `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A04.MomentumDatum` | **exit 0**, `Build completed successfully (9892 jobs)`; `grep A04 <log>` → **no lines** (every warning in the log is a replayed one from unrelated `Source/` and `Paper3/` modules) |
| `cd verification && lake env lean ../formalization/NSFormalization/Section4/A04/MomentumDatum.lean` (fresh compile from source, not a cache replay) | **exit 0**, **0 bytes of output** — the file itself emits no warning under the default linter set |
| `cd verification && lake env lean ../research/A04/axioms_sl2.lean` | **exit 0**; see §2 |
| `grep -nE "sorry\|admit\|native_decide\|axiom\|maxHeartbeats\|set_option" MomentumDatum.lean` | one hit, line 20, inside the module docstring (the words "axioms_sl2.lean"). **Nothing outside comments.** In `axioms_sl2.lean` the only hits are the five intended `#print axioms` commands and docstring text. |
| `make check` | **exit 0** (`check_formalization_plan`, `check_contracts`, `test_contract_policy` 13/13 OK, `check_work_queue`: "30 work items: ownership, contract registration and task cards consistent") |
| `cd verification && lake test` (extra, not required) | **exit 0**; every registered contract "checked; standard logical axioms only" |
| `git status --short` after review | clean (all reviewer scratch files deleted) |

Lane diff is purely additive — 3 new files, 389 insertions, **no existing file
touched**: `formalization/NSFormalization/Section4/A04/MomentumDatum.lean` (219),
`research/A04/ATTEMPTS_SL2.md` (113), `research/A04/axioms_sl2.lean` (57). No
frozen `Contracts/V1` or `Tests` file, no generated file. A04 is already
`in-progress`/`erenup` in `work_items.json`, so no claim commit is expected.

## 2. Axiom audit and the SL2 → SL8 composition

`lake env lean ../research/A04/axioms_sl2.lean`, verbatim output (exit 0, nothing
else printed — so the composed `example` type-checked):

```
'NSFormalization.Section4.A04.momentum_datum' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.isSobolevDatum_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.isScalarSobolevDatum_smul' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.isSobolevDatum_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.isScalarSobolevDatum_neg' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Five `#print axioms`, each exactly the standard three. Requirement met.

**The composed example is genuine.** `axioms_sl2.lean:56-57` is

```lean
  inner_energy_assembly hν hd
    (momentum_datum w hf hm hGd hGc ht hL hN hP hF) hlap hpr hnl hG hFn
```

— a single term application, no `rw`, no `convert`, no `simp`. `inner_energy_assembly`'s
implicit `E` is forced to `RealVectorSobolev (m:ℝ)` by `hlap : ⟪G t, L⟫ ≤ -grad^2`
and `hG : ‖G t‖ = uNorm`; its implicit `Gt` is forced to `deriv G t` by the type of
`momentum_datum …`; its `G` to `G t`. So this really is SL8 instantiated at the
concrete carrier with `Gt := deriv G t`, and it needs lane 053's
`InnerProductSpace ℝ (RealVectorSobolev s)` instance, which is on this branch.
**No glue.**

## 3. Statement fidelity (`momentum_datum`, `MomentumDatum.lean:167-180`)

Against `research/A04/G1_SPLIT.md` §"SL2 — momentum equation in datum form"
(`theorem momentum_datum {…} (ht : t ∈ Ioo 0 T) : deriv G t = ν • L − N − P + F`):

* `w : ClassicalSolutionR ν a f T`, `hf : MemForceR f`, `hm : 2 ≤ m` ✓.
* **The datum path is exactly `HasSmoothSobolevPath`'s body.** `DerivNorm.lean:87-90`
  defines `HasSmoothSobolevPath T u := ∀ m, ∃ G, (∀ t ∈ Ico 0 T, IsSobolevDatum (m:ℝ)
  (fun x => u (t,x)) (G t)) ∧ ContDiffOn ℝ ∞ G (Ico 0 T)`. `momentum_datum`'s `hGd`
  and `hGc` are that body destructured at a fixed `m`, token for token — and are
  character-identical to SL1's (`TimeDerivative.lean:186-187`), so SL1 applies with
  no massaging and a caller can feed `(h m).choose_spec` directly.
* `ht : t ∈ Ioo (0:ℝ) T` ✓ (interior time, as the split says).
* `L N P F : RealVectorSobolev (m:ℝ)` with `hL/hN/hP/hF` the `IsSobolevDatum (m:ℝ)`
  of `spatialLaplacian w.velocity t ·`, `advection w.velocity t ·`,
  `pressureGradient w.pressure t ·`, `f (t,·)` ✓ — i.e. `L` is the datum of `Δu`
  **without** `ν`, which is what the split's SL3 (`⟪G t, L⟫ = −‖∇u‖²`) and SL8's
  `hlap` both require.
* Conclusion `deriv G t = ν • L - N - P + F` in `RealVectorSobolev (m:ℝ)`, with
  `ν • ` the real scalar action — the literal `hmom` of `inner_energy_assembly`
  (`HighEnergy.lean:104`) ✓.

**Signs are right.** Chain checked end to end:

1. `vendor/NavierStokesAndEuler/NavierStokes/R3/ProblemStatement.lean:57-62`:
   `navierStokesResidual ν u p t x = ∂ₜu + (u·∇)u − ν • Δu + ∇p`.
2. `ClassicalSolutionR.momentum` (`A02/SolutionClass.lean`): that residual `= f (t,x)`
   on `Ioo 0 T`.
3. `D01/Pressure.lean:196-203` `temporalDerivative_slice_eq`:
   `∂ₜu = f − (u·∇)u + ν • Δu − ∇p` (one `abel` off the residual).
4. `MomentumDatum.lean:209-215` rewrites the datum-side field to
   `ν • Δu − (u·∇)u − ∇p + f` — the same term reassociated, closed by `abel`.
   `ν • L − N − P + F` is its datum.

The equation transported is the **unprojected** pointwise one; the pressure term
survives as `P` and is killed later by SL4's `⟪G,P⟫ = 0` (= SL8's `hpr`). That is
the correct division of labour and matches the split.

**The key defeq holds.** I wrote and type-checked (then deleted) a scratch file:

```lean
example (u : SpaceTimeField) (t : ℝ) (x : Space) :
    deriv (fun r => u (r, x)) t = temporalDerivative u t x := rfl
example (u : SpaceTimeField) (t : ℝ) :
    (fun x : Space => deriv (fun r => u (r, x)) t)
      = (fun x : Space => temporalDerivative u t x) := rfl
```

Both `rfl`s accepted (`lake env lean` exit 0). Reason: `temporalDerivative u t x :=
fderiv ℝ (fun s => u (s,x)) t 1` (`NavierStokes/ProblemStatement.lean:55-56`) and
`deriv f t := fderiv ℝ f t 1` are the same term. So the `show temporalDerivative
w.velocity t x = _` at line 213 is a legitimate `change`, not a hidden rewrite,
and SL1's datum-side field *is* the momentum residual.

**Proof body audit** (lines 181-217): `hderiv` = SL1's second conjunct; four slice
smoothness facts from D01 with the right interval coercions
(`contDiff_pressureGradient_slice` gets `⟨le_of_lt ht.1, ht.2⟩ : t ∈ Ico 0 T`,
`forceSlice_smoothL2_of_memForceR` gets `0 ≤ t`); `memLp_of_isSobolevDatum`
(which wants `ContDiff ℝ ∞ z`, `D01/DatumToJets.lean:267`) turns each into `MemLp`,
then `locIntField_of_memLp` into the `LocIntField` side conditions of
`A03.isSobolevDatum_add/sub` (`hs : 2 ≤ s` supplied by `hsR` from `hm`); the three
datum steps build `ν•L − N − P + F`; `A03.IsSobolevDatum.unique` closes. No step is
loose; nothing is proved twice.

## 4. The datum-linearity lemmas

**They are genuinely absent elsewhere.**
`grep -rn "isSobolevDatum_smul|isSobolevDatum_neg|isScalarSobolevDatum_smul|isScalarSobolevDatum_neg" --include='*.lean' formalization/ vendor/ research/`
minus this lane's two files returns **nothing**. The full inventory of datum
algebra in A03/D01 is: `A03.isSobolevDatum_iff/_add/_sub` (`VectorTameProduct.lean`),
`A03.isScalarSobolevDatum_mul/_add/_sub` (`ScalarTameProduct.lean`),
`D01.isSobolevDatum_add`, `D01.isSobolevDatum_unique` (`ForceClass.lean`). No `smul`,
no `neg`, scalar or vector. The lane's claim is accurate.

**The `smul` proof is correct.** `angularRealization` is
`ℝ → Lp ℂ 2 volume →L[ℂ] TemperedDistribution Space ℂ` (checked with `#check`), i.e.
ℂ-linear; `IsScalarTower ℝ ℂ ℂ` is found by `inferInstance`; so
`LinearMapClass.map_smul_of_tower` applies with `R := ℝ`, `S := ℂ` through
`LinearMap.CompatibleSMul` and the `LinearMapClass` instance of `ContinuousLinearMap`.
A real scalar therefore passes through the complex-linear map. The remaining steps
are `smul_apply` on the distribution, `hA ψ`, `← MeasureTheory.integral_smul`, and
a pointwise `Complex.real_smul; push_cast; ring` for `c • (ψ x * ↑(a x)) = ψ x * ↑(c * a x)`.
**No `2 ≤ s` and no `LocIntField` appear in the statement** — confirmed from the
signature `{s : ℝ} (c : ℝ) {a : Space → ℝ} {A : RealSobolevHilbert s}` — so the raw
route really is strictly more general than the representative route the split
suggested, as `ATTEMPTS_SL2.md` claims. The vector case is componentwise through
`isSobolevDatum_iff` + `IsSobolevDatum.component`, with `(c • F x) i = c * F x i`
and `(c • A) i = c • A i` by `PiLp` defeq (kernel-accepted). `neg` is `c = -1` + `simpa`.

## 5. Honesty spot-check

The recorded name snag reproduces **exactly**:

* `#check @map_smul_of_tower` → `error: Unknown identifier 'map_smul_of_tower'` (exit 1).
* `#check @LinearMapClass.map_smul_of_tower` → exists, signature as used.
* `#check @ContinuousLinearMap.smul_apply` → `warning: has been deprecated: Use 'smul_apply' instead`;
  the proof uses the bare `smul_apply`, as `ATTEMPTS_SL2.md` says.

Every command and result quoted in `ATTEMPTS_SL2.md` §"Commands and results" that
I could re-run reproduced. The build-job count (9892) matches. The `hP` gap is
stated honestly in three places (module docstring §"Hypotheses beyond `2 ≤ m`",
`ATTEMPTS_SL2.md`, and visibly in the signature) and is not hidden behind an axiom.

---

## Findings

**(1) — note, non-blocking — location of the four datum-linearity lemmas.**
`isScalarSobolevDatum_smul`, `isSobolevDatum_smul`, `isScalarSobolevDatum_neg`,
`isSobolevDatum_neg` (`MomentumDatum.lean:116-148`) are general facts about
`IsSobolevDatum`, not about the momentum equation. They sit in
`Section4/A04` only because the lane may not edit existing files.
*Fix (later SIMP lane, not this one):* move the two scalar lemmas next to
`A03.isScalarSobolevDatum_add/sub` in `A03/ScalarTameProduct.lean` and the two
vector ones next to `A03.isSobolevDatum_add/sub` in `A03/VectorTameProduct.lean`,
leaving `open A03 (…)` re-exports here. Worth flagging in the move: unlike the
existing additive lemmas these need **neither** `2 ≤ s` **nor** `LocIntField`, so
they should be stated with the weaker binders A03 does not currently use.

**(2) — note, non-blocking — the two `neg` lemmas are unused.**
`momentum_datum` uses `isSobolevDatum_sub` for both `−N` and `−P`, so
`isScalarSobolevDatum_neg` / `isSobolevDatum_neg` have no consumer in the tree.
They are one line each, requested by the split, and audited, so keeping them is
cheap. *Fix:* either find them a consumer at relocation time (finding 1) or drop
them; do not let them accrete more unused companions.

**(3) — note, non-blocking — `hf : MemForceR f` is stronger than what is used.**
It is consumed only through `forceSlice_smoothL2_of_memForceR` to get
`ContDiff ℝ ∞ (f (t,·))` → `MemLp … 2` → the `LocIntField` argument of the final
`isSobolevDatum_add`. *Fix (optional, later):* weaken to
`MemLp (fun x => f (t,x)) 2 volume` (or directly `A03.LocIntField (fun x => f (t,x))`),
which would make SL2 apply to forces outside the D01 class. Not worth a lane on its
own — every G1 consumer carries `MemForceR` anyway — but note it if SL2 is ever
reused off the eq:Rhigh path.

**(4) — note, cosmetic — a bare `rfl` on a submodule coercion.**
`MomentumDatum.lean:121-122`,
`hco : ((c • A : RealSobolevHilbert s) : FourierData) = c • ((A : RealSobolevHilbert s) : FourierData) := rfl`.
Correct today (`RealSobolevHilbert s = Source.RealSobolev.realSubspace s`, a
`ClosedSubmodule ℝ FourierData`, whose `•` is the subtype one), but it is a defeq
that a future change of carrier would silently break. *Fix (optional):* use the
named `coe_smul` simp lemma for the submodule instead of `rfl`.

**(5) — note, informational — the `hP` hypothesis is the recorded L9(c) gap.**
`hP : IsSobolevDatum (m:ℝ) (∇p(t,·)) P` is D01 obligation **P2**, not derivable from
`ClassicalSolutionR` (which carries `∇p ∈ L²` at order zero only). Taking it as an
explicit hypothesis is the right call and matches C01. *No fix* — but the lead
should keep it on the gap ledger: SL2 is conditional on P2, and so, therefore, will
be the assembled eq:Rhigh until L9(c) closes.

## Recommendation

Merge as-is. Findings 1 and 2 are the agenda for a later SIMP/relocation lane;
findings 3-5 are informational.
