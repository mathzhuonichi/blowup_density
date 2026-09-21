# REVIEW — lane 117 (D01 / P2 = SL8 final assembly)

Reviewer run in the lane worktree `.claude/worktrees/117-D01-p2-sl8-assembly`
(branch `erenup/117-D01-p2-sl8-assembly`, one commit `0962308` on `origin/erenup/integration`).
Module under review: `formalization/NSFormalization/Section4/D01/PressureJets.lean` (120 lines).
Probes: `/tmp/rev117/` — sources reproduced in the appendices so nothing is lost when `/tmp` is
cleared (`logs/LESSONS.md` 2026-09-14).

## Verdict: **ACCEPT-WITH-NOTES**

P2 = eq:Rpressure's regularity conclusion is genuinely proved, in the registered contract
vocabulary, on a non-vacuous hypothesis package, with standard axioms only. All four checks pass.
The notes are (a) one **missed export** that costs A04 real work (finding 3), (b) two pieces of
now-dead or now-stale code (findings 5, 6), and (c) a wording/scope clarification about what
"unconditional" and "eq:Rpressure" mean here (findings 1, 4). None of them is a reason to hold the
merge.

---

## 1. Compiles / axioms / hygiene — **PASS**

| command (from the worktree, after `. scripts/lean-env.sh`, `cd verification`, `LEAN_NUM_THREADS=6`) | result |
|---|---|
| `lake build NSFormalization.Section4.D01.PressureJets` | `Build completed successfully (9937 jobs).` — only the known vendor `Formal.*` linter warnings |
| `lake env lean ../formalization/NSFormalization/Section4/D01/PressureJets.lean` | **silent**, exit 0 |
| `lake env lean ../research/D01/axioms_sl8_assembly.lean` | three `#print axioms`, all exactly `[propext, Classical.choice, Quot.sound]`; the `Contracts.V1`-vocabulary `example` elaborates with no output |
| `make check` (from the worktree root) | exit 0 — architecture checks, `test_contract_policy.py` 13 tests OK, `check_work_queue.py` "30 work items: ownership, contract registration and task cards consistent." |
| `make test` | exit 0 — all 19 registered contracts "checked; standard logical axioms only" (nothing regressed) |

Axioms probe tail, verbatim:

```
'NSFormalization.Section4.D01.orderZeroDatum_pressureGradient_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.D01.pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'NSFormalization.Section4.D01.temporalDerivative_slice_smoothSquareIntegrableJets_of_memForceR' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Hygiene: `grep -nE 'sorry|admit|axiom|native_decide|maxHeartbeats|set_option'` on the module returns
**one** hit, line 27, inside the module docstring ("No `sorry`, no `axiom`; …"). No `set_option`, no
heartbeat bump, no `native_decide`, no `@[simp]` attribute added. `wc -l` = 120, as claimed. The
probe file `research/D01/axioms_sl8_assembly.lean` is clean.

## 2. Statement fidelity — **PASS**, with findings 1/3/4 below

### (a) The signature is exactly what was claimed

`set_option pp.fullNames true in #check` (`/tmp/rev117/fid_b.lean`):

```
@NSFormalization.Section4.D01.pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR : ∀ {ν : ℝ}
  {a : NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space}
  {f : NavierStokes.ProblemStatement.VelocityField} {T : ℝ}
  (u : NSFormalization.Section4.A02.ClassicalSolutionR ν a f T),
  NSFormalization.Section4.D01.MemForceR f →
    ∀ {t : ℝ},
      t ∈ Set.Ioo 0 T →
        NSFormalization.Section4.D01.SmoothSquareIntegrableJets fun x =>
          NavierStokes.ProblemStatement.pressureGradient u.pressure t x
```

Hypotheses are exactly `u`, `hf : MemForceR f`, `ht : t ∈ Ioo 0 T` — nothing else, no side
condition smuggled in. Confirmations (all `rfl`, `/tmp/rev117/fid_a.lean`, `fid_b2.lean`):

* the `MemForceR` in the statement resolves to **`D01.MemForceR`** (`D01/ForceClass.lean:158`), not
  the `open`ed A02 one — the enclosing namespace wins, exactly the `logs/LESSONS.md` top entry
  recorded on lane 111. Harmless, because
  `example : @A02.MemForceR = @D01.MemForceR := rfl` **compiles**, and so does
  `example : @D01.MemForceR = @BlowupDensity.Contracts.V1.Data.MemForceR := rfl`. So the hypothesis
  *is* the registered contract force class. That class is `Data.lean:544`, a transcription of
  `02-preliminaries.tex:17` eq:Rclasses
  `F_R = {f ∈ C^∞([0,∞);H^∞) : ‖f‖_{L¹_tH^m_x} + ‖f‖_{L²_tH^m_x} < ∞ ∀ m ≥ 0}` — `ContDiffOn ℝ ∞ f
  futureDomain` plus, at every integer `m`, a datum path that is `C^∞` in time and in
  `L¹ ∩ L²(dt on (0,∞))`. Matches the manuscript.
* `pressureGradient` is the pinned upstream `NavierStokes.ProblemStatement.pressureGradient`
  (`vendor/.../ProblemStatement.lean:71`, `∑ᵢ (∂ᵢp)eᵢ`), and
  `example : @NavierStokes.ProblemStatement.pressureGradient = @BlowupDensity.Contracts.V1.pressureGradient := rfl`
  compiles. Its argument is the solution's **own** pressure: retyping the statement with the
  explicit projection `NSFormalization.Section4.A02.ClassicalSolutionR.pressure u` and closing it
  with the theorem term elaborates (no `u.pressure`-vs-something-else slippage).
* `SmoothSquareIntegrableJets` is D01's restatement (`DatumToJets.lean:118`), and
  `example : @D01.SmoothSquareIntegrableJets = @BlowupDensity.Contracts.V1.SmoothSquareIntegrableJets := rfl`
  compiles — the `Bindings/DatumLemmas.lean:61-62` bridge holds at HEAD. `#print` on both sides
  gives the same body `fun v => ContDiff ℝ ↑⊤ v ∧ ∀ (n : ℕ), MemLp (iteratedFDeriv ℝ n v) 2 volume`.
* `ClassicalSolutionR` is A02's restatement. As `CLAUDE.md` states, the `rfl` bridge to
  `Contracts.V1.Data.ClassicalSolutionR` is **impossible** (different inductive types) and indeed
  fails; the binding must go through the field-by-field `Bindings.uniqueness_toA02` — see §6, where
  that binding term is compiled.

### (b) What of P2 / eq:Rpressure is still open

The manuscript (`paper/sections/02-preliminaries.tex:89-94`) says:

> On $\R^3$ we require $\nabla p=(I-\PP)(f-\nabla\cdot(u\otimes u))=:G$.
> For smooth $H^\infty$ data, $G$ is smooth and its Fourier transform is parallel to $\xi$.

and `research/D01/P2_SPLIT.md` "Target" asks for exactly

```lean
SmoothSquareIntegrableJets (fun x : Space => pressureGradient u.pressure t x)
```
for `u : ClassicalSolutionR ν a f T`, `hf : MemForceR f`, `t ∈ Ioo (0:ℝ) T`.

**The recorded P2 target is met character for character.** In particular:

* `Ioo` vs `Ico` / the `t = 0` endpoint: **not a gap for P2**. `P2_SPLIT.md`'s target is `Ioo`, the
  C01 consumer named in `Pressure.lean`'s docstring is `Ioo`, and `ClassicalSolutionR.momentum` —
  which the proof consumes through `temporalDerivative_slice_eq` — is itself only imposed on
  `Ioo 0 T`. `t = 0` is *not* reachable by this route and is not asked for.
* the **pressure itself** (as opposed to its gradient) is not in P2's scope: the manuscript fixes
  the scalar `p` by the radial potential `p(x,t)=∫₀¹G(rx,t)·x dr`, which is A01's
  `pressure_potential` field, not D01's.
* the **identity** half. See finding 4: the module proves eq:Rpressure only at **order 0**, and in
  the `h = f − (u·∇)u + νΔu` spelling rather than the manuscript's `f − ∇·(u⊗u)`. The order-`m`
  identity **is** established in the proof but is not exported (finding 3).

**What A01's `pressure_recovery` still needs from this module: nothing.** `research/A01/Spec.lean:197`
asks for

```lean
pressure_recovery : ∀ t ∈ Ico (0 : ℝ) T,
  IsLerayComplement (fun x => f (t, x) - convectionDivergence u.velocity t x)
                    (fun x => pressureGradient u.pressure t x)
```
with (`Spec.lean:143`)
`IsLerayComplement w G := MemLp G 2 volume ∧ HasSymmetricJacobian G ∧ IsSolenoidal (w − G)`.
All three clauses are **pointwise / order-zero `MemLp`** statements; none of them mentions a Sobolev
datum. Clause 1 is `ClassicalSolutionR.pressure_gradient` (a structure field, already on `Ico`);
clause 2 is lane 106's `A01.PressureGauge.hasSymmetricJacobian_pressureGradient` (or lane 111's
`partialDeriv_pressureGradient_symm` plus differentiability); clause 3 is a pointwise divergence
computation (`div ∂ₜu = 0` on `Ioo`, plus `div Δu = 0`) followed by the `t = 0` limit that
`Spec.lean:189-196` itself flags as "the genuine increment of this field".
So **`orderZeroDatum_pressureGradient_eq` is *not* what `pressure_recovery` needs** — it is a
statement in the `RealVectorSobolev 0` datum carrier, one level above `IsLerayComplement`. It is
neither sufficient nor required there. The lead should not book A01's `pressure_recovery` as
unblocked by this lane.

### (c) Non-vacuity — **PASS**, both directions, verified in Lean

`/tmp/rev117/vacuity.lean` (appendix A), `lake env lean` exit 0, output:

```
'Rev117.p2_on_zeroSol' depends on axioms: [propext, Classical.choice, Quot.sound]
'Rev117.const_not_jets' depends on axioms: [propext, Classical.choice, Quot.sound]
```

* **The hypothesis package is inhabited.** The reviewer rebuilt the lane-111 reviewer's witness from
  scratch (it lived in a now-cleared `/tmp`): `zeroSol (ν) : ClassicalSolutionR ν 0 0 1` — all ten
  fields discharged, including `sobolev` and `pressure_gradient` — together with
  `memForceR_zero : MemForceR (0 : VelocityField)`, and then instantiated the theorem under review:

  ```lean
  theorem p2_on_zeroSol (ν : ℝ) :
      SmoothSquareIntegrableJets (fun x : Space => pressureGradient (zeroSol ν).pressure (1/2) x) :=
    pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR (zeroSol ν) memForceR_zero
      (by constructor <;> norm_num)
  ```
  It elaborates. Note `memForceR_zero` genuinely forces the datum path to be the **zero** path:
  `forceTimeMeasure = volume.restrict (Ioi 0)` is infinite, so `memLp_const_iff` rules out any
  nonzero constant path — the witness is not a loophole.
* **The conclusion is not trivially true of every smooth field.** `const_not_jets`: for `c ≠ 0`,
  `fun _ : Space => c` is `ContDiff ℝ ∞` but **not** `SmoothSquareIntegrableJets`. Proof: its
  order-0 jet has constant norm `‖c‖`, `eLpNorm_congr_norm_ae` transports `MemLp` to the constant
  function, and `memLp_const_iff` then forces `c = 0 ∨ volume (univ : Set Space) < ⊤`, both false
  (`volume (univ : Set Space) = ⊤` closes by `simp`). This is the same phenomenon
  `ClassicalSolutionR.pressure_gradient`'s docstring names ("excludes a nonzero constant pressure
  gradient"), now checked by the kernel. So the theorem has content.

## 3. Consistency with the tree — **PASS**, with findings 3/5/6

* **Imports.** Five imports, all `NSFormalization.Section4.D01.*`. The full transitive closure
  (183 modules, computed by walking `import` lines from the module) contains **zero** `A01` modules:
  `A02.SolutionClass`, four `A03.*`, six `A04.*`, `A05.SmoothJets`, seventeen `D01.*`,
  `I03.Angular`, and Paper3/Source/Mathlib below that. The layering claim in the ATTEMPTS is true.
  The probe's `Longitudinal` import was swapped for `OrderZeroCurl` (where lane 108's lemma lives);
  `Longitudinal` is still in the closure transitively, so nothing was lost.
* **No restated definitions.** The module contains no `def`, no `abbrev`, no `structure` — only
  three `theorem`s. Nothing to bridge, nothing that can drift.
* **`orderZeroDatum_pressureGradient_eq`'s spelling.** It is stated through
  `(smoothL2_momentumResidual_slice u hf ht).memLp` rather than with `h` written out. Two remarks:
  (i) this is *safe* — `orderZeroDatum` takes the `MemLp` proof as an argument and proof
  irrelevance makes the value independent of which proof, so no consumer can be blocked by holding a
  different `MemLp` witness for the same field; (ii) it is nonetheless **less readable**: a reader
  must open `MomentumSlice.lean:64` to learn that the field is
  `fun x => f (t,x) - advection u.velocity t x + ν • spatialLaplacian u.velocity t x`. Since A01's
  `pressure_recovery` does not consume this lemma at all (§2b), usability there is moot; the only
  real consumer is the module's own second theorem and the recommended A04 export (§7). **Style
  note, not a change request** — rewriting the statement would duplicate the field expression and
  invite drift against `MomentumSlice.lean`.
* **Duplication with `Pressure.pressureGradient_slice_smoothSquareIntegrableJets`** — see finding 5.
* **Lane 111's `lerayComplement_orderZeroDatum_add/_sub`** — see finding 6.

## 4. Honesty of `ATTEMPTS_SL8_ASSEMBLY.md` — **PASS**

Claim: "the recipe went through verbatim", with exactly two substitutions. Verified by a mechanical
normalized diff of the module body (lines 44-118) against the previous reviewer's probe
`research/D01/probes/sl8_assembly_probe.lean` (lines 47-116), after renaming the probe's local
names to the module's and stripping whitespace/comments. The diff shows **only**:

1. the probe's local `smoothL2_residual` theorem **deleted**, every use replaced by lane 111's
   exported `smoothL2_momentumResidual_slice`. Checked: `MomentumSlice.lean:64`'s field is
   `fun x : Space => f (t, x) - advection u.velocity t x + ν • spatialLaplacian u.velocity t x`,
   character-identical to the probe's. Substitution 1 as documented.
2. the `H108` hypothesis replaced by `Leray.lerayComplement_zero_orderZeroDatum_eq_self`
   (`OrderZeroCurl.lean:510`), with the extra explicit `(memLp_pressureGradient_slice u ht)`
   argument the real lemma takes. Substitution 2 as documented. The `hcurl` input is lane 111's
   in-tree `partialDeriv_pressureGradient_symm` (`MomentumSlice.lean:188`), as claimed, so no A01
   import — confirmed by the closure walk above.
3. cosmetics: `exact … (by …)` → `refine … ?_`, line re-wrapping, `(0:ℝ)` → `(0 : ℝ)`.
4. **one deviation the ATTEMPTS does not mention**: the probe's `row_i2` and `row_i4` were *theorems*;
   the module inlines them as `have hi2` / `have hi4` inside `orderZeroDatum_pressureGradient_eq`.
   The proof terms are identical, so this is not "new analysis" and the honesty claim stands, but it
   is a structural choice with a consequence — see finding 7.

No failed approaches are claimed and none were found to be hidden; the module built on the first
`lake build` for the reviewer too.

---

## 5. Findings

| # | severity | finding |
|---|---|---|
| 1 | info | **"unconditional" in the module docstring means "no `hut` hypothesis", not "no force hypothesis".** `Pressure.lean:62-66` states that *without* a force hypothesis the conclusion is **false** (take smooth div-free `u` with `H^∞` slices, `p` with `∇p ∈ L² \ H¹`, and *define* `f` by the momentum equation — every structure field holds). That counterexample is not contradicted: such an `f` is not in `F_R`, and the new theorem carries `hf : MemForceR f`. No defect; if `Pressure.lean`'s docstring is ever touched, both places would read better as "unconditional given `f ∈ F_R`". |
| 2 | info | **The registered `D01.datum_lemmas` scope string is now stale.** `verification/contracts.json`, `D01.datum_lemmas`, "Not asserted anywhere: … **any Sobolev datum or jet class for the pressure or its gradient**". That sentence is exactly what this lane removes. It must be updated *in the new version's scope*, not in V1's (V1 is frozen and `check_contracts.py` will reject an edit). See §6. |
| 3 | **medium** | **The order-`m` identity is proved and then thrown away.** Inside `pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR` (lines 99-110), after `refine ⟨Leray.lerayComplement (m : ℝ) Am, ?_⟩` the goal *is* `IsSobolevDatum (m:ℝ) (∇p(t,·)) ((I−P)ₘ Am)` — eq:Rpressure at order `m` as an identity of data — and it is discharged. It is not exported, so every downstream consumer that wants `∇p`'s order-`m` datum (A04's `hP`, and the `hpr` pairing) has to re-derive it or settle for a bare `∃`. The reviewer lifted it out verbatim and it compiles standalone in ~12 lines with standard axioms (appendix B). **Recommend the lane (or the follow-up contract lane) export it**, together with the `∃` corollary and the uniqueness pin. This is the single highest-value change and it costs no new mathematics. |
| 4 | low | **What is proved at order 0 is eq:Rpressure in the `h` spelling, not the manuscript's.** The manuscript's `G = (I−P)(f − ∇·(u⊗u))`; the module's is `(I−P)₀ datum⁰(f − (u·∇)u + νΔu)`. Two deltas: (i) `(u·∇)u` vs `∇·(u⊗u)` — the bridge exists (`convectionDivergence_eq_advection`) but lives in `Section4.A01`, so using it here would invert the layering the lane deliberately preserved; (ii) the extra `νΔu`, which `(I−P)` kills only because `Δu` is divergence-free — the reviewer found **no in-tree `div Δu = 0`** lemma, so this is a real (small) missing step, the same shape as `sum_partialDeriv_temporalDerivative_eq_zero` for `∂ₜu`. Immaterial to P2's regularity target; matters only if someone wants the manuscript's literal display. Record it, do not block. |
| 5 | low (MAINT) | **`Pressure.pressureGradient_slice_smoothSquareIntegrableJets` (`Pressure.lean:376`) is now dead and strictly weaker.** Its hypothesis `hut : SmoothSquareIntegrableJets (∂ₜu(t,·))` is exactly what the new corollary now proves. `grep` over `formalization/ verification/ research/` finds **no** user besides its own docstring and `research/D01/axioms_l9c.lean:33`. Options: retire it, or re-derive it from the new theorem (one line) and keep the name. Either way `Pressure.lean`'s docstring §3 ("the single root gap", "L9(c) stays open") should be updated — it is now the main misleading text in D01. |
| 6 | low (MAINT) | **Lane 111's `lerayComplement_orderZeroDatum_add` / `_sub` (`OrderZeroAlgebra.lean:97,106`) are dead code.** The assembly used `map_sub` on the CLM directly (`PressureJets.lean:82`). Only user anywhere is `research/D01/axioms_sl8_prep.lean:10-11`, which would need updating if they are removed. |
| 7 | low | **Rows i.2 and i.4 are no longer exported.** `hi4` in particular — `(I−P)₀ (datum⁰ ∂ₜu) = 0`, i.e. `∂ₜu(t,·)` is transverse at order 0 — is a reusable fact about a classical solution that now exists only as a `have`. If the follow-up lane exports the order-`m` identity (finding 3) it may as well export this one. |

---

## 6. For the lead — what the P2 contract lane should register

### Where it goes: **a V3 of `D01.datum_lemmas`, not a new `Contracts/V1/PressureJets.lean`**

Three reasons.

1. **P2 is a D01 obligation and its sibling already lives there.** `Contracts/V1/DatumLemmas.lean:269`
   already carries `solution_slice_pressureGradient_contDiff` — "This is *all* the class as specified
   gives for the pressure". The new field is the direct strengthening of that one, in the same record.
2. **The "not asserted" sentence that P2 deletes is in that contract's scope string** (finding 2).
   A separate contract would leave `D01.datum_lemmas`'s registry entry asserting, falsely, that the
   pressure jet class is nowhere registered.
3. **The machinery is already there.** `Contracts/V2/DatumLemmas.lean` exists and defines
   `DatumLemmasV2API extends Contracts.V1.DatumLemmas.DatumLemmasAPI`, bound by
   `Bindings/DatumLemmasV2.lean` with `{ … with … }` over the frozen V1 witness. V3 repeats that
   pattern exactly.

Mechanical constraint checked in `experiments/check_contracts.py:118`:
`assert f'/V{contract["version"]}/' in contract['specification']` — so **version 3 must live in
`verification/Contracts/V3/DatumLemmas.lean`** (a new directory; nothing else in the checker is
version-aware, `CONTRACT_IMPORT_PREFIXES` already allows `Contracts.`, so `import Contracts.V2.DatumLemmas`
is legal).

Registry entry: `id "D01.datum_lemmas_v3"`, `version 3`,
`specification "verification/Contracts/V3/DatumLemmas.lean"`, `binding_module "Bindings.DatumLemmasV3"`,
`test_module "Tests.DatumLemmasV3"`, `declaration "BlowupDensity.Tests.checkedDatumLemmasV3"`.

### Exact field statements (`Contracts.V1.Data` vocabulary — all three compile, appendix C)

Inside `namespace BlowupDensity.Contracts.V3.DatumLemmas` with
`open Set MeasureTheory NavierStokes.ProblemStatement`, `open BlowupDensity.Contracts.V1.Data`,
`open NSFormalization.Paper3 (RealVectorSobolev)` (this is the `open` set
`Contracts/V1/DatumLemmas.lean:125-129` already uses):

```lean
/-- eq:Rpressure's regularity conclusion (`02-preliminaries.tex:89-94`), obligation P2. -/
solution_slice_pressureGradient_smoothJets :
  ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
    (u : ClassicalSolutionR ν a f T), MemForceR f → ∀ t : ℝ, t ∈ Ioo (0 : ℝ) T →
    SmoothSquareIntegrableJets fun x : Space => pressureGradient u.pressure t x

/-- The `∂ₜu(t,·) ∈ H^∞` corollary. -/
solution_slice_temporalDerivative_smoothJets :
  ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
    (u : ClassicalSolutionR ν a f T), MemForceR f → ∀ t : ℝ, t ∈ Ioo (0 : ℝ) T →
    SmoothSquareIntegrableJets fun x : Space => temporalDerivative u.velocity t x

/-- The order-`m` datum of `∇p(t,·)` that `A04.momentum_datum`'s `hP` slot wants. -/
solution_slice_pressureGradient_exists_datum :
  ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
    (u : ClassicalSolutionR ν a f T), MemForceR f → ∀ t : ℝ, t ∈ Ioo (0 : ℝ) T →
    ∀ m : ℕ, ∃ P : RealVectorSobolev (m : ℝ),
      IsSobolevDatum (m : ℝ) (fun x : Space => pressureGradient u.pressure t x) P
```

`temporalDerivative` is already contract vocabulary (`Contracts/V1/Packet.lean:99`);
`pressureGradient` likewise (`Packet.lean:115`), `rfl`-equal to the upstream one (checked).
Field 3 is worth registering separately even though it follows from field 1 by unit L2: it is the
shape A04 consumes, and registering it is what makes `momentum_datum`'s `hP` demonstrably
dischargeable from the contract alone.

### Binding terms (compiled, standard axioms only)

`Bindings/DatumLemmasV3.lean` must `import Bindings.Uniqueness` for the structure conversion
(`Contracts.V1.Data.ClassicalSolutionR` and `A02.ClassicalSolutionR` are different inductive types;
`Bindings.uniqueness_toA02` is the existing ten-field converter, and
`(uniqueness_toA02 u).pressure = u.pressure` is `rfl`, `Bindings/Uniqueness.lean:83`):

```lean
solution_slice_pressureGradient_smoothJets := fun _ _ _ _ u hf _ ht =>
  NSFormalization.Section4.D01.pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR
    (uniqueness_toA02 u) hf ht

solution_slice_temporalDerivative_smoothJets := fun _ _ _ _ u hf _ ht =>
  NSFormalization.Section4.D01.temporalDerivative_slice_smoothSquareIntegrableJets_of_memForceR
    (uniqueness_toA02 u) hf ht

solution_slice_pressureGradient_exists_datum := fun ν a f T u hf t ht m =>
  (NSFormalization.Section4.D01.memHInfty_iff_smoothSquareIntegrableJets.mpr
    (solution_slice_pressureGradient_smoothJets ν a f T u hf t ht)).2 m
```

No `by` block, no coercion, no `show`. All three verified: `#print axioms` on each gives exactly
`[propext, Classical.choice, Quot.sound]` (appendix C).
Bridges needed in the binding: none new — `D01.SmoothSquareIntegrableJets = Contracts.V1.SmoothSquareIntegrableJets`
and `D01.MemForceR = Contracts.V1.Data.MemForceR` are already pinned in `Bindings/DatumLemmas.lean`
(`:61`, `datumLemmas_memForceR_eq`), which V3's binding imports through `Bindings.DatumLemmasV2`.

### Scope-string delta for the V3 registry entry

"… extended by the pressure half of obligation P2 (eq:Rpressure, `02-preliminaries.tex:89-94`):
for a classical solution with a force in `F_R`, the pressure-gradient slice and the time-derivative
slice at every interior time lie in the jet form of `H^∞`, and `∇p(t,·)` therefore has an angular
Sobolev datum at every integer order. **Not asserted**: the identity
`∇p = (I−P)(f − ∇·(u⊗u))` itself in the manuscript's spelling (what is proved is the order-0 datum
identity with the momentum residual `f − (u·∇)u + νΔu` in place of `f − ∇·(u⊗u)`); anything at
`t = 0`; any statement about the scalar pressure `p` as opposed to its gradient; and the
`IsLerayComplement` characterization of A01's `pressure_recovery`."

---

## 7. For the lead — what A04's eq:Rhigh assembly still needs, and what this module gives it

`research/A04/SL5_SPLIT.md:75,100` says the only remaining G1 gap to `energyIdentityHigh` is
**`hpr`**, and calls it "the D01 obligation **P2** (the pressure datum / Leray-regularity gap)".
That identification is **half right**, and the distinction matters for scoping the next A04 lane.

There are two different things called `hpr`:

* **`hP` — the datum's existence.** `A04/MomentumDatum.lean:149`:
  `hP : IsSobolevDatum (m : ℝ) (fun x => pressureGradient w.pressure t x) P`, an *explicit
  hypothesis* of `momentum_datum`. This is **now discharged**: field 3 of §6 above, i.e.
  `(memHInfty_iff_smoothSquareIntegrableJets.mpr (P2 theorem)).2 m`. Verified to compile
  (appendix B, `exists_isSobolevDatum_pressureGradient_slice`). This is what
  `G1_SPLIT.md`'s SL4 meant by "Needs `∇p(t,·)` present in the datum carrier at order `m` — the
  L9(c) obligation currently being closed elsewhere".
* **`hpr : ⟪G t, P⟫ = 0` — the pressure drop.** `A04/HighEnergy.lean`'s `inner_energy_assembly`
  slot. This is a *separate statement* and **this module does not prove it**. `G1_SPLIT.md` SL4
  spells out the intended route: `⟪u, ∇p⟫_{H^m} = −⟪div u, p⟫_{H^m} = 0`, by the
  "pin-the-representative" technique (`representative_ae` + `angularRealization_boundedRepresentative`)
  reducing the datum identity to a pointwise integration by parts, "**once `∇p`'s order-`m` datum is
  in hand**" — which it now is.

**Concrete recommendation: a cheaper route to `hpr` opens up if finding 3 is exported.** With the
order-`m` identity `IsSobolevDatum m (∇p(t,·)) ((I−P)ₘ Am)` and `isSobolevDatum_unique`, any `P` the
A04 lane is holding is *pinned*: `P = (I−P)ₘ Am` (compiled as `pin_pressureGradient_datum`,
appendix B). Then `hpr` becomes `⟪G, (I−P)ₘ Am⟫ = 0`, which is pure operator algebra on the datum
carrier — `(I−P)` self-adjoint plus `(I−P)ₘ G = 0` because `u(t,·)` is solenoidal
(`D01.Leray.lerayComplement_eq_zero_of_transverse` + `orderZeroDatum_transverse_of_divergence_free`,
the exact pair the module already uses at order 0 for `∂ₜu`) — instead of an integration by parts
against representatives. **Caveat, verified: the tree currently has no self-adjointness lemma for
`lerayComplement` at any order** (`grep` for `adjoint|IsSelfAdjoint` over
`Section4/D01/Leray*.lean` and `OrderZero*.lean` returns nothing), so that route needs one new
lemma; `lerayComplement`'s fibre symbol `ξξᵀ/‖ξ‖²` is a real symmetric projection
(`LeraySymbol.lean`, lane 062), so it should be an S item, but the reviewer did not prove it.
The A04 lane should cost the two routes before choosing.

So, for the work queue: **A04 eq:Rhigh's `hP` input is unblocked by this lane; its `hpr` input is
not, and remains an A04 item** of size S–M depending on the route.

---

## Commands run (worktree root `.claude/worktrees/117-D01-p2-sl8-assembly`, after `. scripts/lean-env.sh`)

| command | result |
|---|---|
| `cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.D01.PressureJets` | `Build completed successfully (9937 jobs).` |
| `cd verification && lake env lean ../formalization/NSFormalization/Section4/D01/PressureJets.lean` | silent, exit 0 |
| `cd verification && lake env lean ../research/D01/axioms_sl8_assembly.lean` | 3 × standard axioms; `example` silent |
| `make check` | exit 0 |
| `make test` | exit 0, 19 contracts "standard logical axioms only" |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats\|set_option' …/PressureJets.lean` | 1 hit, docstring line 27 |
| `cd verification && lake env lean /tmp/rev117/fid_a.lean` (appendix D) | all `rfl` bridges pass except the expected `Contracts.V1.Packet` name (fixed in `fid_b2.lean`) |
| `cd verification && lake env lean /tmp/rev117/fid_b2.lean` | only the **expected** failure `ClassicalSolutionR ≠ Data.ClassicalSolutionR` by `rfl` (structure, per `CLAUDE.md`) |
| `cd verification && lake env lean /tmp/rev117/vacuity.lean` | exit 0, both theorems standard axioms |
| `cd verification && lake env lean /tmp/rev117/export_m.lean` | exit 0, three recommended exports, standard axioms |
| `cd verification && lake env lean /tmp/rev117/contract_shape.lean` | exit 0, three contract fields + bindings, standard axioms |
| import-closure walk (python over `import` lines) | 183 modules, **0** `A01` |

---

## Appendix A — `/tmp/rev117/vacuity.lean` (non-vacuity; `zeroSol`, `memForceR_zero`, `const_not_jets`)

```lean
import NSFormalization.Section4.D01.PressureJets

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (ClassicalSolutionR)
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ContDiff

namespace Rev117

/-- A nonzero **constant** field is `C^∞` but NOT in the jet class. -/
theorem const_not_jets {c : Space} (hc : c ≠ 0) :
    ContDiff ℝ ∞ (fun _ : Space => c) ∧ ¬ SmoothSquareIntegrableJets (fun _ : Space => c) := by
  refine ⟨contDiff_const, ?_⟩
  rintro ⟨-, h⟩
  have h0 := h 0
  have hconst : MemLp (fun _ : Space => c) 2 volume := by
    refine ⟨aestronglyMeasurable_const, ?_⟩
    have h2 := h0.2
    rwa [eLpNorm_congr_norm_ae (f := iteratedFDeriv ℝ 0 (fun _ : Space => c))
      (g := fun _ : Space => c)
      (Filter.Eventually.of_forall (fun x => by simp [norm_iteratedFDeriv_zero]))] at h2
  rcases (memLp_const_iff (p := 2) two_ne_zero (by simp)).mp hconst with hz | hv
  · exact hc hz
  · simp at hv

theorem jets_zero : SmoothSquareIntegrableJets (fun _ : Space => (0 : Space)) := by
  refine ⟨contDiff_const, fun n => ?_⟩
  have : iteratedFDeriv ℝ n (fun _ : Space => (0 : Space)) = 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · ext x m; simp
    · exact iteratedFDeriv_const_of_ne (by omega) _
  rw [this]; exact MemLp.zero

theorem datum_zero (s : ℝ) : IsSobolevDatum s (fun _ : Space => (0 : Space)) 0 := by
  intro i ψ
  simp

/-- The zero solution with zero force on `[0,1)`. -/
def zeroSol (ν : ℝ) : ClassicalSolutionR ν 0 0 1 where
  velocity := 0
  pressure := 0
  horizon_pos := zero_lt_one
  velocity_smooth := contDiffOn_const
  pressure_smooth := contDiffOn_const
  initial := fun _ => rfl
  divergence := by
    intro t _ x
    simp [spatialDivergence, spatialDerivative]
  momentum := by
    intro t _ x
    simp [NavierStokesR3.ProblemStatement.navierStokesResidual, temporalDerivative, advection,
      spatialDerivative, spatialLaplacian, pressureGradient]
  sobolev := fun m => ⟨fun _ => 0, continuousOn_const, fun t _ => datum_zero _⟩
  pressure_gradient := by
    intro t _
    simp [pressureGradient]

theorem memForceR_zero : MemForceR (0 : VelocityField) := by
  refine ⟨contDiffOn_const, fun m => ⟨fun _ => 0, fun t _ => datum_zero _, contDiffOn_const, ?_, ?_⟩⟩
  · exact MemLp.zero
  · exact MemLp.zero

/-- The main theorem, instantiated on a concrete classical solution at a concrete time. -/
theorem p2_on_zeroSol (ν : ℝ) :
    SmoothSquareIntegrableJets
      (fun x : Space => pressureGradient (zeroSol ν).pressure (1/2) x) :=
  pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR (zeroSol ν) memForceR_zero
    (by constructor <;> norm_num)

#print axioms p2_on_zeroSol
#print axioms const_not_jets

end Rev117
```

## Appendix B — `/tmp/rev117/export_m.lean` (finding 3: the recommended exports, all compile)

```lean
import NSFormalization.Section4.D01.PressureJets

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (ClassicalSolutionR)   -- NOT MemForceR: ambiguous, see LESSONS
open NSFormalization.Paper3 (RealVectorSobolev)

namespace Rev117Export

variable {ν : ℝ} {a : Space → Space} {f : VelocityField} {T : ℝ}

/-- **eq:Rpressure at order `m` as an identity of data.** -/
theorem isSobolevDatum_lerayComplement_pressureGradient
    (u : ClassicalSolutionR ν a f T) (hf : MemForceR f) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    {m : ℕ} {Am : RealVectorSobolev (m : ℝ)}
    (hAm : IsSobolevDatum (m : ℝ) (fun x : Space => f (t, x) - advection u.velocity t x
      + ν • spatialLaplacian u.velocity t x) Am) :
    IsSobolevDatum (m : ℝ) (fun x : Space => pressureGradient u.pressure t x)
      (Leray.lerayComplement (m : ℝ) Am) := by
  have h0m : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  refine (Leray.isSobolevDatum_lower_iff h0m).mp ?_
  have hii1 : lowerVectorL (m : ℝ) 0 h0m Am
      = orderZeroDatum (smoothL2_momentumResidual_slice u hf ht).memLp :=
    isSobolevDatum_unique (Leray.isSobolevDatum_lower h0m hAm)
      (isSobolevDatum_orderZeroDatum _)
  have hii2 : lowerVectorL (m : ℝ) 0 h0m (Leray.lerayComplement (m : ℝ) Am)
      = Leray.lerayComplement 0
          (orderZeroDatum (smoothL2_momentumResidual_slice u hf ht).memLp) := by
    rw [← Leray.lerayComplement_lowerVectorL, hii1]
  rw [hii2, ← orderZeroDatum_pressureGradient_eq u hf ht]
  exact isSobolevDatum_orderZeroDatum _

/-- The `hP` slot of `A04.momentum_datum`, existence form. -/
theorem exists_isSobolevDatum_pressureGradient_slice
    (u : ClassicalSolutionR ν a f T) (hf : MemForceR f) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (m : ℕ) :
    ∃ P : RealVectorSobolev (m : ℝ),
      IsSobolevDatum (m : ℝ) (fun x : Space => pressureGradient u.pressure t x) P :=
  (memHInfty_iff_smoothSquareIntegrableJets.mpr
    (pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR u hf ht)).2 m

/-- Any order-`m` datum `P` of `∇p(t,·)` a consumer holds is pinned to `(I−P)ₘ Am`. -/
theorem pin_pressureGradient_datum
    (u : ClassicalSolutionR ν a f T) (hf : MemForceR f) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T)
    {m : ℕ} {Am P : RealVectorSobolev (m : ℝ)}
    (hAm : IsSobolevDatum (m : ℝ) (fun x : Space => f (t, x) - advection u.velocity t x
      + ν • spatialLaplacian u.velocity t x) Am)
    (hP : IsSobolevDatum (m : ℝ) (fun x : Space => pressureGradient u.pressure t x) P) :
    P = Leray.lerayComplement (m : ℝ) Am :=
  isSobolevDatum_unique hP (isSobolevDatum_lerayComplement_pressureGradient u hf ht hAm)

end Rev117Export
```

Negative example recorded (`logs/LESSONS.md` top entry reproduced): writing
`open NSFormalization.Section4.D01` **and** `open NSFormalization.Section4.A02 (ClassicalSolutionR MemForceR)`
at file top level (outside any namespace) gives, verbatim:

```
/tmp/rev117/export_m.lean:17:43: error: Ambiguous term
  MemForceR
Possible interpretations:
  NSFormalization.Section4.A02.MemForceR f : Prop

  NSFormalization.Section4.D01.MemForceR f : Prop
```
The module under review is immune because its `open`s sit *inside* `namespace …D01`, where the
enclosing namespace wins.

## Appendix C — `/tmp/rev117/contract_shape.lean` (§6: contract fields + binding terms)

```lean
import Contracts.V1.DatumLemmas
import Contracts.V1.Packet
import Bindings.Uniqueness
import NSFormalization.Section4.D01.PressureJets

namespace Rev117Contract

open Set MeasureTheory
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open NSFormalization.Paper3 (RealVectorSobolev)

def Field1 : Prop :=
  ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
    (u : ClassicalSolutionR ν a f T), MemForceR f → ∀ t : ℝ, t ∈ Ioo (0 : ℝ) T →
    SmoothSquareIntegrableJets fun x : Space => pressureGradient u.pressure t x

def Field2 : Prop :=
  ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
    (u : ClassicalSolutionR ν a f T), MemForceR f → ∀ t : ℝ, t ∈ Ioo (0 : ℝ) T →
    SmoothSquareIntegrableJets fun x : Space => temporalDerivative u.velocity t x

def Field3 : Prop :=
  ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
    (u : ClassicalSolutionR ν a f T), MemForceR f → ∀ t : ℝ, t ∈ Ioo (0 : ℝ) T →
    ∀ m : ℕ, ∃ P : RealVectorSobolev (m : ℝ),
      IsSobolevDatum (m : ℝ) (fun x : Space => pressureGradient u.pressure t x) P

theorem field1 : Field1 := fun _ _ _ _ u hf _ ht =>
  NSFormalization.Section4.D01.pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR
    (BlowupDensity.Bindings.uniqueness_toA02 u) hf ht

theorem field2 : Field2 := fun _ _ _ _ u hf _ ht =>
  NSFormalization.Section4.D01.temporalDerivative_slice_smoothSquareIntegrableJets_of_memForceR
    (BlowupDensity.Bindings.uniqueness_toA02 u) hf ht

theorem field3 : Field3 := fun ν a f T u hf t ht m =>
  (NSFormalization.Section4.D01.memHInfty_iff_smoothSquareIntegrableJets.mpr
    (field1 ν a f T u hf t ht)).2 m

end Rev117Contract
```

Output: all three `#print axioms` give `[propext, Classical.choice, Quot.sound]`.

## Appendix D — `/tmp/rev117/fid_a.lean`, `fid_b2.lean` (bridges)

```lean
-- fid_a.lean (excerpt) — all of these compile
example : @NSFormalization.Section4.A02.MemForceR = @NSFormalization.Section4.D01.MemForceR := rfl
example : @NSFormalization.Section4.D01.SmoothSquareIntegrableJets
        = @BlowupDensity.Contracts.V1.SmoothSquareIntegrableJets := rfl
example : @NSFormalization.Section4.A02.MemForceR
        = @BlowupDensity.Contracts.V1.Data.MemForceR := rfl
-- fid_b2.lean (excerpt)
example : @NavierStokes.ProblemStatement.pressureGradient
        = @BlowupDensity.Contracts.V1.pressureGradient := rfl
example : @NSFormalization.Section4.D01.MemForceR
        = @BlowupDensity.Contracts.V1.Data.MemForceR := rfl
```

The one deliberate failure, confirming `CLAUDE.md`'s structure rule:

```
/tmp/rev117/fid_b2.lean:27:65: error: Type mismatch
  rfl
has type
  ?m.3 = ?m.3
but is expected to have type
  NSFormalization.Section4.A02.ClassicalSolutionR = BlowupDensity.Contracts.V1.Data.ClassicalSolutionR
```
— hence the binding must use `Bindings.uniqueness_toA02`, as §6 prescribes.
