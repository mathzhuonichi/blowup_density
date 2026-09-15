# A01 split-and-start — review of lane 093

Reviewer pass over `erenup/093-A01-split` (commit `2d7fac3`), covering
`formalization/NSFormalization/Section4/A01/ConvectionDivergence.lean`,
`research/A01/A01_SPLIT.md`, `research/A01/ATTEMPTS_A01.md` and
`research/A01/axioms_a01.lean`.  Lean run in the lane worktree at the repo pin.

## Verdict: **ACCEPT-WITH-NOTES**

The Lean is clean, minimal and genuinely load-bearing: `convectionDivergence` is
`rfl`-identical to the draft spec, the Leibniz hypothesis is the right one, and
the payoff theorem is strong enough that I could prove — in 12 lines, standard
axioms — that `ManuscriptLocalRegularity.projected` is a *theorem* about any
`ClassicalSolutionR` (§ Finding 3).  All five recorded failed approaches are
real; two of them I reproduced with negative probes.  Every citation I opened
resolves, and the U05 compile result reproduces exactly.

The table is a solid deliverable, but it carries one wrong claim about the A02
interface (Finding 1), one under-costed row (Finding 2), one row whose "no
inputs" column is wrong (Finding 4), and some bookkeeping drift.  None of these
touch the Lean; all are edits to `A01_SPLIT.md` (plus one docstring line
number).  Merge the Lean as is; fix the memo in the next A01 lane.

---

## 1. Commands and results

All from `/data_8T/ping/blowup_density/.claude/worktrees/093-A01-split`, after
`bash scripts/lean-install.sh` (idempotent, already satisfied),
`. scripts/lean-env.sh`, `export LEAN_NUM_THREADS=6`; `lake` only from
`verification/`, one process at a time.

| command | result |
|---|---|
| `lake build NSFormalization.Section4.A01.ConvectionDivergence` | `Build completed successfully (2616 jobs).` |
| `lake env lean ../formalization/NSFormalization/Section4/A01/ConvectionDivergence.lean` | **silent**, exit 0 (no warnings — the deprecation avoidance in ATTEMPTS is real) |
| `lake env lean ../research/A01/axioms_a01.lean` | 4 declarations, each exactly `[propext, Classical.choice, Quot.sound]` |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats'` on the four lane files | only the four `#print axioms` lines in `axioms_a01.lean` and one prose line in `A01_SPLIT.md:191`. No `sorry`/`admit`/`axiom` declaration, no `native_decide`, no `maxHeartbeats` |
| `make check` | exit 0 (architecture checks, 13 contract-policy tests OK, `30 work items: ownership, contract registration and task cards consistent.`) |
| `make test` | exit 0; 15 registered contracts replayed, each "checked; standard logical axioms only" |

### U05 reproduction

| target | result |
|---|---|
| `lake build Formal.R3EndpointSafeProjectedLocalExistence` | `Build completed successfully (8830 jobs).` — **exactly the number the lane reports**; only style-linter warnings (`linter.style.haveILetI`) |
| `lake build Formal.R3NavierStokesEquation` | `Build completed successfully (8839 jobs).` |
| `lake build Formal.R3HelmholtzPressure` | `Build completed successfully (8810 jobs).` |
| `lake build Formal.FlowMapLocalContDiff` | `Build completed successfully (8767 jobs).` |
| `lake build Formal.R3InversionConsistency` | `Build completed successfully (8809 jobs).` |
| `lake build Formal.R3DecoderFrequencyBridge` | `Build completed successfully (8808 jobs).` |
| `lake build FormalPatched.R3MildContinuation` | `Build completed successfully (8841 jobs).` |
| `lake build FormalPatched.EndpointSafeTwoSpaceUniqueness` | `Build completed successfully (8838 jobs).` |
| `lake build FormalPatched.R3QuantitativeLifespan` | `Build completed successfully (8837 jobs).` |
| `lake build FormalPatched.R3RealLocalMildSolution` | `Build completed successfully (8836 jobs).` |
| `lake build Formal.MildSolutionSemantics` | `error: unknown target` |
| `lake build Formal.MildFlowMapBridge` | `error: unknown target` |
| `lake build Formal.MildZeroUniqueness` | `error: unknown target` |

**Importable roots.** `formalization/lakefile.toml:22-101` declares the `Formal`
library with `srcDir = "../vendor/HeliCorgi"` and **88 explicit roots** — the
import closure of `R3EndpointSafeProjectedLocalExistence`,
`R3NavierStokesEquation`, `R3HelmholtzPressure` and `R3MildContinuation`, minus
the four that do not compile at this pin.  Any of those 88 modules is importable
today.  **The four patched ones** are `FormalPatched.R3RealLocalMildSolution`,
`FormalPatched.R3QuantitativeLifespan`,
`FormalPatched.EndpointSafeTwoSpaceUniqueness`, `FormalPatched.R3MildContinuation`
(`lakefile.toml:113-121`; same namespaces and declaration names as upstream,
`vendor/HeliCorgi` byte-identical).  The three "untested" modules the lane names
are **not roots** and `lake build` reports `unknown target` for each, exactly as
the memo says; adding them is a lakefile change, out of lane scope.

**Verdict on the toolchain claim: reproduced and correct.** U05 does not block
A01.  See Finding 5 for the framing, and Finding 2 for what *does* still block
the rows that cite HeliCorgi.

### Reviewer probes (scratch files under `/tmp/a01rev/`, not committed)

1. **Drop-in fidelity.** `example (u : SpaceTimeField) (t : ℝ) (x : Space) :
   BlowupDensity.A01.Draft.convectionDivergence u t x =
   NSFormalization.Section4.A01.convectionDivergence u t x := rfl` — **compiles**.
2. **Row shapes.** `A3Shape`, `A2Shape`, `P1Shape`, `M4Shape`, `H1Shape`,
   `M2Shape` (the last using the *module's* `convectionDivergence`), plus
   `example … : ContDiffOn ℝ ∞ u.velocity (Ico 0 T ×ˢ univ) := u.velocity_smooth`
   (row B1/c3) and `… := u.sobolev` (row c8) — **all elaborate, no errors**.
3. **Usability of E1's hypothesis.** From `ClassicalSolutionR` at an interior
   time, `DifferentiableAt ℝ (fun y => u.velocity (t,y)) x` is six lines
   (`velocity_smooth.mono` onto `Ioo 0 T ×ˢ univ`, `isOpen_Ioo.prod
   isOpen_univ`, `differentiableOn … (by simp)`, `.differentiableAt`, then
   `.comp x ((differentiableAt_const t).prodMk differentiableAt_id)`).
4. **Non-vacuity.** The zero field inhabits both hypotheses
   (`differentiableAt_const`, `spatialDivergence 0 = 0` by `simp`); and
   `ClassicalSolutionR.horizon_pos : 0 < T` makes `Ioo 0 T` nonempty, so
   `projected` is not vacuously satisfiable.
5. **Negative probes for ATTEMPTS** (§ Finding 8): removing the explicit `x`
   from `HasFDerivAt.comp`, and removing the trailing `rfl` of the second sum
   bullet, each reproduce a failure.

---

## 2. Statement fidelity

**`convectionDivergence` vs `research/A01/Spec.lean:103-105`.** Token for token
identical; the only difference is the binder type, `VelocityField` in the module
against `SpaceTimeField` in the spec, and
`verification/Contracts/V1/Data.lean:104` is `abbrev SpaceTimeField :=
VelocityField`.  Probe 1 above certifies the two are `rfl`-equal, so the module
is a literal drop-in.  No prior definition exists anywhere in `formalization/`,
`verification/` or `vendor/` — the docstring's grep claim holds.

**Leibniz hypotheses.** `DifferentiableAt ℝ (fun y => u (t,y)) x` is the right
and minimal hypothesis: it is exactly what the product `y ↦ u(t,y)_j • u(t,y)`
needs (the scalar factor is `EuclideanSpace.proj j ∘ u`, differentiable by
composition with a CLM), it is stated *in space at frozen time* as the
manuscript's `∇·` requires, and probe 3 shows `ClassicalSolutionR` discharges it
at every interior point.  The divergence term is the vendor's
`spatialDivergence` (`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:67`,
`∑_i (∂_i u)_i`) scalar-multiplying `u (t,x)`; the advection is the vendor's
`advection` (`:63`, `Du(x)·u(x)`).  The identity
`∑_j ∂_j(u_j u_k) = (∇·u)u_k + ((u·∇)u)_k` is the correct component-wise
Leibniz expansion, with the right orientation of the tensor.

**`navierStokesResidual_eq_iff_projected` vs `Spec.lean:214`.** The right-hand
side of the theorem is the `projected` field verbatim with `F := f (t,x)`:
`temporalDerivative u t x - ν • spatialLaplacian u t x = (F -
convectionDivergence u t x) - pressureGradient p t x`.  The left-hand side is
`NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = F`, which is
`ClassicalSolutionR.momentum` (`Section4/A02/SolutionClass.lean:130`) pointwise.
Both sides are quantified at the same `(t,x)` and the equivalence is under
exactly `differentiable in space` + `divergence free` — the two conditions
`ClassicalSolutionR` supplies on `Ioo 0 T`.  Against the manuscript: eq:projected
(`paper/sections/02-preliminaries.tex:81`) is
`∂_tu − νΔu = −P∇·(u⊗u) + Pf`, and eq:Rpressure (`:90`) is
`∇p = (I−P)(f−∇·(u⊗u))`; substituting the second into the first gives
`(f − ∇·(u⊗u)) − ∇p`, which is the Lean right-hand side.  Faithful.

**Could a wrong implementation satisfy it?**  Two vacuity routes, both closed.
(i) `projected` is quantified over `Ioo 0 T`, and `horizon_pos : 0 < T` is a
field of the structure it sits on, so the domain is nonempty.  (ii) The
equivalence itself is inhabited — the zero field satisfies both hypotheses
(probe 4).  The real risk here is the opposite of vacuity: since E1 makes
`projected ⟺ momentum`, the `projected` field carries **no logical content beyond
`momentum`**, which is what `research/A01/REVIEW.md` L7 already recorded and what
Finding 3 now makes a theorem.  That is by design (the manuscript's own spelling
is kept so the contract reads as eq:projected), and it is *not* a definitional
shortcut: `convectionDivergence` is defined as the tensor divergence, and the
Leibniz lemma is the content that connects the two spellings.

---

## 3. Findings

### Finding 1 — §e's "single thing A02 needs" is wrong (severity: **medium**)

`research/A01/A01_SPLIT.md` §e says:

> So the **single thing A02 still needs from A01** is inhabitation of that clause
> … Nothing subtler: A02 needs data, not a proof, from A01 (`A02` `patch`,
> `pressure_normalization`, `restrict` are all A02-internal and already proved).

The first half of §e is right — `verification/Contracts/V1/MaximalPartial.lean:155-162`
and `Section4/A02/Maximal.lean:22-31` take the A01 clause as an explicit
`localSolution` hypothesis, so `exists_maximal` / `horizon_le_lifespan` need only
inhabitation.  But A02 has a second, still-unproved field that consumes A01:
`research/A02/Spec.lean:551` `restart`, whose own docstring says

> The quantifier order — `δ` before `(a,f,u,p,t₀)` — is **A01's
> `horizonLowerBound` quantifier order**, and is the whole point.

So `restart` needs A01's `horizon_lower_bound` (unit **H1**), plus `uniqueness`
and `patch`.  `NEXT_SESSION.md` independently records "A02 只剩 `restart*` /
`insertion_lifespan_eq`（需 A01 + R42）".  This matters for prioritisation: §d
currently presents H1 as "consumed by **A04**'s restart", which under-sells it —
A02's own unproved field needs it too.

*Fix.* Scope the §e sentence to `exists_maximal` / `horizon_le_lifespan`, and add
a second row to §e: `A02.restart ← A01.horizon_lower_bound (H1) + A02.uniqueness
+ A02.patch`.  Update §d's "consumed by A04's restart" to "consumed by A02's
`restart` and, through it, A04's continuation".

### Finding 2 — row A2b is under-costed on the recommended route (severity: **medium**)

Row A2b is sized **M** with the blocker "importable via `FormalPatched.*` (U05
ok)".  Importability is confirmed (all four `FormalPatched.*` build).  But the
recommended order of work at the end of the table runs the **OpenAI/local spine**
(`F1 → C1a+C1b → A1 … A2, A2b, A3, T1, B1, B2`), and the HeliCorgi continuation
lives on the order-3 complex Bessel carrier.  Consuming
`r3EndpointSafeProjected_exists_extension_of_bounded` inside A01 therefore needs
**C1c**, which the table itself sizes **L** and marks a gap ("three Fourier
conventions meet here").  So A2b is M only *if* the spine switches to HeliCorgi
for continuation; on the stated spine it is L, or the table owes a paragraph on
mixing carriers.  The sentence "No row below is blocked *by the toolchain*" is
literally true and should not be read as "no row is blocked": several HeliCorgi
rows are blocked by the **carrier bridge**, which U05 does not touch.

*Fix.* In row A2b's blocker column add "on the OpenAI/local spine, consuming this
requires **C1c** (L)"; and in the U05 section add one sentence distinguishing
toolchain blockers (gone) from carrier-bridge blockers (C1b/C1c, unchanged).

### Finding 3 — row m3's status understates what E1 already bought (severity: **low**, good news)

Row m3 reads "E1 proved; equation transport from source remains".  In fact, with
E1 in hand, `ManuscriptLocalRegularity.projected` is a **theorem about any
`ClassicalSolutionR`** — no transport from any source is needed beyond producing
the `ClassicalSolutionR` itself (which is c7/B2, already counted).  I proved it:

```lean
theorem projected_of_classicalSolution
    (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
    (u : ClassicalSolutionR ν a f T) :
    ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
      temporalDerivative u.velocity t x - ν • spatialLaplacian u.velocity t x =
        (f (t, x) - NSFormalization.Section4.A01.convectionDivergence u.velocity t x)
          - pressureGradient u.pressure t x
```

12 lines, `#print axioms` = `[propext, Classical.choice, Quot.sound]`.  It uses
`velocity_smooth` → `DifferentiableAt`, `divergence`, `momentum`, and the lane's
`navierStokesResidual_eq_iff_projected`.

*Fix.* Mark m3 "**reducible to c7/B2**, no separate obligation", and record
`projected_of_classicalSolution` as a ready ~20-line harvest for the next lane
(see § 5).

### Finding 4 — row B1's "inputs" column is empty, but four real inputs exist (severity: **medium**)

I agree with the table's headline: **B1/c3 is the crux, and no source produces
joint space-time `C^∞` from `H^m`-valued time paths.**  A full sweep of all three
codebases confirms it — every `ContDiffOn ℝ ∞ u (Ico 0 T ×ˢ univ)` in the tree is
either a structure field you must supply, a hypothesis on an already-smooth
field, or the smoothness of an explicitly constructed candidate.  Notably
`vendor/NavierStokesAndEuler/NavierStokes/MaximalLifespan.lean:116`
`candidate_is_classical_solution` projects smoothness straight out of its
`CandidateProperties` hypothesis, and `Source/SmoothLifespan.lean` `Flow` has
exactly two producers (`Flow.restrict :83`, `insertionFlow :218`), both consuming
a `Flow` — the table's claim is right.  `formalization/blueprint/EXTERNAL_REUSE.md`
says the same twice ("do not assume H3 implies C-infinity"; "Connect … common
all-order interval and time regularity").

But B1's `depends on` column lists only `T1, A1` and cites nothing, which reads
as "nothing in tree helps".  Four compiled declarations are directly relevant:

| what it gives | where |
|---|---|
| **joint (time,space) continuity** of the pointwise representative of a continuous `H³` path — the first rung of B1's ladder, and the closest thing that exists anywhere | `formalization/NSFormalization/Paper1/PeriodicH3RepresentativeBridge.lean:24` `continuous_pointwise_representative`; with one spatial derivative from an `H⁴` path at `:83` `differentiated_path_pointwise_continuous`. Its own docstring: "the spatial part of the mild-to-classical bridge; temporal smoothness is deliberately not asserted" |
| `H³ → C⁰` with a bounded point-evaluation CLM (cylinder) | `vendor/NavierStokesAndEuler/Euler/SobolevPointEvaluation.lean:63` `pointEvaluation`; `Euler/EulerProof.lean:10110` `exists_continuous_representative` |
| `L²` frequency data → **pointwise `C¹`** spatial field, with everywhere-classical divergence-free | `vendor/HeliCorgi/Formal/R3ClassicalIncompressibility.lean:58` `contDiff_one_r3PhysicalRepresentative` (analytic core); packaged at `R3DecoderFrequencyBridge.lean:278` and, with the a.e. identification to the `L²` decode, `R3InversionConsistency.lean:139` `r3DecodedFrequency_incompressible_ae_decoder` |
| **precedent**: the same gap, already faced and recorded on the torus as an unproved structure-of-hypotheses | `formalization/NSFormalization/Paper1/PeriodicLocalLifespan.lean:73` `ClassicalPeriodicLocalTheory` (`local_flow`, `finite_h2_extension`), used only as a hypothesis, never proved |

All three HeliCorgi modules are among the 88 roots and build (§ 1).  These do not
overturn the verdict — they are C⁰/C¹, spatial-only or per-slice, order-pinned,
and two of them are periodic/cylinder — but a campaign-sized unit with an empty
inputs column is the wrong signal.  Also: row **c6** (`divergence`) currently says
"transport the source's div-free clause" with no citation;
`r3DecodedFrequency_incompressible_ae_decoder` is that citation on the HeliCorgi
route.

*Fix.* Add the four citations to B1's row (and the third to c6), and add one line
noting the torus precedent, so the next lane starts from the existing rungs
rather than from zero.

### Finding 5 — "U05 finding (key result of this lane)" overstates novelty (severity: **low**)

The port is not new.  `PLAN.md:110` records lane `004-U05-toolchain-probe` merged
(PR #8) and `PLAN.md:120` records `010-U05-port` merged (PR #11, "88 模块全部编
过"); `PLAN.md:224` already states "U05 已完成（HeliCorgi 已移植）"; and
`formalization/lakefile.toml:22` cites `research/U05/{REPORT,REVIEW,PORT}.md`.
The memo's body is careful ("already resolved in this workspace, and this lane
verified it"), but the section title is not.  What this lane genuinely adds is
(a) an independent re-verification, (b) the enumeration of which roots are
importable and which three are `unknown target`, and (c) the mapping from that
fact onto the A01 rows.  That is worth having — and it is **CLAUDE.md that is
stale**, not the repo.

*Fix.* Retitle the section "U05 re-verification — CLAUDE.md is stale" and point
at `PLAN.md:110,120,224`.  See § 6 for the CLAUDE.md edit.

### Finding 6 — "E1 off the critical path" contradicts the table's own T1 row (severity: **low**)

The closing paragraph calls E1 "the one S-unit **off the critical path**", but
§b's T1 row lists `depends on: A3, E1`, and §c's c7/m3 both consume it.  E1 is a
genuine prerequisite with a lot of slack (its successors are gated by L-units),
which is not the same as being off the path.

*Fix.* "E1 is the one S-unit with enough slack to run first: it is an input to
T1/c7/m3 but never the binding constraint."

### Finding 7 — citation drift into `research/D01/RECONCILIATION.md` (severity: **low**)

* `RECONCILIATION.md:173` is cited for "Genuinely absent objects" — in
  `ConvectionDivergence.lean:20` (the Lean docstring) and in the memo.  The
  heading is actually at **`:190`**; `:173` is "## 4. Ledger D01 requirements
  **not** covered".
* `RECONCILIATION.md:243` is cited for "provable-but-vacuous until prop:local
  lands"; the sentence is at **`:240`**.
* `RECONCILIATION.md:160` (D01 unit L9) is **correct**.

The drift is inherited from `Spec.lean`/`COMPARISON.md`, but it has now been
copied into a `formalization/` module that will outlive the memos.

*Fix.* `:173 → :190` in `ConvectionDivergence.lean:20` and in `A01_SPLIT.md`;
`:243 → :240` in `A01_SPLIT.md`.

### Finding 8 — ATTEMPTS is honest; one quoted error message is not reproducible (severity: **low**)

All five entries are real.  Verified:

1. **`HasFDerivAt.comp` needs the explicit point.** `variable (x)` at
   `Mathlib/Analysis/Calculus/FDeriv/Comp.lean:45`, `HasFDerivAt.comp` at `:105`.
   Negative probe (remove `x`): fails, as claimed.  *But* the quoted message
   ("argument `DifferentiableAt.hasFDerivAt hu` has type Prop but expected
   Type") is not what the code reproduces; my probe gives a `Type mismatch` on
   `HasFDerivAt.comp ?m ?m` plus an application-type-mismatch that names
   `DifferentiableAt.hasFDerivAt hu` with two `HasFDerivAt` types.  Substance
   confirmed, wording not.
2. **Higher-order unification on `hc`'s ascription.** Consistent with the shape
   that compiles; not separately probed (it describes an elaboration state, not
   a reproducible one-line edit).
3. **`HasFDerivAt.smul` is outside the import closure.** Confirmed twice: the
   lemma is at `Mathlib/Analysis/Calculus/FDeriv/Mul.lean:71`, and a file
   importing only `NavierStokes.R3.ProblemStatement` reports
   `Unknown constant 'HasFDerivAt.smul'`.  The added import is genuinely needed.
4. **`EuclideanSpace.proj : StrongDual 𝕜 …`** at
   `Mathlib/Analysis/InnerProductSpace/PiL2.lean:288`, `f` explicit in
   `ContinuousLinearMap.hasFDerivAt`.  Confirmed.
5. **The trailing `rfl` is load-bearing.** Negative probe (remove it) leaves
   exactly `⊢ (∑ i, ((fderiv ℝ (fun y => u (t, y)) x) (coordinateVector i)).ofLp i) • u (t, x) = spatialDivergence u t x • u (t, x)`,
   i.e. `rw`'s reducible-transparency rfl does not unfold `spatialDivergence`.
   Confirmed.
6. **Deprecations.** `ContinuousLinearMap.add_apply` and
   `ContinuousLinearMap.smul_apply` are both deprecated at this pin ("Use
   `add_apply` instead"); the module uses the root names and `lake env lean` on
   it is silent.  Confirmed.

*Fix.* Replace the quoted message in entry 1 with the one the probe produces.

### Finding 9 — bookkeeping: the "14 units" arithmetic only works on one reading (severity: **low**)

"A01 owns 14 units (A1 is A03's, C1a is D01's)" followed by
`S = {E1,B2,X1}`, `M = {P1,P2,C1a,A2,A2b,P3,T1,H1}`, `L = {C1b,C1c,A3,B1}` is
3+8+4 = 15 printed, and reaches 14 only by silently dropping C1a from the M list
it is printed in — while F1 is a §b row with a size column but belongs to no size
class at all.

*Fix.* Mark A1 and C1a "(other task)" inline in the size lists and give F1 its
own class, so the total is checkable by reading.

### Finding 10 — informational, for the next lane

* **The future A01 contract cannot import this module.**
  `experiments/check_contracts.py:31-39` whitelists only
  `NavierStokes.R3.ProblemStatement` plus six local canonical modules;
  `NSFormalization.Section4.A01.ConvectionDivergence` is not among them.  The
  contract must restate `convectionDivergence` verbatim with a `rfl` bridge in
  `Bindings/`.  Probe 1 shows the bridge works (the spec's copy and the module's
  are `rfl`-equal), so this is de-risked — but it should be a line in the table.
* **`Section4/*` is outside the CI import closure.**
  `grep -c Section4 formalization/NSFormalization.lean` = 0, so this module is
  built only by explicit `lake build` / `build_changed_lean.py`, not by
  `make test`.  Pre-existing and already recorded in `NEXT_SESSION.md`; noted so
  nobody assumes `make test` covers E1.

---

## 4. Sizes

The size column is inherited verbatim from `research/A01/COMPARISON.md` §3, which
was already reviewed, and I found no size I would move **down**.  Two I would flag
as optimistic, with E1 as the calibration point: E1 was sized **S** and described
in COMPARISON.md as "one-line calculus", and cost 140 lines, one private helper
and five compile iterations.  On that calibration —

* **B2** (assemble nine `ClassicalSolutionR` fields across a carrier bridge) is
  marked S; expect M.
* **H1** is marked M, but the table itself says it "must come from the A3
  propagation, not be read off the source", and there is no quantitative lower
  bound anywhere in tree (`Euler/VolterraUniqueness.lean:69`
  `exists_positive_time_budget` produces `T` from a limit argument with no
  formula — confirmed by reading it, and consistent with `REVIEW.md` H1).  Its
  real size is whatever A3 turns out to be; M is conditional.

Everything else (A3/B1/C1b/C1c = L; A2/A2b/T1/P1/P2/P3 = M; X1 = S) is plausible.

## 5. Citation spot-checks

Opened and confirmed exact: `Formal/R3EndpointSafeProjectedLocalExistence.lean:35`
(`r3EndpointSafeProjected_exists_localMildSolution`, order pinned 3, unforced —
as described); `Formal/R3HelmholtzPressure.lean:259`
(`r3HelmholtzPressure_gradient`, arbitrary `L²` `F`, `𝓢'`-componentwise);
`Formal/R3NavierStokesEquation.lean:142`; `Formal/EndpointSafeTwoSpaceDuhamel.lean:407`
(`EndpointSafeTwoSpaceDuhamelContract` — no forcing field, as F1 claims);
`FormalPatched/R3MildContinuation.lean:84,134`;
`FormalPatched/EndpointSafeTwoSpaceUniqueness.lean:222`;
`Source/OrdinaryForcedLocal.lean:32` (`hq : 6 ≤ q`, `T` unquantified, ordinary
`L²` path, no pressure — as described); `Source/OrdinaryForcedTime.lean:36,50`
(one interior derivative, `ht : t ∈ Ioo 0 T`); `Source/SmoothLifespan.lean:23`
(`Flow`, lacks `sobolev`/`pressure_gradient`, has `energy`/`velocity_bound`/
`derivative_bound` — exactly as described, and never built from data);
`Source/ForcedCylinderLocal.lean:52` and `Euler/QuadraticCoefficients.lean:16`
(`Coefficients.forcing`); `Euler/VolterraUniqueness.lean:69`;
`Euler/QuadraticHeatLocal.lean:32`; `Section4/A02/SolutionClass.lean:114,130`;
`Section4/A02/Maximal.lean:22-31`; `Contracts/V1/MaximalPartial.lean:155-162`;
`Section4/A03/OuterTameProduct.lean:279` (`advectionOf_eq` — the mirrored
technique is real, same `hy`/`map_sum`/`map_smul` shape);
`Section4/D01/{Pressure,DatumToJets}.lean` exist; `appendix-a-local-theory.tex`
`:71-76` (the `C^j_tH^k_x` sentence), `:132-137` (eq:Rhigh), `:142-145`
(eq:highcontinuation — matches A2's displayed inequality exactly), `:147-152`
(the common positive existence duration; the memo writes `:147-150`, the sentence
runs to `:152`); `02-preliminaries.tex:81,90,94,96-100,101,117`;
`04-whole-space.tex:183-192`.  Only the two `RECONCILIATION.md` line numbers are
wrong (Finding 7).

## 6. Recommended next A01 lane, and the doc edits

**Next lane: unit P1** (`pressurePotential G` has gradient `G` under
`HasSymmetricJacobian G`), sized M.  It is the only M-sized A01 unit with *no*
dependency and *no* gap: `COMPARISON.md:191` lists its `depends on` and `blocker`
columns both empty, the manuscript hands over the whole proof in two lines
(`02-preliminaries.tex:96-100`: `∂_jp = ∫₀¹ ∂_r[rG_j(rx,t)] dr = G_j`), and the
only Lean work is differentiating under `intervalIntegral` with its side
conditions.  It pays twice: it discharges `ManuscriptLocalRegularity.pressure_potential`
(m4) outright *and* it is D01 unit **L9(b)**, so it retires an item in two
ledgers.  Everything on the true spine (A3, B1, C1b, C1c) is an L-campaign that
needs a plan lane before a proof lane, and P2 is gated on a Liouville statement
Mathlib does not have; P1 is the one unit that is genuinely shovel-ready.
Inputs: `pressurePotential` (`verification/Contracts/V1/Data.lean:596`),
`HasSymmetricJacobian` (`research/A01/Spec.lean:117`, note it now carries
`Differentiable ℝ G` per `REVIEW.md` H2), `pressureGradient`
(`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:67`),
`PressureGaugeEquivOn` (`Data.lean:589`), and Mathlib's `intervalIntegral`
differentiation-under-the-integral plus FTC.  **Fold in the free harvest first**
(~20 lines, already proved in § Finding 3): add `projected_of_classicalSolution`
to `Section4/A01/`, which turns m3 from an obligation into a theorem and makes
the E1 module's value visible to A02/A04 immediately.

### `CLAUDE.md` — replace line 80

> - 关键链：D01 → A01 → A02 → A04 → R43/R44 → R41（定理 4.1）。A01 还卡 U05（HeliCorgi 工具链兼容）。

with

> - 关键链：D01 → A01 → A02 → A04 → R43/R44 → R41（定理 4.1）。**A01 不再卡 U05**（U05 已于 004/010 两条 lane 完成，PR #8/#11，见 `PLAN.md:110,120,224`）：HeliCorgi mild 栈已就地编进主 workspace，reviewer 于 093 复现 `lake build Formal.R3EndpointSafeProjectedLocalExistence` → 8830 jobs 成功。A01 现在卡的是载体桥 C1b/C1c 与 A3/B1 三个 L 单元（`research/A01/A01_SPLIT.md`）。

### `CLAUDE.md` — replace line 45

> `vendor/HeliCorgi` 是 4.32.1 的独立包，尚未与主包混编（任务 U05）。

with

> `vendor/HeliCorgi` 源码是 4.32.1，但 U05 已把它在本 pin 下**就地编进主 workspace**：`formalization/lakefile.toml:22-101` 的 `Formal` 库（`srcDir` 指向 vendor，88 个显式 root，vendor 零改动）＋ `:113-121` 的 `FormalPatched` 库（4 个在 4.34.0-rc2 下编不过的模块的补丁副本）。`Formal.MildSolutionSemantics` / `MildFlowMapBridge` / `MildZeroUniqueness` 不在 root 列表，`lake build` 报 `unknown target`，要用先加 root（配置变更）。

Line 81 ("可并行起步、互不依赖：U05、D01、A05、I01") should drop `U05`.

### `NEXT_SESSION.md`

Line 24 is stale on two counts (PR #15 is already filed per line 6, and the U05
report already exists at `research/U05/REPORT.md`):

> - `erenup/integration` → `main` 的第一个 PR 何时提（建议：D01 定稿 + U05 报告出来后）。

Replace with a status line, e.g. "PR #15（integration → main）已提交，待 owner
review；U05 报告见 `research/U05/REPORT.md`。"  And add to 现状:

> - **A01**：093 出了 14 单元拆分表 `research/A01/A01_SPLIT.md`，证了 E1（`Section4/A01/ConvectionDivergence.lean`，4 个声明标准 3 公理）。**U05 不再是 A01 的堵点**（reviewer 复现：`Formal.R3EndpointSafeProjectedLocalExistence` 8830 jobs，4 个 `FormalPatched.*` 全绿；3 个 `Mild*` 模块非 root，`unknown target`）。真正的堵点是载体桥 C1b/C1c 与 A3/B1。下一条：P1（唯一无依赖、无 gap 的 M 单元），顺带收 `projected_of_classicalSolution`。
