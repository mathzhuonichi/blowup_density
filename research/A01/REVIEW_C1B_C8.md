# REVIEW — lane 124 (`erenup/124-A01-c1b-c8-0`), row C1b-c8-0 + c8 at `m = 0`

Reviewer run 2026-09-13.  Scope = the single commit `3934cb7` on top of
merge-base `6cbbda5` (5 files, +401, −5).  Probes in `/tmp/rev124/`; every error
/ goal text quoted below was produced by the command shown next to it.

## Verdict: **ACCEPT-WITH-NOTES**

The module compiles, is silent, axiom-clean on all 8 declarations, and says what
row `C1b-c8-0` says.  I verified the three fidelity claims that matter and all
three hold **exactly**: (a) `orderZeroDatumCLM` is a genuinely different term
from `orderZeroDatum` and the `Lp.ext` bridge is provably the *only* non-`rfl`
step (findings 2–3); (b) the conclusion of `datumPath_isSobolevDatum` really
produces the `ClassicalSolutionR.sobolev` shape at `m = 0`, against the A02
restatement, after one `Nat.cast_zero` transport (finding 4); (c) the result is
strongly non-vacuous — I proved `orderZeroDatumCLM` **injective** in a probe, so
the datum path of `t ↦ t • u₀` is continuous and genuinely non-constant for a
concrete `u₀ = indicatorConstLp (ball 0 1) e₀` (finding 6).  Both recorded
failures reproduce verbatim and the deprecation replacements are the right
modern names (findings 11–12).

The notes are placement / hand-off / merge-order items, not code defects:
`orderZeroDatumCLM` is a D01-level object sitting in A01 (finding 8),
`simp only [Nat.cast_zero]` does **not** do the transport the next lane will
need (finding 5), the injectivity spin-off is worth promoting (finding 7), the
B1 hand-off shape is faithful to the table but is *not* the shape the existing
`Source/` machinery produces (finding 9), and row `C1b-c8-m`'s stated blocker
(the vector order-`m` Plancherel isometry) looks **wrong** — continuity at order
`m` does not need it (finding 10).

---

## 1. Compiles / axioms / hygiene — **PASS**

```
$ . scripts/lean-env.sh; cd verification; export LEAN_NUM_THREADS=6
$ lake build NSFormalization.Section4.A01.DatumPathContinuity
Build completed successfully (9874 jobs).
lake build …DatumPathContinuity  2.84s user 0.69s system 169% cpu 2.077 total
```

`lake env lean` on the module from source is **silent** (61 bytes of output, all
of it the `time` line):

```
$ lake env lean ../formalization/NSFormalization/Section4/A01/DatumPathContinuity.lean
EXIT=0
lake env lean   5.75s user 1.16s system 115% cpu 5.979 total
```

Axiom audit — all 8 declarations, standard 3 axioms:

```
$ lake env lean ../research/A01/axioms_c1b_c8.lean
'NSFormalization.Section4.A01.componentCLM' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.componentLp_eq_compLpL' …: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.orderZeroDatumCLM' …: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.orderZeroDatum_memLp_eq' …: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.continuous_orderZeroDatum' …: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.datumPath' …: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.continuousOn_datumPath' …: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A01.datumPath_isSobolevDatum' …: [propext, Classical.choice, Quot.sound]
```

The two non-vacuity `example`s in that file (constant path, identity path) also
elaborate — the file exits 0 with no error.

Gates:

```
$ make check           → OK (13 policy tests; 30 work items consistent)
$ make test            → all registered contracts "checked; standard logical axioms only"  (2.2 s)
$ make test-mutations  → implementation_refactor: accepted / admitted_proof, extra_axiom,
                         weakened_hypothesis: rejected as required.  Mutation suite passed.
```

Token grep over the three new Lean files: the only hits are the eight
`#print axioms` lines in `axioms_c1b_c8.lean`.  No `sorry`, `admit`, `axiom`,
`native_decide`, `maxHeartbeats` or any `set_option` in the module.  No trailing
whitespace; file ends in `\n`.  The committed probe
`research/A01/probes/c1b_c8_probe.lean` still compiles (exit 0, only its five
`#check` outputs) — worth noting because per `logs/LESSONS.md` conformance files
drift silently.

**Finding 1 (info).** `collaboration/work_items.json` already has
`A01 / in-progress / owner erenup`, so this lane correctly has no separate
`claim` commit and touches no registry file.  Nothing to merge in
`contracts.json` / `work_items.json` / `TASKS.md`.

---

## 2. Statement fidelity

`#check` with `pp.fullNames` (`/tmp/rev124/p1_checks.lean`) — all eight exports,
verbatim:

```
componentCLM : Fin 3 → ↥EulerMeanSolenoidal.L2 →L[ℝ] ↥(MeasureTheory.Lp ℂ 2 MeasureTheory.MeasureSpace.volume)
componentLp_eq_compLpL : ∀ (u : ↥EulerMeanSolenoidal.L2) (i : Fin 3),
  NSFormalization.Section4.D01.componentLp ⋯ i = (NSFormalization.Section4.A01.componentCLM i) u
orderZeroDatumCLM : ↥EulerMeanSolenoidal.L2 →L[ℝ] NSFormalization.Paper3.RealVectorSobolev 0
orderZeroDatum_memLp_eq : ∀ (u : ↥EulerMeanSolenoidal.L2),
  NSFormalization.Section4.D01.orderZeroDatum ⋯ = NSFormalization.Section4.A01.orderZeroDatumCLM u
@continuous_orderZeroDatum : ∀ {X : Type u_1} [inst : TopologicalSpace X] (U : X → ↥EulerMeanSolenoidal.L2),
  Continuous U → Continuous fun t => NSFormalization.Section4.D01.orderZeroDatum ⋯
@datumPath : {T : ℝ} → C(↑(Set.Icc 0 T), ↥EulerMeanSolenoidal.L2) → ℝ → NSFormalization.Paper3.RealVectorSobolev 0
@continuousOn_datumPath : ∀ {T : ℝ} (U : C(↑(Set.Icc 0 T), ↥EulerMeanSolenoidal.L2)),
  ContinuousOn (NSFormalization.Section4.A01.datumPath U) (Set.Ico 0 T)
@datumPath_isSobolevDatum : ∀ {T : ℝ} (U : C(↑(Set.Icc 0 T), ↥EulerMeanSolenoidal.L2))
  (v : ℝ × NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space),
  (∀ (t : ℝ) (ht : t ∈ Set.Ico 0 T), (fun x => v (t, x)) =ᵐ[volume] ↑↑(U ⟨t, ⋯⟩)) →
    ContinuousOn (…datumPath U) (Set.Ico 0 T) ∧
      ∀ t ∈ Set.Ico 0 T, NSFormalization.Section4.D01.IsSobolevDatum 0 (fun x => v (t, x)) (…datumPath U t)
```

`continuous_orderZeroDatum` is the `C1b-c8-0` row of `C1B_SPLIT.md:130`
character-for-character (binders, `Continuous U` hypothesis, conclusion).  The
`v : ℝ × Space → Space` of `datumPath_isSobolevDatum` is the contract's
`SpaceTimeField` shape (`Contracts/V1/Data.lean:104` `SpaceTimeField = VelocityField`,
`NavierStokes/ProblemStatement.lean:33` `SpaceTime := ℝ × Space`).

### (a) Is `orderZeroDatumCLM` the same map as D01's `orderZeroDatum`? — **yes, and provably not by tautology**

**Finding 2 (evidence, PASS).**  The claimed equation is **not** definitional, so
`orderZeroDatum_memLp_eq` has real content (`/tmp/rev124/p2_rfl.lean`):

```
example (u : EulerMeanSolenoidal.L2) : orderZeroDatum (Lp.memLp u) = orderZeroDatumCLM u := by rfl
--
error: Tactic `rfl` failed: The left-hand side
  orderZeroDatum ⋯
is not definitionally equal to the right-hand side
  orderZeroDatumCLM u
```

**Finding 3 (evidence, PASS).**  The `Lp.ext` bridge is **exactly** the only
non-`rfl` step — I checked both halves separately
(`/tmp/rev124/p3_rflrest.lean`).  Replacing `componentLp` by `componentCLM`
inside the body of `orderZeroDatum` makes the equation `rfl` (this `example`
compiles; only the second one below errors):

```lean
example (u : EulerMeanSolenoidal.L2) :
    cyclesToAngularRealVector (0:ℝ)
        (WithLp.toLp 2 (fun i => realProjectionTo (0:ℝ) (𝓕 (componentCLM i u))))
      = orderZeroDatumCLM u := rfl            -- ✓ accepted
```

while the single component step is genuinely not definitional:

```
example (u) (i) : componentLp (Lp.memLp u) i = componentCLM i u := by rfl
--
error: Tactic `rfl` failed: The left-hand side
  componentLp ⋯ i
is not definitionally equal to the right-hand side
  (componentCLM i) u
```

So the docstring claim at `DatumPathContinuity.lean:112-115` ("the only non-`rfl`
step is `componentLp_eq_compLpL`; every other factor … matches its bundled
counterpart definitionally") is **exactly right**, in both directions.  The
`fourierCLM`/`restrictScalars`, `realProjectionTo`, `WithLp.toLp` ↔
`(PiLp.continuousLinearEquiv 2 ℝ _).symm` and `cyclesToAngularRealVector`
identifications are all carried by that one `rfl`.

Concrete-`u` check: `/tmp/rev124/p6b_concrete.lean` instantiates the whole chain
at `u₀ = indicatorConstLp 2 measurableSet_ball … (EuclideanSpace.single 0 1)`
and uses the equation to derive a *false-if-tautological* consequence (finding 6).

### (b) Is `datumPath_isSobolevDatum` the `m = 0` case of `ClassicalSolutionR.sobolev`? — **yes, modulo one `Nat.cast_zero`**

The contract field (`verification/Contracts/V1/Data.lean:643-645`, line numbers
re-checked, not copied from an earlier review):

```lean
  sobolev : ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
    ContinuousOn G (Ico (0 : ℝ) T) ∧
      ∀ t ∈ Ico (0 : ℝ) T, IsSobolevDatum (m : ℝ) (fun x => velocity (t, x)) (G t)
```

`Section4/A02/Restrict.lean`'s header points at the single local restatement,
`Section4/A02/SolutionClass.lean:114,133`, whose `sobolev` field is byte-identical
to the above.  Two things had to be checked, and I checked both in
`/tmp/rev124/p4c.lean`:

1. `NSFormalization.Section4.D01.IsSobolevDatum s z A = NSFormalization.Section4.A02.IsSobolevDatum s z A := rfl` — **accepted**.  The A02 restatement (the one the structure field uses) and the D01 predicate the lane proves are definitionally the same.
2. The `Nat` cast is **not** defeq, so the transport is real:

```
example : ((0:ℕ) : ℝ) = (0:ℝ) := rfl
--
error: Type mismatch
  rfl
has type
  ?m.7 = ?m.7
but is expected to have type
  ↑0 = 0
```

With the transport, the contract shape is produced, axiom-clean:

```lean
theorem c8_at_zero {T : ℝ} (U : C(Set.Icc (0:ℝ) T, EulerMeanSolenoidal.L2)) (v : ℝ × Space → Space)
    (hv : ∀ t (ht : t ∈ Set.Ico (0:ℝ) T),
      (fun x => v (t, x)) =ᵐ[volume] ⇑(U ⟨t, Set.Ico_subset_Icc_self ht⟩)) :
    ∃ G : ℝ → RealVectorSobolev (((0:ℕ)) : ℝ),
      ContinuousOn G (Set.Ico (0:ℝ) T) ∧
        ∀ t ∈ Set.Ico (0:ℝ) T,
          NSFormalization.Section4.A02.IsSobolevDatum (((0:ℕ)) : ℝ) (fun x => v (t, x)) (G t) := by
  rw [show ((0:ℕ) : ℝ) = (0:ℝ) from Nat.cast_zero]
  exact ⟨datumPath U, datumPath_isSobolevDatum U v hv⟩
```
```
$ lake env lean /tmp/rev124/p4c.lean
'c8_at_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**No binder or set mismatch.**  `Ico 0 T` on both the `ContinuousOn` and the
`∀ t ∈ …` of the contract; the lane uses `Ico 0 T` in both places; `Icc 0 T` only
appears as the domain of the bundled path `U`, exactly as `exists_local`
(`Source/OrdinaryForcedLocal.lean:32,38`) produces it
(`U : C(Icc 0 T, EulerMeanSolenoidal.L2)`, `0 < T`, `T ≤ S`).  The
`Set.Ico_subset_Icc_self` coercion is the only glue, it appears in the same
place in the hypothesis and in the proof, and `datumPath` is totalised by a
`dite` so `G : ℝ → RealVectorSobolev 0` is a genuine total function as the
contract's `∃ G : ℝ → …` demands.  Neither `restrict`/`Icc` endpoint data nor
`T`-dependence is smuggled in.

**Finding 5 (note, for the next lane).**  `simp only [Nat.cast_zero]` does **not**
do this transport — the type `RealVectorSobolev ((0:ℕ):ℝ)` depends on the cast:

```
$ lake env lean /tmp/rev124/p4b_c8shape.lean
error: `simp` made no progress
```

Only the explicit `rw [show ((0:ℕ):ℝ) = (0:ℝ) from Nat.cast_zero]` works.  Worth
one line in `logs/LESSONS.md` so whoever assembles `ClassicalSolutionR` does not
lose an hour here.

### (c) Non-vacuity — **PASS, stronger than asked**

**Finding 6 (evidence, PASS).**  Rather than just instantiate on a path, I proved
in `/tmp/rev124/p6b_concrete.lean` that **`orderZeroDatumCLM` is injective**, so
it is nowhere near the zero/constant map and the continuity statement has
maximal content.  Route (all inside the probe, 45 lines, standard axioms only):

* `orderZeroDatumCLM w = 0` ⟹ componentwise `realProjectionTo 0 (𝓕 (componentCLM i w)) = 0`
  (`cyclesToAngularRealVector` and `PiLp.continuousLinearEquiv` are `≃L`);
* `𝓕 (componentCLM i w) ∈ realSubspace 0` by `fourier_componentLp_mem`
  (`D01/OrderZeroDatum.lean:89`) rewritten along `componentLp_eq_compLpL`, so
  `realProjection_eq_self` (`Source/RealSobolev.lean:131`) turns the projection
  into the identity and gives `𝓕 (componentCLM i w) = 0`;
* `fourierInv_fourier_eq` ⟹ `componentCLM i w = 0`;
* `ContinuousLinearMap.coeFn_compLpL` + `ae_all_iff` over `Fin 3` ⟹ `w = 0` by `Lp.ext`.

```
'componentCLM_eq_zero_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'orderZeroDatumCLM_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'datum_path_nonconstant' depends on axioms: [propext, Classical.choice, Quot.sound]
'concrete_nonconstant' depends on axioms: [propext, Classical.choice, Quot.sound]
```

with the concrete witness exactly as the brief asked:

```lean
def u0 : EulerMeanSolenoidal.L2 :=
  indicatorConstLp 2 (measurableSet_ball (x := (0:Space)) (ε := 1))
    (measure_ball_lt_top (x := (0:Space)) (r := 1)).ne (EuclideanSpace.single (0:Fin 3) (1:ℝ))
theorem u0_ne_zero : u0 ≠ 0 := …                      -- via norm_indicatorConstLp'
theorem concrete_nonconstant :
    Continuous (fun t : ℝ => orderZeroDatum (Lp.memLp (t • u0))) ∧
      (fun t : ℝ => orderZeroDatum (Lp.memLp (t • u0))) 1
        ≠ (fun t : ℝ => orderZeroDatum (Lp.memLp (t • u0))) 0 := …
```

So the datum path of `t ↦ t • u₀` is continuous **and** takes different values at
`t = 0` and `t = 1`.  This also re-confirms finding 2 from the other side: a
tautological `orderZeroDatum_memLp_eq` could not have produced it.

**Finding 7 (note / opportunity).**  `orderZeroDatumCLM_injective` is 45 lines,
axiom-clean, and is the natural *uniqueness* input for the still-open row
`C1b-unique` (`C1B_SPLIT.md`).  It is also the cheap half of the missing order-0
Plancherel identity (`D01/OrderZeroDatum.lean:40-53`).  Recommend a follow-up
SIMP/D01 lane promote it; the probe text is in `/tmp/rev124/p6b_concrete.lean`
and I have pasted the essential steps above so it is reconstructible.

Negative check on the hypothesis (`/tmp/rev124/p10_neg.lean`, with
`set_option autoImplicit false` per `logs/LESSONS.md`): dropping `hv` and
re-running the same script leaves exactly one hole, at the `congr_field`
argument.  `v` occurs in the conclusion so it cannot be silently re-bound; `hv`
is load-bearing and is the *only* residual assumption.

### (d) Is the hand-off hypothesis the weakest natural one, and is it what B1 will deliver?

**PASS on the table, finding 9 on the tree.**  The hypothesis is on all four axes
exactly what row `C1b-rep` promises (`C1B_SPLIT.md:127`): a.e. (not pointwise),
on `Ico 0 T` (not `Icc`), about `⇑(U t)` (not `ordinaryLift (U t)` / `value 1 (u t)`
— row `C1b-lift0` at `:125` deliberately routes those away as "supplied
upstream"), and about the raw `Lp` coercion, not a smooth representative.  It is
also the weakest form that `IsSobolevDatum.congr_field`
(`Section4/A01/CarrierBridge.lean:79`) can consume, and the lane correctly uses
only the first half of `C1b-rep` (the second half, `velocity (0,·) = a.field`
pointwise, is what discharges `initial`, `Data.lean:636`, and is untouched).

**Finding 9 (note, for whoever briefs B1 — MEDIUM).**  The *existing* "spacetime
velocity ↔ `L²` path" lemmas in the tree all have a **different** shape: they
state pointwise equality against a `SmoothL2Field` path, e.g.
`Source/CompactSlabSobolev.lean:99-102`
(`(hv : ∀ t : s, ∀ x, (U t).field x = v (t, x))`, with
`hU : ∀ n, Continuous (fun t => (U t).jetLp n)`), same at
`Source/InsertionSobolev.lean:25-27` and `Source/PhysicalIntegerSobolev.lean:76-78`.
Converting those to lane 124's `hv` needs `U t = (A t).toLp` plus
`SmoothL2Field.toLp_ae` (`vendor/.../Euler/LpSmoothField.lean:44`) — and
`exists_local` supplies that identification **only at `t = 0`**
(`Source/OrdinaryForcedLocal.lean:41`, `U ⟨0,…⟩ = a.toLp`); no clause identifies
`U t` with any smooth field's `toLp` for `t > 0`.  The only per-slice a.e.
identification in the tree is
`EulerMeanSmoothRepresentative.exists_smooth_representative` /
`representative_ae` (`vendor/.../Euler/MeanSmoothRepresentative.lean:79,92`),
which needs `SmoothOrbit (U t)` — not produced by `exists_local` — and gives no
time-continuity of the representative.  So lane 124's hypothesis is faithful to
the table but B1 will have to *build* it, not inherit it.  This does not affect
this lane; it should be written into the B1 briefing.

---

## 3. Consistency — **PASS**, with one placement note

Imports: the module imports exactly one thing,
`NSFormalization.Section4.A01.CarrierBridge` (lane 119), which already carries
`D01.OrderZeroDatum` + `Euler.MeanSolenoidalSpace` + `Euler.LpSmoothField`.  No
new import was added and none is needed.

Every borrowed object is used from its home, none is restated:

| object | home | how used |
|---|---|---|
| `ContinuousLinearMap.compLpL` | `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean:817` (`def compLpL`, verified) | `componentCLM` body |
| `ContinuousLinearMap.coeFn_compLpL` | same file | the `Lp.ext` bridge |
| `fourierCLM` | `Mathlib/Analysis/Fourier/Notation.lean:167` (`def fourierCLM`, verified) | `.restrictScalars ℝ` in `orderZeroDatumCLM` |
| `realProjectionTo` | `Paper3/RealPositiveDensity.lean:31` (verified) | ditto |
| `PiLp.continuousLinearEquiv` | `Mathlib/Analysis/Normed/Lp/PiLp.lean:1150` `coe_symm_continuousLinearEquiv : ⇑(…).symm = toLp p := rfl` (verified) | ditto — and this `rfl` is what carries the `WithLp.toLp` step of finding 3 |
| `cyclesToAngularRealVector` | `Paper3/AngularRealVectorBochner.lean:15` (verified) | ditto |
| `componentLp`, `componentLp_ae`, `orderZeroDatum`, `fourier_componentLp_mem` | `D01/OrderZeroDatum.lean:72,75,96,89` | imported, not restated |
| `IsSobolevDatum.congr_field`, `isSobolevDatum_zero_ordinaryL2` | `A01/CarrierBridge.lean:79,98` (lane 119) | imported, not restated |

All other docstring citations re-checked against the current files and **correct**:
`Contracts/V1/Data.lean:643`, `D01/OrderZeroDatum.lean:72/96/40-53`,
`Euler/MeanSolenoidalSpace.lean:22`, `Source/OrdinaryForcedLocal.lean:32`,
`Init/Core.lean:1209-1210` (the `@[deprecated dite_eq_left (since := "2026-07-21")]`
attribute on `dif_pos`; ATTEMPTS says `:1210`, which is the theorem line — fine).
No citation drift of the kind `logs/LESSONS.md` warns about.

No duplication with lane 119 or D01: neither `componentCLM` nor
`orderZeroDatumCLM` nor `componentLp_eq_compLpL` exists anywhere else.  Grep over
`formalization/NSFormalization` for `compLpL`/`compLpₗ` finds only
`D01/LerayMultiplier.lean`, `D01/LerayDatum.lean`, `D01/SmoothDatum.lean:100`
(different maps) and this file.

**Finding 8 (note, MAINT — `orderZeroDatumCLM` is a D01 object living in A01).**
`orderZeroDatumCLM` and `componentCLM` mention nothing from A01, nothing from
Euler, and nothing from the carrier bridge: `EulerMeanSolenoidal.L2` is an
`abbrev` for `Lp Space 2 volume` (`Euler/MeanSolenoidalSpace.lean:22`), and the
lane's own committed probe proves the point — `c1b_c8_probe.lean:25` builds the
identical map with domain literally `Lp Space 2 (volume : Measure Space)` and it
works.  Both belong next to `orderZeroDatum` in
`Section4/D01/OrderZeroDatum.lean`; `continuous_orderZeroDatum` would then be a
one-liner there too, and A01 would keep only `datumPath` /
`continuousOn_datumPath` / `datumPath_isSobolevDatum` (the parts that really do
mention the `exists_local` carrier).  I do **not** ask for the move in this lane
— it would put a D01 edit inside an A01 PR.  Log it as MAINT.

Two smaller placement observations, no action needed:

* the inner CLM `Complex.ofRealCLM.comp (EuclideanSpace.proj i)` already has two
  names in the tree — `D01.Pj` (`D01/OrderZeroSymbol.lean:126`) and
  `Source.FourierPhysicalJets.complexComponent` (`:111`) — but **neither is in
  this module's import closure** (`#check NSFormalization.Section4.D01.Pj` →
  `Unknown identifier`), so writing the Mathlib expression inline was the right
  call, not a restatement.  A future SIMP lane could unify the three copies.
* `Source/FourierPhysicalJets.lean:119` has `vectorLpReassembly`, the *reverse*
  assembly `(Fin 3 → Lp ℂ 2) →L[ℝ] Lp Space 2`; not a duplicate.

**Finding 13 (merge order, LOW but act on it).**  Two live lanes collide with
this one on paper, not in Lean:
* lane **125** (`125-D01-finite-order-datum`) also edits `research/A01/C1B_SPLIT.md`,
  appending to row `C1b-m-D` at `:129`, adjacent to the `C1b-c8-0` row this lane
  rewrites at `:130`.  Expect a one-hunk conflict there and nowhere else.
* lane **129** (`129-SIMP-D01-orderzero`) is a simplifier pass over exactly
  `D01/OrderZeroDatum.lean`.  `orderZeroDatum_memLp_eq` ends in `unfold
  orderZeroDatum; rw [key]; rfl`, i.e. it is sensitive to the *shape* of that
  `def`.  Per `logs/LESSONS.md` ("改任何已合陈述的假设时，必须重跑该节点全部
  `axioms_*.lean`"), 129 must re-run `research/A01/axioms_c1b_c8.lean` before
  merging.  Merging 124 first is the cheaper order.

---

## 4. Honesty of `ATTEMPTS_C1B_C8.md` — **PASS, both reproduced verbatim**

**Finding 11 (PASS).**  ATTEMPTS item 2 (`rw` needs `simp only [componentCLM]`
first).  `/tmp/rev124/p7_attempt2.lean` re-runs the proof of
`componentLp_eq_compLpL` with the `simp only [componentCLM]` line deleted:

```
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  ↑↑((ContinuousLinearMap.compLpL 2 volume (Complex.ofRealCLM ∘SL EuclideanSpace.proj i)) u) x
in the target expression
  ↑((↑↑u x).ofLp i) = ↑↑((componentCLM' i) u) x
```

That is the recorded text (`ATTEMPTS_C1B_C8.md:69-71`) verbatim, and the recorded
*cause* ("the goal held `(Ci i) u` (a `def`) not the unfolded `compLpL … u`") is
visible in the goal display.  Correct diagnosis, correct fix.

**Finding 12 (PASS).**  ATTEMPTS item 3 (deprecations).
`/tmp/rev124/p8_depr.lean` restores all four pre-fix spellings:

```
warning: `continuousOn_iff_continuous_restrict` has been deprecated: Use `continuousOn_iff_continuous_domRestrict` instead
warning: `Set.restrict` has been deprecated: Use `Set.domRestrict` instead
warning: `Set.restrict_apply` has been deprecated: Use `Set.domRestrict_apply` instead
warning: `dif_pos` has been deprecated: Use `dite_eq_left` instead
error: `simp` made no progress
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  (Ico 0 T).restrict (datumPath U)
in the target expression
  Continuous ((Ico 0 T).domRestrict (datumPath U))
```

All four replacement names are the ones Lean itself names, i.e. the modern ones,
and `dif_pos {h : Decidable c} (hc : c) … : dite c t e = t hc := dite_eq_left hc`
at `Init/Core.lean:1210` confirms the "same signature" claim in ATTEMPTS.  The
error tail also reproduces the *secondary* point ATTEMPTS records
(`:78-80`): the deprecated `rw` still rewrites the goal into `domRestrict` form,
so a `restrict`-shaped congruence lemma no longer applies — that is why `hEq` had
to be restated.  Nothing in the ATTEMPTS record is embellished; items 1, 4, 5, 6
are consistent with the code as shipped (named `ht` binder at
`DatumPathContinuity.lean:163`; explicit `IsSobolevDatum.congr_field` application
at `:173`; `open NSFormalization.Source.RealSobolev (RealSobolevHilbert)` at `:73`).

---

## 5. For the lead — what remains for row `c8` at `m ≥ 1`

Short answer: **the finite-order constructor is what is missing; the vector
order-`m` Plancherel isometry is not needed for continuity at all, and row
`C1b-c8-m` overstates it.**

**Finding 10 (table correction, MEDIUM — belongs in `C1B_SPLIT.md`, not in code).**
Row `C1b-c8-m` (`C1B_SPLIT.md:131`) lists as an input "the vector order-`m`
Plancherel isometry `‖smoothAngularDatum …‖ = ‖·‖_{Hᵐ}`".  Lane 124 got order-0
continuity with **no norm identity whatsoever** — only the fact that every factor
of `orderZeroDatum` is already a bundled CLM/CLE — and the same is true at order
`m`:

* the order-`m` datum is
  `smoothAngularDatum m s hs A = cyclesToAngularRealVector s (WithLp.toLp 2 (fun i => realProjectionTo s (sobolevOrderLowering m s hs (integerSobolevDatum m (componentField i A)))))`
  (`D01/SmoothDatum.lean:260-266`, with `cyclesComponentDatum` at `:243-258`);
* `sobolevOrderLowering` is a CLM (`Paper3/SobolevOrderLowering.lean:26`),
  `realProjectionTo` is a CLM, `PiLp.continuousLinearEquiv` and
  `cyclesToAngularRealVector` are CLEs — the whole tail bundles exactly as in
  lane 124;
* the one non-CLM factor is `integerSobolevDatum m (componentField i A)`, whose
  argument is a `SmoothL2Field` (a `structure`, not a normed space, so there is
  no CLM to bundle) — **but the tree already has its continuity lemma**:
  `Source/PhysicalIntegerSobolev.lean:61-63`
  `continuous_vectorSobolevDatum (A : K → SmoothL2Field Space) (hA : ∀ j, Continuous (fun t => (A t).jetLp j)) (n : ℕ) : Continuous (fun t => vectorSobolevDatum n (A t))`.

So order-`m` continuity = that lemma + the CLM tail, no isometry.  What it costs
instead is the **hypothesis** `∀ j, Continuous (fun t => (A t).jetLp j)` (all `L²`
jets continuous in time), which `exists_local` supplies only for the *force* path
(`Source/OrdinaryForcedLocal.lean:35`) and never for the velocity — the velocity
comes out as the bare `U : C(Icc 0 T, EulerMeanSolenoidal.L2)` (`:38`).  That is
B1/T1-strength input, i.e. the real order-`m` blocker, and it is a *different*
blocker from the one the row currently names.

**Lane 125's constructor does not hand this over directly.**  Its shipped
induction step is
`isSobolevDatum_raise {s} {z} {A} (hA : IsSobolevDatum s z A) (hg : ∀ i, RaisableWitness (A i)) : IsSobolevDatum (s+1) z (WithLp.toLp 2 (fun i => raiseHilbert (A i) (hg i)))`
(`D01/FiniteOrderDatum.lean:223-229`), and `raiseHilbert` is multiplication by
`sobolevBesselWeight 1 ξ = (1+‖ξ‖²)^{1/2}` (`:130,187`), an **unbounded**
multiplier on `L²`; `RaisableWitness` is precisely the field-dependent `MemLp`
proof that the product lands in `L²`, and the output is `MemLp.toLp` of that
product — a function of `(datum, proof)`, not of a normed-space argument.  So on
the raising route there is **no bounded operator to bundle** and continuity in
`t` would have to be proved by hand (uniform-in-`t` domination), not by the
lane-124 trick.  (It is an explicit `def`, not `Classical.choice`, so that
particular worry does not apply.)  The asymmetry is exactly *lowering is a CLM,
raising is not* — which is why the `smoothAngularDatum` route above (which only
ever lowers) is the one that inherits lane 124's argument.

Recommended edits to `C1B_SPLIT.md` for the next briefing (not this lane's job):

1. row `C1b-c8-m`: replace "needs the vector order-`m` Plancherel isometry" with
   "needs `∀ j, Continuous (fun t => (A t).jetLp j)` for the velocity path
   (B1/T1-strength); the CLM tail and `continuous_vectorSobolevDatum`
   (`Source/PhysicalIntegerSobolev.lean:61`) already exist, no isometry";
2. add the finding-9 caveat to whatever brief B1 gets.

---

## Commands run (all from the lane worktree)

```
. scripts/lean-env.sh ; cd verification ; export LEAN_NUM_THREADS=6
lake build NSFormalization.Section4.A01.DatumPathContinuity            → 0, 9874 jobs
lake env lean ../formalization/.../A01/DatumPathContinuity.lean        → 0, silent
lake env lean ../research/A01/axioms_c1b_c8.lean                       → 0, 8× standard axioms
lake env lean ../research/A01/probes/c1b_c8_probe.lean                 → 0, 5 #checks only
make check / make test / make test-mutations                           → 0 / 0 / 0
lake env lean /tmp/rev124/p1_checks.lean    (pp.fullNames signatures)  → 0
lake env lean /tmp/rev124/p2_rfl.lean       (whole eq is NOT rfl)      → 1, quoted
lake env lean /tmp/rev124/p3_rflrest.lean   (rest IS rfl; step is NOT) → 1, quoted
lake env lean /tmp/rev124/p4b_c8shape.lean  (simp only fails)          → 1, quoted
lake env lean /tmp/rev124/p4c.lean          (c8 shape at m=0)          → 0, standard axioms
lake env lean /tmp/rev124/p6b_concrete.lean (injectivity + concrete)   → 0, standard axioms
lake env lean /tmp/rev124/p7_attempt2.lean  (ATTEMPTS item 2)          → 1, quoted
lake env lean /tmp/rev124/p8_depr.lean      (ATTEMPTS item 3)          → 1, quoted
lake env lean /tmp/rev124/p10_neg.lean      (drop hv, autoImplicit off)→ single hole at congr_field
```
