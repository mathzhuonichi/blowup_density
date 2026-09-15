# D01 force-class closure: `F_R + C_c^∞(R³×(0,∞)) ⊆ F_R`

Lane 028, task **D01**. Target: the obligation `research/section4/STATEMENTS.md:270`
("`⟪D01:Cc_infty⟫` on `R³ × (0,∞)` and the fact that `F_R + C_c^∞(R³×(0,∞)) ⊆ F_R`"), i.e.
the sentence `paper/sections/04-whole-space.tex:51` that Theorem 4.2 (`thm:Rinsert`,
`04-whole-space.tex:31`) uses to put `g_ε = g + H_ε + F_ε` (`:48`) in `F_R` (`:33`).
`cor:Rclasses` uses the same closure at `:198`.

Deliverable: `formalization/NSFormalization/Section4/D01/ForceClass.lean` (435 lines, no
`sorry`, no `axiom`, no `native_decide`; all 23 theorems have axiom set exactly
`propext, Classical.choice, Quot.sound`).

Consumers who asked for it: `research/R42/COMPARISON.md` §4.3 and
`research/R42/ATTEMPTS.md` §5 (lane 027) — "`Section4/I03/Angular.lean` builds the path and
its `MemLp`, but not its time regularity, and there is no additivity lemma for
`IsSobolevPath`"; `research/B01/REVIEW.md` issue 3 and its reuse table line 64 (lane 018) —
"no `ContDiff` for `realCompactSobolevTimeSlice` / `realVectorSlice` /
`angularRealVectorSlice`".

---

## 1. What is proved

All four goals of the task card are done. `Data.*` line numbers are
`verification/Contracts/V1/Data.lean`.

### Goal 1 — `F_c ⊆ F_R`

| declaration | statement |
|---|---|
| `contDiff_realCompactSobolevTimeSlice` (`:107`) | the real-subspace cycles trajectory of a compact smooth scalar is `ContDiff ℝ ∞` in time |
| `contDiff_realVectorSlice` (`:114`) | same for the Euclidean three-vector (`PiLp 2`) trajectory |
| `contDiff_angularRealVectorSlice` (`:122`) | same after the cycles→angular convention change |
| `contDiff_angularPath` (`:133`) | **the missing ingredient**: `ContDiff ℝ ∞ (I03.angularPath s F hF hc)`, on all of `ℝ` |
| `memForceR_of_memForceCompact` (`:189`) | `Data.MemForceCompact f → Data.MemForceR f` |

### Goal 2 — additivity

| declaration | statement |
|---|---|
| `SchwartzPairable` (`:207`) | `∀ i ψ, Integrable (fun x => ψ x * (z x i : ℂ))` — the side condition the Bochner integral needs |
| `memLp_component_of_isSobolevDatum` (`:241`) | a **continuous** field with a datum at order `s ≥ 0` has `MemLp (fun x => (z x i : ℂ)) 2 volume` |
| `schwartzPairable_of_isSobolevDatum` (`:250`) | hence it is Schwartz-pairable |
| `isSobolevDatum_add` (`:261`) | `IsSobolevDatum s z A → IsSobolevDatum s w B → IsSobolevDatum s (z+w) (A+B)` under pairability of both |
| `isSobolevDatum_unique` (`:286`) | the datum is unique (`Data.lean:145`, unit L1), by `Paper3.angularRealization_injective` |
| `contDiff_futureSlice` (`:301`) | `ContDiffOn ℝ ∞ f futureDomain → 0 ≤ t → ContDiff ℝ ∞ (fun x => f (t,x))`, including at `t = 0` |
| `schwartzPairable_slice_of_memForceR` (`:309`) | every `t ≥ 0` slice of an `F_R` force is Schwartz-pairable |
| `isSobolevPath_add` (`:320`) | **additivity of `Data.IsSobolevPath`**, exactly the shape `research/R42/COMPARISON.md` §4.3 asks for |
| `memForceR_add` (`:330`) | `Data.MemForceR f → Data.MemForceR g → Data.MemForceR (f + g)` — **no side hypothesis** |
| `memForceR_add_compact` (`:344`) | `Data.MemForceR g → Data.MemForceCompact h → Data.MemForceR (g + h)` |

### Goal 3 — the inserted force

| declaration | statement |
|---|---|
| `memForceR_of_eq` (`:394`) | pointwise equality transports `MemForceR` |
| `memForceR_of_compact_difference` (`:401`) | `MemForceR g → MemForceCompact (fun z => gε z - g z) → MemForceR gε` |
| `memForceR_of_force_formula` (`:428`) | `MemForceR g → MemForceCompact H → MemForceCompact F → (∀ z, gε z = g z + H z + F z) → MemForceR gε` |

These are the two shapes `Contracts.V1.InsertionFamily` (lane 027) offers: the field
`forceDifference_compact : ∀ ε ∈ Ioc 0 ε₀, Data.MemForceCompact (fun z => force ε z - g z)`
feeds the first, the field `force_formula : ∀ ε z, force ε z = g z + forceCorrection ε z +
scaling.F ε z` feeds the second. Both are stated over contract-level facts only, so the
binding module in `verification/Bindings/` can apply them without `formalization/` seeing
`Contracts.*`. `memForceCompact_of_smooth_support` (`:352`) builds a `MemForceCompact` from
the three fields `CorrectionAPI.force_smooth` / `force_compactSupport` / `force_positive_time`
(`Contracts/V1/Correction.lean:426,429,440`) for callers that prefer that route.

**The two routes are not equally available today.** Route 2 additionally needs
`MemForceCompact (ScalingAPI.F ε)`, and `ScalingAPI.F ε = scaledForce P.force x₀ T ε =
dilateField ((ε⁻¹)^3) ((ε⁻¹)^2) ε⁻¹ (T-ε²) x₀ P.force` (`Contracts/V1/Scaling.lean:115,448`),
whereas `PacketAPI.force_smooth` / `force_support` (`Contracts/V1/Packet.lean:209,214`) are
stated for the **unscaled** packet force and nothing transports them through `dilateField`. So
**route 1 (`forceDifference_compact`) is the one R42 can discharge today** — it is a direct
contract field needing nothing extra. Route 2 becomes usable once a
`MemForceCompact (scaledForce …)` lemma exists; that is a small follow-up, not a blocker.

### Goal 4 — `F_c` closure and `AgreesOnFuture`

| declaration | statement |
|---|---|
| `memForceCompact_add` (`:358`) | `F_c` is closed under addition |
| `memForceR_congr` (`:369`), `memForceR_of_agreesOnFuture` (`:380`) | `F_R` is extensional for `Data.AgreesOnFuture` (`Data.lean:128`), in both directions |

---

## 2. Route, and the two things that were actually missing

### 2.1 Time regularity (the `ContDiffOn ℝ ∞ G futureTimes` clause, `Data.lean:548`)

`Paper3.contDiff_compactSobolevTimeSlice` (`Paper3/CompactSobolevTime.lean:18`) already has
genuine Banach-valued `C^∞` for the **scalar complex cycles** trajectory. The chain from there
to `I03.angularPath` is three maps, all of them already in the tree and all of them bounded
linear, so nothing analytic is added:

```
compactSobolevTimeSlice  --realProjectionTo (CLM, RealPositiveDensity.lean:21)-->
realCompactSobolevTimeSlice  --PiLp 2 assembly (contDiff_piLp)-->
realVectorSlice  --cyclesToAngularRealVector (CLE, AngularRealVectorBochner.lean:15)-->
angularRealVectorSlice = I03.angularPath
```

Each step is one `ContinuousLinearMap.contDiff.comp` (or `(contDiff_piLp 2).mpr`). Total: four
one-line theorems. This is exactly the transport `research/B01/COMPARISON.md` unit 5 and
`research/B01/REVIEW.md` issue 3 record as absent.

`Paper3.contDiff_compactVectorFourierLp` (`Paper3/CompactForceAdmissibility.lean:14`) was **not**
reused: it is the *complex* `compactVectorFourierLp` (cycles, no reality constraint), and
`Data.MemForceR` wants the real-subspace angular carrier. Redoing the `PiLp` step on
`realVectorSlice` is two lines, whereas relating the two vector carriers is not.

### 2.2 Additivity of `IsSobolevPath` (`Data.lean:174`)

`Data.IsSobolevDatum s z A` is
`∀ i ψ, angularRealization s (A i) ψ = ∫ x, ψ x * (z x i : ℂ)`. The left side is additive for
free (`Paper3.angularRealization` is a `→L[ℂ]`, `Paper3/AngularFourierDilation.lean:176`). The
right side is a **Bochner** integral, which Mathlib totalizes to `0` on a non-integrable
integrand, so `∫ ψ·(z+w) = ∫ ψ·z + ∫ ψ·w` is *false in general* and `integral_add` demands
both pairings integrable. This is not a Lean artefact of the formalization: it is the
"totalization caveat" the contract itself records at `Data.lean:148-155`, which also names the
repair — "the `m = 0` clause of `MemForceR` put the slice in `L²`, where Schwartz times `L²` is
`L¹`".

Turning that sentence into a proof needs *datum ⟹ physical `L²`*, i.e. the `⟹` half of
`RECONCILIATION.md` unit L2. Lane 025's `Section4/D01/DatumToJets.lean`
(`memLp_of_isSobolevDatum`) has it, but it was in review in a separate worktree and cross-
worktree imports are forbidden. Only the **order-zero scalar** case is needed here, and it is
much smaller than the general jet statement:

* `cyclesComponent` (`:221`) = `(cyclesToAngular s).symm (A i)`, using
  `Paper3.cyclesToAngular` (`Paper3/AngularTameProduct.lean:11`);
* `compactRep_cyclesComponent` (`:227`) — `IsSobolevDatum` pairs against *every* Schwartz test,
  which is more than `Source.FourierPhysicalJets.CompactRep` (`:14`) asks; the realizations
  agree by `Paper3.angularRealization_eq_cycles` (`AngularTameProduct.lean:30`);
* `memLp_component_of_isSobolevDatum` (`:241`) — `FourierPhysicalJets.physicalLp_ae` (`:28`),
  the **scalar** order-zero inversion, which needs only `Continuous f`, not `ContDiff`.

This is 25 lines against lane 025's `physicalJetLp` tensor-reassembly route (needed only for
`j ≥ 1`). Attribution is in the module docstring: when `DatumToJets` lands, §4 of `ForceClass`
can be deleted in favour of its `memLp_of_isSobolevDatum`. **The names do not collide** —
lane 025 uses `cyclesComponentOfAngular`, `loweredComponent`, `jetOfDatum`,
`memLp_of_isSobolevDatum`; this module uses `cyclesComponent`, `compactRep_cyclesComponent`,
`memLp_component_of_isSobolevDatum`. Checked mechanically by diffing the two declaration lists:
the only clash found was `contDiff_slice` (lane 025 `DatumToJets.lean:366`, on
`Ico 0 T ×ˢ univ`), and this module's version was renamed `contDiff_futureSlice` (on
`futureDomain`) because of it. Both modules live in `NSFormalization.Section4.D01`, so a third
module may import both.

Consequence worth recording: `memForceR_add` needs **no** hypothesis beyond `MemForceR` on both
summands, because pairability of each slice is derived from the class's own `m = 0` datum plus
`ContDiffOn ℝ ∞ f futureDomain`. The extra smoothness clause that `REVIEW_A` issue 1 forced
into `MemForceR` (`Data.lean:521-527`) is load-bearing a second time here: without it the
slices need not be continuous and `physicalLp_ae` would not apply.

---

## 3. Rejected routes

1. **Take `SchwartzPairable` (or `∀ t ≥ 0, MemLp (fun x => f (t,x)) 2 volume`) as a hypothesis
   of `memForceR_add`.** This was the first plan and it works, but it pushes a *second*,
   independent obligation onto R42 that no contract field supplies. To be precise about what
   R42 does and does not have: `Data.ClassicalSolutionR` (`Data.lean:624`) has **no force-class
   field**, and neither does `InsertionFamilyAPI` — `g ∈ F_R` (`04-whole-space.tex:32`) cannot
   be projected out of `reference`, and R42 must add it as a hypothesis or as a new contract
   field. So `MemForceR g` is already an assumption on R42's side; adding `SchwartzPairable g`
   on top would be a further assumption with no contract behind it either, and one the
   manuscript never states. Replaced by §2.2, which derives pairability from `MemForceR` itself,
   so R42's single added hypothesis suffices. The hypothesized form survives as
   `isSobolevDatum_add` / `isSobolevPath_add`, which still take pairability explicitly, since
   they are stated at arbitrary real order where no `MemForceR` is available.
2. **Try to make additivity formal, without integrability.** Considered and rejected: if
   `ψ·z` is non-integrable and `ψ·w` is integrable (the compact case), then `ψ·(z+w)` is
   non-integrable, so `∫ψ·(z+w) = 0` while `∫ψ·z + ∫ψ·w = ∫ψ·w`, which is nonzero in general.
   There is no `integral_add` variant with one-sided integrability that would help.
3. **Strengthen `Data.MemForceR` (a V2 contract) to carry the physical `L²` slice.** Rejected:
   `Contracts/V1/*` is frozen, and `MemForceR` is the universally quantified reference force of
   Theorem 4.1(i), so strengthening it weakens that theorem — the same argument `Data.lean:124`
   makes against strengthening it with a zero-extension.
4. **Reuse `Paper3.compact_vector_force_sobolev_regular`
   (`Paper3/CompactForceAdmissibility.lean:52`) for goal 1.** It is literally the `MemForceR`
   shape (`ContDiff` + `MemLp 1` + `MemLp 2` for every integer order), but at the
   *complex cycles* carrier `compactVectorFourierLp`, on `volume` rather than
   `positiveTimeMeasure`, and with no `IsSobolevPath` pairing. Reaching `Data.MemForceR` from it
   still requires the real projection, the convention change and the pairing — i.e. the whole of
   §2.1 plus `I03.angularPath_pairing`. Building directly on `I03.angularPath`, which already
   has the pairing and the `MemLp` on `positiveTimeMeasure`, is strictly shorter.
5. **`MemForceCompact.neg` / `.sub`.** Started, then dropped: Mathlib's `HasCompactSupport.neg`
   did not resolve under dot notation at this pin (`hf.2.1.neg'` looks for `Function.neg'`
   because `HasCompactSupport` unfolds to `IsCompact (tsupport f)`), and nothing in the four
   goals needs them — the contract *hands* `MemForceCompact (fun z => gε z - g z)`, it does not
   ask for it to be produced. `memForceCompact_add` is kept because goal 4 names it.

## 4. Failed attempts and Lean frictions (all fixed)

* `tsupport (f + g) ⊆ tsupport f ∪ tsupport g`: after `closure_mono (Function.support_add f g)`
  and `rw [closure_union]` the goal is syntactically `closure (support f) ∪ closure (support g)
  ⊆ tsupport f ∪ tsupport g`, which `rw` does not close because `tsupport` is a `def`, not a
  notation. `exact subset_rfl`.
* `gε z = g z + (gε z - g z)` fails with `ring`: `Space = EuclideanSpace ℝ (Fin 3)` is an
  additive group, not a ring. `abel`.
* `(z + w) x i` needs `PiLp.add_apply` explicitly (`WithLp` is not a bare type synonym at this
  pin); `((A + B) i : FourierData) = (A i) + (B i)` for
  `A B : RealVectorSobolev s = Product (Fin 3) (RealSobolevHilbert s)` *is* `rfl`, submodule
  coercion included.
* The `t = 0` slice: `ContDiffOn ℝ ∞ f (Ici 0 ×ˢ univ)` does give `ContDiff ℝ ∞ (fun x => f (0,x))`,
  via `ContDiffOn.comp_contDiff` (`Mathlib/Analysis/Calculus/ContDiff/Comp.lean:145`) with
  `x ↦ (0,x)`, whose range lies in the set. No one-sided-derivative special case was needed.
  This matters because `IsSobolevPath` demands a datum at *every* `t ≥ 0`, `t = 0` included
  (`Data.lean:166-173`).

## 5. Hypotheses carried, and remaining gaps

* **No hypothesis** beyond the contract predicates in `memForceR_add`,
  `memForceR_add_compact`, `memForceR_of_memForceCompact`, `memForceCompact_add`,
  `memForceR_congr`.
* `isSobolevDatum_add` and `isSobolevPath_add` carry `SchwartzPairable` explicitly, because at a
  general real order `s` there is no class to derive it from. Every `MemForceR` caller gets it
  free from `schwartzPairable_slice_of_memForceR`.
* `memLp_component_of_isSobolevDatum` needs `0 ≤ s` (it lowers to order `0` through
  `FourierPhysicalJets.physicalLp`). Integer orders `m : ℕ`, which is all `MemForceR` uses, are
  fine.

Gaps this module does **not** close:

1. **`Data.ClassicalSolutionR ν a g_ε T`** — the other half of `research/R42/COMPARISON.md`
   §4.3. Its `sobolev` field wants a *continuous* order-`m` datum path for `u_ε` on `Ico 0 T`,
   not a force path on `[0,∞)`; `u_ε = v + w_ε + U_ε` is not compactly supported, so
   `I03.angularPath` does not apply to it and §2.1 does not transport. It needs the datum path
   of a non-compact smooth field with `L²` jets — that is `SmoothDatum.smoothAngularDatum` at
   each time, plus a continuity-in-time statement that does not exist. Not attempted.
2. **`F_R ⊆ F_rd` / `F_c ⊆ F_rd`** (`04-whole-space.tex:186-191`, `cor:Rclasses`): `MemForceRapid`
   is untouched here. `research/B01/COMPARISON.md` optional follow-up C.
3. **Norms.** Nothing in this module says anything quantitative:
   `Data.forceSobolevENorm q s (f + g) ≤ …` is not proved, and the triangle inequality for that
   infimum is not formal either (it needs the same pairability argument plus
   `eLpNorm_add_le`). `04-whole-space.tex:51` only needs membership, so this was out of scope;
   `R46`/`B01` will want it.
4. **`AgreesOnFuture` for `F_c`.** `MemForceCompact` is *not* `AgreesOnFuture`-invariant (it
   constrains `t < 0`, where it forces `f = 0`), so no congruence lemma is stated for it. This
   is a property of the contract, not a gap.

---

## 6. Verification

Environment: `bash scripts/lean-install.sh`, then `. scripts/lean-env.sh`,
`LEAN_NUM_THREADS=6`, Lake run from `verification/`.

| command | result |
|---|---|
| `lake build Contracts.V1.Data NSFormalization.Section4.D01.SmoothDatum NSFormalization.Section4.I03.Angular NSFormalization.Paper3.AngularRealVectorBochner` | OK (9876 jobs, 5m10s cold) |
| `lake build NSFormalization.Section4.D01.ForceClass` | OK (9877 jobs) |
| `make check` | exit 0 (plan check, contract check, 13 policy tests, work-queue check) |
| `python3 experiments/build_changed_lean.py --base-ref erenup/integration --dry-run` | `Changed Lean modules: NSFormalization.Section4.D01.ForceClass` — the single module, built above.  (Against `--base-ref main` the command additionally lists the 38 modules already committed on the branch; `targets()` applied to the working-tree path `formalization/NSFormalization/Section4/D01/ForceClass.lean` gives the same single module either way.) |

Scratch (`verification/Bindings/ScratchD01ForceClass.lean`, built OK, **deleted**; the olean
was removed too). Definitional agreement with the contract, all by `rfl` / `Iff.rfl`:

```lean
example : (futureTimes : Set ℝ) = Data.futureTimes := rfl
example : (forceTimeMeasure : Measure ℝ) = Data.forceTimeMeasure := rfl
example (s) (z : Data.SpatialField) (A) : IsSobolevDatum s z A ↔ Data.IsSobolevDatum s z A := Iff.rfl
example (s) (f : Data.SpaceTimeField) (G) : IsSobolevPath s f G ↔ Data.IsSobolevPath s f G := Iff.rfl
example (f : Data.SpaceTimeField) : MemForceR f ↔ Data.MemForceR f := Iff.rfl
example (f : Data.SpaceTimeField) : MemForceCompact f ↔ Data.MemForceCompact f := Iff.rfl
example (f g : Data.SpaceTimeField) : AgreesOnFuture f g ↔ Data.AgreesOnFuture f g := Iff.rfl
```

and the contract-level statements discharged by the new lemmas with a bare term, which is the
real test that a binding module will work:

```lean
example {f} (h : Data.MemForceCompact f) : Data.MemForceR f := memForceR_of_memForceCompact h
example {f g} (hf : Data.MemForceR f) (hg : Data.MemForceR g) : Data.MemForceR (f + g) :=
  memForceR_add hf hg
example {g h} (hg : Data.MemForceR g) (hh : Data.MemForceCompact h) : Data.MemForceR (g + h) :=
  memForceR_add_compact hg hh
example {f g} (hf : Data.MemForceCompact f) (hg : Data.MemForceCompact g) :
    Data.MemForceCompact (f + g) := memForceCompact_add hf hg
example {g gε} (hg : Data.MemForceR g) (hd : Data.MemForceCompact (fun z => gε z - g z)) :
    Data.MemForceR gε := memForceR_of_compact_difference hg hd
example {g H F gε} (hg : Data.MemForceR g) (hH : Data.MemForceCompact H)
    (hF : Data.MemForceCompact F) (hform : ∀ z, gε z = g z + H z + F z) : Data.MemForceR gε :=
  memForceR_of_force_formula hg hH hF hform
example (f) (h : Data.MemForceCompact f) : f ∈ Data.forceClassR := memForceR_of_memForceCompact h
```

`#print axioms` on all 23 theorems of the module
(`contDiff_realCompactSobolevTimeSlice`, `contDiff_realVectorSlice`,
`contDiff_angularRealVectorSlice`, `contDiff_angularPath`, `memForceR_of_memForceCompact`,
`schwartzPairable_of_memLp`, `compactRep_cyclesComponent`,
`memLp_component_of_isSobolevDatum`, `schwartzPairable_of_isSobolevDatum`,
`isSobolevDatum_add`, `isSobolevDatum_unique`, `contDiff_futureSlice`,
`schwartzPairable_slice_of_memForceR`, `isSobolevPath_add`, `memForceR_add`,
`memForceR_add_compact`, `memForceCompact_of_smooth_support`, `memForceCompact_add`,
`memForceR_congr`, `memForceR_of_agreesOnFuture`, `memForceR_of_eq`,
`memForceR_of_compact_difference`, `memForceR_of_force_formula`):
every one is `[propext, Classical.choice, Quot.sound]`.
