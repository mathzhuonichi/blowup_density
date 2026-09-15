# Review — lane 080 (R42 split item #2a, `blowup_essSup`)

Commit under review: `77f3b9a`.  Reviewer ran every command below in the lane
worktree `.claude/worktrees/080-R42-blowup-esssup`; scratch checks were written to
`/tmp`, nothing in the lane was modified.

## Verdict: **ACCEPT-WITH-NOTES**

The mathematics is right, the module compiles warning-free, the axiom footprint is
clean, and — the point that matters most — the conclusion of
`limsupLeft_speedENorm_eq_top` is *literally* the blow-up hypothesis that
`Contracts/V1/MaximalPartial.lean:223` `lifespan_le_of_unbounded` consumes, with no
glue lemma needed (verified, finding 0).  One substantive cleanup (finding 1) should
be applied before merge: the `SpeedUnboundedAt` restatement is a **second** local
copy of a predicate that already exists, already bridged, and is already reachable
without adding an import.

---

## Findings

### 0. (info, PASS) The conclusion is exactly the consumer's hypothesis

`Contracts/V1/MaximalPartial.lean:223` wants

```
limsupLeft T (fun t => speedENorm (fun x : Space => u (t, x))) = ⊤
```

with `u : SpaceTimeField` and the *contract's* `limsupLeft` / `speedENorm`.  The lane
proves it with `A02.limsupLeft` / `A02.speedENorm` and `u : ℝ × Space → Space`.  These
line up by `rfl` through `Bindings/MaximalPartial.lean:57,61`.  Verified by compiling
(`/tmp/r42b.lean`, no errors):

```lean
example {T : ℝ} {u : BlowupDensity.Contracts.V1.Data.SpaceTimeField} (hT : 0 < T)
    (hblow : BlowupDensity.Contracts.V1.SpeedUnboundedAt T u)
    (hcont : ∀ t ∈ Ioo (0:ℝ) T, Continuous (fun x => u (t, x))) :
    BlowupDensity.Contracts.V1.MaximalPartial.limsupLeft T
        (fun t => BlowupDensity.Contracts.V1.MaximalPartial.speedENorm
          (fun x : Space => u (t, x))) = ⊤ :=
  NSFormalization.Section4.R42.limsupLeft_speedENorm_eq_top hT hblow hcont
```

It typechecks as written — contract predicate in, contract conclusion out, no
rewriting.  This is the strongest evidence the lane delivered the right object.

`pp.fullNames` shapes, for the record:

```
@NSFormalization.Section4.R42.limsupLeft_speedENorm_eq_top :
  ∀ {T : ℝ} {u : ℝ × NavierStokes.ProblemStatement.Space → NavierStokes.ProblemStatement.Space},
    0 < T → NSFormalization.Section4.R42.SpeedUnboundedAt T u →
      (∀ t ∈ Set.Ioo 0 T, Continuous fun x => u (t, x)) →
        (NSFormalization.Section4.A02.limsupLeft T fun t =>
           NSFormalization.Section4.A02.speedENorm fun x => u (t, x)) = ∞

BlowupDensity.Contracts.V1.MaximalPartial.limsupLeft : ℝ → (ℝ → ℝ≥0∞) → ℝ≥0∞
BlowupDensity.Contracts.V1.MaximalPartial.speedENorm : BlowupDensity.Contracts.V1.Data.SpatialField → ℝ≥0∞
NSFormalization.Section4.A02.limsupLeft : ℝ → (ℝ → ℝ≥0∞) → ℝ≥0∞
NSFormalization.Section4.A02.speedENorm : NSFormalization.Section4.A02.SpatialField → ℝ≥0∞
```

### 1. (**major**, `BlowupEssSup.lean:54`) The `SpeedUnboundedAt` restatement is a duplicate — delete it

`NSFormalization.Source.PacketScaling.SpeedUnboundedAt`
(`formalization/NSFormalization/Source/PacketScaling.lean:22`) is the pre-existing
canonical local copy.  Three facts, each checked:

* **Character-identical.**  `diff <(sed -n '22,24p' Source/PacketScaling.lean)
  <(sed -n '54,56p' Section4/R42/BlowupEssSup.lean)` → empty.  Also `rfl`-defeq
  (`example (T u) : PacketScaling.SpeedUnboundedAt T u = R42.SpeedUnboundedAt T u := rfl`
  compiles).
* **Already reachable with no new import.**  A file whose only import is
  `NSFormalization.Section4.A02.Patch` — exactly the lane module's import line —
  resolves `#check @NSFormalization.Source.PacketScaling.SpeedUnboundedAt`
  successfully (`/tmp/r42e.lean`).  So dropping the `def` costs *nothing*; the module
  can add `open NSFormalization.Source.PacketScaling` or use the qualified name.
* **Already bridged.**  `verification/Bindings/Scaling.lean:50` carries
  `Contracts.V1.SpeedUnboundedAt T u = PacketScaling.SpeedUnboundedAt T u := rfl`,
  and the contract's own docstring (`Contracts/V1/Scaling.lean:118-123`) names
  PacketScaling as the implementation it mirrors.

This violates the repo rule "本地重述只允许一份" (CLAUDE.md, contract-import section).
The concrete harm is a **silent shadow**: `Assembly.lean:40` opens the same namespace
`NSFormalization.Section4.R42` and `Assembly.lean:43` does
`open NSFormalization.Source NSFormalization.Source.PacketScaling`.  Reproduced
(`/tmp/r42f.lean`, `/tmp/r42g.lean`): with the lane module imported, a bare
`SpeedUnboundedAt` inside `namespace NSFormalization.Section4.R42` resolves to
`NSFormalization.Section4.R42.SpeedUnboundedAt` — no ambiguity error, the opened
PacketScaling name is simply shadowed.  Harmless today (they are defeq), but if the
contract ever gets a V2, `Bindings/Scaling.lean:50` would catch the PacketScaling
copy while the unbridged R42 copy drifts unnoticed.  That is precisely the failure
mode the bridge policy exists to prevent.

**Fix (one line each):** delete `BlowupEssSup.lean:47-56` (docstring + `def`), add
`open NSFormalization.Source.PacketScaling` to the `open` block at line 41, and
shorten the module docstring paragraph at lines 31-34.  Then **no new bridge is
needed at all** — `Bindings/Scaling.lean:50` already covers it.

*Root cause, for the record:* `ATTEMPTS_BLOWUP.md` says "no local copy existed in
`Section4/{I03,R42,A02}`; grep confirmed only a comment mention in
`Section4/R42/Lifespan.lean`".  Literally true, but the grep was scoped to `Section4/`
and missed `Source/`, where the contract docstring points.

### 2. (minor, `BlowupEssSup.lean:109`) `_hT : 0 < T` should be dropped

It is unused in the proof, and it is **not** required by the consumer's interface:
`lifespan_le_of_unbounded` carries its own `0 < T` at its own boundary, so the caller
gains nothing by also feeding it here.  Stronger — `0 < T` is *derivable* from
`hblow`, since `SpeedUnboundedAt` asserts `∃ t ∈ Ioo 0 T`.  Compiled
(`/tmp/r42b.lean`):

```lean
example {T : ℝ} {u : VelocityField} (hblow : R42.SpeedUnboundedAt T u) : 0 < T := by
  obtain ⟨t, x, ht, _, _⟩ := hblow 1 one_pos 1 one_pos
  exact ht.1.trans ht.2
```

Dropping the binder makes the lemma strictly easier to apply and removes an
`_`-prefixed placeholder from a public signature.  Lead decides; the ATTEMPTS note
("kept in the signature (interface: the A02 consumer supplies it)") is the only
argument for keeping it, and finding 0's `example` shows the consumer does not need
it.  **Recommend: drop.**

### 3. (info, PASS) `hcont` *is* obtainable from `InsertionFamilyAPI.velocity_smooth`

`velocity_smooth` (`Contracts/V1/InsertionFamily.lean:196`) gives
`ContDiffOn ℝ ∞ (velocity ε) (Ico 0 T ×ˢ univ)`.  Full `Continuous (fun x => u (t,x))`
for `t ∈ Ioo 0 T` follows because `Ioo 0 T ×ˢ univ` is an *open* subset of the domain,
so `ContinuousOn` upgrades to `ContinuousAt` there.  Compiled in full (`/tmp/r42b.lean`,
~9 lines): `.continuousOn` → `.mono` onto the open box → `ContinuousOn.continuousAt`
with `IsOpen.mem_nhds` → compose with `y ↦ (t, y)` (`fun_prop`).

The lane's choice of `Ioo` (not `Ico`) is the right one and deliberate: at `t = 0` the
point sits on the boundary of `Ico 0 T ×ˢ univ` and only `ContinuousWithinAt` is
available.  **Note for the assembly lane:** this ~9-line helper is *not* in the lane
and will have to be written there (ATTEMPTS correctly declares it an input, "Gap"
section).

### 4. (info, PASS) Lemma 1 cannot be satisfied by a degenerate measure

`volume : Measure Space` with `Space = EuclideanSpace ℝ (Fin 3)` is the honest
Lebesgue measure, not a trivial instance.  All compiled (`/tmp/r42d.lean`):

```lean
example : Measure.IsAddHaarMeasure (volume : Measure Space) := by infer_instance
example : Measure.IsOpenPosMeasure (volume : Measure Space) := by infer_instance
example : volume (ball (0 : Space) 1) ≠ 0 := (measure_ball_pos volume 0 one_pos).ne'
example : volume (ball (0 : Space) 1) ≠ ⊤ := measure_ball_lt_top.ne
example : volume ({0} : Set Space) = 0 := measure_singleton 0
```

Haar + balls of positive *finite* mass + null singletons rules out the zero measure,
a Dirac mass, and a counting/`⊤`-everywhere measure.  `ofReal_le_eLpNormTop_of_continuous`
is a real statement about the real `L^∞` norm.

### 5. (nit, `research/R42/axioms_blowup.lean:7`) Comment is factually wrong

"(`SpeedUnboundedAt` is a `def`; it depends on no axioms.)"  It actually prints
`[propext, Classical.choice, Quot.sound]` (inherited through the `EuclideanSpace` /
norm instances).  `ATTEMPTS_BLOWUP.md`'s "Commands / results" section is correct;
only this draft comment is wrong.  Cosmetic.

### 6. (info, PASS) ATTEMPTS is honest

All four cited claims checked against this Mathlib rev:

| claim | verified |
|---|---|
| `nhdsLT_basis` at `Topology/Order/LeftRightNhds.lean:234`, `[NoMinOrder α] (a : α) : (𝓝[<] a).HasBasis (· < a) (Ioo · a)` | exact, line and signature |
| `ae_lt_of_essSup_lt` at `MeasureTheory/Function/EssSup.lean:248`, side goal by `isBoundedDefault` autoparam | exact |
| `le_limsup_of_frequently_le'` at `Order/LiminfLimsup.lean:517`, `[CompleteLattice β]`, no cobounded side condition | exact |
| deprecation `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` | real: `Mathlib/Data/Set/Operations.lean:81`, `@[deprecated (since := "2026-07-09")] alias mem_setOf_eq := mem_ofPred_eq` |

The recorded `zero_le` failure was **reproduced verbatim** (`/tmp/r42h.lean`, same
`open` set as the module):

```
error: Function expected at
  zero_le
but this term has type
  0 ≤ ?m.22
```

Also confirmed negative: `nhdsWithin_Iio_basis'`, `Filter.HasBasis.nhdsWithin_Iio`,
`Filter.limsup_eq_top_iff`, `ENNReal.limsup_eq_top_iff` — none present under those
names.  ATTEMPTS' failure log is accurate.

---

## Commands and results

All from the lane worktree, after `bash scripts/lean-install.sh` (idempotent, `== OK`),
`. scripts/lean-env.sh`, `export LEAN_NUM_THREADS=6`; lake run only from `verification/`,
one process at a time.

| command | result |
|---|---|
| `cd verification && lake build NSFormalization.Section4.R42.BlowupEssSup` | `Build completed successfully (9943 jobs).` (only pre-existing upstream warning from `Source/BoundedViscosityUniqueness.lean`) |
| `lake env lean ../formalization/NSFormalization/Section4/R42/BlowupEssSup.lean` | **silent** — no output at all |
| `lake env lean ../research/R42/axioms_blowup.lean` | 3 declarations, each `[propext, Classical.choice, Quot.sound]` — `SpeedUnboundedAt`, `ofReal_le_eLpNormTop_of_continuous`, `limsupLeft_speedENorm_eq_top` |
| `grep -nE 'sorry\|admit\|axiom\|native_decide\|maxHeartbeats' BlowupEssSup.lean` | no hits |
| same grep on `research/R42/axioms_blowup.lean` | only the three `#print axioms` lines and a docstring word — no `axiom` declaration |
| `make check` | architecture checks pass; `test_contract_policy.py` 13/13 OK; `check_work_queue.py` "30 work items … consistent" |
| `diff` contract `Scaling.lean:124-126` vs `BlowupEssSup.lean:54-56` | identical |
| `diff` `Source/PacketScaling.lean:22-24` vs `BlowupEssSup.lean:54-56` | identical (finding 1) |
| scratch `/tmp/r42b.lean` (consumer-shape example, `0 < T` derivable, `hcont` from `ContDiffOn`) | all compiled |
| scratch `/tmp/r42d.lean` (Haar / open-pos / ball / singleton) | all compiled |
| scratch `/tmp/r42e.lean` (`PacketScaling` reachable from `A02.Patch` alone) | `#check` succeeded |
| scratch `/tmp/r42f.lean`, `/tmp/r42g.lean` (Assembly preamble shadowing) | resolves to `NSFormalization.Section4.R42.SpeedUnboundedAt`, no error |
| scratch `/tmp/r42h.lean` (`zero_le _`) | reproduced the recorded error |

---

## Where clause #2 stands for the R42 assembly lane

**In hand.** The full pointwise → `L^∞` bridge, proved and axiom-clean:
`R42.ofReal_le_eLpNormTop_of_continuous` (a continuous field's essential supremum
dominates any value it attains, on genuine Lebesgue `volume`) and
`R42.limsupLeft_speedENorm_eq_top` (pointwise `SpeedUnboundedAt T u` + slice
continuity on `(0,T)` ⟹ `limsupLeft T (speedENorm ∘ slices) = ⊤`).  Its conclusion
plugs directly into `MaximalPartial.lifespan_le_of_unbounded`'s blow-up hypothesis
with zero glue — verified by construction, not by inspection — so clause #2 of
`LIFESPAN_SPLIT.md` is no longer the residual it was; item 2a is closed.

**Still missing, and it belongs to the assembly lane.** Two inputs, both declared as
such in ATTEMPTS' "Gap" section:
1. the raw `SpeedUnboundedAt family.T (velocity ε)` — available as
   `InsertionFamilyAPI.blowup` (`Contracts/V1/InsertionFamily.lean:304`), so this is
   plumbing through the binding layer, not new mathematics;
2. the slice-continuity `hcont` on `Ioo 0 T`, which must be derived from
   `InsertionFamilyAPI.velocity_smooth` (`InsertionFamily.lean:196`).  Finding 3
   shows the derivation exists and is ~9 lines, but **it is not written anywhere yet**.

Plus the housekeeping of findings 1 and 2 before this module is imported by
`Assembly.lean`.
