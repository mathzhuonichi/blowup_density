# UREG — registering `T01.mean_zero_calculus` (lanes 419 → 427)

Lane 427 record.  Lane 419's text is kept verbatim at the bottom under
"superseded".

## What the registration had to clear

`MeanZeroSobolevCalculusAPI` is Type-valued (seven constants are data fields),
so the contract is registered through `Nonempty` (`meanZeroCalculusStatement`)
and the acceptance declaration is a `def`, not a `theorem` — unlike
`T02.localization`, whose `LocalizationAPI` is `structure … : Prop` and can be
transported by `theorem checkedLocalization`.

## 1. The blocking duplicate (the reason 419 stopped)

Lanes 400 (`Section3/T12/GradientLSix.lean`) and 405
(`Section3/T12/GradientLambdaL3.lean`) were written in parallel inside the one
namespace `NSFormalization.Section3.T12` and each declared

```
theorem contDiff_dirDeriv … : ContDiff ℝ ∞ (dirDeriv i w) :=
  (hw.fderiv_right (by simp)).clm_apply contDiff_const
```

Any module importing both — the binding needs both — died with
`import NSFormalization.Section3.T12.GradientLambdaL3 failed, environment
already contains 'NSFormalization.Section3.T12.contDiff_dirDeriv'`.  A full
name-collision scan over the eleven `Section3/T12/*.lean` modules
(`grep` of every `theorem|lemma|def|abbrev|instance|structure` head, then
`sort | uniq -d`) found **exactly one** duplicated name — no other helper
collides.

The two copies have the **same proof term**; they differ only in generality:

* lane 400: `{w : Space → F}` with `variable {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]` — general;
* lane 405: `{v : SpatialField}` — the `F := Space` instance, since
  `SpatialField` is the reducible `abbrev Space → Space`.

Fix: the general one moved verbatim into the new leaf module
`formalization/NSFormalization/Section3/T12/DirDeriv.lean`
(`import NSFormalization.Section4.A05.SmoothJets` only), both modules now import
it and neither declares it.  No exported statement changed; every call site in
`GradientLSix.lean`, `GradientLambdaL3.lean` and
`Section3/T20/CriticalTrilinear.lean` still elaborates, because the lane-405 uses
instantiate `F := Space` by reducible unfolding of `SpatialField`.

Rejected alternative: putting the lemma in `Section4/A05/SmoothJets.lean` next to
`dirDeriv`.  That module is in the registered `A05.gradient_l6` closure and the
brief's exception only licenses the two T12 modules, so a new T12 leaf module is
the smaller change.

## 2. What was wrong with lane 419's binding

`Bindings/MeanZeroCalculus.lean` as delivered by 419 never compiled (419
reported only that the *contract* file compiles).  Three independent faults:

1. It opened **both** `BlowupDensity.Contracts.V1.MeanZeroCalculus` **and**
   `NSFormalization.Section3.T12`, so every bridge's left-hand side was
   ambiguous: `error: overloaded, errors …` on the bare names
   `periodicScalarSobolevENorm`, `MemPeriodicHmScalar`, … .  Fixed by opening
   only the contract side and writing the canonical side fully qualified — the
   house pattern of `Bindings/TorusData.lean`.
2. It never opened `NavierStokes.ProblemStatement`, so `Space` in the bridge
   binders resolved to a different constant:
   `Application type mismatch: z has type Space → ℝ but is expected to have type
   NavierStokes.ProblemStatement.Space → ℝ`.
3. It never opened `scoped ENNReal`, so `(p : ℝ≥0∞)` in
   `periodicLpENorm_eq` was a parse error (`expected token`).

Also fixed: `MeanZeroCalculus.lift` / `.gradientTensor` / `.laplacian` do not
resolve from inside `namespace BlowupDensity.Bindings` (Lean looks for
`BlowupDensity.Bindings.MeanZeroCalculus.…`); the bridges must spell
`Contracts.V1.MeanZeroCalculus.lift` and so on.

All eleven `rfl` bridges then hold as written — no fieldwise conversion was
needed anywhere, and the three derivative spellings are `rfl` for the same
reason `Bindings/GradientL6.lean:27,32` are.

## 3. Contract fidelity

A token-level diff (comments and whitespace stripped) of
`Contracts/V1/MeanZeroCalculus.lean` against `research/T12/Spec.lean`'s
`BlowupDensity.T12.Draft` body found 419's file already token-for-token correct
except that it **dropped the Spec's three defeq checks**
(`Spec.lean:534-546`, `lift v = BlowupDensity.Contracts.V1.lift v` etc.).  Those
are restored, which required adding `import Contracts.V1.GradientL6`; the
docstrings of the three derivative spellings were restored to the Spec's, which
cite the manuscript lines and the registered source.  The only remaining token
difference is the added `def meanZeroCalculusStatement`, as intended.

## 4. Registry

419 wrote the entry as a **top-level key** of `verification/contracts.json`
next to `"contracts"`, not as an element of the `contracts` list, so
`check_contracts.py` still reported 42 contracts and the entry carried none of
the required `specification` / `binding_module` / `test_module` /
`declaration` / `enabled` keys.  Rewritten as the 43rd list element.
`parent_task` is `T01`, not `T12`: the `work_items.json` T12 deliverable says
"register … under parent task T01", T01's blueprint contract is the node that
reads "prove the uniform mean-zero critical embedding", and the two precedents
`T01.torus_local_theory` (T11's content) and `T02.localization` (T13's content)
both take the parent named by their id prefix.

## 5. Non-vacuity witness

`Tests/MeanZeroCalculus.lean` rebuilds lane 377/396's witness
`meanZeroProbe = meanZeroPartT (x ↦ cos(2π x₀)·e₀)` (research probes are not
Lean modules and cannot be imported), proves it nonzero, smooth, periodic and
mean-zero, and instantiates five of the nine fields on it.  Finiteness of the
homogeneous norm comes from `T13.periodicHomogeneousENorm_lt_top`, which is
stated directly on `meanZeroPartT f` for smooth periodic `f`, so no separate
datum construction is needed.  `Tests` is `warningAsError = true`; the
transplanted proof produces no warnings.

---

## Superseded — lane 419's record, verbatim

# UREG registration attempts

Created the V1 contract restatement and initial binding. Canonical theorem modules currently expose duplicate helper declarations when imported together, so combined assembly requires a dedicated reconciliation import module.
