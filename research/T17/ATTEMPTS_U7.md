# T17 U7 attempts — `force_smooth` / `force_periodic` / `force_support`

Lane 425, module `formalization/NSFormalization/Section3/T17/ForceSupport.lean`.

## Successful route

All three fields go through `Transport.force_eq`, which rewrites the T17 force
of the concrete `correctionData` as `latticeLift G` with

```
G = NSFormalization.Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)
```

the Section 4 single Euclidean copy.

* **`force_smooth`** — `Paper1.CorrectionForceNorms.physicalForce_smooth`
  (`formalization/NSFormalization/Paper1/CorrectionVectorNorms.lean:22`) gives
  `ContDiff ℝ ∞ G` from the global `hv`.  Its all-time spatial slice support in
  `ball x₀ (ε·θR)` comes from `Source.LocalizedInsertion.correctionForce_support`
  (`tsupport (force) ⊆ tsupport (correction)`) composed with
  `Source.PhysicalRemoval.physical_support`.  `T16.latticeLift_smooth` closes it.
* **`force_periodic`** — `Transport.correctionForce_periodic` already packages
  `force_eq` + `T16.latticeLift_periodic`; the field is a direct `exact`.
* **`force_support`** — the time factor is `T16.latticeLift_timeSupport`
  (`HasCompactSupport G` from `physicalForce_compact`, cylinder support from the
  same `correctionForce_support ∘ physical_support`).  The spatial factor is the
  new `latticeLift_spaceSupport` of §0 (below), applied with the compact set
  `C = Prod.snd '' tsupport G`, which lies in the **open** ball because `G` has
  compact support inside it; `T16.periodicSet_mono` then lands in
  `periodicSet (ball x₀ (ε·θRadius))`.

`hv : ContDiff ℝ ∞ v` (the documented G1 premise, `research/T17/SPEC_ISSUES.md`)
enters in exactly two places: `physicalForce_smooth` needs it globally
(`force_smooth` only), and `force_eq`'s `ContDiffOn ℝ ∞ v (Ioo 0 (T+δ) ×ˢ ball x₀ r)`
premise is discharged by `hv.contDiffOn` in all three theorems.  No other named
input, no placeholder, no `Prop` stub.

## What did not work, and why

1. **`T16.latticeLift_sliceSupport` directly.** Its signature is
   `(hslice : ∀ t y, w (t,y) ≠ 0 → y ∈ ball x₀ ρ) (hρr : ρ < r) (t : ℝ) :
   tsupport (fun x => latticeLift w (t, x)) ⊆ periodicSet (ball x₀ r)`
   (`Section3/T16/LatticeLift.lean:275`).  Two mismatches with the canonical
   field: (a) it needs a **strictly larger** radius `r > ρ`, so instantiating it
   at `ρ = ε·θR` yields `periodicSet (ball x₀ r)` with `r > ε·θR` — i.e. a
   *weaker* set than the field's `periodicSet (ball x₀ (ε·θRadius))`, which the
   brief forbids; (b) it bounds the tsupport of a single **spatial slice**, while
   the field bounds the tsupport of the space-time function.  A slice bound for
   every `t` does not give the space-time bound (the space-time closure can pick
   up points no single slice closure sees).
2. **`closure (A ×ˢ B) = closure A ×ˢ closure B` with `B = periodicSet C`.**
   This reduces the goal to `closure (periodicSet C) ⊆ periodicSet (ball x₀ ρ)`,
   i.e. to `IsClosed (periodicSet C)` for compact `C` — a locally-finite-union
   fact with no lemma in the tree (`grep -rn "periodicSet" formalization/` gives
   only `periodicSet`, `periodicSet_mono`, and the two slice lemmas).  Proving it
   from scratch needs the discreteness of the lattice, i.e. re-deriving what
   `NavierStokes.PeriodicLocalization.periodize_locally_eq_sum` already gives.
3. **Case split on `z.1 ∉ Ioo …` / `z.2 ∉ periodicSet …` with
   `notMem_tsupport_iff_eventuallyEq`.** The time case is fine
   (`latticeLift_timeSupport`), but the spatial case needs a *space-time*
   neighbourhood on which the lift vanishes, and the slice lemma only produces a
   spatial one.

**What fixed it.** `periodize_locally_eq_sum hsc z` is already stated at a
**space-time** point `z` (`vendor/NavierStokesAndEuler/NavierStokes/PeriodicLocalization.lean:136`),
so `T16.latticeLift_sliceSupport_closed`'s proof (`Section3/T16/Assembly.lean:201`)
transposes verbatim to the space-time level: each `translate w n` has support
inside the closed preimage `(fun z : SpaceTime => z.2 - lattice n) ⁻¹' C`, the
finite sum vanishes on a space-time neighbourhood, so the point is off the
space-time tsupport.  That is `latticeLift_spaceSupport` in §0 of the new module
(new theorem, no edit to any existing module), and it needs only `IsClosed C`,
not compactness — compactness is used only to produce `C` from `tsupport G`.

## Negative probes (must fail; run at /tmp/u7mut, not committed)

* narrowing the time window to `Ioo (T - ε^2) (T + ε^2)`:
  `error: Type mismatch … has type … Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) …
  but is expected to have type … Ioo (T - ε ^ 2) (T + ε ^ 2) …`
* dropping `periodicSet` (single copy only):
  `error: Type mismatch … ×ˢ periodicSet (ball x₀ (ε * … .θRadius)) …
  but is expected to have type … ×ˢ ball x₀ (ε * … .θRadius)`

The printed type in both errors confirms the delivered statement uses
`Metric.ball` (open), never `closedBall`.

## Axioms

`research/T17/axioms_u7.lean`: all five declarations print exactly
`[propext, Classical.choice, Quot.sound]`.
