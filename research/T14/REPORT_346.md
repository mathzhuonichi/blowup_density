# Lane 346-T14-packet-energy report

## 1. Theorems with exact statements

In `NSFormalization.Section3.T14`, the new module defines

```lean
def accumulatedForce (F : VelocityField) (t : ℝ) : ℝ :=
  ∫ s in Ioo (0 : ℝ) t, Real.sqrt (l2Sq F s)
```

and proves the two packet fields:

```lean
theorem energy_le_work_of_packet {ν : ℝ} {u f : VelocityField} {p : PressureField}
    {K : Set Space} (hν : 0 < ν) (hcarrier_compact : IsCompact K)
    (hvelocity_smooth : ContDiffOn ℝ ∞ u preSingularDomain)
    (hpressure_smooth : ContDiffOn ℝ ∞ p preSingularDomain)
    (hforce_smooth : ContDiff ℝ ∞ f)
    (hforce_support : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (hvelocity_support : ∀ t ∈ Ico (0 : ℝ) 1,
      tsupport (fun x : Space => u (t, x)) ⊆ K)
    (hzero_initial_velocity : ∀ x : Space, u (0, x) = 0)
    (hdivergence_free : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
      spatialDivergence u t x = 0)
    (hnavier_stokes : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ x : Space,
      NavierStokesR3.ProblemStatement.navierStokesResidual ν u p t x = f (t, x)) :
    ∀ t ∈ Ico (0 : ℝ) 1,
      l2Sq u t + 2 * ν * (∫ s in Ioo (0 : ℝ) t, dissipation u s)
        ≤ 2 * (∫ s in Ioo (0 : ℝ) t,
          Real.sqrt (l2Sq f s) * accumulatedForce f s)
```

```lean
theorem work_eq_square_of_packet {f : VelocityField}
    (hforce_smooth : ContDiff ℝ ∞ f)
    (hforce_support : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f) :
    ∀ t ∈ Ico (0 : ℝ) 1,
      2 * (∫ s in Ioo (0 : ℝ) t,
        Real.sqrt (l2Sq f s) * accumulatedForce f s)
      = accumulatedForce f t ^ 2
```

The force-support projection and interval FTC lemmas are exported helpers in
the same namespace and are audited alongside these two declarations.

## 2. Files

- `formalization/NSFormalization/Section3/T14/PacketEnergy.lean`: raw-field
  energy/work proofs, compact-support projection, and interval/set-integral
  conversions; it imports no `Contracts.*` module.
- `research/T14/probes/api_on_canonical.lean`: token-level reconciled API
  restatement, `rfl` primitive bridge, canonical packet import theorem and
  selected family, plus the velocity non-vacuity example.
- `research/T14/axioms_packet_energy.lean`: axiom audit for every exported
  declaration in the proof module.
- `research/T14/ATTEMPTS.md`: explored routes and exact transient diagnostics.
- `research/T14/COMPARISON.md`: proof-lane status update.

## 3. Gaps and exact error text

There is no remaining theorem or elaboration gap. The transient diagnostics
encountered during development (namespace ambiguity, derivative conversion,
set-integral conversion, and contract/source `rfl` bridges) are preserved with
their exact Lean error text in `research/T14/ATTEMPTS.md`.

All audited declarations have exactly `[propext, Classical.choice, Quot.sound]`.
No prohibited proof primitive or placeholder is present.

## 4. Commands run and results

All Lean commands used `. scripts/lean-env.sh`; Lake commands ran from
`verification/` with `LEAN_NUM_THREADS=6`.

- `lake build NSFormalization.Section3.T14.PacketEnergy`: passed, 0 errors.
- `lake env lean ../formalization/NSFormalization/Section3/T14/PacketEnergy.lean`:
  passed with 0 output.
- `lake env lean ../research/T14/probes/api_on_canonical.lean`: passed; only
  its three requested standard axiom lines were printed.
- `lake env lean ../research/T14/axioms_packet_energy.lean`: passed; every
  line printed exactly the three standard axioms.
- `make check` from the worktree root: passed (architecture, contract-policy,
  and work-queue checks; exit 0).
