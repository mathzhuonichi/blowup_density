# T11 — lead amendments to the proof plan (`T11_SPLIT.md`)

## Amendment 1 (2026-09-18 01:30Z): the named local-existence input gets order-wise force bounds

Lane 311 (`EXISTENCE_ROUTE.md` §"Residual input and a quantifier issue") showed that the input of `T11_SPLIT.md` §1 U9,
`PeriodicQuantitativeLocalInput`, cannot be instantiated by U10: it demands one bound `K` for `forceSobolevENormT 1 m g` **at every order `m`**, while a smooth
compactly supported force only has a finite norm at each order separately (a single nonzero mode times a time bump has norms growing like `W(k)^(m/2)`).

**Decision.** Replace the input by the order-wise version; the local time `δ` may depend on `ν`, the `H¹` datum bound `K`, and the whole family of force bounds:

```lean
def PeriodicQuantitativeLocalInput' : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∀ M : ℕ → ℝ≥0∞, (∀ m, M m ≠ ⊤) → ∃ δ : ℝ, 0 < δ ∧
    ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 1 a ≤ K →
      ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g →
        (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ M m) →
          ∃ w : ClassicalSolutionT ν a g δ, PeriodicLocalRegularity ν a g δ w
```

This is exactly what U10 can instantiate: for a fixed `f ∈ forceClassT` and `S ≥ 0`, the shifts `timeShiftT t₀ f`, `t₀ ∈ Icc 0 S`, have
`forceSobolevENormT 1 m (timeShiftT t₀ f) ≤ forceSobolevENormT 1 m f =: M m` at every order (translation invariance of the time integral — prove it in U10), and
`M m ≠ ⊤` by lane 312 (T10 item 11). It is also what Appendix A proves: the existence time depends on the datum norm and on (finitely many) force norms.
U9b–e prove `PeriodicQuantitativeLocalInput'`; lane 311's `quantitative_lifespan_lower_bound` is re-derived from the primed input in U9b (one-line change).
The `H¹` ball itself stays as stated (risk §3 of the split unchanged).

## Amendment 2 (2026-09-18 06:20Z, planned for U9e/U17): the provable existence input is the `H³`-ball version; the `H¹`-ball statement stays as the manuscript's named predicate

`PeriodicQuantitativeLocalInput'` (amendment 1) asks for a horizon `δ` uniform over an **`H¹` ball** of data. The existence machinery we have (lanes 313/317/330/334: Picard in the
`H³ × H²` two-space contract, all-order persistence, classical assembly) yields `δ` depending on `‖A‖_{H³}` and the order-wise force bounds — uniform over an **`H³` ball**, not over an
`H¹` ball. Uniformity over `H¹` balls is the subcritical Fujita–Kato local theory, which is not in the tree and is exactly the wall Section 4 hit (`ManuscriptHorizonLowerBoundH1` kept as a named
unproved predicate; the fixed-force `H⁷` narrowing registered as `RestartFixedForce`, owner-approved wording pending).

**Decision.** Same honest route as Section 4:
1. U9e proves `PeriodicQuantitativeLocalInputH3` — the primed input with `periodicSobolevENorm 3 a ≤ K` in place of `periodicSobolevENorm 1 a ≤ K` (everything else identical) — outright.
2. The `restart` field of `PeriodicContinuationAPI` with the `H¹` ball is **kept verbatim** in the V1 spec/contract as a named predicate (`PeriodicRestartH1 : Prop`, documented as the manuscript's
   statement, not proved), exactly as `ManuscriptHorizonLowerBoundH1`; U17 registers the proved API where `restart`/`restartBeyond`/`extendsBeyond` quantify over the `H³` ball (a V2-style
   narrowing, `RestartH3`), and checks that every consumer (T18/T19/T20) restarts only with data whose `H³` norm is controlled — T20's `eq:H1energy` route must be re-read at that point; if a consumer
   genuinely needs the `H¹` ball, that is an owner-level gap to report, never a silent weakening.
3. Lanes 321/332/337 are parametrized by the input `H`, so the `H³` versions are obtained by re-instantiation (a small lane), not by re-proving.
