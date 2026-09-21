# D01 attempts and decisions

Lane 009, 2026-09-13.  Alternatives that were tried and rejected while
reconciling `research/D01/DraftA.lean` and `research/D01/DraftB.lean` into
`verification/Contracts/V1/Data.lean`.  One sentence each; the full
object-by-object record is [`RECONCILIATION.md`](RECONCILIATION.md).

* **Draft A's `MemForceR` without `f ∈ C^∞` — rejected.** REVIEW_A machine-checked
  that every clause reaches `f` only through a Lebesgue integral, so a null-set
  edit of the field preserves membership and sits at distance `0` from the
  original; `B^R_{ν,a,T}` then leaks, 4.1(i) is vacuous and the "only if" of
  4.1(ii) is false. Draft B's `ContDiffOn ℝ ∞ f futureDomain` is adopted.
* **Draft B's bundled `ForceR` structure — rejected as the carrier.** It makes
  `F_c`, `F_rd`, `F_R` three different types, so `F_c ⊆ F_rd ⊆ F_R` and "the
  same `T^ν_{max,R}(a,·)` in all three" (STATEMENTS §9 items 11–12) cannot be
  stated. Replaced by predicates on one `SpaceTimeField` type.
* **Draft A's literal Fourier `H^s` norm (`angularVectorSobolevNorm`,
  `forcePhysicalTimeNorm`) — rejected.** Mathlib's `𝓕` totalizes to `0` off
  `L¹` and `H^∞ ⊄ L¹` on `R³`, so the quantity is junk on exactly the slices
  `F_R` contains (REVIEW_A issue 2, which also falsified comparison unit L4).
  Replaced by the datum-infimum norms.
* **Draft B's `∫⁻` of a pointwise infimum — rejected.** With no measurability
  it is the *lower* Lebesgue integral and can under-report the `L^q` norm
  (REVIEW_B issue 3). Replaced by `eLpNorm` of a Banach-valued path, with
  `AEStronglyMeasurable` inside the quantified data so the fail-safe value is
  `⊤`.
* **Draft B's `CompletedDense` over all `ℝ → ForceDistribution` — rejected.**
  A target off `H^s` sits at distance `⊤` from every candidate, so the
  predicate is false for every `S` (REVIEW_B issue 1). The target is now
  quantified over the completion: a datum path with `MemBochnerDatum`.
* **Draft B's `.toReal` energy norm — rejected.** `⊤ ↦ 0` makes the *bound*
  eq:REclose satisfiable by a field of infinite energy (REVIEW_B issue 2).
  Draft A's `ℝ≥0∞` form is adopted.
* **Zero-extending forces below `t = 0` — considered and rejected.** It would
  make `MemForceR` extensional and give a separated metric for free, but it
  strengthens membership and therefore *weakens* the universally quantified
  reference force of 4.1(i). Recorded instead as `AgreesOnFuture`, the
  equivalence to quotient by (REVIEW_B issue 5).
* **A separate scalar `Ḣ^{-1}` (draft A) — rejected.** prop:Renergy needs the
  vector, time-integrated norm, and `research/section4/REVIEW.md` item 1 shows
  all three homogeneous usages are one formula. One `IsHomogeneousDatum s` for
  `−3/2 < s < 3/2` replaces it, with the manuscript's temperedness estimate
  added as an explicit `Integrable` clause (REVIEW_B issue 4).
* **A distributional `Ḣ^{3/2}` — rejected.** The temperedness integral
  `∫|ξ|^{-2s}|φ̂|²` diverges at `2s = 3`, and `app-B:101` refuses the space.
  The `Ḣ^{3/2}` *quantity* is `homogeneousFourierENorm (3/2)` instead.
* **A physical-field `L^q_tḢ^s_x` through an `L² → 𝓢'` homogeneous multiplier
  — rejected.** `Paper3/HomogeneousRealization.lean` deliberately does not build
  one, and `‖ξ‖` is not `HasTemperateGrowth`. It was first deferred altogether;
  after review it is supplied instead through `IsSliceDistribution`, the same
  Schwartz pairing `IsSobolevDatum` already uses, so `forceHomogeneousENorm`
  needs no multiplier and no new Parseval convention.
* **Importing `Paper1.InsertionEnergy` / `R3.CompactEnergy` for `E_T`, and
  `Euler.LpSmoothField` for `H^∞` — rejected.** Both are proof modules outside
  the canonical-convention list; the first also forces the `.toReal`. They are
  binding targets (units L2, L11), not contract imports.
* **`experiments/check_contracts.py` rejected the contract on first run.** Its
  allowlist permitted only `Mathlib`/`Lean`/`Init`/`Contracts.` imports in a
  versioned specification. Widened to an explicit `CONTRACT_CANONICAL_MODULES`
  frozenset, with a regression test in `experiments/test_contract_policy.py`.
  Flagged for review.
* **A `NavierStokes.` package prefix on the vendor half — rejected on review.**
  It admitted all 643 upstream modules, comparator machinery included, where
  `Data.lean` needs exactly one; replaced by the exact entry
  `NavierStokes.R3.ProblemStatement` in the same frozenset. The bare roots
  `Mathlib`/`Lean`/`Init` are now matched exactly or with a dot, so
  `MathlibExtras.X` and `Initialize.X` no longer pass.
* **Unit-testing `contract_import_allowed` alone — insufficient.** A refactor
  that stopped consulting the predicate would pass; two end-to-end cases now
  drive `check()` over a throwaway tree instead.
* **A local-integrability side condition on `IsSobolevDatum` — rejected.** It
  would close the junk-`0` corner but would stop the predicate matching
  `angularRealVectorSlice_pairing`; the corner is unreachable from `MemHInfty`
  and from the `m = 0` clause of `MemForceR`, and is documented instead.
* **A measurability clause inside `E_T` — rejected.** `E_T` appears on both
  sides of eq:REclose, so it must stay a plain quantity; the caveat is
  documented and cannot bite, because every field Section 4 measures with it is
  a difference of classical velocities, smooth on `Ico 0 T ×ˢ univ`.
* **Leaving the reconciliation sections in `collaboration/tasks/D01.md` —
  rejected.** The card is generated by `experiments/tasks.py render`, which
  overwrites appended content; the table and this log now live beside the
  reconciliation record in `research/D01/`.
