# ATTEMPTS — lane 140-A01-euler-pairing (rows D-euler-pairing / C1b-m-E; E1+E2+payoff)

Deliverable module: `formalization/NSFormalization/Section4/A01/EulerPairing.lean`
(namespace `NSFormalization.Section4.A01`).  Axioms record: `research/A01/axioms_euler_pairing.lean`
(all declarations + a non-vacuity theorem = `[propext, Classical.choice, Quot.sound]`).

## Outcome: E1, E2 and the payoff all CLOSED.

The lane closes more than the brief's floor (E2 was the guaranteed obligation): E2, E1 (descent +
recursion + top-level from the cylinder solution) and the datum payoff all compile with standard axioms.

## E2 — `weakDeriv_pairing_of_translation_hasDerivAt` (the real obligation)

Statement (exact `HasWeakDerivsL2` pairing shape): for `z w : EulerMeanSolenoidal.L2` and
`h : HasDerivAt (fun t => EulerMeanSolenoidal.translation (t • coordinateVector j) z) w 0`,
`∫ ψ·wᵢ = ∫ (−∂ⱼψ)·zᵢ` for every `ψ : 𝓢(Space,ℂ)`, `i : Fin 3`.

Route that worked (the review's "cheaper" route):
* Pairing functionals as `innerSL ℂ` composites, transferred through `ContinuousLinearMap.compLpL`
  of `Complex.ofRealCLM ∘ EuclideanSpace.proj i` (`complexComponentCLM`).
* LHS: compose the pairing CLM with the given strong-derivative path → `HasDerivAt (fun t => ∫ ψ·(translation (t•eⱼ) z)ᵢ) (∫ ψ·wᵢ) 0`.
* Change of variables (`integral_add_right_eq_self`) moves the translation onto `ψ`.
* RHS: differentiate the smooth `L²` orbit of `ψ` via `EulerLpTranslation.smooth_hasFDerivAt`
  (needs only `MemLp ⇑ψ 2` and `MemLp (fderiv ℝ ⇑ψ) 2`, both from `SchwartzMap.memLp` /
  `SchwartzMap.fderivCLM.memLp`); its `L²` derivative in direction `−eⱼ` is `−∂ⱼψ`
  (`EulerLpDerivative.derivativeMap_ae` + `SchwartzMap.lineDerivOp_apply_eq_fderiv`).
* The two scalar functions coincide, so `HasDerivAt.unique` equates the derivatives.
* No smoothness of `z`, no dominated-convergence bound, no compact cutoff (contrast LESSONS 094).

Single `set_option maxHeartbeats 400000 in` (commented): the *statement* is a composite of `Lp`
continuous-linear-map/`innerSL` objects, so its elaboration is heavy; the proof itself does no search.
Verified it compiles at 250000 (default 200000 is just short); 400000 leaves CI margin, ≤ the LESSONS
guideline.  Not heartbeat-chasing.

### E2 dead ends / gotchas
* `volume` in the `complexComponentCLM` type is ambiguous (`MeasureSpace ?m` stuck) — must annotate
  `(volume : Measure Space)` in both the def type and the `compLpL` call.
* `EuclideanSpace.proj i u = u i` is `rfl`, but there is no `EuclideanSpace.proj_apply` lemma; close
  the coeFn goal with `simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]; rfl`.
* `RCLike.inner_apply` gives `inner ℂ a b = b * conj a` (conj on the *first* slot, product flipped),
  so the LHS needs `simp only [starRingEnd_apply, star_star]; ring`, the RHS `Complex.conj_ofReal`.
* `inner` now takes the field explicitly: `inner ℂ a b`, and `L2.inner_def` is `inner 𝕜 f g = ∫ …`.
* `hv : HasDerivAt (fun t => t • v) v 0` for `v : Space` — `simpa only [one_smul] using (hasDerivAt_id 0).smul_const v`
  FAILS with a `PiLp.normedAddCommGroup` vs `WithLp.instAddCommGroup` instance mismatch on `Space`
  and an unreduced `id y`.  Adding `id_eq` to the simp set (`simpa only [id_eq, one_smul] using …`,
  the vendor's exact incantation in `MeanSmoothRepresentative.orbitDerivative_hasDerivAt`) fixes it.
* `integral_add_right_eq_self` leaves `μ` a metavar (`IsAddRightInvariant ?m` stuck) — pass
  `(μ := (volume : Measure Space))`.
* `EulerLpDerivative.derivativeMap_ae` takes the measure explicitly first: `derivativeMap_ae volume D a`.
* `EulerMeanSolenoidal.L2 = Lp EulerSmoothLimit.Space 2 volume` (NOT the `ProblemStatement.Space`
  spelling, though the two are defeq) — the integrand `fun t => ∫ …, z (x + t•eⱼ) …` needs `fun t : ℝ`
  annotated or `t`'s `HSMul` is stuck.

## E1 — descent, recursion, cylinder top level (bonus; brief called this "bookkeeping")

* `hasDerivAt_meanTranslation_of_lift` (**the linchpin**): pulls the lift-level
  `Euler/CylinderSobolevSpace.word_hasDerivAt` (in `EulerLiftedGradientSpace.translation` along
  `translationPath`) back to the ordinary-`L²` translation orbit E2 consumes.  Uses
  `EulerMeanOrdinaryLift.ordinaryLift_translation`, the fst identity
  `(translationPath 1 (standardDirection j.succ) t).1 = t • coordinateVector j`
  (`simp [translationPath, coveringMap, standardDirection_succ, coordinateVector]`), and the CLM
  left-inverse `LinearIsometry.adjoint_comp_self ordinaryLift` (`one_apply_eq_self`, not the
  deprecated `ContinuousLinearMap.one_apply`).
* `exists_descend`: the review feared a `jet_word_eq`-style induction for the angle-invariance of
  `ofJet J`.  **Not needed** — `value_injective` collapses the array angle-invariance to the *value*
  (word-0) level, where it is exactly the angle-invariance of `word 1 u _ w` (a `congrArg` on the
  clause-7 hypothesis of `u`).  `word_has_jet` → `ofJet` (`value_ofJet`) → `exists_ordinary_value`.
* `hasWeakDerivsL2_of_word`: induction on the order `m`; the step descends `Fin.cons j.succ w`, recurses,
  and feeds `word_hasDerivAt` through `weakDeriv_pairing_of_lift_hasDerivAt`.  The `word 1 u _ w` proof
  arguments differ between `word_hasDerivAt` and `exists_descend` but match by proof irrelevance
  (`have e1 : word 1 u hlt.le w = ordinaryLift Zw := hZw.symm`, then `rw [e1, e2] at hderiv`).
* `hasWeakDerivsL2_of_cylinder` / `exists_isSobolevDatum_m_of_cylinder`: plug the `exists_local`
  outputs (`u : SobolevSpace 1 (q+1)`, clause-7 angle invariance, clause-4 `ordinaryLift U = value 1 u`);
  `value 1 u = word 1 u (Nat.zero_le _) Fin.elim0` by `rfl`.

## Order budget and horizon (recorded per brief)

`exists_local {q} (hq : 6 ≤ q)` fixes `T` **after** `q`; descending each word costs 3 orders, so the
chain gives `HasWeakDerivsL2 (⇑(U t)) m` for `m + 3 ≤ q + 1`, i.e. **`m ≤ q − 2`**, on the interval
`T = T(q)` — each finite order on its own horizon.  A common `T` for all `m` (`∀ m` at one horizon,
`MemHInfty`-strength) needs a `q`-independent horizon = A3's persistence-of-regularity obligation, not
D-euler-pairing's.

## Review follow-up (REVIEW_EULER_PAIRING.md, applied by the lead as records only)

- Module docstring line ~42 says `m ≤ q − 3`; the proved budget is `m ≤ q − 2` (`m + 3 ≤ q + 1`, forced by `exists_descend`'s `n + 3 ≤ q`; at `q = 6` the top order is 4). Docstring fix deferred to the next SIMP pass; ATTEMPTS and both split tables are right.
- E2's sign convention was cross-checked by two independent routes on a smooth field (this lane's E2 vs lane 132's `smoothField_weakDeriv_pairing`); `w = +∂ⱼz`, the minus sign on ψ. The `HasDerivAt` hypothesis is load-bearing (collapse: without it every L² field would pair to 0 with every Schwartz function).
- `complexComponentCLM` is the same term as lane 124's `DatumPathContinuity.componentCLM` (`rfl`); dedupe in a MAINT lane, not here.
- Heartbeats: E2 elaborates at 250000; 200000 times out at `whnf` on the statement; 400000 kept as margin.
- **A3-L1·k unblocked (reviewer probes preserved under `probes/rev140_*`)**: with this lane, `sobolevENorm 2 (⇑U) ≠ ⊤` and `sobolevNormAt 2 v t = ‖A‖` for the produced datum, so the vacuity warning in `A3_SPLIT.md:70,118-126` is lifted. The one remaining piece between `exists_local` and `Kbnd` is the **quantitative** constructor: `‖A‖² ≤ c_m Σ_{|α|≤m} ‖∂^α z‖²_{L²}` tracked along the induction of `exists_isSobolevDatum_of_memLp_derivs` (`‖word‖ ≤ ‖u‖` and `‖ordinaryLift Zw‖ = ‖Zw‖` are one-liners) — lane `A3-L1·k-quant`, D01-owned, M ≈120–200 lines, no external input.
- c8 (continuity of the order-m datum path) is unchanged in nature but smaller: the datum is now a canonical function of `t` by uniqueness; the obstacle remains jet-continuity of the velocity path (B1/T1 strength), cheapest via the `smoothAngularDatum` CLM tail.
