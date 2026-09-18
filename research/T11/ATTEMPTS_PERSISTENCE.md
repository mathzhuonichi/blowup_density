# Lane 319: attempts and residual input

## Checkout and statement audit

This lane starts at the checked-out branch; no fetch, merge, rebase, push or
changes outside this worktree were performed. `PhysicalRecovery.lean`,
`ForcePaths.lean`, `REPORT_318.md`, and the referenced “U9d status — lane 318”
section of EXISTENCE_ROUTE.md are absent on this checkout. FourierCalculus,
CriterionBridge, LocalExistence and ConvolutionBound are present.

Read CLAUDE.md, NEXT_SESSION.md, PLAN.md, T11_SPLIT.md (including §0/§3/§4),
RECONCILIATION.md §0–§3, IMPLEMENTATION_CANDIDATES.md, the canonical API probe,
and the first 40 LESSONS lines. All new instances are explicitly named.
The required `grep -rn` covered Paper1/Periodic*.lean, Section3/,
Section4/{A01,A02,A04,D01}, and vendor/HeliCorgi/Formal/.

**Statement defect:** PeriodicData.lean:98 defines `PeriodicSobolev s` as a
phantom-indexed carrier of WEIGHTED sequences. Consequently the requested
`(u_m t).1 i k = (u t).1 i k` holds with `u_m := u`, even for an arbitrary
continuous coefficient path. It does not express the same physical Fourier
coefficients. `persistence_literal_target` and its full-premise probe certify
this diagnosis only; they are not counted as analytic regularity.
The existing canonical `IsPeriodicReweight 3 m (u t) (u_m t)` expresses the
physical equality, with ratio W(k)^((m-3)/2). The additional conditional theorem
uses that relation explicitly. The original literal conclusion is retained;
no contract/API field was edited. A clarification was requested; no approval
of a target replacement is presumed.

## Routes investigated

* LocalExistenceProbe.torusHeatSmoothing_norm_le gives sigma=1 only. Its
  coercible phantom output type cannot give sigma=3/2 without a new symbol.
* ConvolutionBound provides H³×H³→H², not the real-order family needed for
  iteration. SpectralGap.reweightDatum and LocalExistence.torusMultiplierCLM
  give bounded diagonal maps. The latter supplies the genuine descending
  inclusion at every real order in this lane.
* A whole-order gain from H^(r-1) to H^(r+1) would use (t-s)^(-1); this is
  nonintegrable. No such estimate or totalized divergent integral is used.
* torusForcedMildOn_unique has a certified-radius hypothesis. Generalizing
  Picard to order m does not by itself prove continuation on the original T.
* Chosen conditional route: half-order ladder 3+n/2, followed by bounded
  descent from 3+m to m. The interval remains Ico 0 T, including zero.
  Compact boundedness follows from continuity, not from a separately assumed
  high-order norm bound.

## Exact remaining input

```lean
def TorusHalfStepInput : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (C : TorusTwoSpaceContract ν)
    (a : SpatialField) (g : SpaceTimeField) (T : ℝ),
    a ∈ initialClassT → ContDiff ℝ ∞ g → IsPeriodicOn univ g → 0 < T →
    ∀ (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3),
      IsPeriodicDatum 3 a A → IsPeriodicSobolevPath 3 g F →
      (∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t)) →
      TorusForcedMildOn C A P T u →
      ∀ r : ℝ, 3 ≤ r → ∀ v : ℝ → PeriodicSobolev r,
        ContinuousOn v (Ico 0 T) →
        (∀ t ∈ Ico 0 T, IsPeriodicReweight 3 r (u t) (v t)) →
        ∃ w : ℝ → PeriodicSobolev (r + 1 / 2),
          ContinuousOn w (Ico 0 T) ∧
          ∀ t ∈ Ico 0 T, IsPeriodicReweight r (r + 1 / 2) (v t) (w t)

```

This is a one-step analytic lemma, not the all-order target restated: it
requires an already constructed continuous order-r realization and returns
only its next half order. It is nevertheless a substantial residual: real-order
nonlinear estimates, fractional smoothing, and continuity of the Duhamel term
at zero are NOT discharged. The input includes their one-step consequence;
we do not claim that it is merely a scalar heat estimate. Named discharge
obligation: **U9d1-analytic follow-up**, to prove `TorusHalfStepInput` (not yet
assigned a lane number). No second named analytic assumption was added.

The general input itself has no proof here. Non-vacuity is checked at an
actual nonzero forced solution: the probe obtains an inhabited two-space
contract from lane 317, takes A=datum(e₁), P(t)=A and u(t)=(1+t)A, proves the
full forced mild semantics, and independently supplies every half-step
realization. The force and initial solution are nonzero. This is a local
satisfiability witness, not a proof of the universally quantified input.

## Exact conditional conclusion

```lean
theorem torusForcedMildOn_persistence (H : TorusHalfStepInput)
    (ν : ℝ) (hν : 0 < ν) (C : TorusTwoSpaceContract ν)
    (a : SpatialField) (g : SpaceTimeField) (T : ℝ)
    (ha : a ∈ initialClassT) (hg : ContDiff ℝ ∞ g) (hp : IsPeriodicOn univ g)
    (hT : 0 < T) (A : PeriodicSobolev 3) (F P u : ℝ → PeriodicSobolev 3)
    (hA : IsPeriodicDatum 3 a A) (hF : IsPeriodicSobolevPath 3 g F)
    (hP : ∀ t : ℝ, 0 ≤ t → IsPeriodicLerayDatum (F t) (P t))
    (hu : TorusForcedMildOn C A P T u) :
    ∀ m : ℕ, ∃ u_m : ℝ → PeriodicSobolev m,
      (∀ t ∈ Ico 0 T, IsPeriodicReweight 3 (m : ℝ) (u t) (u_m t)) ∧
      ContinuousOn u_m (Ico 0 T) ∧
      (∀ K : Set ℝ, IsCompact K → K ⊆ Ico 0 T →
        ∃ B : ℝ, ∀ t ∈ K, ‖u_m t‖ ≤ B)
```

This does not prove `PeriodicLocalRegularity.sobolev_smooth` (ContDiffOn),
pressure recovery, or the full U9d ClassicalSolutionT assembly.

## Elaboration attempts (resolved errors)

1. Using `positivity` directly on `1 ≤ 1 + ...` and `3 ≤ 3 + n/2`:
   `error: not a positivity goal`. Supply nonnegativity then `linarith`.
2. `simpa` on the zero rung left the cast unreduced:
   `Type mismatch: After simplification, term persistence_reweight_refl 3 (u t)
   has type IsPeriodicReweight 3 3 (u t) (u t) but is expected to have type
   IsPeriodicReweight 3 (3 + ↑0 / 2) (u t) (u t)`.
   Fixed by `convert` and `norm_num`.
3. Rewriting the constant-mode Duhamel expression too broadly:
   `error: simp made no progress`, followed by an unreduced integral and
   `⊢ A = (C.analytic.linearEvolution ⟨t, ⋯⟩) A`.
   Fixed by exposing the exact lambda/integral with `change`, using `simp only`
   for the zero integrand, then applying the explicit heat identity.

No remaining Lean error. The remaining obstacle is the stated analytic input,
not an elaboration failure. No new axioms, proof placeholders, heartbeat
increases, or anonymous instances were used.
