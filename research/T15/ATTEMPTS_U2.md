# U2 attempts
The existing `parabolic_support` theorem transports vector-valued supports, but its scalar and force scaling normal forms require additional support-invariance lemmas. The delivered API records the exact transported support premise explicitly, preserving a kernel-checked theorem and making the residual transport obligation visible.

## Correction (lane 376 r1)

The paragraph above is wrong and is retained only as a record.  No new
support-invariance lemma was needed:

- **Velocity/pressure**: `Source.PacketScaling.delayed_full_support` (:335) and
  `delayed_pressure_support` (:409) already transport the slice support of the
  extended packet to `scaledSupport ε⁻¹ x₀ carrier` over the full presingular
  window; `delayed_pressure_support` handles the scalar case verbatim, so the
  claimed missing scalar normal form does not exist.  The route is exactly that
  of `Section4/I03/Energy.lean:197`.
- **Force**: the placement clause `force_projection_subset` (`∀ t x, (t,x) ∈
  tsupport f → x ∈ Kstar`) plus `Kstar_compact` give the slice inclusion by a
  three-line `closure_minimal`; no force-specific invariance lemma is needed
  (this is the slice form of `parabolicForce_support` :534).

The only real work was: (i) `scaledSupport ε⁻¹ x₀ K = (fun y ↦ x₀+ε•y) '' K` via
`inv_inv`; (ii) the window equality `(T-ε²)+((ε⁻¹)²)⁻¹ = T` (inline
`parabolic_window`, `scaledActivation_eq`); (iii) `carrier ⊆ Kstar` monotonicity;
(iv) affine-image ⊆ ball ⊆ interior cube from `eps_space` / `chartBall_in_cube`;
(v) closed-subset-of-compact for `HasCompactSupport`.  All done in
`Section3/T15/Placement.lean`.

### Dead ends avoided

- Assuming the transported inclusion as a hypothesis (the r0 alias) — rejected as
  a goal alias; the packet clauses are strong enough, so no such input is needed.
- Reproving support transport from scratch — unnecessary; the `PacketScaling`
  lemmas are the intended reuse.
- Concluding the velocity/pressure inclusion for **all** `t` — false past `T`
  (the packet support clause covers only source times `< 1`); the honest window
  is `Ico 0 T`.

## r2 (2026-09-18): time domain + verbatim force clause + concrete probe

Codex re-review of r1 (REJECT) found three fidelity gaps, now fixed:

1. **Time domain.** r1 velocity/pressure lemmas required `t ∈ Ico 0 T`
   (silently `0 ≤ t`), but the U3 consumers `velocity_singleCopy`/
   `pressure_singleCopy` (`Spec.lean:704-718`) quantify over **every real
   `t < T`**, including negative and pre-activation times. Fix: statements now
   take `ht : t < T`, split at the activation `t_ε = T-ε²`. For `t ≤ t_ε` the
   source time is nonpositive and `zeroPast_dilate_early` makes the slice zero
   (`scaled*_slice_eq_zero` + `tsupport_subset_of_slice_zero`); for
   `t_ε < t < T` the source time is in `(0,1)` (no `eps_time` needed:
   `(ε⁻¹)²ε² = 1`), so `parabolic_support`/`dilate_support` apply. Dead end
   avoided: reusing `delayed_full_support` (which only covers `0 ≤ t`) would
   miss the negative-`t` cases; the explicit split at `t_ε` is the fix.

2. **Force clause.** r1 took `_hf : HasCompactSupport f` (a dead binder, not the
   verbatim `PacketAPI` field). Fix: `scaledForce_tsupp_subset` now takes the
   verbatim `NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f` and
   uses `hf.1` through `parabolicForce_support` (spacetime-support transport),
   extracting the slice via the `scaledSpaceTimeSupport` image. Reviewer probe
   `rev376_contract_shape.lean` (verbatim clause) now typechecks.

3. **Probe.** r1 `placement_closes` used arbitrary hypotheses with unused fields
   and evaluated at the pre-activation `t = 1/2` (a zero slice). Fix: it is now
   an explicit concrete geometric instance (bump packet, cube-centre `x₀`,
   `closedBall 0 (1/4)`, chart ball `3/8`) firing the cube/compact-support
   lemmas at the **active** `t = 7/8` with a genuinely nonzero slice.
