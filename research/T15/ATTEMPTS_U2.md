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
