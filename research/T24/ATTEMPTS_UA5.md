# T24a Ua5 — attempts and proof route

## Exact source shape

`SpeedUnboundedAtOne U` says that for every `M > 0` and every `δ > 0`
there are `t,x` with `t ∈ Ioo 0 1`, `1 - δ < t`, and
`M < ‖U (t,x)‖`.  It does not directly require `t > τ₁`.

`AffineAdmissible c r τ₀ τ₁ b` contains smoothness, compact support, support
inside `Ioo τ₀ τ₁ ×ˢ ball c r`, and zero divergence.  It does **not** contain
`τ₁ < 1`, so the canonical Ua5 theorem takes that geometric inequality as a
separate hypothesis.  Its only packet hypothesis is the raw clause
`SpeedUnboundedAtOne U`.

## Closing route

Given the requested neighborhood width `δ`, invoke the raw packet clause with
`min δ (1 - τ₁)`.  Positivity follows from `δ > 0` and `τ₁ < 1`.  Its witness
satisfies both the original inequality `1 - δ < t` and `τ₁ ≤ t`.  Ua1's
`late_agreement` then rewrites
`affineVelocity U b (t,x)` to `U (t,x)`, preserving the speed inequality.

This closes the field without a named analytic input or an eventual-equality
lemma.  The registered-spelling probe applies it to
`BlowupDensity.Bindings.packet ν hν` and separately checks that `b = 0` is an
admissible witness, so the universal field is not being discharged through an
empty admissible class.

## Probe iteration

The first probe draft imported only `Contracts.V1.Packet` and attempted to open
`NSFormalization.Section4.A02.SpaceTimeField`; that namespace was not in the
import closure.  Importing `Contracts.V1.Data` and using its registered
`SpaceTimeField` spelling fixed the issue.  The probe then elaborated with no
output.

