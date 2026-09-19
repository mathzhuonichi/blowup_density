# Lane 477 / U2 attempts

Initial scope: exact G0 counterexample and repaired quantifiers; raw local
correction, spatial extension and un-periodised cross transport.

The implementation layer cannot import Contracts. Exact Spec checks therefore
run in a standalone research probe; no substitute API is introduced.

Initial inspection: `sed` on a guessed T14/PacketImport.lean and
`rg` on T16/CompactCorrection.lean failed with `No such file or directory`.
The actual local radial-potential results live in T16/BallPotential.lean.

## Un-periodised cancellation: first elaboration

Replacing the lattice-support step with closure of the physical support gave:
```text
LocalCorrection.lean:174:4: error: Type mismatch: After simplification, term
  hy
 has type
  y ∈ Function.support fun x => scaledVelocity U x₀ T ε (t, x)
but is expected to have type
  parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U) (t, y) ≠ 0
```
Fix: expose membership as a nonzero value before the definitional rescaling bridge.

Exposing membership still left the rescaling names unequal to the elaborator:
```text
LocalCorrection.lean:175:4: error: Type mismatch: After simplification, term
  hy
 has type
  @Ne Space (scaledVelocity U x₀ T ε (t, y)) 0
but is expected to have type
  @Ne Space (parabolicVelocity ε⁻¹ (T - ε ^ 2) x₀ (zeroPastField U) (t, y)) 0
```
Next: unfold both rescalings explicitly.
