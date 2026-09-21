# Lane 494 attempts

- Read COMMON_PHASE5, P3, article Remark 3.13, and canonical T14–T19 APIs.
- Built T18.Assembly and T15.SingleCopy successfully.
- Statement correction: ENNReal divergence uses `𝓝 ⊤`; `atTop` on a type
  with a greatest element requires eventual equality to that element.
- The source time is shifted by `scaledStartTime T ε = T - ε²`.
- Existing-module edits: none so far.

## Closed Lean step

- Raw packet energy contradiction, positivity, and finiteness compile.
- Single-copy rescaling proves the permitted lower inequality (not equality).
- Correction bound uses `forceProfileConst 0`, its chart identity, support, and
  lattice periodicity. The order-zero global derivative variant also compiles.
- Arbitrary canonical insertion records need no extra packet premise: the
  scaling solution, uniqueness, and blowup imply nonzero forcing. Compact-time
  periodicity gives finite amplitude even though the raw clauses were erased.
- Both extended-valued convergence to `𝓝 ⊤` and finite-real `atTop` divergence.
- Initial elaboration errors resolved: `mul_le_mul_left'` is absent in this pin
  (use ordered `mul_le_mul`); `atTop_pow` needs `IsOrderedMonoid ℝ` (use
  `Filter.tendsto_pow_atTop` and `atTop_mul_atTop₀`); rewriting a solution's
  dependent force index alone detached its velocity equality (rewrite the
  existential solution before destructuring it).
- No residual mathematical hypotheses or failed proof branches remain.

## Contract step

- Added Contracts.V1.ForceAmplitude, Bindings.ForceAmplitude and Tests.ForceAmplitude.
- `lake build Tests.ForceAmplitude`, the conformance probe and every `#print axioms` pass.
- Every new theorem prints exactly propext, Classical.choice, Quot.sound.
- Authorized existing-file edit: verification/contracts.json registers T03.force_amplitude.
