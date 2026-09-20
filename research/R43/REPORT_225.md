# Lane 225 — general-datum Proposition 4.3

## 1. Theorem proved

`universal_of_memForceR` proves the exact universal field of RCritical1API,
substituting the existing explicit positive constant `criticalConst` for c:

```lean
∀ ν : ℝ, 0 < ν →
      ∀ a : SpatialField, a ∈ initialClassR →
        ∀ f : SpaceTimeField, MemForceR f →
          dotHomogeneousENorm (1 / 2) a + forceHomogeneousENorm 1 (1 / 2) f
              < ENNReal.ofReal (criticalConst * ν) →
            maximalLifespanR ν a f = ⊤
```

The constant is
`min (1 / (8 * trilinearConst))
(1 / (4 * (A05.gradientL6Const * A05.criticalL3Const)))`,
independent of viscosity, datum, and force. The exact field text is preserved
in COMPARISON_UNIVERSAL.md and compared token for token after that substitution.

## 2. What is in Lean

New Universal.lean contains nine theorems: the general scalar bootstrap,
classical general-datum bootstrap, initial-plus-prefix estimate, slice critical
bound, slice absorption, maximal-family absorption, explicit general H² budget,
A04 finiteness, and universal global existence.

The bootstrap uses the existing C01 general square-root estimate and Paper1
continuous bootstrap. The H² budget retains both initial contributions:
`32*S*energyBudget a f S^2 + 32*ν⁻¹*gradientSq a`, plus
`32*(ν⁻¹)^2*∫₀ˢ l2Sq(f(t))`. The finite maximal endpoint is included.

The audit checks all nine declarations and four conformance declarations;
all 13 reports are exactly [propext, Classical.choice, Quot.sound].
It includes examples at a=f=0 and at zero datum with arbitrary small force,
recovering lane 223's inhomogeneous endpoint from universal. The final
conformance theorem uses Contracts.V1.Data vocabulary.

## 3. Remaining gaps

None for this theorem. No added analytic hypothesis, re-cut, or heartbeat
override. Both RCritical1API conclusion fields are now proved with the same
constant; the companion comparison records all four components. Contract
registration and a bundled research-structure instance are not claimed.
Only five new deliverable files are added; existing modules are unchanged.

## 4. Commands and results

All Lean commands sourced scripts/lean-env.sh, ran from verification/, and
used LEAN_NUM_THREADS=6.

- lake build NSFormalization.Section4.R43.Universal: exit 0; no new warnings,
  but Lake replays existing dependency warnings, so aggregate output is not silent.
- lake env lean ../formalization/NSFormalization/Section4/R43/Universal.lean:
  exit 0, exactly zero bytes of output.
- lake env lean ../research/R43/axioms_universal.lean: exit 0; 13 exact audits
  and both examples pass.
- make check: exit 0, including 30-work-item consistency.
- lake test (make test recipe from verification/): exit 0.
- make test-mutations: exit 0, all three prohibited mutations rejected.
- Exact statement token comparison, audit-output verification, forbidden-proof
  scan, and git diff --check: pass.

Committed on erenup/225-R43-universal; no push, merge, or rebase.
