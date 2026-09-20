# Lane 225 — companion to COMPARISON.md

## Statement fidelity

The exact field at Spec.lean:211–218 is copied below, including the field name:

```lean
  universal :
    ∀ ν : ℝ, 0 < ν →
      ∀ a : SpatialField, a ∈ initialClassR →
        ∀ f : SpaceTimeField, MemForceR f →
          dotHomogeneousENorm (1 / 2) a + forceHomogeneousENorm 1 (1 / 2) f
              < ENNReal.ofReal (c * ν) →
            maximalLifespanR ν a f = ⊤
```

Universal.lean proves this type with the sole substitution
`c := criticalConst`. The constant is the same positive, viscosity-independent
minimum as lane 223:

```lean
min (1 / (8 * trilinearConst))
  (1 / (4 * (A05.gradientL6Const * A05.criticalL3Const)))
```

There is no discrepancy or re-cut. The conclusion is infinite lifespan, not a
finite-horizon lower bound. Smallness is strict, in ENNReal, with the datum
infimum homogeneous spatial norm and the global homogeneous force norm.
Paper 04-whole-space.tex:83–88 states this conclusion and its zero-datum
inhomogeneous consequence. Lines 100–104 give the bootstrap; lines 125–132
give the budget and continuation. The audit repeats the physical-field
definition verbatim (qualifying SpatialField to disambiguate namespaces),
proves its definitional equality, and checks the theorem using Data objects
and the existing maximal-lifespan bridge.

## General initial energy

C01 V4 EnergyAbsorption.lean:83–95 already registers the general H² budget.
Bindings/EnergyAbsorptionV4.lean:31–34 binds it to C01.h2TimeIntegral.
The initial contribution is exactly `32 * ν⁻¹ * gradientSq a`, and the
low-frequency contribution is
`32 * S * energyBudget a f S ^ 2`, where the budget includes the initial L²
norm. No initial term is discarded or replaced by a zero-datum estimate.
MaximalEndpoint.lean:15–40 supplies the same terminal-S budget to every
shorter interval; thus equality S=T_max is included without evaluating u(S).

The new scalar wrapper uses C01.sqrt_energy_le_primitive' and
Paper1.continuous_bootstrap, with N(t)=y(0)+criticalForcePrimitive f t,
ρ=cν, and K=ν/(2*trilinearConst). Projection onto [0,S] only extends the
scalar norm for the continuity lemma; no solution or force is extended.
The conversion from ENNReal proves initial-norm finiteness before using
ofReal_toReal. The final statement contains no toReal.

## API status

| RCritical1API field | Status |
|---|---|
| c | Endpoint.criticalConst |
| hc | Endpoint.criticalConst_pos |
| universal | Universal.universal_of_memForceR, this lane |
| inhomogeneousAtZero | Endpoint.inhomogeneousAtZero_of_memForceR, lane 223 |

All four components are now supplied with the same constant. This lane does
not register a new contract or modify the research spec. There is no remaining
named analytic hypothesis. The audit specializes universal to recover the
inhomogeneous zero-datum theorem and proves the actual smallness at a=f=0.
