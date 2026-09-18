# ClassicalAssembly — lane 320 attempts

## Scope and searches

Read the binding split/reconciliation, implementation candidates, lane 318 report and
EXISTENCE_ROUTE's nonintegrable-kernel caution. In this checkout FourierCalculus is
present; ForcePaths and lane 319 persistence are absent. No other worktree was used.
The required `grep -rn` covered `Paper1/Periodic*.lean`, `Section3/`,
`Section4/{A01,A02,A04,D01}`, and `vendor/HeliCorgi/Formal/`; matches are in
`tmp/320/search.txt`. This was a declaration search, not a proof of nonexistence.
Existing pressure symbol operators are coefficient Poisson algebra; pressure flow
bridges take an existing flow. Neither was used as unconditional physical recovery.

## Exact sole named input

```lean
def PersistenceInput (T : ℝ) (u : ℝ → PeriodicSobolev 3) : Prop :=
  ∀ m : ℕ, ∃ u_m : ℝ → PeriodicSobolev (m : ℝ),
    ContinuousOn u_m (Ico 0 T) ∧
      ∀ t ∈ Ico 0 T, ∀ i k,
        torusPhysicalCoeff (m : ℝ) (u_m t) i k = torusPhysicalCoeff 3 (u t) i k
```

This is pointwise U9d1 persistence for the supplied u on the original horizon;
all other U9d data are irrelevant to the predicate itself. Equality is of unweighted
coefficients, equivalent to IsPeriodicReweight by a proved lemma. ContinuousOn is
not replaced by ContDiffOn. No second analytic input is introduced.
Non-vacuity: classicalAssembly_nonzero proves this predicate together with actual
mild semantics and full classical recovery at nonzero velocity AND nonzero force.
persistence_of_classicalSolutionT also proves necessity for every existing classical
solution with the specified H³ datum path.

## Successful routes

1. Inverse-weight multiplication and Real.rpow_add prove the exact reweight bridge.
2. The datum at natural order 2*N+3, viewed only for algebra on the common carrier,
   satisfies physicalCoeff 3 G = W^N physicalCoeff 3 u. The equality is proved
   explicitly before reusing H³ summability: no phantom cast is taken as an estimate.
3. Induct on the derivative order of exp(periodicPhase k x). The Fréchet derivative
   is character times the phase CLM; bounded CLM composition propagates the norm
   bound. The finite phase sum gives ‖phase‖ ≤ 3 W. contDiff_tsum yields spatial C∞.
4. Complexified physical divergence equals the sum of scalar spatial partials.
   Fourier differentiation and finite-sum integration give the weighted trace symbol;
   smooth periodic inversion proves both directions of physical/coefficient divergence.
5. Mode divergence is a real CLM. Bochner interval-integral commutation uses the
   existing mild integrability fields. Heat scalar multipliers, the exact contract's
   bilinear symbol, and endpoint-safe smoothing preserve the solenoidal constraint.
   At nonpositive elapsed time the actual smoothing branch is zero.
6. The canonical Section4 convection identity gives the exact projected field from
   an existing ClassicalSolutionT. This lemma never supplies the missing solution.

## Compiler failures and repairs

Actual logs: tmp/320/direct*.log and build.log. Selected exact error text:

```text
Unknown constant `ContinuousLinearMap.norm_smulRight_le`
(deterministic) timeout at `whnf`, maximum number of heartbeats (400000) has been reached
unexpected token 'set_option'; expected 'lemma'
failed to synthesize instance of type class LE Type
The target expression is not type-correct under the `implicit` transparency level
```

The smulRight norm estimate was proved directly by opNorm_le_bound; omitting that
lemma's explicit operator argument caused costly unification and the timeouts.
Only two declaration-local 400000 heartbeat settings remain, both commented.
The set_option parser error was a doc-comment placement error; the doc comment now
follows the local setting. NNReal scope fixes ℝ≥0 notation. Explicit ℝ on
EuclideanSpace.proj fixes scalar inference. An explicit ContDiff ℝ ∞ intermediate
fixes the unconstrained derivative order. Fourier rewrite failures through the
lp carrier were repaired with typed calc equalities / congrArg₂, without disabling
instance checks. The final module has no warnings or incomplete proofs.

## Remaining analysis — not a compiler error

The general existential target is NOT proved, even assuming PersistenceInput.
The remaining steps are time regularity of all datum paths, joint smoothness up to
zero, physical pressure with its gradient/gauge/Poisson identities, and momentum.
Interior FTC alone does not discharge Ico smoothness. A proof using a naive two-order
heat gain would encounter the documented (t-s)^(-1) nonintegrable bound; this lane
uses no such argument. No unsatisfiable or whole-target peeling premise is supplied
to hide these gaps. The requested full closure probe therefore cannot be provided;
the named probe explicitly tests only the delivered fields and the nonzero family.
See REPORT_320.md for the exact unchanged target, all files, and gate results.
