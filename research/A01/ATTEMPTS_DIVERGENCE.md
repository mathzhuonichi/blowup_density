# Lane 163: reverse cylinder divergence descent

## Theorem proved by this lane

`A01/ConstructorDivergence.lean` derives ordinary solenoidality of an unrestricted
ordinary L2 carrier U from the actual cylinder constraint
`ordinaryLift U ∈ divergenceFreeSpace 1 1 0`. It then derives pointwise spatial
divergence zero for any actual smooth representative agreeing almost everywhere
with U. The time-path consumer takes exactly the local theory's `u`, `U`, lift
compatibility, and cylinder divergence conclusions.

The reverse carrier bridge assumes no smoothness, angular invariance, derivative
order, or prior ordinary solenoidality. `EulerMeanSolenoidal.L2` is unrestricted
`Lp Space 2 volume`; its name is not used as evidence of solenoidality.

## Mathematical route and existing support

The previous lane's read-only survey identified lifting compact scalar tests as
the next proof. A more precise source search found that this analytic core is
already proved in `Euler/CylinderGradientEmbedding.lean`:

- `scalarLift_compact`: compact support of `φ ∘ Prod.fst`, using the compact circle.
- `scalarLift_smooth` and `scalarLift_gradient`: smooth local lifts and the actual
  chain-rule identity for lifted gradients.
- `embedding_gradient_mem`: the continuous embedding carries the closed ordinary
  gradient space to the cylinder gradient space, via the real test generators
  and closure. At period=1 and κ=1, this is exactly the required inclusion.

The only carrier alignment needed is equality of that `embedding 1` and
`ordinaryLift`. Both have the same a.e. representative `z ↦ U z.1`; Lp extensionality
proves their equality. The cylinder orthogonality condition can then be applied
to the lift of every ordinary gradient and pulled back by the isometry's inner
product identity. This proves membership in the ordinary gradient orthogonal
complement, with no distributional placeholder.

Finally `EulerMeanClassical.solenoidal_representative_divergence` supplies the
already proved weak-test, a.e., and continuity upgrade for a genuine smooth field.
The final path lemma uses `divergence_eq_coordinate_sum` to match the actual
`NavierStokes.ProblemStatement.spatialDivergence` vocabulary of A02 c6.

## Outputs and remaining obligations

Six exports: `ordinaryLift_eq_embedding`, `ordinaryLift_gradient_mem`,
`solenoidal_of_ordinaryLift`, `divergence_eq_zero_of_ordinaryLift`,
`solenoidal_path_of_cylinder`, `spatialDivergence_eq_zero_of_cylinder`.

The first four are per-carrier statements. The final two consume the existing
local-theory path conclusions on Icc 0 S. The pointwise result additionally takes
the actual smooth slice and a.e. handoff; it does not construct B1's joint smooth
velocity. It does not extend the interval beyond S, prove a classical constructor,
or address pressure, momentum, and force/datum input-output links.

## Validation

The assigned Luna `wave3_compile` agent is checking the new module and
`research/A01/axioms_constructor_divergence.lean`. That probe prints all six
export axioms, instantiates q=6 on a nonempty zero-carrier slab, and invokes the
actual `localTheory_on_prescribed_horizon` to obtain a continuous ordinary
solenoidal path with the true initial ordinary datum. No ordinary solenoidal
hypothesis is added to that consumer. This author runs no Lean commands.
The first module build succeeded without source changes:
`tmp/build_163_ConstructorDivergence.log` reports 9986 jobs and a successful
87-second target build. The first probe log
`tmp/probe_163_axioms_constructor_divergence.log` reports only the standard three
axioms for all six source exports and the zero-carrier pointwise consumer.
Its real local-theory consumer initially omitted the open namespace
`EulerMeanSmoothRepresentative`, so `ordinarySobolev` was unresolved. That probe-only
namespace omission is fixed; the assigned Luna compiler is rerunning the probe.
No mathematical statement or source proof changed in response to that error.

## Final verification

The root agent confirmed the assigned Luna compiler's actual corrected probe
exit code is 0. I read `tmp/probe_163_axioms_constructor_divergence_r2.log`:
all six source exports, the q=6 zero-carrier consumer, and the actual
`localTheory_on_prescribed_horizon` consumer depend only on `propext`,
`Classical.choice`, and `Quot.sound`; no errors remain. The original module build
also succeeded. No Lean command was run by this author, and no module-source
revision was needed after the first build.

Source-level checks confirmed both new Lean files are UTF-8 without BOM, use LF,
and end with one newline. `git diff --check` passed. Broader contract and mutation
checks are handled separately by the root and assigned compiler.
