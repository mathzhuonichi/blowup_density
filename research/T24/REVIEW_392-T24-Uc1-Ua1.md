ACCEPT-WITH-NOTES

## 1. What the lane claims

The worker claims exactly Uc1 and Ua1: conservative forcing from rest gives
zero velocity on `[0,T)`, and the five elementary affine fields are radius
positivity, the strict time window, zero initial velocity, late agreement, and
injectivity (`research/T24/REPORT_392.md:5`, `research/T24/REPORT_392.md:9`).

The claim is faithful to the sources.  The paper states the affine construction
and its zero-initial/late-agreement/injectivity consequences at
`paper/sections/03-torus.tex:668-687`, and states conservative zero-from-rest on
the classical lifespan at `paper/sections/03-torus.tex:723-738`.  The exact Spec
fields are `radius_pos` and `window` at `research/T24/Spec.lean:1014` and
`research/T24/Spec.lean:1019`, `zero_initial` at
`research/T24/Spec.lean:1055`, `late_agreement` at
`research/T24/Spec.lean:1061`, `distinct` at
`research/T24/Spec.lean:1091`, and `zero_from_rest` at
`research/T24/Spec.lean:1408`.

The worker's remaining-gap claim is also scoped correctly: it lists Uc2 and
Ua2--Ua8 without pretending that this lane assembled either API
(`research/T24/REPORT_392.md:27`).  No theorem outside Uc1/Ua1 is claimed.

One hygiene note remains.  The mathematical definitions are correct, but three
docstring citations are one line late relative to the numbered TeX source:

1. At `formalization/NSFormalization/Section3/T24/AffineBasics.lean:25`, change
   `03-torus.tex:672-673` to `03-torus.tex:671`.
2. At `formalization/NSFormalization/Section3/T24/AffineBasics.lean:31`, change
   `03-torus.tex:674` to `03-torus.tex:673`.
3. At `formalization/NSFormalization/Section3/T24/AffineBasics.lean:35`, change
   `03-torus.tex:674` to `03-torus.tex:673`.

## 2. What is in Lean

The canonical potential and force definitions at
`formalization/NSFormalization/Section3/T24/Conservative.lean:28` and
`formalization/NSFormalization/Section3/T24/Conservative.lean:33` are
token-for-token the Spec bodies at `research/T24/Spec.lean:1367` and
`research/T24/Spec.lean:1372`.  The theorem at
`formalization/NSFormalization/Section3/T24/Conservative.lean:37` has the exact
quantifier order, positivity guards, force, half-open interval, and pointwise
conclusion of `research/T24/Spec.lean:1408`.  Its proof honestly transfers all
relevant solution fields at
`formalization/NSFormalization/Section3/T24/Conservative.lean:43` into the cited
tree theorem `zero_of_negative_gradient_on_Ico`, whose hypotheses and conclusion
are visible at
`formalization/NSFormalization/Paper1/ConservativeForce.lean:91`.  In
particular, the solution class really constrains smoothness on `[0,T)`, initial
data, divergence, momentum, and periodicity
(`formalization/NSFormalization/Section3/T10/PeriodicData.lean:265`), while the
residual and periodicity spelling bridges are definitional
(`formalization/NSFormalization/Section3/T11/FlowConversion.lean:28`,
`formalization/NSFormalization/Section3/T11/FlowConversion.lean:35`).  The named
`hT` premise is redundant with `S.horizon_pos`, but it is required verbatim by
the Spec and does not make the statement vacuous.

The affine vocabulary at
`formalization/NSFormalization/Section3/T24/AffineBasics.lean:22`--`51` has the
same bodies as the Spec.  The five theorems at
`formalization/NSFormalization/Section3/T24/AffineBasics.lean:54`, `:58`, `:64`,
`:78`, and `:93` have exactly the corresponding field conclusions once the
outer `affineVariationStatement` parameter hypotheses and the packet's raw
`zero_initial_velocity` clause are exposed.  The support arguments use the
strict `Ioo τ₀ τ₁` cylinder, so neither an empty time interval nor an
extended-real junk value is involved.  The two admissibility arguments in
`distinct` are intentionally unused because translation is injective on the
larger class of all fields; this strengthens, rather than weakens, the requested
restricted statement (`formalization/NSFormalization/Section3/T24/AffineBasics.lean:97`).

The conformance probe proves the three affine vocabulary copies by `rfl` at
`research/T24/probes/uc1_ua1_closes.lean:39`, converts the distinct contract
solution structure fieldwise at `research/T24/probes/uc1_ua1_closes.lean:54`,
and closes all five affine fields using the registered packet at
`research/T24/probes/uc1_ua1_closes.lean:71`.  The conversion used there is the
honest fieldwise `ofContract` at
`verification/Bindings/TorusLocalTheory.lean:217`; packet operator bridges are
likewise `rfl`, for example `verification/Bindings/Packet.lean:40`--`70`.

Non-vacuity is witnessed by a concrete positive cylinder with
`(τ₀,τ₁)=(1/4,3/4)` and the zero smooth compactly supported
divergence-free perturbation
(`research/T24/probes/rev392_nonvacuity.lean:12`); its strict window is proved at
`research/T24/probes/rev392_nonvacuity.lean:21`.  This probe compiles with zero
output.

The substantive negative mutation widens the main conservative conclusion from
`Ico 0 T` to `Icc 0 T` at
`research/T24/probes/rev392_widened_interval.lean:15`.  The production proof
then fails exactly because the endpoint is unsupported:

```text
../research/T24/probes/rev392_widened_interval.lean:21:42: error: Application type mismatch: The argument
  ht
has type
  t ∈ Icc 0 T
but is expected to have type
  t ∈ Ico 0 T
in the application
  zero_from_rest ν hν T hT φ hφ S t ht
```

## 3. Gaps

The lane is intentionally partial: Uc2 `potential_pairing` and affine Ua2--Ua8
remain, exactly as the worker records at `research/T24/REPORT_392.md:29`.  A
whole-tree search of `formalization/NSFormalization/Section4` for declarations
named `potential_pairing`, `divergence_free`, `momentum`, `force_smooth`,
`force_support`, `speed_unbounded`, `energy_finite`, `infinite_dimensional`, or
`nonisolated` returned no matches.  A broader conceptual search returned only
the following unrelated existing facts, not any missing T24 field:

```text
formalization/NSFormalization/Section4/R42/Assembly.lean:188:  rw [hassoc, NavierStokes.ResidualCalculus.spatialDivergence_add v (fun z => w z + U z) t x
formalization/NSFormalization/Section4/A01/ConvectionDivergence.lean:32:* `convectionDivergence_eq_advection_add_smul_div`: the general Leibniz identity
formalization/NSFormalization/Section4/A01/ConvectionDivergence.lean:92:theorem convectionDivergence_eq_advection_add_smul_div
formalization/NSFormalization/Section4/A01/ConvectionDivergence.lean:118:  rw [convectionDivergence_eq_advection_add_smul_div u t x hu, hdiv, zero_smul, add_zero]
formalization/NSFormalization/Section4/A01/LerayBridge.lean:212:  exact (divergenceFreeSpace 1 1 0).add_mem
```

Thus the worker's gap statement is accepted.  The only required fixes are the
three one-line citation corrections listed in part 1; there is no proof or
statement fix.

## 4. Commands and results

Environment preparation succeeded with Lean `v4.34.0-rc2`; `lake test` ended
with exact terminal line `== OK` and exit code 0.  All Lake commands below were
run from `verification/` after sourcing `scripts/lean-env.sh`, with
`LEAN_NUM_THREADS=6` on the build.

`lake build NSFormalization.Section3.T24.Conservative NSFormalization.Section3.T24.AffineBasics`
returned exit code 0.  It replayed pre-existing warnings from dependencies, but
none named either T24 module; its exact terminal line was:

```text
Build completed successfully (9928 jobs).
```

Each of these returned exit code 0 and exactly zero output:

```text
lake env lean ../formalization/NSFormalization/Section3/T24/Conservative.lean
lake env lean ../formalization/NSFormalization/Section3/T24/AffineBasics.lean
lake env lean ../research/T24/probes/uc1_ua1_closes.lean
lake env lean ../research/T24/probes/rev392_nonvacuity.lean
```

`lake env lean ../research/T24/axioms_uc1_ua1.lean` returned exit code 0 with
exact output:

```text
'NSFormalization.Section3.T24.PeriodicPotentialT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.conservativeForceT' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.zero_from_rest' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.affineCylinder' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.AffineAdmissible' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.affineVelocity' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.affinePressure' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.crossAdvection' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.affineForce' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.affineCkSeminorm' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.radius_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.window' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.zero_initial' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.late_agreement' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T24.distinct' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`make check` returned exit code 0.  Because its JSON closure dump is very large,
the exact terminal output is reproduced here:

```text
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.046s

OK
python3 experiments/check_work_queue.py
45 work items: ownership, contract registration and task cards consistent.
```

The forbidden-token scan over both modules, the shipped probe, and the axiom
file returned no output for `sorry`, `admit`, declaration-level `axiom`, or
`native_decide`; the `maxHeartbeats` scan also returned no output.  The formal
modules have no `Contracts.*` import.  `git diff --check
origin/erenup/integration-section3...HEAD` returned no output.  The exact
committed diff-name result was:

```text
A formalization/NSFormalization/Section3/T24/AffineBasics.lean
A formalization/NSFormalization/Section3/T24/Conservative.lean
A research/T24/ATTEMPTS_UC1_UA1.md
A research/T24/REPORT_392.md
M research/T24/T24_SPLIT.md
A research/T24/axioms_uc1_ua1.lean
A research/T24/probes/uc1_ua1_closes.lean
```

Thus no pre-existing Lean module was modified.  No path under `verification/`
was touched (the corresponding diff command returned zero lines), so the
conditional `scripts/gates.sh` and
`check_contracts.py --base-ref origin/erenup/integration-section3` gates do not
apply to this lane.
