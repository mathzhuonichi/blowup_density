REJECT

## 1. What the lane claims

The revised report claims a genuine, non-identity construction: the coefficient
potential is the Leray complement of the physical source, the pressure is its
scalar Fourier inversion, and the gauge, periodicity, gradient `MemLp`, spatial
slice smoothness, Poisson equation, canonical `F - Q` coefficient bridge, and
all-order scalar Sobolev membership are delivered
(`research/T11/REPORT_326.md:28-44`, `research/T11/REPORT_326.md:64-140`).
It explicitly leaves joint slab smoothness and joint continuity open
(`research/T11/REPORT_326.md:151-180`), which is an honest partial delivery:
the required `ClassicalSolutionT.pressure_smooth` field is the joint
`ContDiffOn` statement in `formalization/NSFormalization/Section3/T10/PeriodicData.lean:275-277`.
The mathematical target is the torus prescription
`Delta p = div f - sum_{i,j} partial_i partial_j (u_i u_j)` with zero mean
(`paper/sections/02-preliminaries.tex:84-88`), and the tree’s derivative/Leray
symbols are exactly `2*pi*i*k_j` and the zero-mode identity/nonzero-mode
projection (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:184-202`).

## 2. What is in Lean

The claimed construction is real. `lerayPotentialCoeff` sets the zero mode to
zero and uses the nonzero-mode quotient by
`(2*pi*i) * sum_j k_j^2` (`formalization/NSFormalization/Section3/T11/MildPressure.lean:157-163`),
and `mildPressureCoeff`/`mildPressure` actually build from that source and
series rather than aliasing an input pressure
(`formalization/NSFormalization/Section3/T11/MildPressure.lean:644-656`).
The Leray-complement identity has an explicit source datum, order, and
`k != 0` hypothesis (`formalization/NSFormalization/Section3/T11/MildPressure.lean:267-292`).

The pressure-field theorems have the advertised shapes: spatial slice
`ContDiff`, periodicity, zero-mean gauge, and the exact gradient `MemLp` field
are at `formalization/NSFormalization/Section3/T11/MildPressure.lean:658-689`,
and the Poisson theorem matches `PeriodicLocalRegularity.pressure_poisson`
(`formalization/NSFormalization/Section3/T11/LocalTheory.lean:79-92`) at
`formalization/NSFormalization/Section3/T11/MildPressure.lean:699-738`.
The new convolution theorem and its convection identification are stated
with smooth periodic hypotheses and the expected infinite convolution
(`formalization/NSFormalization/Section3/T11/MildPressure.lean:831-877` and
`formalization/NSFormalization/Section3/T11/MildPressure.lean:958-1004`).
The exact canonical `F - Q` statement and the Leray form are present at
`formalization/NSFormalization/Section3/T11/MildPressure.lean:1037-1101`.
The all-order scalar datum and `MemPeriodicHmScalar` exports are present at
`formalization/NSFormalization/Section3/T11/MildPressure.lean:1148-1171`, and
the bundle is a conclusion with genuine fields, not a target-repackaging
input (`formalization/NSFormalization/Section3/T11/MildPressure.lean:1179-1219`).
The nonzero witness is a real one-mode pressure instance
(`formalization/NSFormalization/Section3/T11/MildPressure.lean:1223-1386`),
so the delivered pressure package is not certified only over an empty interval.

## 3. Gaps

1. **Blocking gate: the axiom audit does not audit every module declaration and
   the omitted declarations fail the required exact list.** The module declares
   `testFrequency` and `testFrequency_ne_neg`
   (`formalization/NSFormalization/Section3/T11/MildPressure.lean:1292-1303`),
   but `research/T11/axioms_mild_pressure.lean:7-14` deliberately excludes both.
   This is not an acceptable way to meet the lane requirement that every
   `#print axioms` be exactly `[propext, Classical.choice, Quot.sound]`.
   The independent scratch probe
   `research/T11/probes/rev326_axiom_exact.lean:3-5` prints exactly:

   ```text
   'NSFormalization.Section3.T11.mildPressure_fields' depends on axioms: [propext, Classical.choice, Quot.sound]
   'NSFormalization.Section3.T11.testFrequency' depends on axioms: [propext]
   'NSFormalization.Section3.T11.testFrequency_ne_neg' depends on axioms: [propext]
   ```

   Fix by making those declarations satisfy the required audit and adding them
   back to the guarded axiom file; merely omitting them or re-exhibiting them as
   unguarded examples does not satisfy the gate.

2. **Disclosed partial result (not a second hidden theorem):** the required
   joint pressure field remains unproved. `MildPressureFields` stores only
   spatial slice smoothness (`formalization/NSFormalization/Section3/T11/MildPressure.lean:1179-1206`),
   while `ClassicalSolutionT.pressure_smooth` is joint slab `ContDiffOn`
   (`formalization/NSFormalization/Section3/T10/PeriodicData.lean:265-277`).
   The report records this exact residual and the separate missing joint
   continuity (`research/T11/REPORT_326.md:151-176`); this is acceptable for a
   partial lane but must not be described as a completed `ClassicalSolutionT`
   pressure-smooth field.

Statement and hygiene checks otherwise pass: the only named input used by the
module is lane 320’s `PersistenceInput` (its exact definition is
`formalization/NSFormalization/Section3/T11/ClassicalAssembly.lean:25-30`),
the two local instances are explicitly named
(`formalization/NSFormalization/Section3/T11/MildPressure.lean:23-26`), and
the module has no `sorry`, `admit`, `axiom`, or `native_decide` tokens. The
required “not in the tree” search was repeated over the whole Section 4 tree
and the specified Paper1/Section3/Section4/vendor roots: no smooth-periodic
product Fourier-convolution theorem was found before this lane’s new theorem;
the nearest Paper1 hits are finite-support `FiniteFourier` convolution lemmas.

## 4. Commands and results

All Lean commands below were run after `. scripts/lean-env.sh`; `lake` was run
from `verification/` only. `verification/.lake/packages` is the shared symlink.

```text
cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.MildPressure
... dependency linter warnings replayed ...
Build completed successfully (9986 jobs).

cd verification && lake env lean ../formalization/NSFormalization/Section3/T11/MildPressure.lean
<empty output; exit 0>

cd verification && lake env lean ../research/T11/probes/mild_pressure_closes.lean
<empty output; exit 0>

cd verification && lake env lean ../research/T11/axioms_mild_pressure.lean
<empty output; exit 0 (the file uses #guard_msgs, and omits the two failing declarations)>

cd verification && lake env lean ../research/T11/probes/rev326_pressure_sign_mutation.lean
../research/T11/probes/rev326_pressure_sign_mutation.lean:21:2: error: Type mismatch
  mildPressure_poisson hg hgp hu
has type
  ∀ t ∈ Ico 0 T,
    ∀ (x : Space),
      scalarSpatialLaplacianT (mildPressure g u) t x =
        spatialDivergence g t x -
          spatialDivergence (fun z => convectionDivergenceT (torusPhysicalVelocity u) z.1 z.2) t x
but is expected to have type
  ∀ t ∈ Ico 0 T,
    ∀ (x : Space),
      scalarSpatialLaplacianT (mildPressure g u) t x =
        spatialDivergence g t x +
          spatialDivergence (fun z => convectionDivergenceT (torusPhysicalVelocity u) z.1 z.2) t x
exit 1 (substantive sign mutation; expected failure)

make check
... architecture JSON and contract-closure output ...
Ran 13 tests in 0.046s
OK
45 work items: ownership, contract registration and task cards consistent.
exit 0

make test
... dependency warnings and registered test infos ...
exit 0
```

The direct axiom probe exited 0 but exposes the blocking mismatch above. The
branch has no `verification/` changes
(`git diff --name-only origin/erenup/integration-section3...HEAD` lists only
the new `MildPressure.lean`, research records/probes, and this review file), so
the conditional `scripts/gates.sh` and
`python3 experiments/check_contracts.py --base-ref origin/erenup/integration-section3`
gate was not applicable and was not run.
