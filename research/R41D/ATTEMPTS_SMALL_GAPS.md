# R41D G2--G5 attempts and closure record (lane 234)

## 1. Pre-proof repository audit

The required searches were run before adding the module, over
`formalization/NSFormalization/Section4/{D01,R41,R45}`,
`verification/Contracts/V1/{Data,DatumLemmas}.lean`,
`verification/Bindings/`, and `research/R45/` (which exists).  The search terms
included `MemForceRapid`, `forceClassRapid`, `MemForceCompact`,
`initialClassSchwartz`, and the zero-force `forceSobolevENorm` spellings.

No later lane had proved G2, G3, G4, or G5.  In particular,
`Contracts/V1/DatumLemmas.lean` provides the compact-to-ambient and ambient
compact-difference interfaces, but deliberately leaves the rapid class alone.
The zero ambient-force witness in `Section4/A04/ZeroSolution.lean` is useful
context, but it does not prove the rapid inclusion or the norm-infimum fact.

The definitions were then checked directly at `Contracts/V1/Data.lean:225-236`
and `:509-578`, against the local D01/A02 restatements and the paper passages
`02-preliminaries.tex:20-60` and `04-whole-space.tex:190-200`.  All four requested
statements are satisfiable as written; no discrepancy record is needed.

## 2. G2: rapid force to ambient force

The unsuccessful short route was to treat the inclusion as a purely pointwise
decay fact.  `MemForceR` contains more structure: for every integer order it
requires a smooth Banach-valued Sobolev datum path and both time `L¹` and `L²`
membership.  Those clauses cannot be discharged just by unfolding definitions.

The completed route in `Section4/R41/ClassFacts.lean` is:

1. Take every future-time normal derivative of the rapid force and show each
   spatial slice is a Schwartz map.
2. Bundle all spatial jets in `L²`, prove their time continuity by dominated
   convergence, and prove normal differentiation in `L²`.
3. Define the canonical order-`m` angular datum path `rapidDatum`.  Smoothness
   is lifted from order zero through the injective lowering map, using the
   existing injective-path derivative theorem.
4. Select one scalar polynomial decay belonging to both time `L¹` and `L²`.
   The rapid seminorm bounds separate into this time factor and an `L²_x`
   spatial factor, giving a bound for each jet path.
5. Apply `C01.norm_smoothAngularDatum_sub_sq_le` against the zero smooth field.
   The resulting finite jet sum bounds the datum norm by the same scalar time
   decay.  `MemLp.mono'` supplies both required time integrability clauses.
6. Assemble `D01.MemForceR` with `rapidDatum hf m 0` at each order `m`.

This yields both `memForceR_of_memForceRapid` and
`forceClassRapid_subset_forceClassR`.

## 3. G3--G5

- G3: compact spacetime support gives a compact common spatial projection and
  a finite future-time cutoff.  The existing compact-spatial decay estimate
  then proves `memForceRapid_of_memForceCompact`.  Rapid estimates are stable
  under addition, so `g + (f-g) = f` closes the requested correction lemma.
- G4: a real vector-valued Schwartz map is split into three complex Schwartz
  components.  `B01.spatialDatum_isSobolevDatum` supplies a datum at every
  integer order, while the solenoidal clause is retained unchanged.
- G5: the constant zero datum path is admissible and strongly measurable, so
  it is an explicit zero competitor in the defining infimum.  This proves the
  norm is zero for every time exponent `q`, hence also for `q = 1` or `q = 2`.
  `sub_self_force` records the accompanying pointwise identity.

## 4. Conformance and trust audit

`research/R41D/axioms_class_facts.lean` contains `rfl` bridges for the local and
`Contracts.V1.Data` spellings of the rapid, ambient, compact, Schwartz, and norm
definitions.  It restates G2--G5 in contract vocabulary and includes zero
non-vacuity examples.  Every audited local and contract-facing result reports
exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, `axiom`, or `native_decide` is used.

## Lead correction (review 234, 2026-09-17)

G5 (`forceSobolevENorm q s 0 = 0`) already existed on integration as lane 235's lemma in `verification/Bindings/DensityFromInsertion.lean:16-27`; only G2–G4 were genuinely absent. `ClassFacts.lean`'s G5 proof stands as the `formalization/`-side (local-vocabulary) version.
