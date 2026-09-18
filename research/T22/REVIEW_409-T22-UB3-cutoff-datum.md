ACCEPT

## What the lane claims

The worker report claims the two U-B3 targets with the neighbourhood clause in filter form:
`exists_cutoff` has `IsOpen Ω`, `IsCompact K`, and `K ⊆ Ω`, and returns a smooth,
compactly supported real cutoff with `tsupport χ ⊆ Ω` and
`∀ᶠ x in 𝓝ˢ K, χ x = 1` (`research/T22/REPORT_409.md:11-28`).  It also claims the
explicit-open-set wrapper `exists_cutoff_isOpen` (`research/T22/REPORT_409.md:19-28`).

For (b), the report claims `isCutoffDatum_realizes_zeroExtension` with smoothness and
compact support of `χ`, support containment, the neighbourhood-one condition, the
`IsCutoffDatum` graph, the restriction equality, and support of the zero extension
(`research/T22/REPORT_409.md:30-49`).  The added `ContDiff` and `HasCompactSupport`
hypotheses are explicit and load-bearing for the Schwartz multiplier/domain-test step;
they are not hidden vacuity hypotheses, and U-Z1 supplies them from (a).

The mathematical target matches the paper's compact-support cutoff route: the paper
requires `K ⊂⊂ Ω`, a cutoff in `C_c^∞(Ω)` equal to one near `K`, and uses multiplication
to identify the zero extension (`paper/sections/03-torus.tex:608-624`).  The split's
registered U-B3 target and status record the same filter/open-set forms and the same
extra hypotheses (`research/T22/T22_SPLIT.md:95-103`, `research/T22/T22_SPLIT.md:194-211`).

## What is in Lean

The declarations are exactly present in the new module.  `exists_cutoff` is stated at
`formalization/NSFormalization/Section3/T22/CutoffDatum.lean:65-67`, and its proof uses
`exists_compact_between`, the smooth manifold Urysohn lemma, and the compact support
closure (`:68-80`).  The explicit wrapper is at `:83-89`.  The second theorem's exact
binders and conclusion are at `:97-104`; its proof constructs the Schwartz multiplier
and proves the pointwise identity before changing the set integral to a whole-space
integral (`:105-159`).

The hypotheses are all isolated and consumed: `hχs`/`hχc` establish temperate growth and
compact support (`:106-110`, `:127-128`), `hχΩ` supplies the domain support (`:126`,
`:135-151`), `hχ1` is used on the zero-extension support (`:133-139`), and `hcut`, `hA`,
and `hsupp` are used in the final calculation (`:152-159`, `:133-140`).  There is no
`⊤.toReal`, empty-interval, or otherwise vacuous side condition.

The definitions consumed by the proof agree with the cited tree: `DomainTest`,
`restrictDatum`, `restrictField`, `zeroExtension`, and `IsCutoffDatum` are exactly the
objects at `formalization/NSFormalization/Section3/T22/Domain.lean:25-56`; the restriction
bridge is `RestrictBridge.lean:25-44`; the general datum restriction bridge is
`OrderZero.lean:194-203`; and `IsSobolevDatum` is the direct whole-space pairing at
`formalization/NSFormalization/Section4/D01/SmoothDatum.lean:233-239`.  Thus there is no
missing pairing bridge being silently assumed.

The worker's Mathlib citations were checked at the cited declarations: compact
containment (`verification/.lake/packages/mathlib/Mathlib/Topology/Compactness/LocallyCompact.lean:172`),
the smooth cutoff (`.../Geometry/Manifold/PartitionOfUnity.lean:525-531`),
`contMDiff_iff_contDiff` (`.../Geometry/Manifold/ContMDiff/NormedSpace.lean:67-70`),
compact-support temperate growth (`.../Analysis/Distribution/TemperateGrowth.lean:121-126`),
and pointwise Schwartz multiplication (`.../Analysis/Distribution/SchwartzSpace/Basic.lean:747-751`)
all match the route in `research/T22/ATTEMPTS_UB3.md:8-47`.

## Gaps and negative checks

No U-B3 gap remains.  The report's old failed-API discussion is explicitly marked
superseded, while the current route and the U-Z1 handover caveat are stated at
`research/T22/REPORT_409.md:77-94`.  I grepped the whole Section4 tree for the two
reported missing names (`exists_smooth_tsupport_subset` and
`exists_contDiff_one_nhds_of_subset`) and found no matches; the direct `IsSobolevDatum`
definition and existing bridge cited above are present.

The substantive mutation probe changes the cutoff constant from `1` to `2` in
`research/T22/probes/rev409_mutation_constant.lean:15-18`.  Running it fails as expected
with:

```text
../research/T22/probes/rev409_mutation_constant.lean:18:2: error: Type mismatch: After simplification, term
  exists_cutoff hΩ hK hKΩ
 has type
  ∃ χ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ω ∧ ∀ᶠ (x : Space) in 𝓝ˢ K, χ x = 1
but is expected to have type
  ∃ χ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ Ω ∧ ∀ᶠ (x : Space) in 𝓝ˢ K, χ x = 2
```

For non-vacuity, `research/T22/probes/rev409_nonvacuity.lean:17-22` proves the concrete
`ball 0 1`/`closedBall 0 (1/2)` geometry, and `:34-44` chooses the actual cutoff from
`exists_cutoff` and closes (b) for the zero field and zero datum without externally
assuming any cutoff properties.  This probe typechecks.

## Commands and results

All Lean commands were run after `. ../scripts/lean-env.sh`, from `verification/`, with
`LEAN_NUM_THREADS=6` for the build.  The required results were:

```text
$ LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T22.CutoffDatum
exit=0
Build completed successfully (9874 jobs).

$ lake env lean ../formalization/NSFormalization/Section3/T22/CutoffDatum.lean
(no output; exit 0)

$ lake env lean ../research/T22/probes/cutoff_datum_closes.lean
(no output; exit 0)

$ lake env lean ../research/T22/probes/rev409_nonvacuity.lean
(no output; exit 0)

$ lake env lean ../research/T22/axioms_ub3.lean
'NSFormalization.Section3.T22.exists_cutoff' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.exists_cutoff_isOpen' depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section3.T22.isCutoffDatum_realizes_zeroExtension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

The build replayed pre-existing dependency linter diagnostics, but the new module itself
produced no warning and the build exited 0.  `make check` also exited 0; its exact terminal
summary was:

```text
"source_hashes_match": false
Explicit axiom/admission tokens, all copied sources: 11
.............
Ran 13 tests in 0.042s
OK
45 work items: ownership, contract registration and task cards consistent.
```

The `source_hashes_match: false` and copied-source admission count are pre-existing
architecture diagnostics (the output names `Paper1.BoundaryCorollary:90`); they are not
files changed by this lane.  `git diff --name-only origin/erenup/integration-section3...HEAD`
was empty because this lane commit is already reachable from the current integration ref;
`git diff --name-only HEAD^..HEAD` lists only the new U-B3 module and its research/record
files, so no existing module was modified.  No `maxHeartbeats` declaration is
present in the lane module or probes.  `verification/` was untouched, so the conditional
`scripts/gates.sh` and `check_contracts.py --base-ref origin/erenup/integration-section3`
gate was not applicable.

The forbidden-token scan found no code-level `sorry`, `admit`, `axiom`, or `native_decide`
declaration in the module or probes; the textual matches are only the module's prohibition
comment and the `#print axioms` audit names (`formalization/NSFormalization/Section3/T22/CutoffDatum.lean:44-45`,
`research/T22/axioms_ub3.lean:10-12`).
