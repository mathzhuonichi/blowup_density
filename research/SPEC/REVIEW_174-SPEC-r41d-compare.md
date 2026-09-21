ACCEPT

## 1. What the lane claims

The lane claims a specification reconciliation, not a proof.  Its report says
that `Spec.lean` contains two definitions and one structure, with separate
`L¹_tH^s` and `L²_tH^s` density fields, the order
`∀ a, ∀ g, ∀ radius, ∃ f`, and an explicit two-case R42 witness
(`research/R41D/REPORT_174.md:3-18`).  This is accurate: there is no theorem or
lemma declaration in `Spec.lean`; the only declarations are
`IsR41DForceClass`, `R42InsertedWitness`, and `RDensityAPI`
(`research/R41D/Spec.lean:77-78,93-107,121-169`).

Clause-by-clause statement fidelity is accepted.

- The manuscript fixes `nu,T>0`, gives `s_q=2/q-3/2`, and states density for
  every fixed `a∈X_R` (`paper/sections/04-whole-space.tex:7-13`).  Both Lean
  fields retain `0<nu`, `0<T`, and `a∈initialClassR`; the latter is exactly
  the registered `H^∞∩L²_σ` class
  (`research/R41D/Spec.lean:135-147,157-169`;
  `verification/Contracts/V1/Data.lean:480-509`).
- The quantifier order is literally `nu,T,s,a,g,radius,f`, hence after the
  global parameters it is `∀ a, ∀ g, ∀ radius, ∃ f`; the witness may
  depend on the reference and radius but neither is chosen after it
  (`research/R41D/Spec.lean:136-147,158-169`).
- The thresholds are the exact strict specializations `s<1/2` and `s<-1/2`,
  with the correct sign in the L² branch
  (`research/R41D/Spec.lean:138,160`; paper line 13).  The distances use the
  registered full-time norms `forceSobolevENormL1` and
  `forceSobolevENormL2`, not `.toReal` or a finite-time surrogate
  (`research/R41D/Spec.lean:144,166`;
  `verification/Contracts/V1/Data.lean:215-236`).  Their time measure is
  `(0,∞)` (`verification/Contracts/V1/Data.lean:115-118`), as required by
  `paper/sections/01-introduction.tex:118-140`.
- The ambient selector permits exactly `F_R`, `F_c`, and `F_rd`
  (`research/R41D/Spec.lean:69-78`), whose registered definitions match the
  manuscript classes (`verification/Contracts/V1/Data.lean:518-578`;
  `paper/sections/04-whole-space.tex:182-195`).  The same `Y` occurs in both
  `g∈Y` and `breakdownSetIn Y`, so the topology and returned class cannot
  drift (`research/R41D/Spec.lean:140-144,162-166`).
- `breakdownSetIn` is exactly `{f | f∈Y ∧ T_max(nu,a,f)≤ofReal T}`
  (`verification/Contracts/V1/Data.lean:667-674`), matching
  `B^R_{nu,a,T}` (`paper/sections/02-preliminaries.tex:38-46`).  The registered
  lifespan is an `ENNReal` supremum: no solution gives `0`, while unbounded
  horizons give `⊤` (`verification/Contracts/V1/Data.lean:650-658`).
- The proof split is stated rather than left in prose.  The first arm says
  `T_max(a,g)≤T ∧ f=g`; the second says `T<T_max(a,g)` and retains one
  aligned R42 V2 family (`research/R41D/Spec.lean:145-147,167-169`).  This is
  exactly the split at `paper/sections/04-whole-space.tex:176-177`, including
  the equality case in the first branch.
- The inserted witness uses one `L` and one positive `epsilon`, aligns
  `family.a`, `.g`, `.T`, and `.force`, retains a positive margin and strict
  reference lifespan, requires the physical difference `f-g` to be compact,
  and fixes the inserted lifespan exactly at `T`
  (`research/R41D/Spec.lean:93-107`).  These are the clauses of Theorem 4.2
  (`paper/sections/04-whole-space.tex:31-43`).  The inherited record really
  contains `regular`, `referenceLifespan`, and `lifespan`
  (`verification/Contracts/V1/InsertionLifespan.lean:108-137`), while V2 adds
  the full-horizon solution, maximal identification, and displayed blow-up
  (`verification/Contracts/V2/InsertionLifespan.lean:117-158`).  The same base
  family carries initial data, closed-endpoint earlier history, compact force
  difference, energy rate, and force convergence
  (`verification/Contracts/V1/InsertionFamily.lean:196-226,259-266,304-327`).
  Thus the `[0,T)`/history endpoint choices are inherited faithfully rather
  than replaced by an `Icc 0 T` solution window.
- The rapid-decay instance deliberately retains the stronger theorem-wide
  assumption `a∈X_R`; the paper first says Theorem 4.1 remains valid for
  `F_rd` and then gives `a∈S_sigma` as an “in particular” case
  (`paper/sections/04-whole-space.tex:194-198`).  The missing inclusion
  `initialClassSchwartz ⊆ initialClassR` is isolated as G4, not silently
  assumed.

`COMPARISON.md` accounts for every semantic A/B difference: structure-level
versus field-level class parameterization, canonical versus expanded breakdown
membership, proof provenance, first/second branch evidence, same-family data,
and the named force-class selector (`research/R41D/COMPARISON.md:19-35`).  The
choices are justified by the cited manuscript lines.  Where both drafts agree,
I found no disagreement with the paper.  The stronger proof-provenance rider is
not forced by Theorem 4.1's extensional sentence alone, but it is explicitly
required by the R41D task and is supported by the proof at lines 176-177 and the
same-family assertion at lines 13 and 42-43.  Drafts A and B remain byte-for-byte
identical to their blind-lane versions (hashes respectively
`4ca1ccdae356f0cbd0df67151a66150d162bffcd` and
`ce1bdd3908b1bf1dbdf75f642352271a39093fb9`).

## 2. What is in Lean

The exact frozen surface is:

1. `IsR41DForceClass Y := Y=forceClassR ∨ Y=forceClassCompact ∨
   Y=forceClassRapid` (`research/R41D/Spec.lean:77-78`).
2. `R42InsertedWitness nu T a g f`, the single-family existential detailed
   above (`research/R41D/Spec.lean:93-107`).  Its apparently repeated margin,
   regularity, compactness, and lifespan conjuncts are honest projections after
   the alignment equalities; they are neither free proposition variables nor
   unused hypotheses.
3. `RDensityAPI Y.forceClass`, `densityL1`, and `densityL2`
   (`research/R41D/Spec.lean:121-169`).  There is no axiom, admitted proof,
   native decision, heartbeat override, or placeholder proposition field.

The main vacuity/falsity risks are handled correctly:

- `⊤` cannot satisfy either strict norm inequality, including when the radius
  is `⊤`; no `.toReal` appears (`research/R41D/Spec.lean:141-166`;
  `verification/Contracts/V1/Data.lean:215-228`).
- `nu,T` are positive and both the reference and approximant carry the
  manuscript class hypotheses, so the `T_max=0` empty-supremum convention was
  not exposed by dropping datum admissibility
  (`research/R41D/Spec.lean:136-147,158-169`).  The inserted branch additionally
  has exact positive lifespan because `T>0` (`research/R41D/Spec.lean:107`).
- `Y` cannot be chosen as an unrelated empty set because of `forceClass`; the
  permitted classes are concretely nonempty.  The probe constructs the zero
  force in all three classes and the zero datum in `X_R`
  (`research/SPEC/probes/rev174_fidelity.lean:14-31`).
- The same probe proves the contract norm of the zero force is zero for every
  `q,s`, and hence every positive radius ball around zero is inhabited
  (`research/SPEC/probes/rev174_fidelity.lean:33-51`).  This also confirms that
  G5 is a missing exported helper, not a hidden inconsistency.
- The inserted solution remains on `Ico 0 T`; earlier history retains both
  endpoint inequalities (`verification/Contracts/V1/InsertionFamily.lean:196-226`).
  The selected epsilon is in the family range and that range is below the
  scaling range (`research/R41D/Spec.lean:101`;
  `verification/Contracts/V1/InsertionFamily.lean:154-164`), where
  `2*epsilon^2 < min T delta`; in particular `T-2*epsilon^2>0`, so the displayed
  history window is not empty (`verification/Contracts/V1/Scaling.lean:191-209`).
  No `Icc 0 T` solution window is introduced in R41D itself.

Hygiene is clean for the specification.  Against
`origin/erenup/integration...HEAD`, all ten changed tracked paths are new files
under `research/R41D/`; no existing `formalization/`, `verification/`, paper,
record, or script file was modified.  The only current untracked material is
the permitted reviewer directory `research/SPEC/` containing this review and
probe.

## 3. Gaps

The five entries at `research/R41D/COMPARISON.md:62-68` are real as missing
named proof interfaces, none blocks forming this statement, and their owners
are appropriate.

- G1: a full-tree `grep -RInE
  'InsertionLifespanV2API|insertionLifespanV2Statement|R42InsertedWitness'
  formalization/NSFormalization/Section4` produced no output.  Contracts only
  expose the conditional V2 record/statement
  (`verification/Contracts/V2/InsertionLifespan.lean:117-180`), and its binding
  starts from an already assembled family
  (`verification/Bindings/InsertionLifespanV2.lean:81-93`).  The source-level
  density theorem returns a compact correction and source lifespan, not an
  aligned V2 family (`formalization/NSFormalization/Source/WholeSpaceDensity.lean:41-48`).
  Assignment to R42 assembly with A02 selection, or consumer-local R41D glue,
  is correct.
- G2 and G3: a full-tree `grep -RInE 'MemForceRapid|forceClassRapid'
  formalization/NSFormalization/Section4` produced no output.  In contracts the
  only mathematical definitions are `MemForceRapid`/`forceClassRapid`
  (`verification/Contracts/V1/Data.lean:565-578`), and the datum-lemma contract
  explicitly says `F_rd` is untouched
  (`verification/Contracts/V1/DatumLemmas.lean:86`).  There is no rapid-to-`F_R`
  inclusion or compact-difference closure.  The generic inclusion belongs in
  D01; the corollary-specific closure is reasonably owned by R45/D01.
- G4: a full-tree `grep -RIn 'initialClassSchwartz'
  formalization/NSFormalization/Section4` produced no output.  Contract/binding
  search finds only the definition
  (`verification/Contracts/V1/Data.lean:511-514`), not the inclusion.  D01 as
  supplier and R45 as consumer is the correct split.
- G5: a full-tree and contracts/bindings search for a
  `forceSobolevENorm[_L1/_L2]` zero theorem found none.  The nearest reusable
  pieces are `isSobolevDatum_zero`
  (`formalization/NSFormalization/Section4/D01/SmoothDatum.lean:241-246`) and
  `memForceR_zero`
  (`formalization/NSFormalization/Section4/A04/ZeroSolution.lean:68-75`).  The
  reviewer probe derives the missing stronger all-`q` norm equality in fifteen
  lines (`research/SPEC/probes/rev174_fidelity.lean:33-47`).  Calling this a
  small D01 norm-vocabulary gap is accurate.

The table also correctly rejects false gaps.  Compact-to-`F_R`, compact
additivity, and `F_R` compact-difference closure are exactly present at
`verification/Contracts/V1/DatumLemmas.lean:333-355,381-383`; margin selection
is present at `verification/Contracts/V1/MaximalPartial.lean:200-214`; and
R42 force convergence is a genuine `Tendsto` field at
`verification/Contracts/V1/InsertionFamily.lean:318-327`.

## 4. Commands and results

The lead's lane-specific instruction says this is a specification-only review:
the applicable gates are `lake env lean` on the two blind drafts and frozen
specification, plus `make check`.  Accordingly, module `lake build`, an axioms
file, `scripts/gates.sh`, and `check_contracts.py --base-ref ...` are not
applicable: there is no proof declaration/module target and `verification/`
was not touched.

Exact Lean gate results:

```text
. scripts/lean-env.sh && cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R41D/DraftA.lean
exit 0
(no output)

. scripts/lean-env.sh && cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R41D/DraftB.lean
exit 0
(no output)

. scripts/lean-env.sh && cd verification && LEAN_NUM_THREADS=6 lake env lean ../research/R41D/Spec.lean
exit 0
(no output)
```

The restored fidelity/non-vacuity probe also exits 0 with no output.  Because
research files are not Lake modules, the command first compiled `Spec.lean` to
a temporary `.olean` outside the worktree and added that temporary root to
`LEAN_PATH`; it made no lane-source or git-state change.

For the substantive negative check I changed only the L² assumption in the
scratch conformance statement from `s < -1/2` to `s < 1/2`.  Lean exited 1
with the expected error (the repeated common tail is included to show this was
not caused by dropping an argument):

```text
../research/SPEC/probes/rev174_fidelity.lean:69:2: error: Type mismatch
  A.densityL2
has type
  ∀ (nu : ℝ),
    0 < nu →
      ∀ (T : ℝ),
        0 < T →
          ∀ s < -1 / 2,
            ∀ a ∈ initialClassR,
              ∀ g ∈ Y,
                ∀ (radius : ℝ≥0∞),
                  0 < radius →
                    ∃ f ∈ breakdownSetIn Y nu a T,
                      forceSobolevENormL2 s (f - g) < radius ∧
                        (maximalLifespanR nu a g ≤ ENNReal.ofReal T ∧ f = g ∨
                          ENNReal.ofReal T < maximalLifespanR nu a g ∧ R42InsertedWitness nu T a g f)
but is expected to have type
  ∀ (nu : ℝ),
    0 < nu →
      ∀ (T : ℝ),
        0 < T →
          ∀ s < 1 / 2,
            ∀ a ∈ initialClassR,
              ∀ g ∈ Y,
                ∀ (radius : ℝ≥0∞),
                  0 < radius →
                    ∃ f ∈ breakdownSetIn Y nu a T,
                      forceSobolevENormL2 s (f - g) < radius ∧
                        (maximalLifespanR nu a g ≤ ENNReal.ofReal T ∧ f = g ∨
                          ENNReal.ofReal T < maximalLifespanR nu a g ∧ R42InsertedWitness nu T a g f)
```

After restoring `s < -1/2`, the same probe again exited 0 with no output.

`make check` was run twice and exited 0 both times.  The second complete stdout
capture had 25,428 lines / 1,045,301 bytes and SHA-256
`4e3d10690e1fc4524704145ba39e514890b24345b37af342766746641d66b9a1`.
The full capture is identified by that size and digest; the following are
selected verbatim leading, status, and terminal lines (the two `...` markers
replace the enormous registered-closure inventories):

```text
python3 experiments/check_formalization_plan.py --check
{
  "task_count": 30,
  "source_counts": {
    "formalization": 477,
    "vendor/NavierStokesAndEuler": 2486,
    "vendor/HeliCorgi": 129
  },
  "source_manifest_entries": 2975,
  "missing_copied_imports": [],
  "citation_interfaces_reachable": [],
  "tokens_in_copied_umbrella_closure": [
    {
      "module": "NSFormalization.Paper1.BoundaryCorollary",
      "path": "formalization/NSFormalization/Paper1/BoundaryCorollary.lean",
      "line": 90,
      "token": "sorry"
    }
...
  "source_hashes_match": false
}
Explicit axiom/admission tokens, all copied sources: 11
python3 experiments/check_contracts.py
{
  "registered_contracts": 27,
...
  "base_compatibility_checked": false,
  "scope": "Architecture checks only; run lake test for Lean type and axiom checks."
}
python3 experiments/test_contract_policy.py
.............
----------------------------------------------------------------------
Ran 13 tests in 0.044s

OK
python3 experiments/check_work_queue.py
30 work items: ownership, contract registration and task cards consistent.
```

The two displayed diagnostics are pre-existing copied-source/inventory reports,
not gate failures; this lane changes none of those files.  Final
`git diff --name-only origin/erenup/integration...HEAD` contains only the ten
new `research/R41D/*` deliverables listed in the worker report, and final
`git status --short` adds only `?? research/SPEC/` for the authorized reviewer
artifacts.

Verdict: ACCEPT.  Fixes required: none.
