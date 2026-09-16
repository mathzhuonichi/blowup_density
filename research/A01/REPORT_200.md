# REPORT 200 — exact forcing identification; conditional norm bound

## 1. Theorems with exact statements and constants

This lane does **not** close the general-data forcing bound unconditionally.
It proves the exact word-family identification and source contribution, and
reduces the remaining estimate to ONE named finite spatial inequality.
No all-order constructor or classical-solution-level lemma is used.

```lean
def E (q : ℕ) : ℝ := mildNormConstant q
def A (q : ℕ) : ℝ := mildNormConstant q * (1 + A03.outerTameConst (q+1))
```

`mildNormConstant q = sqrt(card(SobolevWord(q+1)))` is lane 196's
full-family comparison constant; `outerTameConst k = 6 * vectorTameConst k`.
Both constants are nonnegative. E is sufficient for the force contribution
unconditionally. A is an explicit **candidate** whose sufficiency remains
part of `CylinderCommutatorBound`; including `outerTameConst` in its formula
is not itself a derivation of a commutator estimate. Neither depends on ν;
later Young absorption would introduce `A q ^ 2 / (4 * ν)`.

Exact exported target (the extra `hcomm` is essential):

```lean
theorem forcingFamilyBound_of_cylinder {q : ℕ} (hq : 6 ≤ q) {ν S : ℝ} (hν : 0 < ν)
    (a : SmoothL2Field Space)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (hcomm : CylinderCommutatorBound q hq) :
    ForcingFamilyBound hq hν a F hF (E q) (A q)
```

At reviewed HEAD `494e1d4` against integration `5ca3bea`, and again after
rebasing onto integration `79b3677`, the checked `ForcingFamilyBound` declaration
has the exact argument sequence `hq hν a F hF E A`: there is no `ha` argument in
those specific revisions. Accordingly, the displayed conclusion is token-for-token
`ForcingFamilyBound hq hν a F hF (E q) (A q)`. This is a revision-scoped interface
observation, not a claim about later versions of the predicate. The result preserves
every competitor, the actual maximal approximation limit, 16 times the order-7
restriction, and `energyGradientNorm`; at these revisions it requires no separate
solenoidal datum argument once the spatial hypothesis is supplied.

The unconditional principal identifications and source estimate are:

```lean
theorem cylinderEnergyForcing_ae {q : ℕ} (hq : 6 ≤ q) {S T : ℝ}
    (hT : 0 ≤ T) (hTS : T ≤ S)
    (F : Icc (0 : ℝ) S → SmoothL2Field Space)
    (hF : ∀ n, Continuous fun t => (F t).jetLp n)
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (U : TimeLp T (SobolevSpace 1 (2+q))) :
    (cylinderEnergyForcing hq hT hTS F hF u U : ℝ → ℝ) =ᵐ[timeMeasure T]
      fun r => familyNorm ((extendPath T hT
        ((sobolevPath F hF (q+1)).comp (timeInclusion hTS)) r).val +
        cylinderCommutator hq (extendPath T hT u r) (U r))
```

```lean
theorem force_word_norm_le {q : ℕ} {S T : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1))) (r : ℝ) :
    familyNorm (extendPath T hT (f.comp (timeInclusion hTS)) r).val ≤ E q * ‖f‖
```

```lean
theorem sourceTime_add_pressureTime_ae {q : ℕ} (hq : 6 ≤ q) {S T : ℝ}
    (hT : 0 ≤ T) (hTS : T ≤ S)
    (f : C(Icc (0 : ℝ) S, SobolevSpace 1 (q+1)))
    (u : C(Icc (0 : ℝ) T, SobolevSpace 1 (q+1)))
    (V : TimeLp T (SobolevSpace 1 ((q+1)+1))) :
    (fun r => ForcedSourceUpgrade.sourceTime hq hT hTS f u V r +
      energyPressureTime hq hT hTS f u V r) =ᵐ[timeMeasure T] fun r =>
        extendPath T hT (f.comp (timeInclusion hTS)) r -
        asymmetricTransport 1 (by omega : 6 ≤ q+1) (velocityComponents 1 0)
          (velocityComponents_norm 1 0 (by norm_num) (by simp)) (extendPath T hT u r) (V r)
```

`energyForcingNorm_ae` specializes the vendor's weighted representative to the
literal Unit/full-word family. `energyRawTime_ae` constructs its raw-residual
representative. `source_pressure_cancel` and `forcing_array_rearrange` prove
the algebra before taking norms. The pressure complement cancels exactly with
the projected source, so no pressure constant or pressure analytic hypothesis
is left. The maximal limit and its reindexing are exactly lane 198's objects;
no extra representative premise is passed to the downstream theorem.

## 2. Files

* New `formalization/NSFormalization/Section4/A01/ForcingFamilyBound.lean`:
  14 declarations, three commented local heartbeat limits of 400000.
* New `research/A01/axioms_forcing_bound.lean`: all 14 declarations and four
  zero-data helper proofs audit to exactly `[propext, Classical.choice, Quot.sound]`.
  The exact forcing target is proved on zero data for all competitors and
  limits; the new spatial commutator and its inequality are separately checked
  at zero. A negative scalar pairing/norm example is kernel checked.
* New `research/A01/ATTEMPTS_FORCING_BOUND.md`: positive route, failed routes,
  satisfiability limitations, searched APIs, and compiler diagnostics.
* Updated only the requested forcing-bound subrow of `research/A01/A3_SPLIT.md`.
* New `research/A01/REPORT_200.md`: this four-part report.
* Added reviewer artifact `research/A01/REVIEW_200-A01-forcing-bound.md` and the
  two reviewer probes `research/A01/probes/rev200_forcing_sign.lean` and
  `research/A01/probes/rev200_sign.lean`.

The branch was fetched and rebased onto integration `79b3677`. The duplicate
lane-199 replay was skipped because that lane had landed; integration's
`MildEnergyEnvelope.lean`, including `energyComparison_unique`, was retained.
No pre-existing Lean module, contract, generated task record, or other worktree
was changed, and no push was performed.

## 3. Gap with exact statement and error text

The sole missing analytic fact is the following **spatial** estimate. It is
stronger than restriction to mild competitors, but requires only compatible
finite Sobolev elements. It contains no force, PDE time evolution, endpoint
smoothness, or hidden all-order data.

```lean
def cylinderCommutator {q : ℕ} (hq : 6 ≤ q)
    (v : SobolevSpace 1 (q+1)) (V : SobolevSpace 1 (2+q)) :
    SobolevWord (q+1) → LiftL2 1 := fun w =>
  transportL2Bilinear 1 (by omega : 3 ≤ q+1) 1 0 v
    (boundedWordBlock 1 1 w.1.val (by have := w.1.isLt; omega) w.2 V) -
  (asymmetricTransport 1 (by omega : 6 ≤ q+1) (velocityComponents 1 0)
    (velocityComponents_norm 1 0 (by norm_num) (by simp)) v
    (restrictOperator 1 (by omega : (q+1)+1 ≤ 2+q) V)).val w
```

```lean
def CylinderCommutatorBound (q : ℕ) (hq : 6 ≤ q) : Prop :=
  ∀ (v : SobolevSpace 1 (q+1)) (V : SobolevSpace 1 (2+q)),
    restrictOperator 1 (by omega : q+1 ≤ 2+q) V = v →
    familyNorm (cylinderCommutator hq v V) ≤
      A q * (16 * ‖restrictOperator 1 (Nat.succ_le_succ hq) v‖) *
        Real.sqrt (∑ i : Fin 4, ∑ w : SobolevWord (q+1),
          ‖(derivativeOperator 1 (q+1) i
            (restrictOperator 1 (by omega : (q+1)+1 ≤ 2+q) V)).val w‖^2)
```

The hypothesis has not been proved for nonzero data; in particular sufficiency
of the candidate A remains open. The zero conformance does not prove this
globally quantified hypothesis. The exact identity of Z with the source plus
this array IS proved, so the residual no longer includes identification,
pressure, source, time representatives or maximal-limit compatibility.

The tensor tame route `outerProductTame` → `outerSobolevNormAt_le` →
`inner_energy_Rhigh` controls a signed pairing. Its finite physical datum
premises and its extension to this family norm have not been supplied here.
Vendor base/external commutator lemmas were inspected; their smooth/all-order
representative hypotheses and base/Gevrey estimates cannot simply be applied
to these finite carriers. See ATTEMPTS for exact candidates and scope.
There is no outstanding Lean error; the missing estimate is explicit rather
than represented by an unfinished proof.

The rebase and the reviewer sign probe do not change this gap. The latter checks
the opposite commutator presentation of the same forcing identity; the norm bound
remains conditional on the single spatial estimate above.

Resolved diagnostic text:

```text
(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
(deterministic) timeout at `isDefEq`, maximum number of heartbeats (400000) has been reached
Tactic `rewrite` failed: Did not find an occurrence of the pattern
```

Splitting representative/cancellation/array lemmas and using typed congruence
resolved these without exceeding the permitted heartbeat budget.
The requested `research/A01/REVIEW_199-A01-envelope.md` is absent in this
checkout (`No such file or directory`); REPORT_199, REVIEW_198 §3, and the
prompt's route were read instead.

## 4. Commands and results

Lean shells source `. scripts/lean-env.sh`; Lake is invoked from `verification/`.
The shared dependency-package symlink was checked before compilation.

Post-rebase results on integration `79b3677`:

* `LEAN_NUM_THREADS=6 lake build NSFormalization.Section4.A01.ForcingFamilyBound`:
  PASS, 10248 jobs; only pre-existing dependency warnings were replayed.
* `LEAN_NUM_THREADS=6 lake env lean ../formalization/NSFormalization/Section4/A01/ForcingFamilyBound.lean`:
  PASS with zero output.
* `LEAN_NUM_THREADS=6 lake env lean ../research/A01/axioms_forcing_bound.lean`:
  PASS; all 18 audits report exactly `[propext, Classical.choice, Quot.sound]`.
* Reviewer negative probes: `rev200_forcing_sign.lean` exits 1 at line 50 on
  the mutated minus-commutator conclusion, and `rev200_sign.lean` exits 1 at
  line 11 on the mutated array sign. Both mutations are rejected as intended.
* `make check`: PASS. Its historical copied-source token and
  `source_hashes_match=false` findings remain informational.
* `make test`: PASS, 10573 jobs.
* `git diff --check`: PASS; the new proof module, axiom audit, and probes contain
  no `sorry`, `admit`, `axiom`, or `native_decide` proof token.

All source and record changes stay in this worktree and are committed on
`erenup/200-A01-forcing-bound`.
