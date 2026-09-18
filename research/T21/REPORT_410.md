# Lane 410-SPEC-t21-draft-a — T21 Draft A report

## 1. The theorem and corollary stated

This lane completes the Section 3 torus main assembly at
`paper/sections/03-torus.tex:8-16` and `:506-509`.

* `MainTheoremAPI.fixedInitialDensity` states theorem (i) for every fixed
  `a ∈ initialClassT`, `ν>0`, `T>0`, and `s<1/2`, using the registered relative
  `L¹(0,∞;H^s(T³))` predicate `RelativelyDenseT`.
* `MainTheoremAPI.zeroInitialDensity_subcritical` and
  `zeroInitialDensity_only_if` are the two directions of theorem (ii), with
  the exact zero initial velocity and the same relative topology.  The public
  `mainStatement` restores the paper's biconditional.
* `NonDensityAPI` states the corollary's explicit relative critical ball with
  radius `ENNReal.ofReal (c*ν)`, where `c` is the selected T20
  `CriticalRegularityTAPI.c`; it records positive radius, zero-force
  membership, ball disjointness from `𝓑⁰_{ν,T}`, monotonicity from order
  `1/2` to every `s≥1/2`, and the resulting non-density.  The public
  `nonDensityStatement` is the paper-order corollary.

The completed file also retains the long canonical T19 density package and
the canonical T20 critical-regularity package that were present as uncommitted
partial work.  No placeholder `Prop` fields were introduced.

## 2. What Lean now contains

`research/T21/DraftA.lean` elaborates as a statements-only file.  Its namespace
`BlowupDensity.T21.DraftA` defines `zeroInitialVelocity`, `zeroForce`,
`criticalForceBall`, `NonDensityAPI`, `MainTheoremAPI`, `mainStatement`,
`nonDensityStatement`, and the input shape `mainOfInputs`.

The T19 structures remain under `BlowupDensity.T19`, with the registered
`TorusData`/`TorusLocalTheory` names used directly.  The T20 copied block
remains under `NSFormalization.Section3.T20`; it is `Type`-valued because its
constants (including `c`) are data.  T21's result structures are `Prop`-valued
and consume that T20 data rather than creating another critical constant.
Two `example … := rfl` checks guard the copied critical-radius spelling and
the registered breakdown-set specialization.  `COMPARISON_A.md` contains the
paper-clause table, R41 counterparts, representation choices, ambiguities,
the T19/T20/T11 proof-input list, and implementation candidates.

## 3. Gaps and scope

This is a specification lane, so the fields are intentionally not proved.
The proof/assembly work still needs the following concrete inputs listed in
the comparison file:

* the torus analogue of R41's force Sobolev monotonicity, proved from the
  coefficient weights and lifted measurable paths;
* the zero-force class and zero-centred norm normalization;
* the order contradiction turning T20's global lifespan `=⊤` into exclusion
  from `breakdownSetT`, followed by the relative-ball argument; and
* the existing T19 fixed-initial density and its `criticalOrder 1 = 1/2`
  bridge, together with T20's `globalRegularity` field.

The torus statement deliberately has only the single critical exponent
`1/2` (`q=1`); the Section 4 `q=2` and `s=-1/2` branch is not imported into
the theorem.  The file contains no `True` field, zero-radius trap, real
`sSup`, `sorry`, `admit`, `axiom`, or `native_decide` token.

## 4. Commands and results

From the lane worktree:

```text
cd verification && lake env lean ../research/T21/DraftA.lean
```

completed with exit code 0 and no diagnostics.

The requested quality scan was:

```text
grep -nE ': *True|:= *0$|→ *True' research/T21/DraftA.lean
```

It produced no output.  The additional prohibited-token scan for
`sorry|admit|axiom|native_decide` also produced no output, and `git diff
--check` was clean.  No push, merge, or rebase was performed; the deliverables
are committed on branch `erenup/410-SPEC-t21-draft-a`.
