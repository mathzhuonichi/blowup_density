# T21 N11/N13/N14/N15 attempts

## Active route

The implementation threads the exact `NonDensityAPI.nonDensity` field because
lane 472 owns the `NonDensityAPI` declaration and is running in parallel.  The
final assembly can apply `mainTheoremAPI D N.nonDensity` after that lane lands.
The shared `breakdownSetTZero` definition is unfolded in this independent
module to avoid redeclaring lane 472's canonical constant; the two types are
definitionally equal.

## Failed approach 1: missing namespace qualification

The first build omitted `open NSFormalization.Section3.T19 (criticalOrder)`.
Lean reported:

```text
error: NSFormalization/Section3/T21/Main.lean:28:19: Function expected at
  criticalOrder
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  1

Hint: The identifier `criticalOrder` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
error: NSFormalization/Section3/T21/Main.lean:42:25: Function expected at
  criticalOrder
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  1

Hint: The identifier `criticalOrder` is unknown, and Lean's `autoImplicit` option causes an unknown identifier to be treated as an implicitly bound variable with an unknown type. However, the unknown type cannot be a function, and a function is what Lean expects here. This is often the result of a typo or a missing `import` or `open` statement.
error: NSFormalization/Section3/T21/Main.lean:99:19: invalid {...} notation, expected type is not of the form (C ...)
  MainTheoremAPI
error: NSFormalization/Section3/T21/Main.lean:106:0: type of theorem `NSFormalization.Section3.T21.mainOfDensityAndNonDensity_holds` is not a proposition
  {MainTheoremAPI : Sort u_1} →
    T19.PeriodicDensityAPI →
      (∀ (nu : ℝ),
          0 < nu →
            ∀ (s : ℝ), 1 / 2 ≤ s → ∀ (T : ℝ), 0 < T → ¬RelativelyDenseT 1 s forceClassT (breakdownSetTZero nu T)) →
        MainTheoremAPI
```

The last two messages were cascades from the failed structure declaration.

## Documentation patch context mismatch

The first status-line patch used an outdated dependency sentence.  The patch
tool reported:

```text
apply_patch verification failed: Failed to find expected lines in /data_8T/ping/blowup_density/.claude/worktrees/474-T21-N11-N13-N15-main/research/T21/T21_SPLIT.md:
**Size, model:** S, codex-sol. **Deps:** none.
```

Reading the exact range showed the current text is `**Deps:** proved T19 U1.`;
the corrected context applied cleanly.

## Gate scheduling race

I initially launched the module rebuild and the probe/audit in parallel after
changing the shared definition spelling.  The rebuild had removed the stale
object before the audit process imported it, producing:

```text
../research/T21/axioms_n11_n15.lean:1:0: error: object file '/data_8T/ping/blowup_density/.claude/worktrees/474-T21-N11-N13-N15-main/formalization/.lake/build/lib/lean/NSFormalization/Section3/T21/Main.olean' of module NSFormalization.Section3.T21.Main does not exist
```

This is a scheduling failure rather than a Lean proof failure; the module build
completed successfully, after which the probes were rerun sequentially.
