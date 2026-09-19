# ATTEMPTS — T20 U12 `globalRegularity` (lane 441)

Target: `Section3/T20/GlobalRegularity.lean`,
`NSFormalization.Section3.T20.globalRegularity`, the `globalRegularity` field
of `CriticalRegularityTAPI` verbatim at `c = criticalSmallnessH1`.

## Failed approaches, with exact error text

1. **Real addition normalization in monotonicity of the exhausting sequence.**
   I tried to prove `((i : ℝ) + 2) ≤ ((j : ℝ) + 2)` by
   `exact add_le_add_right (Nat.cast_le.2 hij) 2`. Lean normalized the returned
   expression in the opposite commutative order and reported:

   ```text
   GlobalRegularity.lean:61:6: error: Type mismatch
     add_le_add_right (Nat.cast_le.mpr hij) 2
   has type
     2 + ↑i ≤ 2 + ↑j
   but is expected to have type
     ↑i + 2 ≤ ↑j + 2
   ```

   Keeping the cast inequality as `hijR` and closing the linear rearrangement
   with `linarith` avoids depending on elaborator normalization.

2. **Using only the second conjunct of U11.**  After rewriting the selected
   classical solution's velocity to the maximal velocity, I tried to apply
   `continuationBound ... .2.1` directly to the `squaredHTwoIntegralT` goal.
   That conjunct bounds `meanModeCriterionIntegral`; the first conjunct is the
   required equality. Lean reported:

   ```text
   GlobalRegularity.lean:103:2: error: Type mismatch
     LE.le.trans hb (add_le_add ?m.693 le_rfl)
   has type
     meanModeCriterionIntegral (bb n) g u ≤
       ?m.690 + ENNReal.ofReal (Ccriterion * ν⁻¹ ^ 2) * meanFreeForceLTwoSqIntegral (meanFreeForce g)
   but is expected to have type
     ∫⁻ (x : ℝ) in Ioo 0 (bb n), (periodicSobolevENorm 2 fun x_1 => u (x, x_1)) ^ 2 ≤
       ENNReal.ofReal S * criticalRho g ^ 2 +
         ENNReal.ofReal (Ccriterion * ν⁻¹ ^ 2) * meanFreeForceLTwoSqIntegral (meanFreeForce g)
   ```

   The estimate must first compose the equality with the bound, then rewrite
   `hwv`.

3. **Equality transitivity selected instead of order transitivity.**  The first
   correction above used `hc.1.trans hc.2.1`; because `hc.1` is an equality,
   Lean selected `Eq.trans` and expected another equality:

   ```text
   GlobalRegularity.lean:103:24: error: Application type mismatch: The argument
     hc.right.left
   has type
     meanModeCriterionIntegral (bb n) g w.velocity ≤
       ENNReal.ofReal (bb n) * criticalRho g ^ 2 +
         ENNReal.ofReal (Ccriterion * ν⁻¹ ^ 2) * meanFreeForceLTwoSqIntegral (meanFreeForce g)
   but is expected to have type
     meanModeCriterionIntegral (bb n) g w.velocity = ?m.680
   in the application
     Eq.trans hc.left hc.right.left
   ```

   The order-compatible spelling is `hc.1.le.trans hc.2.1`.

4. **A convenience order lemma is not available at root in this pin.**  For
   the monotonicity of the term
   `ENNReal.ofReal b * criticalRho g ^ 2`, I tried the familiar
   `mul_le_mul_right'`. Lean reported:

   ```text
   GlobalRegularity.lean:106:8: error(lean.unknownIdentifier): Unknown identifier `mul_le_mul_right'`
   ```

   The explicit four-premise `mul_le_mul ... le_rfl bot_le bot_le` works for
   `ℝ≥0∞`.

5. **The probes were invoked before Lake had emitted the new module's
   object file.**  A direct `lake env lean` check of the source does not create
   the `.olean`; running the probe and audit immediately afterwards gave:

   ```text
   global_regularity_closes.lean:1:0: error: object file '.../formalization/.lake/build/lib/lean/NSFormalization/Section3/T20/GlobalRegularity.olean' of module NSFormalization.Section3.T20.GlobalRegularity does not exist
   axioms_u12.lean:1:0: error: object file '.../formalization/.lake/build/lib/lean/NSFormalization/Section3/T20/GlobalRegularity.olean' of module NSFormalization.Section3.T20.GlobalRegularity does not exist
   ```

   Build `NSFormalization.Section3.T20.GlobalRegularity` before checking its
   consumers.

6. **The zero-force probe omitted the namespace import for the time
   measure.**  Its datum witness uses `forceTimeMeasure`, but the selective
   `A02` open listed only the field types. Lean reported:

   ```text
   global_regularity_closes.lean:55:33: error(lean.unknownIdentifier): Unknown identifier `forceTimeMeasure`
   global_regularity_closes.lean:56:20: error(lean.unknownIdentifier): Unknown identifier `forceTimeMeasure`
   ```

   Add `forceTimeMeasure` to the selective `NSFormalization.Section4.A02`
   open.
