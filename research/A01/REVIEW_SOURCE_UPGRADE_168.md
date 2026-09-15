# Lane 168 source-upgrade review

Final verdict: **ACCEPT — source review, both module builds, and all nine declaration axiom audits verified from Luna logs.** Full 26-check test suite and mutation suite passed; see the final test-evidence addendum. Earlier pending entries below are historical and superseded by the final verification addendum.

Reviewed 2026-09-15. Applied this tree's `.claude/skills/lane-review/SKILL.md` source, statement-fidelity, citation and minimality checks. The assigned reviewer scope prohibits git, compilation and Lean edits; Luna owns build/typecheck evidence. The initial source-only assessment below is supplemented by the final log verification addendum.

## Findings

1. **Pass — actual nonlinear bridge.** `sourceTime` constructs the real Leray projection of force minus asymmetric transport, in `TimeLp T H(q+1)`. The coefficient is the existing continuous `u : C([0,T], H(q+1))`; only the differentiated state is `W : TimeLp T H(q+2)`. `sourceTime_ae` exposes exactly that representative, with no substituted force, sign change, arbitrary source or assumed high continuity.
2. **Pass — restriction, datum and horizon.** `truncate_leray` uses the common underlying L2 projection. `sourceTime_restriction` combines the actual transport restriction and W's a.e. lower restriction to identify the original `nonlinearSource`. The consumer obtains T, u, U and W together from lane 166; it preserves positive T, T <= S, both initial values, ordinary lift, the literal forced quadratic Duhamel equation and the physical force slice. `truncate_forcePath` identifies the adjacent force orders of the same physical force. No W, high source, classical solution, or desired persistence premise appears in the consumer assumptions.
3. **Pass — a.e. scope and honest limitation.** Equality is under `timeMeasure T = volume.restrict (Icc 0 T)`, not an all-time/endpoint equality. W is the original velocity only after Sobolev restriction a.e.; the theorem does not give W an endpoint trace. The squared norm is integrable, not merely an unconstrained integral. This supplies a useful nonlinear source for persistence, but does not prove continuous higher persistence, an all-order common horizon, pressure, time smoothness, uniqueness, or the paper's classical theorem. The route explicitly leaves these open.
4. **Note — retained versus omitted lane-166 fields.** The new consumer deliberately drops the low-path norm bound, divergence statement, angle invariance, and explicit squared-norm integrability of W. This does not invalidate the source bridge; W's latter integrability follows from its TimeLp type. For a later constructor needing the other constraints, obtain lane 166 once and apply `sourceTime`, `sourceTime_restriction`, and `sourceTime_integrable_sq` to that same witness. Calling the two existential consumers independently does not identify their T or u. Do not describe the 168 output as preserving every lane-166 field.
5. **Note — probe and evidence.** The probe prints all new declaration axioms and specializes the full 168 theorem with `#check` at q=6. It neither replaces the initial datum nor discards the equation from that theorem's type. Its phrase “preserving its complete output” is accurate only about 168 itself. This is only specialization typechecking, not an additional conformance theorem. The proved and axiom-audited `exists_local_source_of_memForce` is itself the direct lane-166 consumer; duplicating its entire statement is not required for this source review. Build/typecheck and actual axiom lists remain pending.
6. **Pass — attempts document and same-witness explanation.** The author supplied `ATTEMPTS_SOURCE_UPGRADE_168.md` during review. It accurately lists the retained fields, explicitly explains the single-lane-166-witness use needed for omitted constraints, describes the q=6 probe as specialization only, and leaves compilation and linear trace pending. No unsupported completion claim found.

## Citation checks

Opened and checked the following source declarations rather than relying on names:

- `vendor/NavierStokesAndEuler/Euler/TimeSobolevTransport.lean:32,39`: `transportTime` and `transportTime_ae` genuinely multiply a continuous Hs coefficient with a TimeLp H(s+1) state, returning TimeLp Hs and its literal a.e. transport.
- `vendor/NavierStokesAndEuler/Euler/TimeCorrectionSource.lean:65`: `restrict_transport_state` requires exactly the higher state's adjacent restriction and yields `transportBilinear b e`, matching its use with b=e=u.
- `vendor/NavierStokesAndEuler/Euler/SmoothFieldSobolevTime.lean:44`: `restrict_sobolev` identifies the same smooth field under Sobolev restriction, supporting force-order compatibility.

Additional checks: `ForcedCylinderLocal.lean:60` confirms `source_eq` is P(f-advection(u,u)) despite the internal coefficient convention `forcing := -f`. `ForcedMaximalRegularity.lean:61` has the actual force/datum/mild-equation witness used by the consumer. `HeatGradientEnergy.lean:96`, `HeatGradientIntegral.lean:16`, and `MaximalTopCauchy.lean:48` support the route's distinction between an energy estimate, dropping the terminal gradient term, and Bochner Cauchy convergence. The proposed linear trace/regularization alignment is explicitly planning, not supplied mathematics.

The paper target at `paper/sections/02-preliminaries.tex:105` requires maximal smooth existence, uniqueness and H2-integral continuation. This module claims only an analytic substep. `verification/Contracts/V1/Data.lean` was inspected for the stable specification conventions; this module imports existing real analytic objects and does not introduce mirrored contract definitions or claim contract conformance of a completed classical solution.

## Commands and verification status

- Read-only `Get-Content`, `rg --files`, and targeted `rg -n` inspected the new module, probe, route, supplier declarations, paper proposition and contract conventions.
- `rg -n 'sorry|admit|axiom|native_decide' formalization/NSFormalization/Section4/A01/ForcedSourceUpgrade.lean`: no matches.
- No git, Lean, lake, compilation, mutation checks or rendered Markdown QA were run by this reviewer. All compiled acceptance and dependency-axiom evidence: **pending Luna report**.
- No source edits. The adapter is a small direct reuse of existing transport, force and projection compatibility; no unnecessary architecture or replacement definitions found.


## Follow-up source review: heat terminal energy and elaboration repairs

Verdict remains **ACCEPT-WITH-NOTES; all nine new declaration axiom audits and final compilation pending**. This follow-up is source-only and does not certify the initial failed build as repaired by compilation.

7. **Pass — terminal energy from genuine heat time laws.** `HeatGradientTrace.heat_gradient_trace_dissipation` requires positive viscosity, s <= t, continuity of the H3 state and H1 source on Icc(s,t), and the actual first-spatial-derivative heat evolution law at every interior time and spatial direction. It does not assume an energy inequality. Its proof matches the previously opened `HeatGradientIntegral.heat_laplacian_integral_bound` internal `hi`, retaining G(t) instead of dropping it: terminal gradient energy plus viscous Laplacian squared time integral is bounded by initial gradient energy plus inverse-viscosity times source L2 squared time integral. The H1 source is needed by the differentiated PDE assumption, while only its undifferentiated L2 norm occurs in the quantitative bound. No replacement by an arbitrary scalar energy premise occurred.
8. **Pass — point estimate and scope.** `heat_gradient_trace_bound` drops only nonnegative dissipation, using s <= t for the orientation of the interval integral and positive viscosity for its sign. These are estimates for already regular heat paths, not a theorem producing a continuous high-order path from the TimeLp source. The new route/attempts sections correctly retain actual-source alignment, finite-word summation, uniform Cauchy convergence and completion/identification as outstanding work. In particular the source-upgrade TimeLp G does not directly satisfy the trace lemma's continuous H1-source assumption without the missing regularization argument.
9. **Pass — source elaboration repairs preserve semantics.** `ContinuousMap.ext` proves the same force-path identity pointwise. The new local heartbeat allowance changes no statement. The consumer now names the original lane-166 witness W0 and applies `restrictOperator` through `compLpL` from order 2+q to the equal order (q+1)+1. This is canonical equal-order reindexing of the same Bochner path, not a fresh existence choice or a regularity assumption. `coeFn_compLpL` and `restrictOperator_comp` explicitly recover the original a.e. restriction of W0 to u on the original timeMeasure T. T, u, U, datum, force and mild equation remain those of the one lane-166 obtain.
10. **Documentation note.** At this reading, the attempts document's final phrase “The previously submitted source-upgrade Lean file is unchanged” predates the reported elaboration repairs. Clarify it to avoid suggesting the submitted text had no changes. This is not a mathematical blocker; the repairs are reviewed above.

Follow-up checks: opened both new trace declarations, their two-item axiom probe, the repaired source consumer, force compatibility proof, and updated route/attempts. The original seven source declarations plus the two trace declarations total nine pending axiom audits. Targeted `rg -n 'sorry|admit|axiom|native_decide'` found no matches in either implementation module (rg exit 1 means no matches). No compilation or git command was run, and no Lean source was edited by this reviewer.


## Final verification addendum

**ACCEPT for the implemented source-upgrade and regular-heat terminal-energy substeps.** This does not assert completion of continuous persistence or the paper's classical local theorem.

Read the actual Luna logs in this worktree without rerunning compilation:

- `tmp/build_168_ForcedSourceUpgrade_r3.log`: Built `NSFormalization.Section4.A01.ForcedSourceUpgrade`; `Build completed successfully (10201 jobs).`
- `tmp/build_168_HeatGradientTrace.log`: Built `NSFormalization.Section4.A01.HeatGradientTrace`; `Build completed successfully (3829 jobs).`
- `tmp/probe_168_axioms_source_upgrade.log`: all seven requested source declarations report exactly `propext`, `Classical.choice`, `Quot.sound`. The final output is the ordinary q=6 specialization type of the existing consumer, including the original datum, force and Duhamel equation; no additional conformance theorem is claimed.
- `tmp/probe_168_axioms_heat_trace.log`: both trace declarations report exactly the same three standard axioms.

The explicit type annotation on the consumer's F is the existing continuous force path in H(q+1) on Icc(0,S); its defining term is unchanged. It resolves elaboration without adding hypotheses or changing force, witness or horizon semantics.

Finding 10 is closed: the attempts document now records that the trace module was added independently and that the source adapter received elaboration fixes with unchanged mathematical statements and same-witness semantics. The earlier pending build/axiom notes record review chronology; the logs above supersede them.

Full 26-test suite and mutation-check results were initially pending here and are now verified in the test-evidence addendum below; they were not inferred from module build success. This reviewer performed no compilation, git action, test execution or Lean edit.


## Final test-evidence addendum

The remaining test-evidence pending items are closed. Luna reported native exit code 0 for both runs; this reviewer separately read their actual logs, without rerunning either command:

- `tmp/lake_test_168_persistence.log`: counted 26 `Contract ...: checked; standard logical axioms only` entries and inspected the final checked outputs through `Tests.RegularityPartial`.
- `tmp/mutations_168_persistence.log`: `implementation_refactor: accepted`; `admitted_proof`, `extra_axiom`, and `weakened_hypothesis` each `rejected as required`; final line reports the mutation suite passed.

Native process exit codes are attributed to Luna's execution report, not inferred from this reviewer's successful file-read command. The mutation suite is an infrastructure check, not a PDE proof. Final verdict remains **ACCEPT** for the implemented substeps, with no remaining build/axiom/test evidence pending in this review. The mathematical persistence work identified above remains future work.
