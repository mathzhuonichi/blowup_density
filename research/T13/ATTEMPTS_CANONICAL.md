# T13 canonical-module attempts

No Lean elaboration, module build, probe, or policy-gate attempt failed while
constructing the canonical module.  Consequently there is no error diagnostic
to preserve.

The first module build replayed pre-existing upstream linter warnings, then
built `NSFormalization.Section3.T13.Localization` successfully.  Those
warnings were not errors and did not originate in any file added by this lane.
