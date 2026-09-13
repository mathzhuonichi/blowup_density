# Repository-wide collaboration and the main branch

The default branch was renamed from `codex/section4-blueprint` to `main` on
13 September 2026. This corrects a misleading setup choice: the entire project
is shared, while Section 4 is only the current research priority.

The rename preserves commit history and the complete repository tree. GitHub
returned `main` as the default branch and retained the existing status checks,
one-review requirement and administrator enforcement. The repository remains
private. `erenup` has accepted the invitation and has write access to the
whole repository, not a directory or one paper.

The accompanying PR updates the explicit CI push filter and the collaboration
documentation. It follows the existing review rule; branch protection is not
disabled to merge the correction without the other contributor's review.

For an existing clone checked out on the old branch, first save any local work
and then run:

```sh
git branch -m codex/section4-blueprint main
git fetch origin
git branch --set-upstream-to=origin/main main
git remote set-head origin -a
```

Existing task branches can remain in use. New clones check out `main` by default.
