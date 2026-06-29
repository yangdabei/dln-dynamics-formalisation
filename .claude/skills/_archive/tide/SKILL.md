---
name: tide
description: The Tide loop — take a human-provided direction outward from existing formalised material, deliberate with GPT-5.5 Pro to pick a minimal candidate lemma, then hand off to the lean-formalisation skill. Use when the user invokes the tide ("/tide", "let's do a tide step", "run a tide on X"), or asks to take a forward-looking exploration+formalisation step outward from a formalised repo (laplace, threepoint, …).
---

# The Tide loop

The Tide is the operational loop of the [automation project](../../../projects/automation/README.md): a tide of agents spreading outward from already-formalised territory. Each tide step picks a small piece of new ground, agrees on what to claim, and tries to formalise it. Successes extend the shoreline; failures cost only tokens.

This skill orchestrates **three steps** for one such excursion. It is deliberately thin — the heavy lifting in Step 3 is the `lean-formalisation` skill; the heavy lifting in Step 2 is the multi-model deliberation against the existing seabed.

## Auto mode

If the user invokes this skill with an `auto` modifier (e.g. *"run a tide on X auto"*, *"tide on the 2D pure-quartic case, auto mode"*), the user wants tides to keep running back-to-back without stopping. **Before Step 1**, invoke the `loop` skill exactly once:

```
/loop 15m Continue with what you think best, don't stop, it's fine if the session fills up the context
```

Then proceed with the normal flow (preflight → Step 1 → …).

**The loop is a fallback heartbeat, not the driver.** In auto mode, the *default* between actions is to continue immediately to the next best action — close out the current Tide, then roll straight into `tide-pick` (or the next obvious step) without waiting. The 15-minute `/loop` wakeup is a safety net that re-engages you if you somehow stop or stall; it is **not** a pacing signal and you should not idle for it. If you ever find yourself at a natural stopping point in auto mode (a Tide closed, a retrospective committed, a survey written), the correct next action is to *immediately* start the next step, not to wait for the loop to fire.

Only invoke `/loop` once per session. If a loop is already running, skip this step. If `tide-pick` already started the loop before handing off, it is already running and there is nothing to do here.

## Inputs

- **Direction** (from the user). A short English description of the outward step. Example: *"the laplace repo formalises covariances against a posterior with nondegenerate L; extend to simple degenerate cases."*
- **Seabed pointer** (usually obvious from the direction). A formalised repo to launch from (`sri/lean/laplace/`, `sri/lean/threepoint/`, …).
- **Research project** (inferred from the seabed unless explicit). Look up the seabed repo in the `lean` field of every project in `projects.json` and pick the one that owns it: `laplace` → `primer`, `threepoint` → `patterning`, etc. If the lookup is ambiguous, ask once.

If the direction is vague or the seabed pointer is ambiguous, ask once before proceeding. Cheap up front.

If **no** direction has been given at all (the user said "pick a tide", "find something to formalise", "run the tide loop" without naming a target), don't try to invent one — invoke the [`tide-pick`](../tide-pick/SKILL.md) skill instead. It surveys the SRI portfolio, presents 5–6 ranked candidates, and (after a short user-pause) hands back here with a chosen direction.

### GPT-5.5 Pro credentials (preflight)

Step 2's deliberation depends on the `timaeus-research` skill's GPT-5.5
Pro consult. **Verify the credentials file exists before starting**:

```bash
test -f .agents/skills/timaeus-research/credentials.json
```

If missing, surface to the user *before* writing the tide log. Either
they top up the credentials file or they explicitly choose to proceed
without GPT (acceptable for mirror-shaped tides where the candidate is
already deliberated and the closed form is numerically verified — see
the L1 sextic-J-function tide for a worked example of the
"proceed-without-GPT" path). What is *not* acceptable is silently
discovering the wall mid-deliberation and proceeding by default; the
user should know.

### Race-detection preflight (active-tides ledger)

Before the worktree-creation step, check whether a concurrent session is already working on the same logical candidate. The branch-name collision check that `tide-worktree create` does on its own is necessary but not sufficient — two sessions can pick the same logical candidate under *different* branch names, and only discover the duplication at merge time.

The active-tides ledger at `projects/automation/active-tides.md` is the shared source of truth. It is a **local, gitignored, flock-synchronised file** — all parallel sessions on this host share that single file, no `git pull` is involved. It records every in-flight Tide's seabed, branch, and a **one-line semantic description of the direction** (not the branch name). The ledger is bootstrapped from `active-tides.template.md` on first use; periodic `tide-worktree archive` moves terminal entries to `active-tides-archive.md`.

```bash
# Check for in-progress entries with overlapping direction.
.claude/skills/tide/tide-worktree check "<one-line semantic description>"
# Exit 0 = no overlap. Exit 1 = potential overlap (listed on stdout).
```

If `check` surfaces matches, judge whether they're semantically overlapping (the keyword match is a starting point, not the final word). If yes and the match is <24h old, surface to the user that another session may be working on this and ask whether to proceed, pick something else, or abort. The user makes the call; the ledger is informational, not blocking.

### Branch hygiene (preflight)

**Rule: each Tide runs in its own `git worktree`.** Two retrospectives have documented the failure class shared checkouts produce — import-line clobber between `git add` and `git commit`, untracked files vanishing on branch-switch, stray commits landing under the wrong agent's commit message — when concurrent Tide agents share a single Lean-repo working tree. The structural fix is to give each Tide its own worktree.

After passing the race-detection preflight, create a dedicated worktree using the bundled helper, passing the same direction string so the claim lands in the ledger atomically with the worktree:

```bash
.claude/skills/tide/tide-worktree create <repo> <topic> \
    --direction "<one-line semantic description>"
# Creates branch tide/<topic> based on <repo>/main, appends a claim
# entry to active-tides.md under flock (no SRI git commit).
# Echoes the absolute worktree path: sri/lean/<repo>-tide-<topic>/.
```

Omitting `--direction` is supported (and creates a worktree without a ledger entry), but only do so for ad-hoc experimentation outside the Tide protocol. Tides run through the protocol should always claim.

Work in that directory for the rest of the Tide. The worktree shares its `.git` with the canonical clone, so commits are visible across worktrees and merging back is normal git. The worktree directory itself is gitignored (by `sri/lean/.gitignore`'s `*/` rule, same as the canonical clones).

Audit before starting (and at any time):

```bash
.claude/skills/tide/tide-worktree list
```

shows every active Tide worktree across all `sri/lean/<repo>/` repos.

**Linear chains.** When the new Tide must branch off the tip of an unmerged previous Tide — because the new proof depends on a load-bearing piece of scaffolding the previous Tide added — pass the parent branch as the base:

```bash
.claude/skills/tide/tide-worktree create <repo> <topic> tide/<previous> \
    --direction "<text>"
```

This keeps the chain linear and makes the eventual merge straightforward. Otherwise, multiple Tide branches off `main` are *fine* as long as each is in its own worktree; what was previously the "at most one in-flight Tide branch per repo" rule is relaxed by the worktree mechanism.

**After merge or abandonment.** Once the Tide is done (whether it landed on `main` or is being abandoned), release the ledger entry to terminal status. `release` now also removes the worktree by default — a single step:

```bash
.claude/skills/tide/tide-worktree release <repo> <topic> \
    --status merged --note "<commit-SHA or short rationale>"
# Or: --status abandoned --note "duplicate of parallel session's <topic>"
```

`release` updates the entry's `Status:` line in place under flock, then removes the worktree directory — reclaiming the ~8 GB `.lake` Mathlib build cache each worktree carries — while preserving the branch. Do **not** skip this: leaving worktrees around is what let 100+ orphans accumulate to 760 GB of stale `.lake` caches in mid-2026.

Safety: under `--status merged`/`stale`, removal is refused (the ledger update still succeeds) if the tree has uncommitted *tracked* source, so nothing unmerged is destroyed — commit/merge it, then `tide-worktree remove <repo> <topic>`. `--status abandoned` force-discards a dirty tree. Pass `--keep-worktree` to release the ledger entry but leave the directory on disk (then clean it up later with `remove`).

If the entry is stale (the session crashed without releasing), the next `tide-pick` survey refresh will auto-mark entries older than 48h as `Status: stale`; if you discover a stale entry of your own, you can release it manually with `--status stale --note "session crashed at <SHA>"`.

## Step 1. Record the direction

Create a tide log entry at **`lean/<seabed>/tide-log/YYYY-MM-DD-tide-<short-topic>.md`** — *inside the seabed Lean repo*, alongside `retrospectives/`. Write it inside the tide's dedicated worktree (created at preflight), not in the canonical seabed clone; the file commits with the proof on the `tide/<topic>` branch.

This is a routing change from the older `projects/<research>/tide-log/` location. The old path put every tide's process log on the SRI main branch (one commit per tide), and made the SRI history a coordination log rather than a code history. The new path keeps the process log with its proof, in the same repo, on the same branch — no SRI commit at all for the markdown log. Legacy entries in `projects/<research>/tide-log/` stay where they are; new tides write to the seabed location.

First section of the file:

```
# Tide: <short topic>

**Direction (user):** <verbatim>
**Seabed:** <repo>, commit <SHA at start>
**Started:** <ISO date>
```

This file is the single durable process artefact of the tide step. Append to it through Steps 2 and 3.

### What goes where (per Tide step)

A Tide step typically produces several artefacts. Sort them as follows:

- **`lean/<seabed>/tide-log/`** *(inside the seabed worktree)* — *process* records. The deliberation log itself, GPT-5.5 Pro consults preserved verbatim (`gpt55_<topic>_v1.md`, etc.), handoff notes. Committed on the tide branch alongside the proof; lands in the seabed repo's history on merge.
- **`lean/<seabed>/retrospectives/`** — the per-tide LaTeX retrospective (Step 4). Same repo, sibling directory.
- **`projects/<research>/staging/`** *(in SRI)* — *output* drafts not yet integrated into a paper or shared elsewhere. Prose snippets that *might* land in a paper appendix, Python scripts producing figures, the figures themselves, intermediate notes from side excursions. The Tide skill writes here by default; integration into a paper's Overleaf clone is a separate, deliberate step (see the §"Outputs" guidance below).
- **`projects/automation/`** *(in SRI)* — Tide-loop *infrastructure*: the skill itself, cross-project candidates surveys, retrospectives that span many projects. Not per-step logs.

## Step 2. Exploration (Claude ↔ GPT-5.5 Pro)

Goal: agree on a **minimal candidate lemma or theorem** that

- steps outward from the seabed (close enough that the existing skill + library should reach it),
- has a closed-form expectation where possible (e.g. specific potentials like `L = x^4`, `L = x^2 y^4`, specific observables with vanishing or non-vanishing gradients),
- is small — one statement, not a programme.

### Procedure

1. **Read the seabed.** Skim the relevant repo's theorem signatures and `CLAUDE.md`. Note what is already proven and what infrastructure exists. Don't read full proof bodies.
2. **Draft 2–3 candidates.** For each, give: the precise statement (in LaTeX or Lean-flavoured pseudocode), a one-line rationale for why it is the *minimal* useful step, and the expected closed-form value if computable. Append to the log under `## Candidates v1 (Claude)`. *Draft the most specific true thing*: GPT will often propose a strict generalisation that costs nothing extra (a moment family rather than one moment, a substitution lemma for arbitrary `f` rather than a specific monomial). Let it.
3. **Consult GPT-5.5 Pro** via the `timaeus-research` skill. Send the candidates verbatim and ask three specific questions:
   - *Are the statements correct as written?*
   - *Which is the minimal good target — smallest infrastructure delta from the seabed, cleanest closed form?*
   - *Are there better candidates I missed close to this seabed?*

   Save the response verbatim under `## GPT-5.5 Pro v1`.
4. **Integrate.** Read the response, accept or revise. If revising, draft `## Candidates v2 (Claude)` and consult again as `## GPT-5.5 Pro v2`. Do not silently overwrite earlier rounds; future readers (and the next tide step) read the deliberation.
5. **Vote.** A round ends with both parties stating which single candidate they back. Record the votes in the log:

   ```
   ## Vote
   - Claude: candidate B
   - GPT-5.5 Pro: candidate B
   ```

   The candidate is **agreed** when Claude and GPT-5.5 Pro back the same one. Typically one round suffices; the 4-round cap is a safety valve. If they disagree after 4 rounds, surface the disagreement to the user with both positions stated cleanly; do not push to Step 3.

   Micro-divergences on architecture (e.g. Claude votes for `volume.prod` integration while GPT suggested iterated integrals) are not disagreements at this level: vote on the *target candidate*, note the architectural divergence in the log, and let Step 3 resolve it.

### What "minimal" means here

The candidate should feel like the smallest possible step outward — closer to "evaluate the existing machinery on a specific potential" than to "prove a generalisation". If the deliberation keeps producing ambitious general statements, push back: ask GPT explicitly, *"What is the most trivial-looking statement that is still a real step outward?"*

### Sanity check before Step 3

When the candidate has a closed-form expectation that can plausibly be evaluated numerically (a specific potential, finite integrals, scalar coefficients), append `## Numerical check` to the log with a small numpy/scipy snippet (or a hand calculation) comparing the closed form to numerical integration at a concrete parameter value. A mismatch here is vastly cheaper to find than mid-proof.

Not every candidate admits this — some statements are structural (existence, equalities of distributions, identities that don't reduce to a number). When a numerical check isn't feasible, say so explicitly in the log under `## Numerical check` (one line: *"not feasible: <reason>"*) and proceed. Don't fake a check just to populate the section, and don't refuse to proceed because one isn't possible.

## Step 3. Attempted formalisation

Hand off to the `lean-formalisation` skill with:

- the agreed candidate statement (Lean-flavoured pseudocode if not yet pinned to Mathlib symbols),
- the seabed repo to extend,
- a link to the tide log entry,
- the closed-form expectation from the numerical check.

**Branch hygiene.** Work in the dedicated worktree created by the preflight step (the script handles branch creation, ledger claim, and base-ref bookkeeping; you don't need separate `git checkout` or `git worktree add` calls). When the new Tide depends on an unmerged previous Tide's tip, the preflight's `tide-worktree create <repo> <topic> tide/<previous> --direction "<text>"` form keeps the chain linear; otherwise multiple Tides off `main` can run concurrently in parallel worktrees.

When merging stacked Tide PRs sequentially, **retarget all stacked PRs to `main` before the first merge** (or do not delete branches until the entire stack has merged). Otherwise, deleting the base branch on the first merge auto-closes the next PR in the stack, costing a PR number to recover from.

The formalisation runs in a loop until it succeeds. No early stop conditions — it either produces a proof or the user interrupts. Multi-session continuity follows the lean-formalisation skill's handoff discipline (write a handoff note in `notes/` at session boundaries).

When the formalisation succeeds, append a `## Result` section to the tide log entry recording the commit SHA, the theorem names committed, and one or two lines on what surprised us. The bulk of the closing work happens in Step 4.

If the formalisation extends what the project's `lean` field in `projects.json` covers, update the description there.

## Step 4. Retrospective

Every Tide step ends with a per-tide retrospective: a short LaTeX document (typically 1–3 pages of PDF, 100–300 lines of source) that puts the tide in context for a human reader and synchronises the human and AI layers of the process. This is the single artefact the researcher reads to understand what happened, in 10–15 minutes; it is also what the *next* tide reads to inherit the playbook.

A retrospective is not a structured form. It is narrative LaTeX prose, with a human-readable mathematical statement of what was proven, a sketch of how the proof actually works, an honest account of where progress stalled and how it was unblocked (including the decisive GPT-5.5 Pro consults, quoted verbatim where load-bearing), and a separation of what was Mathlib lookup from what was new. The voice treats the reader as a peer, not a manager.

**Do not open the abstract with a session tide-count** (e.g. "Thirty-third tide today.", "Tide 25 of the toric arc.", "T34."). The count is meaningful to the agent during a long loop but is noise to the human reader of the published mirror, and it ages badly once the retrospective is read outside the session that produced it. Open with the mathematical content. If positional context inside an arc genuinely matters (e.g. "closes the four-tide accepts arc opened by ..."), name the arc, not the ordinal.

**Template:** [`projects/automation/retrospective_template.tex`](../../../projects/automation/retrospective_template.tex). Copy and fill in.

**Worked example to read alongside the template:** [`lean/laplace/retrospective.tex`](../../../lean/laplace/retrospective.tex) — the retrospective on the anharmonic 1D Laplace covariance formalisation. It is longer than a per-tide retrospective should be (it covers eight stages rather than one), but the voice, section discipline, and treatment of GPT-5.5 Pro consults are exactly the model. Read this end-to-end before writing your first per-tide retrospective.

Two further exemplars worth skimming if the per-tide template feels under-specified for your case: [`retrospective2.tex`](../../../lean/laplace/retrospective2.tex) (multivariate sharp track, few-day saga) and [`retrospective_tide.tex`](../../../lean/laplace/retrospective_tide.tex) (five-tide synthesis across the 1–2 May run).

**Location:** `<seabed>/retrospectives/<YYYY-MM-DD>-tide-<topic>.tex` in the seabed Lean repo (sibling to the existing `retrospective*.tex`). Committed alongside the proof.

**Mandatory sections** (deviation needs a one-line note saying why):

1. *Setting* — where this tide sits in the broader programme, what the seabed was, why this candidate was the minimal good target.
2. *The thing formalised* — a human-readable mathematical statement, the Lean signature verbatim, one paragraph of context.
3. *Proof strategy* — the mathematician's narrative of how the proof works, naming load-bearing Mathlib lemmas.
4. *Roadblocks and resolutions* — what was hard, GPT consults that pivoted strategy, architectural divergences from the deliberation plan.
5. *What was Mathlib, what was new* — the honest lookup-vs-synthesis accounting.
6. *Lessons* — what carries forward to `CLAUDE.md`, the `lean-formalisation` skill, or this skill.
7. *Follow-ups* — concrete next-tide candidates, deferred upstreaming, deferred paper integration.

After the retrospective lands, append a `## Retrospective` line to the tide log entry pointing at the LaTeX file (e.g. `Retrospective: <seabed>/retrospectives/2026-05-01-tide-quartic-moments.tex`).

### TeX hygiene

Long monospaced identifiers — branch names like `tide/grammar-precursor-bounded-prior`, commit SHAs, file paths like `projects/automation/log/2026-05-02-tide-candidates-survey.md`, fully-qualified Lean names — are the single biggest cause of overfull `\hbox` warnings in retrospectives, because LaTeX cannot break inside `\texttt{...}` and the words are too long for the line.

**Rule.** Keep prose narrative-shaped: in the body, refer to the artefact by a short descriptive name and **put the long monospaced identifier in a footnote**. For example:

```
... extends through five prior tide steps\footnote{Branches:
\texttt{tide/quartic-moments}, \texttt{tide/2d-semi-degenerate},
\texttt{tide/universal-scaling}, \texttt{tide/f1-large-t}, and
\texttt{tide/2d-pure-quartic}.} ...
```

rather than dropping all five branch names inline. The same applies to long file paths, long Lean theorem names, and commit SHAs (which can also be truncated to 7 characters when uniqueness allows).

**Mandatory check.** After running `pdflatex`, grep the log for overfull boxes and fix any that survive:

```bash
pdflatex -interaction=nonstopmode <file>.tex >/dev/null 2>&1
grep -E "Overfull \\\\hbox" <file>.log
```

A clean retrospective produces no overfull-hbox lines. If a residual overfull is genuinely unavoidable (an unbreakable display formula, say), record it explicitly with a one-line LaTeX comment so a future reader knows it was considered.

### Cross-references to earlier tides

When a retrospective references another published tide or experiment, use the `\tideref` / `\experimentref` macros from the template rather than bare `\texttt{...}`:

```latex
The \tideref{2026-05-20-tide-mult-family} run derived the m=2 Bessel-K form.
% Custom link text:
See \tideref[the mult-family tide]{2026-05-20-tide-mult-family} for the closed form.
% Experiments work the same way:
The \experimentref{2026-05-22-experiment-cross-cell-c-fv} measured 0.250.
```

These expand via `hyperref` to an absolute `https://therisensea.org/<kind>/<slug>/` link in the PDF (so the standalone PDF works), and the HTML renderer rewrites them to relative `/<kind>/<slug>/` links on the site itself. Slugs match the filename without extension: e.g. `lean/<seabed>/retrospectives/2026-05-20-tide-mult-family.tex` → `\tideref{2026-05-20-tide-mult-family}`.

### HTML mirror on therisensea.org

**The tide loop does not publish to therisensea.** Once the LaTeX
retrospective is committed in the seabed repo, this skill's
responsibility for human-facing output ends. The HTML mirror at
<https://therisensea.org> is produced by a *separate* publish step,
the [`tide-publish`](../tide-publish/SKILL.md) skill, invoked by the
user or a periodic cron.

Why split it out: the previous in-tide call to `tide-mirror close`
ran with every Tide step, and parallel Tide sessions racing the
home-page regenerate kept clobbering manual header edits (the
Theory/Experiments tab nav was lost repeatedly to this race). The
fix is structural — agents write retrospectives, a single
serialised publish step writes HTML.

**Do not invoke `tide-publish` from inside a Tide loop.** That
re-introduces exactly the race we just removed. A Tide agent's
output is the `.tex` retrospective committed alongside the proof;
the user-driven or scheduled publish run picks it up later.

When the user later asks to publish (or a cron tick fires),
`tide-publish` walks every seabed under `sri/lean/`, renders the
HTML for any retrospective not yet mirrored, splices the home index
between its `<!-- tide-entries:begin/end -->` markers (preserving
everything outside), commits, and pushes — all under a file lock on
the therisensea clone so concurrent publishes serialise.

If you have a one-off reason to render *just* the HTML preview of a
particular retrospective (for example: you want to eyeball the
formatting before committing the `.tex`), the underlying renderer is
still available as `.agents/skills/tide/tide-mirror render <repo>
<slug>`. That subcommand writes only the per-tide page and never
touches the home index; it is the safe "look at how my LaTeX
translates" tool. Use it on a *staging* `.tex` if you must preview;
do not commit the per-tide page from this codepath — let the publish
step do that under the lock.

### Close out any matching survey item

If this Tide originated from a candidate listed in a recent cross-project survey (`projects/automation/log/<YYYY-MM-DD>-tide-candidates-survey.md`, typically within the last ~14 days), update that survey to mark the candidate closed:

```bash
ls -t projects/automation/log/*-tide-candidates-survey.md | head -3
```

Open the most recent survey and locate the matching candidate heading (search by topic, not by numbering — numbering may have shifted in a refresh). The candidate heading should already carry a `🟡 In progress` annotation written by `tide-pick` at handoff time (see the tide-pick skill's "Claim before handoff" sub-section). **Replace** that annotation — do not append a second one — with the closure annotation:

```markdown
### 2. 2D pure-quartic affine covariance ✓ Closed
**Closed by:** `tide/2d-pure-quartic`, commit `<SHA>`,
retrospective `lean/laplace/retrospectives/2026-05-02-tide-2d-pure-quartic.tex`.
```

(The `**Claimed by:** ...` line should be deleted at the same time; it is no longer load-bearing once the candidate is closed.)

Use `✓ Closed` when the headline statement was fully formalised; `~ Partial` when only some sub-cases were taken (note which); `~~struck through~~ — superseded by <other>` when the candidate was decomposed and replaced by a different formulation. Don't delete the entry — `tide-pick` reads completion patterns to calibrate future surveys, and the historical record is cheap.

If the candidate appeared in *multiple* recent surveys (refresh chains), annotate only the most recent one; older surveys stay frozen. The survey edit is now the *only* SRI-side close-out for a typical Tide — the tide-log markdown and the LaTeX retrospective both live in the seabed repo, and the active-tides ledger is gitignored. Commit the survey edit on its own.

If the Tide started without a `🟡 In progress` claim (e.g. it was invoked from a user-named direction that didn't go through `tide-pick`, or `tide-pick` predates this convention), still write the `✓ Closed` annotation; just skip the replace-vs-append step since there is nothing to replace.

If the Tide did *not* originate from any survey (a user-driven direction with no survey ancestry), skip this step.

### Release the active-tides ledger entry

Independently of the survey close-out, mark the active-tides ledger entry terminal. The ledger lives at `projects/automation/active-tides.md` and was claimed at preflight by `tide-worktree create --direction "..."`. Release it now:

```bash
# Headline statement landed:
.claude/skills/tide/tide-worktree release <repo> <topic> \
    --status merged --note "<commit-SHA>"
```

```bash
# Dead-end branch (raced against parallel session, scope shrank to nothing,
# etc.):
.claude/skills/tide/tide-worktree release <repo> <topic> \
    --status abandoned --note "<short rationale>"
```

The `release` command rewrites the entry's `Status:` line in place under flock (no SRI git commit) and then removes the worktree directory in the same step, reclaiming its ~8 GB `.lake` cache (branch preserved). No separate `remove` call is needed in the normal path. If the tree still has uncommitted tracked source under `--status merged`, removal is skipped with a warning (the ledger release still applies) — commit/merge, then run `tide-worktree remove <repo> <topic>`.

If the Tide was claimed without a ledger entry (a direct `tide-worktree create` call without `--direction`, or pre-protocol work), skip this step. Future Tides should always claim through the protocol.

## Outputs: integrating into papers

A Tide step often produces material that *could* belong in a research paper — a primer appendix subsection, a footnote with a numerical check, a worked example, or a `\leanref` margin marker tagging an existing claim. **Never edit paper content (whether the auto-synced `papers/*.tex` files or an Overleaf clone) without explicit user authorisation — the user must explicitly request the paper edit or confirm it for the specific paper in this session.** Standing instructions like "continue with what you think best" do *not* authorise paper edits; they authorise SRI-side / Lean-side work. Paper edits affect shared author-owned artefacts and are out of scope for autonomous Tide work.

The discipline is:

1. **Stage by default.** Write the prose draft (or the proposed `\leanref` additions, with target lines and commit SHA pin) to `projects/<research>/staging/<topic>.{md,tex}`. Self-contained: a statement, a proof sketch, a `\leanref` placeholder if relevant. Do not push to a paper's Overleaf clone, and do not edit `papers/*.tex` (which is auto-synced from Overleaf and would be clobbered anyway).
2. **Integrate only on explicit user authorisation.** When the user explicitly asks for the staged content to land in the paper (and confirms which paper / which Overleaf clone), then a co-author (typically the user themselves, via Overleaf, or a session they explicitly authorise) integrates it. Until that authorisation arrives, the staging note in `projects/<research>/staging/` is the durable artefact and the paper stays untouched.
3. **One-line `\leanref` markers are still staged**, not directly inserted. The "small edit" exemption that earlier versions of this skill carried is removed: even a single `\leanref` marker is a paper edit and needs explicit authorisation. Write the proposed marker (file path + line number + theorem name + commit SHA) into the staging note and wait.

This separation — staged drafts in the SRI repo vs. paper-ready prose in Overleaf, gated on explicit user authorisation — is what keeps Tide outputs from clobbering human-written papers and from making paper changes the author hasn't agreed to.

## Logging discipline (what gets written down)

Per Tide step, the durable artefacts are:

- `lean/<seabed>/tide-log/YYYY-MM-DD-tide-<topic>.md` *(in the seabed repo)* containing, in this order:
  1. Direction (verbatim from the user).
  2. Seabed snapshot (relevant theorem signatures, what's already proven).
  3. Candidates v1 (Claude's drafts).
  4. GPT-5.5 Pro v1 (response preserved verbatim, or a pointer to the saved file).
  5. Candidates v2 / GPT v2, etc., if multiple rounds.
  6. Vote.
  7. Numerical sanity check (or "not feasible: <reason>").
  8. Step 3 hand-off (file path, theorem names, proof sketch).
  9. Result (commit SHA, theorems committed, notes on what surprised us).
  10. Retrospective pointer (path to the per-tide LaTeX retrospective).
- `lean/<seabed>/tide-log/gpt55_<topic>_v1.md` *(in the seabed repo)* — full GPT response. Verbatim. Not a summary.
- `lean/<seabed>/retrospectives/YYYY-MM-DD-tide-<topic>.tex` *(in the seabed repo)* — the per-tide retrospective (Step 4). Committed with the proof.
- `projects/<research>/staging/<topic>.{tex,py,…}` *(in SRI)* — any prose, scripts, or figures that aren't yet integrated into a paper.
- `projects/automation/active-tides.md` *(local, gitignored)* — the per-Tide claim entry (one for each in-flight Tide) lives here. Flock-synchronised; bootstrapped from `active-tides.template.md`. `tide-worktree create --direction "..."` appends; `tide-worktree release` updates the Status line; `tide-worktree archive` evicts old terminal entries to `active-tides-archive.md`. The ledger is the cross-session source of truth for race detection on this host.

The first three artefacts now land in the seabed repo (not the SRI repo). SRI sees only the staging file and the survey-closeout edit per Tide.

These are not optional. Every Tide step writes all four categories (when applicable) and claims-then-releases its ledger entry. The markdown tide log is the process record; the LaTeX retrospective is the human-facing synthesis; the ledger is the cross-session co-ordination layer. Together they make future Tide steps cheaper by recording what was tried, what GPT corrected, what the numerical sanity looked like, and how the proof actually worked.

## References

- [Automation project README](../../../projects/automation/README.md) — the tide framing (seabed / shoreline / rising tide).
- [`lean-formalisation` skill](../lean-formalisation/SKILL.md) — Step 3's engine.
- [`timaeus-research` skill](../timaeus-research/SKILL.md) — GPT-5.5 Pro access for Step 2.
- [Retrospective template](../../../projects/automation/retrospective_template.tex) — Step 4's skeleton.
- [`tide-publish` skill](../tide-publish/SKILL.md) — the separate, user-or-cron-invoked step that mirrors retrospectives to <https://therisensea.org>. Not part of the Tide loop itself.
- Stylistic exemplars for retrospectives: [`retrospective.tex`](../../../lean/laplace/retrospective.tex), [`retrospective2.tex`](../../../lean/laplace/retrospective2.tex), [`retrospective_tide.tex`](../../../lean/laplace/retrospective_tide.tex) in the laplace repo.
- Formalisation Second Steps (gdoc) and Formalising Covariances (gdoc) — the conceptual origin of this loop. Linked from the automation project's `gdocs`.
