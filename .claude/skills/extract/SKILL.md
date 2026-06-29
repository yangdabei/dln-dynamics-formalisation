---
name: extract
description: >
  Extract the formal content of a paper — definitions, lemmas, propositions, corollaries,
  theorems — into a single markdown file, with proofs transcribed VERBATIM and the whole thing
  reordered so proof dependence is linear (every result preceded by everything its proof uses).
  Use when handed a paper (a local `.tex`/`.md`, or an arXiv id) and asked to "extract the
  statements", "pull out the definitions and results", "convert the theorems/proofs to markdown",
  "make a linear statement list", or to prep a source for downstream formalisation. Proofs usually
  live in an appendix; this skill stitches them back next to their statements in dependency order.
  Operates on **markdown or LaTeX source only** — never a PDF; if no local `.tex`/`.md` is at hand,
  fetch the LaTeX source from arXiv. Output is one `.md` file, not Lean — for turning the extracted
  results into green Lean, hand the file to `auto-formalise`.
---

# extract — linear, verbatim statement+proof extraction from a paper

Turn a paper into **one markdown file** that lists its formal content (every definition, lemma,
proposition, corollary, theorem) with each **proof transcribed verbatim**, ordered so that
**proof dependence is linear**: a result never appears before something its proof relies on.
Papers state results in narrative order and bury proofs in an appendix; this skill reunites
statement with proof and topologically sorts the whole thing bottom-up.

This is a *faithful transcription* task, not a summarisation task. Do not paraphrase, compress,
or "improve" proofs. The output is meant to be the ground-truth statement source that a human or
`auto-formalise` reads next, so fidelity to the paper is the whole point.

## Inputs

- **Source** — the paper as **LaTeX or markdown**: a local `.tex` (or multi-file TeX project) or
  `.md`, or an arXiv id. **Never a PDF.** If only an arXiv id / URL is given, or no local source
  is at hand, fetch the LaTeX source (not the compiled PDF) — see "Getting the source". Ground
  truth; everything in the output must be traceable to it.
- **Selection** (optional) — `all` (default), or a subset ("just §4 and §5", "the main theorem
  and its prerequisites"). Ask once only if the paper is huge and the user was vague.
- **Output path** (optional) — where to write the `.md`. Default:
  `<source-dir>/<source-stem>_statements.md`. Confirm if unsure.
- **Policy flags** (optional, ask if ambiguous; otherwise apply sensible defaults):
  - *Examples* — include or exclude worked examples / explicit counterexample constructions in
    the appendix. Default: **include**, but examples are frequently noise for a statement list,
    so flag the choice in the preamble.
  - *Remarks* — include or drop `Remark` blocks. Default: **include**. (`remove remarks` is a
    common follow-up — see "Editing passes".)
  - *Cited results* — external theorems the paper states but does not prove (e.g. a hardness
    result it imports): include the **statement** with a "stated without proof, as in the paper"
    note. Default: **include**.
  - *Mathlib-first* — for any result that is a **standard fact already in Mathlib** (rank–nullity,
    SVD existence, QR, Frobenius-norm identities, a named classical theorem, etc.), default to
    **pointing at the Mathlib declaration instead of transcribing the paper's proof**: keep the
    statement, and in place of the proof write a one-line `*Mathlib:* \`Matrix.…\`` pointer
    (best-effort decl name + module). This mirrors `auto-formalise`'s Mathlib-first ladder so the
    extracted file feeds straight into reuse rather than re-proving. Default: **on**. Only
    transcribe the paper's own argument for such a result if the user asks, or if the paper's
    proof differs in a load-bearing way (note the divergence).

## Procedure

### 0. Getting the source (LaTeX / markdown only)

Work from text source, never a PDF — the LaTeX carries exact `\begin{theorem}…\end{theorem}`
environments, `\label`/`\ref` cross-references (the dependency graph, for free), and unambiguous
math. If you only have an arXiv id or URL:

- Fetch the **e-print source**, not the PDF: `https://arxiv.org/e-print/<id>` (or `/abs/<id>` →
  "Other formats" → source). It downloads as a `.tar.gz` (occasionally a bare `.tex`/`.gz`).
- Unpack it; a paper is often several files (`main.tex` + `sections/*.tex` + a `.bib`). Find the
  root (the one with `\documentclass`) and follow its `\input`/`\include` to gather all bodies.
- A `.bbl` or `.bib` resolves `\cite` keys to the cited-result names you'll need for "stated
  without proof" rows.

If the arXiv source is unavailable (some papers ship PDF-only), say so and ask the user for a
`.tex`/`.md` — do **not** fall back to reading a PDF.

### 1. Read the whole source

Make a first pass over the *entire* document — every included `.tex`, plus the appendix and any
supplement — before extracting anything. You need the global picture to order results, and
proofs usually sit in a different file/section than their statements. With LaTeX you can grep the
structure fast: list every theorem-like environment and every `\label`/`\ref`/`\eqref` to map
statements to the proofs and lemmas they invoke.

Track, per statement: its **kind** (Definition / Lemma / Proposition / Corollary / Theorem /
Remark), its **number/label** as printed *and* its `\label` key, where the **statement** is, and
where the **proof** is. A statement in the body whose proof is "see Appendix C" gets matched to
that appendix proof; note both numbers (e.g. `Theorem 4.3 (= Theorem C.13)`).

### 2. Build the dependency DAG

For each result, record what its **proof** invokes (other lemmas/props/defs, and any setup
prose it leans on). Edges point statement → its prerequisites. This is the graph you will
topologically sort. Watch for cross-appendix edges — they decide section order (e.g. if
Appendix D's proof cites a proposition proved in Appendix E, then E precedes D in the output,
even if the paper prints D before E).

Definitions used by a proof are prerequisites too: place each definition before its first use.

### 3. Topologically sort, bottom-up

Emit a linear order in which **every result is preceded by all results its proof uses**. Concretely:

- Setup / notation / shared definitions first (the foundations every later proof reads off).
- Then results in dependency order. When the paper's appendix structure already happens to be
  bottom-up within a section, keep that local order; only reorder across sections where a
  forward reference forces it.
- Self-contained results (no internal dependencies — e.g. a standalone combinatorial lemma) can
  go just before the result that needs them.

If the graph has a genuine cycle (rare; usually means two results are proved together), keep
them adjacent and say so in a one-line note.

### 4. Inline the load-bearing setup prose

Proofs often depend on a paragraph of setup that the paper states once and reuses ("Fix a root
vertex…", "define the cross-Gram matrix M_e := …", "the reduced problem is…"). These are not
numbered statements but the proofs are unreadable without them. Lift each such paragraph in as a
short *Setup for X* / italicised note immediately **before** the first statement that needs it,
so the linear file stays self-contained. Do not invent setup — only relocate what the paper
already says.

### 5. Transcribe verbatim, math as LaTeX-in-markdown

- **Statements and proofs are copied faithfully**, not reworded. Preserve the paper's wording,
  case names ("Base case", "Inductive step"), and step labels.
- Render math with `$…$` (inline) and `$$…$$` (display) — GitHub/KaTeX flavour. Keep the paper's
  symbols (e.g. `\operatorname{rank}`, `\mathrm{mat}_e`, `\otimes`, `\overline{G\cdot\theta}`).
- Bold the statement header with its label, e.g. `**Lemma B.1 (Full Tucker rank implies …).**`,
  then the statement, then `*Proof.*` … ending each proof with `$\quad\square$`.
- Reproduce displayed equations the proof refers to; don't drop a line because it "looks
  obvious". Verbatim means verbatim.

### 6. Apply selection / exclusion policy

- Excluded examples: omit the block, and say so explicitly in the preamble ("Per request,
  Appendix F (the … example) is omitted"). Never silently drop content.
- Pure-discussion sections with **no formal statements** (a "why this matters" appendix) can be
  omitted; note it.
- Cited-but-unproved results: keep the statement, mark "stated without proof, as in the paper".
- Mathlib-available standard facts (default *Mathlib-first* on): keep the statement, replace the
  proof with a `*Mathlib:*` pointer to the existing declaration, and record it as a leaf in the
  dependency table (`Depends on → Mathlib`). When unsure whether a clean Mathlib lemma exists,
  flag it as a candidate rather than asserting a decl name you haven't confirmed.

### 7. Assemble the file

Structure:

1. **Title** + one-line provenance (which `.tex`/`.md` file or arXiv id).
2. **Preamble**: what was extracted, the **ordering principle** ("arranged so proof dependence
   is linear; order is bottom-up, differing from the paper's reading order"), and the
   **exclusions** actually applied.
3. The linear sequence of Setup → Definitions → results-with-proofs.
4. A **dependency summary table** at the end (`| Result | Depends on |`) — a quick audit that the
   order is genuinely linear, and a map for whoever reads next.

Write it with one `Write` call. Then sanity-check: grep the file for every statement label to
confirm none was dropped, and that no proof cites a result appearing *later* in the file.

## Editing passes (common follow-ups)

The output is often iterated. Handle these as targeted `Edit`s, preserving everything else:

- **`remove remarks`** — delete each `Remark` block. If a remark is *load-bearing* (a later proof
  cites it — e.g. a "spectators" extension reused downstream), don't break the proof: demote its
  content to an unlabelled note and rewire the citations ("by … with the spectator extension
  above") rather than deleting outright. Update the dependency table. Then grep `Remark` to
  confirm none remain.
- **`drop examples` / `include examples`** — toggle the example blocks; update the preamble note.
- **renumber / retitle sections** — keep the original statement labels intact (they are the link
  back to the paper); only change the surrounding section headers.

After any pass, re-run the two sanity checks (no dropped labels; no forward citations).

## Done when

The file contains every selected statement with its verbatim proof, in an order where no proof
references a later result; load-bearing setup is inlined; exclusions are stated in the preamble;
and the dependency table at the foot matches the body. The file should stand alone — a reader
(or `auto-formalise`) needs only it, not the original source, to see what is being claimed and how
each claim is proved.
