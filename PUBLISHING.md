# Publishing the results

The one publication checklist: what is done and what still needs the
owner's own accounts. State as of 2026-09-09; the evidence ledger is
`STATUS.md`, the retrospective is `docs/INSIGHTS.md`, the OEIS texts are
`OEIS_DRAFT.md`.

## Checklist

Done:

- [x] `LICENSE` (Apache-2.0), `CITATION.cff`, `.zenodo.json` (2026-09-09)
- [x] Papers rebuilt from the current sources in CI (`build-papers`):
      `f5/paper/f5.pdf`, `f6/paper/f6.pdf`, `f6/theory.pdf`
- [x] Independent checks: 205-cube re-solve with the pinned toolchain on a
      second machine, hashes compared record by record; `leanchecker` over
      every module (`STATUS.md`, "Independent checks")
- [x] Release-prep pull request #5 merged into `main` (2026-09-09)
- [x] Draft GitHub release `v1.0.0` created (2026-09-09), assets attached:
      `campaign.jsonl.gz` (sha256 `c9026b08…`, 40,943,262 bytes),
      `audit_final.txt`, `lean_identity.txt`, `recheck_2026-09-09.txt`,
      `recheck_2026-09-09.jsonl`, `leanchecker_2026-09-09.txt`,
      `cubesL_results.txt`, `f5.pdf`, `f6.pdf`, `theory.pdf`

Remaining (needs the owner's accounts, in this order):

- [ ] Publish the draft release `v1.0.0` (this creates the tag; do it
      after the Zenodo switch below, and after the current tree is on
      `main`, because the Zenodo snapshot is the tagged tree plus the
      assets — path moves must land before it)
- [ ] Repository public (the OEIS and paper links must resolve); then the
      CI badge for `lean-verify` in `README.md`
- [ ] Zenodo DOI (GitHub integration, see step 1 below); DOI into
      `CITATION.cff` and `README.md`
- [ ] arXiv: both papers, same day (step 2)
- [ ] OEIS: A357269 add a(6) = 48; comments on A357271 / A344669
      (texts in `OEIS_DRAFT.md`; step 3)
- [ ] Venue submissions; artifact evaluation via `VERIFYING.md` + CI
      (step 4)
- [ ] (Optional) note to Dan Eilers (step 5)

## Done in the repository

- `LICENSE`: Apache License 2.0 (the license of the Lean ecosystem this
  builds on; change it if you prefer another, nothing else depends on it).
- `CITATION.cff` and `.zenodo.json`: citation metadata (author, title,
  keywords, license) read by GitHub's "Cite this repository" box and by
  Zenodo's GitHub integration.
- `.github/workflows/build-papers.yml`: compiles `f5/paper/f5.tex`,
  `f6/paper/f6.tex` and `f6/theory.tex` with TeX Live on every push that
  touches them and on manual dispatch; the PDFs are uploaded as the
  `papers` artifact and committed to the repository from that artifact.
- `OEIS_DRAFT.md`: the exact comment and link texts for A357269,
  A357271 and A344669.
- Independent re-checks (see `STATUS.md`, "Independent checks"): a random
  sample of certified cubes re-solved and re-checked on a second machine
  with the pinned CaDiCaL and the hash-checked arm64 cake_lpr, hashes
  compared record by record; Lean's `leanchecker` run over every module.
- Draft release `v1.0.0` on GitHub with the evidence files and the three
  PDFs attached (list above); the repository is still private.

## Needs the owner's accounts (in this order)

1. **Zenodo DOI.** Log in to <https://zenodo.org/account/settings/github/>,
   flip the switch for `jxucoder/smp-max`, then publish the draft release
   `v1.0.0` (Zenodo archives releases made *after* the switch; if the
   release was published earlier, re-tag). Zenodo reads `.zenodo.json`
   for the metadata and mints a DOI within minutes. Put the DOI badge in
   `README.md` and the DOI in `CITATION.cff` (`doi:` field) afterwards.
   The release assets, if attaching by hand instead of using the
   automatic archive: `f6/campaign/campaign.jsonl.gz` (sha256 in
   `f6/CAMPAIGN.md` and `STATUS.md`), `f6/campaign/audit_final.txt`,
   `f6/campaign/lean_identity.txt`, the two `recheck_2026-09-09.*` files
   and `leanchecker_2026-09-09.txt` from `f6/campaign/`,
   `f5/cubesL/cubesL_results.txt`, the three PDFs.
2. **arXiv.** Two submissions, same day, each citing the other and the
   repository:
   - `f6/paper/f6.tex` → primary `math.CO`, cross-list `cs.LO`, `cs.DM`.
     Upload the single `.tex` file (the bibliography is inline, no `.bib`);
     ancillary files: none needed, the repository is the artifact.
   - `f5/paper/f5.tex` → primary `cs.LO`, cross-list `math.CO`.
   Use the abstracts from the `.tex` files verbatim. After the ids are
   assigned, fill them into `OEIS_DRAFT.md`, the `preferred-citation`
   of `CITATION.cff`, and `README.md` ("Background and prior work").
3. **OEIS.** Log in, edit A357269 (add a(6) = 48, the comment and the
   links), A357271 (comment), A344669 (comment) with the texts in
   `OEIS_DRAFT.md`. The editors will ask for a reference they can open:
   the public repository suffices; add the arXiv links when known.
4. **Venues.** f(5) paper: ITP 2027 (CFP around January–March 2027);
   f(6) paper: a combinatorics journal or a SAT/CP venue. Both drafts
   need expanding to venue length. Artifact evaluation: `VERIFYING.md`
   plus the CI badge.
5. **Optional note to Dan Eilers** (OEIS A357269/A357271/A344669 author),
   who conjectured a(6) = 48 and computed f(5) = 16 in 2022; the papers
   credit him by name. Earlier decision: name credit only, no email;
   revisit at publication time.
