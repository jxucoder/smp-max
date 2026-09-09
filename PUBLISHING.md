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
   assigned, fill them into `OEIS_DRAFT.md`, add a `preferred-citation`
   block to `CITATION.cff`, and replace the `note` of the BibTeX entry in
   `README.md` ("Cite"; optionally also "Background and prior work").
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
