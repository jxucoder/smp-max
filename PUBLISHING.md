# Publishing the results

What has been done for the release and what still needs the owner's own
accounts. State as of 2026-09-09; the evidence ledger is `STATUS.md`.

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
- `f6/OEIS_DRAFT.md`: the exact comment and link texts for A357269,
  A357271 and A344669.
- Independent re-checks (see `STATUS.md`, "Independent checks"): a random
  sample of certified cubes re-solved and re-checked on a second machine
  with the pinned CaDiCaL and the hash-checked arm64 cake_lpr, hashes
  compared record by record; Lean's `leanchecker` run over every module.

## Needs the owner's accounts (in this order)

1. **Zenodo DOI.** Log in to <https://zenodo.org/account/settings/github/>,
   flip the switch for `jxucoder/smp-max`, then create a GitHub release
   (or re-tag: Zenodo archives releases made *after* the switch). Zenodo
   reads `.zenodo.json` for the metadata and mints a DOI within minutes.
   Put the DOI badge in `README.md` and the DOI in `CITATION.cff`
   (`doi:` field) afterwards. The release assets to attach by hand if not
   using the automatic archive: `f6/campaign/campaign.jsonl.gz` (sha256 in
   `f6/CAMPAIGN.md`), `f6/campaign/audit_final.txt`,
   `f6/campaign/lean_identity.txt`, `f5/cubesL/cubesL_results.txt`, the
   three PDFs.
2. **arXiv.** Two submissions, same day, each citing the other and the
   repository:
   - `f6/paper/f6.tex` → primary `math.CO`, cross-list `cs.LO`, `cs.DM`.
     Upload the single `.tex` file (the bibliography is inline, no `.bib`);
     ancillary files: none needed, the repository is the artifact.
   - `f5/paper/f5.tex` → primary `cs.LO`, cross-list `math.CO`.
   Use the abstracts from the `.tex` files verbatim. After the ids are
   assigned, fill them into `f6/OEIS_DRAFT.md`, the `preferred-citation`
   of `CITATION.cff`, and `README.md` ("Background and prior work").
3. **OEIS.** Log in, edit A357269 (add a(6) = 48, the comment and the
   links), A357271 (comment), A344669 (comment) with the texts in
   `f6/OEIS_DRAFT.md`. The editors will ask for a reference they can open:
   the public repository suffices; add the arXiv links when known.
4. **Venues.** `INSIGHTS.md` lists the plan (f(5) paper: ITP 2027; f(6)
   paper: a combinatorics journal or SAT/CP). Artifact evaluation:
   `VERIFYING.md` plus the CI badge.
5. **Optional note to Dan Eilers** (OEIS A357269/A357271/A344669 author),
   who conjectured a(6) = 48 and computed f(5) = 16 in 2022; the papers
   credit him by name.
