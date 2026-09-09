# Manuscripts and working notes

The sources and PDFs below are the rebuilt versions from upstream commit
`5e8cb3c`, preserved byte-for-byte while moving them. Their printed dates
remain the authors' original dates; the order-6 paper includes the completed
Lean proof and certificate campaign.

| Document | Scope | Files |
|---|---|---|
| Order 5 | Lean theorem and checked certificates; printed date 2026-08-31 | [PDF](f5/f5-max-stable-matchings.pdf), [TeX](f5/f5-max-stable-matchings.tex) |
| Order 6 | Complete formal reduction, faithfulness and coverage, with external certificate checks; printed date 2026-09-01 | [PDF](f6/f6-max-stable-matchings.pdf), [TeX](f6/f6-max-stable-matchings.tex) |
| Schedule reduction | Earlier working notes, explicitly superseded by the order-6 paper | [PDF](notes/f6-schedule-reduction.pdf), [TeX](notes/f6-schedule-reduction.tex) |

The [ledger](../docs/results.md) records current evidence. Resolve paths and
module filenames quoted inside the manuscripts using the
[migration map](../docs/path-migration.md). Mathematical declarations and
namespace names are unchanged. Rebuild a PDF whenever its TeX source changes;
the `build-papers` workflow compiles all three manuscripts at their new paths.
