# OEIS submissions (draft, 2026-09-09)

Text to paste into the OEIS edit forms once the repository is public and
the papers have arXiv identifiers. Submitting needs the owner's OEIS
account; nothing here has been sent. Replace `<arXiv:...>` and keep the
repository link. OEIS style: comments are one paragraph, signed and dated
by the editor form; links go in the Links section as `<a href=...>` lines.

## A357269 — maximum number of stable matchings of an order-n instance

Data: `1, 2, 3, 10, 16` → `1, 2, 3, 10, 16, 48`.

Comment:

> a(6) = 48. The upper bound is a Lean 4 theorem (f6_eq_48_of_unsat in the
> linked repository) whose only hypothesis, the unsatisfiability of 318736
> CNF formulas defined in Lean, is discharged by CaDiCaL refutations each
> checked by the formally verified LRAT checker cake_lpr; the lower bound
> is the dihedral Latin instance of A351413. The proof reduces instances to
> rotation schedules (sequences of cyclic partner exchanges from the
> identity matching): every instance is dominated in stable-matching count
> by the read-off instance of a legal schedule, and the schedule space is
> exhausted by certified SAT refutations. a(5) = 16 is likewise a Lean
> theorem with 120 certified refutations (f5_eq_16_of_unsat). - Jiarui Xu,
> Sep 09 2026

Links:

> Jiarui Xu, <a href="https://github.com/jxucoder/smp-max">smp-max:
> certified maximum numbers of stable matchings</a>, Lean development,
> certificates' audited journal and verification guide (2026).
>
> Jiarui Xu, <a href="<arXiv:f6>">f(6) = 48: the maximum number of stable
> matchings of an order-6 instance</a>, arXiv:<id> [math.CO], 2026.
>
> Jiarui Xu, <a href="<arXiv:f5>">A machine-checked proof that f(5) = 16</a>,
> arXiv:<id> [cs.LO], 2026.

## A357271 — conjectured maxima / lower bounds (composition bounds)

Comment:

> a(6) = 48 is now proved (see A357269 and the link). For n = 7 the lower
> bound 85 (two explicit instances, all rotations of size 2, 20 of 21
> rotations) improves the 81 of the linked Ong et al. (2024) file; the
> instances and a three-way recount are in f7/lb85.txt of the linked
> repository. - Jiarui Xu, Sep 09 2026

Link: the repository link above (f7/lb85.txt).

## A344669 — number of maximal profiles (Eilers)

Comment:

> a(3) = 1092, a(4) = 144 and a(5) = 507254400 independently confirmed by
> brute force (n = 3) and SAT enumeration (n = 4, 5; for n = 5, 4227120
> canonical solutions with man 1's list fixed, times 5! = 120) in the linked
> repository (f5/cube_enum.py, f5/enum_results.txt for n = 5;
> docs/history/NOTES.md for n = 3, 4). - Jiarui Xu, Sep 09 2026

## A351413 (extremal Latin instances) — no change

The dihedral instance is already there; it is the lower-bound witness for
a(6) in A357269 (kernel-checked count: Lower6.lean, dihedral6_count).

## Checklist before submitting

- [ ] repository public (the links must resolve for the editors)
- [ ] arXiv ids known (or submit the repository link alone and add the
      arXiv links in a second edit)
- [ ] the papers' abstracts agree with the comments above (numbers:
      318,736 certificates; 120 at order 5; 85 at order 7)
