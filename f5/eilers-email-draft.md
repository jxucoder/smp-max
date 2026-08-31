# Draft email to Dan Eilers (NOT SENT — owner decides)

**To**: iccinfo@irvine.com (and a copy via ResearchGate message to
https://www.researchgate.net/profile/Dan_Eilers)
**Subject**: Your f(5)=16 result — independent confirmation and a machine-checked proof (Ada)

---

Dear Mr. Eilers,

I am writing about your determination that the maximum number of stable
matchings in the stable marriage problem of order 5 is 16 (OEIS A357269),
and your companion counts of maximal profiles (A344669).

First, the good news: your numbers all check out. Working independently
of your MiniZinc computation, I have:

- re-derived f(5) = 16 by SAT (a witness instance in 0.1s; refutation of
  ">= 17" by three different solver configurations);
- produced what I believe is the first proof certificate for the upper
  bound: the refutation is split into 120 cube formulas, each refuted
  with a DRAT/LRAT proof checked end-to-end by the formally verified
  checker cake_lpr;
- formalized the argument in the Lean 4 proof assistant: a single
  machine-checked theorem (no `sorry`, standard axioms) states that the
  unsatisfiability of those 120 formulas implies f(5) <= 16, alongside a
  kernel-computed proof that an explicit witness has exactly 16 stable
  matchings;
- confirmed A344669(5) = 507,254,400 and your reduced count of 176,130
  by exhaustively enumerating all 4,227,120 canonical solutions.

A short paper describing this is in preparation; it credits the priority
for f(5)=16 and the profile counts to you throughout, and I would be
glad to send you the draft before making anything public. If your own
paper (listed as "in preparation" on the OEIS) has appeared or is close,
I would very much like to cite it properly.

Two questions, if you have the time and inclination:

1. Is there anything you would like stated differently about your 2022
   computation (method, dates, attribution)?
2. I am starting to look at f(6), where your dihedral 48-instance is the
   conjectured optimum (A357271). If you have unpublished notes,
   heuristics, or negative results from your own attempts at n = 6 — or
   thoughts on the pseudo-Latin route — I would be grateful for any
   pointers, with credit of course.

With admiration for your long stewardship of this problem,

Jiarui Xu
jxucoder@gmail.com
(repository with all code, proofs and a verification guide available on
request; it will be made public alongside the paper)

---

Notes for the owner:
- The subject line includes "Ada" because irvine.com's contact page asks
  for it (their spam filter); harmless here.
- Suggested timing: send BEFORE arXiv, so he hears it from us first.
- If he replies with his own paper draft, we cite it; if he does not
  reply within ~2 weeks, proceed with publication (credit is already in
  the paper regardless).
