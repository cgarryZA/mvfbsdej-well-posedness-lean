### A:eq:coeffdiff: Dissertation.PaperSpec.A.coeffDiffNorm
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash 1d032902209e76e50e3f27b76888b87d (pl-fp-v1:7c26034f9edf2415fdefd8745d6aa29d3dde63e96a03cbe27f8501d57db71adb)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T00:44:30Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T00:30:26Z):
Reading of the notion behind coeffDiffNorm: the coefficient-difference magnitude S_s of Step 1
of the contraction in the proof of Lemma 4.2 (manuscript/paper/sections/04-proof-wellposedness.tex,
lines 312-331), used in (4.9).

Paper's notion: for two trial tuples Theta^1, Theta^2 in S with Borel law flows mu^{Theta^k}_s
(Lemma A.1),
  delta psi_s := psi(s, Theta^1_s, mu^{Theta^1}_s) - psi(s, Theta^2_s, mu^{Theta^2}_s),
  psi in {b, sigma, h, f},
  S_s := |delta b_s| + |delta sigma_s|_F + ||delta h_s||_{L^2(nu)} + |delta f_s|,
a nonnegative function of (s, omega). |.| is the Euclidean norm on R^n, R^m, |.|_F the Frobenius
norm on R^{n x d}, ||.||_{L^2(nu)} the norm of L^2(nu; R^n) (for h, which takes values in
L^2(nu;R^n); if h is represented pointwise in e, the norm is (int_E |delta h(e)|^2 nu(de))^{1/2}).
For h the paper allows evaluation at the left-limit tuple (Theta_s^-, mu^{Theta,-}_s) or at
(Theta_s, mu^Theta_s): the two agree dt x dP-a.e. (text after (4.7)), and S only enters
dt x dP-integrals.

What a faithful Lean definition must be: a function of (the two tuples or their values at s, the
two laws or law flows, the coefficients, s, omega) returning the real number above, with exactly
these four summands, the Euclidean / Frobenius / L^2(nu) norms (not sup norms), and the law
arguments the (Borel) laws of Theta^k_s (or Theta^{k,-}_s for h) under P, in P_2(\mathcal H).
Edge cases: if h is given as a pointwise function of e and the L^2(nu) norm is a Bochner or
lintegral expression, a non-square-integrable difference must not be sent to a junk value that
changes the meaning (for coefficients with values in L^2(nu) this cannot happen; for a pointwise
representation the norm should be the ENNReal lintegral or the L^2 class norm); the norm of a
matrix must be Frobenius (Lean's default operator/sup norm on matrices would differ). The
argument order (Theta^1 minus Theta^2) is immaterial for norms.
Comparison (verdict recorded 2026-10-20T00:43:39Z):
Comparison of Dissertation.PaperSpec.A.coeffDiffNorm (Dissertation/PaperSpec/A/Sec4Frozen.lean)
with S_s of Step 1 of the contraction in the proof of Lemma 4.2
(manuscript/paper/sections/04-proof-wellposedness.tex, lines 312-326: delta psi_s at lines
315-317, S_s at line 326). That passage defines the notion.

coeffDiffNorm P C Theta1 Theta2 s omega :=
  ||b(s, Theta1 s omega, lawP2 P (Theta1 s)) - b(s, Theta2 s omega, lawP2 P (Theta2 s))||_e
  + same for sigma, h, f, in [0, infinity].
- Four summands b, sigma, h, f: as printed.
- Norms: b, f take values in EuclideanSpace (Euclidean norm), sigma in EuclideanSpace on
  Fin n x Fin d (Frobenius norm), h in Lp(EuclideanSpace R^n, 2, nu) (L^2(nu; R^n) norm). As
  printed; no sup norm.
- Arguments: the H-valued values Theta^k_s(omega) and the laws lawP2 P (Theta^k_s), i.e. Law(Theta^k_s)
  when Theta^k_s is square integrable and the Dirac mass at 0 otherwise. The paper uses the Borel
  representative mu^{Theta^k}_s of Lemma A.1, equal to Law(Theta^k_s) for a.e. s; for a trial in S,
  Theta^k_s is square integrable for a.e. s, so the two agree off a Lebesgue-null set of times,
  which is all that matters as S_s enters only dt x dP-integrals.
- h at (Theta_s, mu_s) rather than at the left-limit tuple: the text after (4.7) allows either form
  inside dt x dP integrals.
- [0, infinity]-valued (sum of extended norms), which is the same nonnegative real.

Representation choices (harmless): extended-real value; pointwise law (with a Dirac junk value off
L^2) in place of the Borel law flow; h at (Theta_s, mu_s); the definition takes arbitrary H-valued
processes (it is applied to tupleAt of the trials, whose U channel is the L^2(nu) class of the
coordinates, 0 off L^2(nu), a dt x dP-null set for a tuple of S).
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
(1) The value lies in [0, infinity] as a sum of extended norms. It is the same nonnegative number.
(2) The law argument is lawP2 P (Theta^k_s): the actual law when Theta^k_s is square integrable,
and the Dirac mass at 0 otherwise. The paper uses the Borel representative of Lemma A.1. For a
tuple of S the two agree for a.e. s, and S_s enters only dt x dP-integrals.
(3) h is evaluated at (Theta_s, mu_s) rather than at the left-limit tuple, which the text after
(4.7) allows.
(4) The norms are Euclidean on R^n and R^m, Frobenius on n x d matrices (EuclideanSpace on index
pairs) and L^2(nu) for h, as printed.
Disagreements with the author's review (shown 2026-10-20T00:43:45Z): No disagreement. Two harmless conventions the review leaves implicit. First, the law argument is
the pointwise law lawP2 (a Dirac mass at 0 off L^2), not the Borel representative of Lemma A.1;
they agree for a.e. s for a tuple of S, and S_s enters only dt x dP-integrals. Second, h is
evaluated at (Theta_s, mu_s) rather than at the left-limit tuple, which the text after (4.7)
permits.
