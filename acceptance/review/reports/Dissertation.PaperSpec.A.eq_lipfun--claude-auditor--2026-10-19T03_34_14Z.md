### A:rem:wasserstein-bounds: Dissertation.PaperSpec.A.eq_lipfun
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba187b5540277706218 (pl-fp-v1:cadfdb4b31fcb2639bbf5e06ecc4470b9019e5c6744b338cdfe4ab607d38bb09)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:34:14Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:14Z):
Reading of spec eq_lipfun: (2.10) in Remark 2.6 (02-model-assumptions.tex:211-221).

Paper claim. Let K be a separable Hilbert space and phibar : H -> K Lipschitz (H the paper's
separable Hilbert space). Then for all mu, mu' in P_2(H):
  | int_H phibar dmu - int_H phibar dmu' |_K <= Lip(phibar) W_2(mu,mu').
Implicit: phibar is Bochner integrable under every mu in P_2(H) (Lipschitz => linear growth and
P_2 => finite first moment), so the means are genuine.
A faithful formal statement: for every separable Hilbert K (a normed/Banach K is broader, fine),
every L-Lipschitz phibar (L = Lip(phibar) or any L >= 0 with the Lipschitz bound, with the same
constant in the conclusion), every mu, mu' probability measures on H with finite second moment:
the inequality with W_2 the quadratic Wasserstein distance (infimum over couplings of
(int |theta - theta'|_H^2 dpi)^{1/2}). A version for a general separable Hilbert (or Polish metric
with norm) space in place of H is broader, instantiation H = the paper's. The norm on H must be the
Hilbert norm (sqrt of the sum of squares). If phibar's integrability is not part of the conclusion,
the Bochner integral junk value must not be the source of truth (it is automatic for P_2, so fine).
Comparison (verdict recorded 2026-10-19T03:32:34Z):
Comparison, eq_lipfun (Sec2.lean:33-43).

For all nu sigma-finite on countably generated E, n, m, d, K a complete separable real inner
product space (separable Hilbert), phi : H -> K and L >= 0 with |phi theta - phi theta'| <= L
|toL2 theta - toL2 theta'| (Lipschitz for the Hilbert norm of H), for all mu, mu' in P_2(H):
|int phi dmu - int phi dmu'|_K <= L w2H(mu,mu'), w2H the Hilbert-norm W_2 (infimum over couplings of
the quadratic cost, of the images under toL2). L any Lipschitz constant (L = Lip(phi) is the
printed case). Integrability of phi under mu not stated; automatic (continuous, linear growth,
P_2), so the means are genuine. H realised as TupleH (max norm) with the Hilbert norm via toL2.
Witness eq_lipfun_hypotheses: phi = y-projection, L = 1.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: H is the product TupleH with the max norm, and the Lipschitz hypothesis and
W_2 use the Hilbert norm through toL2 and w2H, so the inequality is the paper's (2.10); P_2(H) is
the set of laws of finite second moment (same set in either norm); the Lipschitz constant is any L
with the Lipschitz bound (L = Lip(phi) gives the printed form); integrability of phi under P_2 laws
is not stated but automatic, so no junk Bochner value enters.
Disagreements with the author's review (shown 2026-10-19T03:32:45Z): Label only. The review records "faithful"; I record "faithful with representation choices", for
choices it does not list: H is the max-norm product TupleH with the Hilbert norm entering through
toL2 and w2H; the Lipschitz constant is any L with the bound (L = Lip(phi) the printed case); and the
integrability of phi under P_2 laws is not stated but automatic, so the Bochner means are genuine.
No disagreement on the meaning.
