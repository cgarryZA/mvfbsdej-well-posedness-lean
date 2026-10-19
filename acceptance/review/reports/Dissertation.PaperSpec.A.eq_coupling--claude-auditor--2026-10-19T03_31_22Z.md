### A:rem:wasserstein-bounds, A:rem:freelaw: Dissertation.PaperSpec.A.eq_coupling
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba17af7c36ae6c33114 (pl-fp-v1:c06c57a8182b802f4febab5ebac000d011c3ca6dba4ea3d8ef4bffca45217da2)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:31:22Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:08Z):
Reading of spec eq_coupling, clauses "(2.8)" (Remark 2.6) and "the W_2 term is dominated by the synchronous
coupling bound (2.8)" (Remark 5.6).
Setting: at a time t, on the standing probability space, two diagonal inputs (Theta,mu), (Theta',mu'):
Theta, Theta' in L^2(Omega,F_t;H) with mu = Law Theta, mu' = Law Theta' in P_2(H); H with the l2-product
norm |theta|_H^2 = |x|^2+|y|^2+|z|_F^2+||u||^2; W_2 the Villani (Def 6.1) quadratic Wasserstein distance
W_2(mu,mu')^2 = inf over couplings pi of int |theta - theta'|_H^2 dpi.
Claim: W_2(mu,mu')^2 <= E[|dX|^2+|dY|^2+|dZ|_F^2+||dU||^2] = E|Theta - Theta'|_H^2.
Faithful formal: for all t (or any sigma-algebra / any probability space -- broader is fine), all square-
integrable H-valued Theta, Theta' (F_t-measurable), W_2(Law Theta, Law Theta')^2 <= E|Theta-Theta'|_H^2,
with W_2 as defined for H's Hilbert norm, and the right side written as the sum of the four component
squared norms (or as |.|_H^2, if H's norm is the l2 product). If the Lean H carries the sup product norm, the
W_2 in the statement is not the paper's W_2 (I'd flag it at the W_2 definition). Remark 5.6's clause is the
same inequality (it says (2.8) dominates the W_2 term in every use). No hypotheses on coefficients.
Comparison (verdict recorded 2026-10-19T03:29:18Z):
Comparison, eq_coupling (Sec2.lean:74-84) vs reading.
- ∀ probability space (Ω, P), ν σ-finite on countably generated E, n,m,d, Θ, Θ' : Ω → H with
  MemLp Θ 2 P, MemLp Θ' 2 P. The paper's diagonal inputs at t (F_t-measurable, square integrable, on the
  standing basis) are instances; dropping F_t-measurability and the basis is harmless (the bound is
  about laws on one probability space).
- w2H(Law Θ, Law Θ')² ≤ E[|δX|² + |δY|² + |δZ|_F² + ‖δU‖²_{L²(ν)}], w2H the W2 of the Hilbert norm of H
  (via toL2), lawP2 the law in P2(H) (non-junk since Θ ∈ L²), right side a Bochner integral of an
  integrable function. Exactly (2.8) with the paper's W2.
- Remark 5.6's clause is the same inequality. Witness eq_coupling_hypotheses: two distinct L² tuples.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) the paper's W2 on P2(H) is w2H, the Wasserstein distance of the Hilbert
norm realised through toL2 (the product type itself carries the max norm), so the left side is the
paper's W2; (2) the bound is stated for any two square-integrable random tuples on any probability space,
which contains the diagonal inputs at any time t of the standing basis; (3) the expectation of the
four-channel sum is a Bochner integral of an integrable function. Harmless.
Disagreements with the author's review (shown 2026-10-19T03:29:29Z): none
