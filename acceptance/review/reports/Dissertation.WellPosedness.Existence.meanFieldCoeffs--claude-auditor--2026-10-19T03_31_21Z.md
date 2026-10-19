### A:ex:concrete, A:sec5:overview: Dissertation.WellPosedness.Existence.meanFieldCoeffs
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash e170fd42ef8bf937a752d819f1e43056 (pl-fp-v1:455908fcb0dabe5bda9aa05cf4aad73633ad81518ce2f29a4670d0545a3cdc1d)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:31:21Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:07Z):
Reading of def meanFieldCoeffs (Example 5.1(ii)).
Paper: n=m=d=1, G=1, theta=(x,y,z,u):
  b = -2y - m_Y(mu),  sigma = -2z - m_Z(mu) (1x1 matrix),  h = -2u - m_U(mu) in L2(nu;R) (h(e) = -2u(e)-m_U(mu)(e)),
  f = 2x + m_X(mu),   g(x,rho) = 2x + b(rho)  (b(rho)=int x rho(dx) the barycentre).
m_Psi(mu) = Bochner mean of the Psi-component under mu in P_2(H) (m_U(mu) the Bochner mean in L2(nu)).
Deterministic, time-independent, for arbitrary sigma-finite nu. A faithful Lean def is exactly this five-tuple
with correct signs and coefficients 2 and 1; junk of Bochner integrals for non-integrable measures is irrelevant
on P_2. (Same coefficients as Li-Min Example 3.1.)
Comparison (verdict recorded 2026-10-19T03:29:17Z):
Comparison, def meanFieldCoeffs (MeanField.lean:209-218) vs reading.
b = -(2•y) - (tupleMean μ).2.1 = -2y - m_Y(μ); σ = -(2•z) - (tupleMean μ).2.2.1 = -2z - m_Z(μ);
h = -(2•u) - (tupleMean μ).2.2.2 = -2u - m_U(μ) in L2(ν); f = 2•x + (tupleMean μ).1 = 2x + m_X(μ);
g x ρ = 2•x + barycentre ρ. Signs and coefficients match. m_Ψ are the channels of the Bochner mean
(= marginal Bochner means, tupleMean_eq). Generalised to Coeffs ν n n d (paper n=d=1).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) defined for every n (=m) and d, the paper's case n=d=1 being an instance;
(2) the marginal means are the channels of tupleMean μ (Bochner mean in H), equal to the marginal
Bochner means; (3) h is an L2(ν) class; (4) time over ℝ, ignored. Harmless.
Disagreements with the author's review (shown 2026-10-19T03:29:27Z): No disagreement on substance. Label only: the review records "broader" (general n = m and d); I record
"faithful with representation choices", the printed system being the instance n = d = 1. I agree with the
review's note that the means are genuine (no Bochner junk) only when L²(ν) is separable, which the paper's
standing setting guarantees and the definition does not assume.
