### A:sec:examples: Dissertation.WellPosedness.System.liMinCoeffs
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 0d9a685aa46f2a71719d94d7674f9ea4 (pl-fp-v1:317b4da127a5e5b3619de51505f75f9e69c80248c5dec8bae20d0a60b8d96707)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:31:22Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:08Z):
Reading of def liMinCoeffs (Li-Min Example 3.2 as cited in §5 preamble).
The paper does not print it; Li-Min (arXiv:1812.10254, Ex 3.2, m=n=d=1): dx = E[y]dt + dB + int k Ntilde,
-dy = E[x]dt - z dB - int k Ntilde, y(T) = -E[x(T)], x(0)=1. Hence the coefficient system must be
 b(t,theta,mu) = m_Y(mu),  sigma(t,theta,mu) = 1 (1x1),  h(t,theta,mu) = u in L2(nu;R) (h(e) = u(e)),
 f(t,theta,mu) = m_X(mu),  g(x,rho) = -b(rho) = -int x rho(dx).
(The initial datum x(0)=1 is separate.) Faithful Lean def: exactly these, with Bochner means; sign
conventions matching (1.1): Y_t = g + int_t^T f ds - ..., so f = +m_X. Any other linear system (e.g. b=y
pointwise, or g = -x) would not be Li-Min's Example 3.2 (though could have the same mean ODE).
Comparison (verdict recorded 2026-10-19T03:29:18Z):
Comparison, def liMinCoeffs (LiMinSystem.lean:57-66) vs reading (from Li-Min arXiv:1812.10254 Ex 3.2,
which I read: dx = E[y]dt + dB + ∫ k Ñ, -dy = E[x]dt - z dB - ∫ k Ñ, y(3π/4) = -E[x(3π/4)], x(0)=1,
m=n=d=1). Lean: b = (tupleMean μ).2.1 = m_Y(μ); σ = toLp (fun _ => 1) = 1; h = θ.2.2.2 = u;
f = (tupleMean μ).1 = m_X(μ); g ρ = -barycentre ρ. Exactly the reading, signs matching (1.1)
(Y_t = g + ∫_t^T f ds - ..., with -dy = E[x]dt giving f = +m_X). Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:29:29Z): none
