### A:sec:examples: Dissertation.PaperSpec.A.sec5_limin
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba132884b458e231942 (pl-fp-v1:fd036e103f5368cf4f20517beaf40eb130251cb1b72529ed48017c688017ea08)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:31:22Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:08Z):
Reading of spec sec5_limin, clause "the system of Li-Min Example 3.2 satisfies (2.3) and Assumptions 2.2-2.3
and has no solution on T = 3pi/4 from an initial datum of nonzero mean" (§5 preamble).
The manuscript does not print the system; from Li-Min (arXiv:1812.10254) Example 3.2, with m=n=d=1:
 dx = E[y(t)] dt + dB_t + int_E k(t,e) Ntilde(dt,de),  -dy = E[x(t)] dt - z dB_t - int_E k Ntilde,
 x(0)=1, y(3pi/4) = -E[x(3pi/4)].
In the present paper's coefficient form: b = m_Y(mu), sigma = 1, h = u (h(t,theta,e,mu)=u(e)),
f = m_X(mu), g(x,rho) = -b(rho) (barycentre). Li-Min's mean ODE: X' = Y, Y' = -X, X(0)=E xi0,
Y(T) = -X(T): no solution at T=3pi/4 iff E xi0 != 0.
Faithful formal statement: in the standing setting (arbitrary sigma-finite nu on countably generated E;
the paper says "the jump system ... is linear, hence Lipschitz"; any nu, including nu=0 or nu(E)=inf):
 (a) (2.3): (t,theta,mu) |-> h = u is Borel into L2(nu);
 (b) Assumption 2.2: origin values in L^2(0,T) (b(.,0,delta_0)=0, sigma=1, h(.,0,.,delta_0)=0, f=0) and
     xi0 in L^2(Omega,F_0) -- the hypothesis on the datum;
 (c) Assumption 2.3: diagonal Lipschitz bound with some L (e.g. L=1) and lipT for g;
 (d) at T=3pi/4, for every xi0 in L^2(Omega,F_0;R) with E xi0 != 0, there is no solution Theta in S (cadlag
     adapted, S^2 x S^2 x H^2_W x H^2_N, satisfying both identities a.s. for every t) of (1.1) with these
     coefficients (the paper's solution notion; "no adapted solution" -- no Hweak solution is the same by
     Remark 3.4).
Quantifier order: for all bases and all such xi0. Restricting to xi0=1 is narrower than the clause (still Li-
Min's case); restricting nu (e.g. nu finite) narrower. Witness: xi0 = 1 (constant, F_0-measurable).
Comparison (verdict recorded 2026-10-19T03:29:18Z):
Comparison, sec5_limin (Sec5Preamble.lean:32-49) vs reading.
- Setting: Lévy driver with d = 1, ν σ-finite on countably generated E (any activity), 𝒢₀ independent;
  filtration enlJoint; T = 3π/4. Matches the standing setting with n = m = d = 1.
- System: liMinCoeffs ν = (m_Y(μ), 1, u, m_X(μ), -b(ρ)): Li–Min Example 3.2 (checked against
  arXiv:1812.10254, Ex. 3.2). Matches.
- JointBorel (3π/4) (liMinCoeffs ν): includes h Borel into L²(ν) on [0,T] × H × P2(H), i.e. (2.3),
  plus the standing joint Borel measurability of b, σ, f, g. Matches (a) (with more).
- ∀ deterministic x₀, Assumption22 (ξ₀ := x₀ ∈ L²(F_0); origin values in L²(0,T)). Matches (b) for
  Li–Min's datum x(0) = 1; for a random datum ξ₀ ∈ L²(F_0) Assumption 2.2 is the same origin-value
  condition plus the datum's own property, so nothing about the system is lost.
- ∃ L, Assumption23 (L ≥ 0, interior diagonal Lipschitz with the Hilbert W2, terminal (2.6)). Matches (c).
- ∀ ξ₀ : Ω → R¹ with ∫ ξ₀ ≠ 0 (no other condition), no tuple (X,Y,Z,U) is a WeakSolution (H_weak tuple
  satisfying (1.1), with X_T ∈ L²) at T = 3π/4. Paper solutions (in H) are WeakSolutions
  (PaperSolution.toWeakInt), so this is at least the printed non-existence, for every datum of nonzero
  mean, in the larger class H_weak. Matches (d), stronger in the class.
- Witness sec5_limin_hypotheses: a driver (ν = δ_0), an independent 𝒢₀ = ⊥, and a datum of nonzero mean.
Caveat: the meaning of the non-existence rests on WeakSolution being the paper's H_weak solution
notion (a definition in the closure, not one of my units).
Verdict: broader.
Witness: —
Verdict: broader — Broader: non-existence is asserted in H_weak (WeakSolution) rather than in H, and for every datum
ξ₀ with nonzero mean (no measurability/L² requirement), for any σ-finite ν. The printed clause is the
instance: the standing basis, Li–Min's datum ξ₀ = 1 (deterministic, so Assumption22 applies), and the
solution class H, which embeds in H_weak (PaperSolution.toWeakInt), so no H-solution exists either.
Disagreements with the author's review (shown 2026-10-19T03:29:29Z): none
