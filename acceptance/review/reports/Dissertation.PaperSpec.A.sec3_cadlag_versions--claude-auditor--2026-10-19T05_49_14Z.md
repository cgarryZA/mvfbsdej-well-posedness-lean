### A:sec3:one-null-set: Dissertation.PaperSpec.A.sec3_cadlag_versions
Pins: manuscript A None; project 90f9502669c17b205fb9360fcfbae619d4e499e8; hash ed839d34f480cba18328d3bafc39f8ed (pl-fp-v1:eb7c741d40d22b4375f96ad03b5a2a164c00966d7ad4d0b083048236a488388f)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T05:49:14Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T05:36:17Z):
Reading of the clause "both sides of each identity are cadlag in t: the stochastic integrals of
(1.1) have adapted versions with every path cadlag" (sec. 3, 03-main-results.tex:34-37).

Paper: "A solution of (1.1) is a tuple Theta in S satisfying both identities of (1.1) almost
surely for every t in [0,T] ... Both sides of each identity are cadlag in t, so the exceptional
null set may be taken independent of t." This clause is the first half: the cadlag property.
The left-hand sides X, Y are cadlag by membership in S; the ds-integrals are continuous in t;
what needs a statement is that the stochastic integrals are (have versions that are) cadlag.

Faithful formal statement (on the standing basis: usual conditions, the augmented filtration,
d-dim BM W, PRM N with sigma-finite nu, any T > 0):
 (W) for every progressively measurable (or predictable) matrix-valued integrand phi with
     E int_0^T |phi_s|^2 ds < inf (this covers sigma(s,Theta_s,mu_s) under Assumptions 2.2-2.3
     and Z in H2_W), the Ito integral t -> int_0^t phi dW (t in [0,T]) has a version I~ :
     for every t, I~_t = int_0^t phi dW a.s.; I~ adapted to (F_t); every path of I~ cadlag
     (in fact continuous) on [0,T];
 (N) for every predictable (P (x) calE-measurable) psi with E int_0^T int_E |psi|^2 nu(de) ds
     < inf (covering h(s,Theta_s^-,e,mu_s^-) and U in H2_N), the compensated Poisson integral
     t -> int_0^t int_E psi Ntilde(ds,de) has a version that is adapted with every path cadlag.
A version stated for the general admissible integrand is broader than "the integrals of (1.1)"
and its instance is those integrands. Must hold at arbitrary sigma-finite nu (infinite activity),
every path (not only a.s. -- with the complete filtration these are interchangeable, but the
clause says every path), adaptedness to the paper's filtration, and "version" in the
modification sense (equal a.s. at each fixed t). Narrower if: only finite nu, only the Brownian
integral, only Z and U but not the coefficient integrands, or only "a.s. cadlag". Mismatched if
it states something else (e.g. only that the integral is a martingale, or a version on a
countable dense set only).
Comparison (verdict recorded 2026-10-19T05:47:31Z):
Comparison: Dissertation.PaperSpec.A.sec3_cadlag_versions (PaperSpec/A/Sec3SpaceNorm.lean:37-92)
against my reading.

Lean: for every standing basis (LevyDriver D, 𝒢₀ independent, enlJoint), all n, m, d, T,
coefficients C, a tuple Θ of H_weak (PaperWeakTuple) and a γ with PaperAdmissibleInt (the
integrals of (1.1) along Θ exist; γ represents h(s, Θ⁻_s, ., μ⁻_s)): for each coordinate of each
of the four stochastic integrals of (1.1) -- the Brownian integral of the diffusion process
(row i, sum over j), the compensated Poisson integral of jumpProc γ (coordinate i), the
Brownian integral of Z (row k) and the compensated Poisson integral of U (coordinate k) --
there is M : ℝ → Ω → ℝ with M Adapted to enlJoint, M_t = integral_t a.s. for every
t in [0,T], and for EVERY ω the path right-continuous on [0,T) with left limits on (0,T].

Against my reading:
 (W) Brownian integrals of σ(s,Θ_s,μ_s) and of Z: covered (each row, any d), versions adapted to
     the paper's filtration, every path cadlag on [0,T]. (Continuity is not claimed, nor did
     the clause claim it; cadlag is the clause.)
 (N) compensated Poisson integrals of h(s,Θ⁻_s,·,μ⁻_s) (through its representative γ) and of U:
     covered, at arbitrary σ-finite ν (no finiteness of ν), adapted, every path cadlag.
 Version in the modification sense (a.s. equality at each fixed t in [0,T]): yes.
 Every path, not only a.s.: yes.
 Scope: the integrands are exactly those of (1.1) along Θ, but Θ ranges over H_weak tuples along
 which the integrals exist, with arbitrary coefficients C (no Assumptions 2.2-2.5 and no solution
 property). This is broader than the printed context (both sides of the identities of a solution);
 the printed claim is the instance in which Θ is a solution in S, which supplies hΘ and hA (a
 Solution contains PaperWeakSolutionIntEnl, which extends PaperWeakTuple and PaperAdmissibleInt).
 Hypotheses can be met: the witness sec3_cadlag_versions_hypotheses exhibits a genuine basis
 (d = 1, ν = δ₀), a tuple with nonzero Z and U of energy 1, and admissibility for the
 Example 5.1(i) coefficients, so the statement is not vacuous.
Verdict: broader (any admissible H_weak tuple and any coefficients; instance: a solution).
Witness: —
Verdict: broader — The proposition gives adapted versions, cadlag on [0,T] along every path, for the four stochastic integrals of (1.1): ∫σ dW, the compensated Poisson integral of the jump representative γ, ∫Z dW and the compensated Poisson integral of U. It does so along any tuple of H_weak for which the integrals of (1.1) exist (PaperWeakTuple + PaperAdmissibleInt), for arbitrary coefficients and at arbitrary σ-finite ν. The printed claim concerns the identities of a solution. It is the instance in which Θ is a solution in S: Solution contains PaperWeakSolutionIntEnl, which extends PaperWeakTuple and PaperAdmissibleInt, with its own γ. The witness sec3_cadlag_versions_hypotheses shows that the hypotheses can be met with nonzero integrands.
Disagreements with the author's review (shown 2026-10-19T05:48:52Z): none
