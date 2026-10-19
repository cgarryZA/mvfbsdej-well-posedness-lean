### A:eq:zeromean: Dissertation.PaperSpec.A.eq_zeromean
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1ca027a9d4d1614c9 (pl-fp-v1:e314aa964749e23c86495ea27e32e48d154c51e2f09e3d1fc5ced7502708b61a)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:31:22Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:09Z):
Reading of spec eq_zeromean, clause "the compensated integral has mean zero" ((2.2)).
Setting: standing basis, PRM N with compensator dt x nu, Ntilde = N - dt x nu, nu sigma-finite; predictable
psi: Omega x [0,T] x E -> R (or R^j), calP ⊗ calE-measurable.
Claim: if E int_0^T int_E |psi_s(e)| nu(de) ds < infinity then E int_0^T int_E psi_s(e) Ntilde(ds,de) = 0.
Here the compensated integral of an L^1(dP x ds x nu) predictable integrand is the pathwise difference
int psi dN - int psi dnu ds (int |psi| dN is a.s. finite and integrable by (2.1)); the paper uses (2.2)
precisely for L^1-only integrands (M^2 in Lemma 4.1 with integrand e^s |dU|^2, and the fifth term of
(4.10)), so the statement must cover L^1 integrands, not only L^2 ones (an L^2-isometry integral version
would be narrower). Faithful formal: for all predictable psi with the L^1 condition: the N-integral is
integrable and E[int psi dN - int psi dnu ds] = 0 (equivalently E int psi dN = E int psi dnu ds as reals).
Hypothesis exactly the L^1 condition plus predictability.
Comparison (verdict recorded 2026-10-19T03:29:18Z):
Comparison, eq_zeromean (Sec2Basics.lean:67-79) vs reading.
- Setting as in eq_compid: Lévy driver, σ-finite ν, independent 𝒢₀, filtration enlJoint. Matches.
- ∀ T, ∀ real ψ on Ω × ℝ × E measurable for the marked predictable σ-algebra, with
  E ∫_{(0,T]} ∫_E |ψ| dν ds < ∞ (lintegral). Matches the hypothesis of (2.2) (L¹ only, not L²).
- Conclusion: E[ ∫_{(0,T]×E} ψ(ω,·) dN(ω) - ∫_{(0,T]} ∫_E ψ dν ds ] = 0, the compensated integral read
  pathwise as the difference -- exactly the L¹ reading the paper needs (M² in Lemma 4.1, the fifth term
  of (4.10)).
- Junk check: all integrals are Bochner integrals (0 when not integrable). Under the hypothesis, by (2.1)
  E∫|ψ| dN = E∫|ψ| dν ds < ∞, so ψ(ω,·) is N(ω)-integrable a.s., the compensator integral is finite a.s.,
  and the ω-integrand is P-integrable (measurable as a kernel integral); hence the Lean equation is the
  genuine expectation, and cannot be met through the junk value. The statement does not separately
  assert the integrability, which the paper takes for granted; equivalent given (2.1).
- Witness sec2_compensation_nonzero_hypotheses: a nonzero integrable instance.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) predictable = measurable for the marked predictable σ-algebra of the
standing filtration, on Ω × ℝ × E, integrals over (0,T]; (2) the compensated integral of an L¹
integrand is the pathwise difference ∫ψ dN - ∫∫ψ dν ds (the paper's reading for L¹ integrands);
(3) the expectations are Bochner integrals: their junk value 0 is never reached under the L¹ hypothesis,
since the integrand is then integrable by (2.1), so the statement is the paper's.
Disagreements with the author's review (shown 2026-10-19T03:29:29Z): none
