### A:eq:coefmeas: Dissertation.WellPosedness.System.CrossEval
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash c32e743968a018740000000000000000 (pl-fp-v1:7da7095ff71fcad22444215e5622f225b575148af29e77b2341a322f849929fc)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:31:22Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:08Z):
Reading of def CrossEval (used by eq:coefmeas).
Paper notion: the coefficient evaluation along an input: (s,omega) |-> psi(s, Theta_s(omega), mu_s) for
psi in {b,sigma,f}, and (s,omega,e) |-> h(s, Theta_{s-}(omega), e, mu_s^-) for the jump coefficient, where
Theta is a tuple process and mu (mu^-) the Borel law flow. The paper also evaluates one system's coefficients
along another solution (Theorem 3.1: psi^1(t,Theta^2_t,mu^2_t)) -- possibly the "cross" in the name.
A faithful Lean notion: a structure (or function) combining a tuple process Theta and a Borel law flow
mu: [0,T] -> P_2(H) (no requirement that mu_s = Law(Theta_s) is needed for (2.5); if it requires it, it
is the diagonal), producing the composite processes. Faithful if the evaluation is literally
psi(s, Theta_s(omega), mu_s) with mu Borel; extra hypotheses (e.g. requiring measurability of the composite
as a field) would make (2.5) circular / vacuous-content.
Comparison (verdict recorded 2026-10-19T03:29:18Z):
Comparison, def CrossEval (CrossEval.lean:99-129) vs reading.
CrossEval ℱ P T C X Y Z U γ is the predicate: γ represents e ↦ h(s, Θ_s(ω), e, lawP2 P Θ_s) in L²(ν) for
a.e. s ∈ [0,T], a.s.; driftProc, diffusionProc, driverProc (the coefficient evaluations ψ(s, Θ_s(ω),
lawP2 P Θ_s) on [0,T], 0 off it) are jointly and progressively measurable; jumpProc T γ is jointly
measurable and marked progressively measurable. So it is (2.5) along a tuple, for a coefficient system C
(possibly another system's, hence "cross"). In the statements it occurs only inside CoeffRegular, i.e. as
the conclusion of eq_coefmeas -- so my reading's worry (the measurability being a hypothesis, making
(2.5) circular) does not arise.
Against the paper: the composite evaluation is literally ψ(s,Θ_s(ω),μ_s) with μ_s the true law at each
time (Borel in s); the b, σ, f part is the first line of (2.5); the jump part is a progressive,
Θ_s-evaluated representative, weaker than the second line of (2.5) (predictable, at Θ_{s-}), harmless
for the first-line clause.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) CrossEval is the predicate "(2.5) holds along the tuple Θ for the system C"
(it is a conclusion in eq_coefmeas, not a hypothesis); (2) coefficient processes use the true law
lawP2 P Θ_s at every time and are 0 off [0,T]; (3) both joint measurability and progressive measurability
are recorded; (4) the jump channel is a jointly measurable, marked progressively measurable
representative γ of h(s,Θ_s,·,μ_s) -- weaker than the paper's second line of (2.5) (predictable at
Θ_{s-}); harmless for the first-line clause, but CrossEval should not be cited as the full second line.
Disagreements with the author's review (shown 2026-10-19T03:29:28Z): none
