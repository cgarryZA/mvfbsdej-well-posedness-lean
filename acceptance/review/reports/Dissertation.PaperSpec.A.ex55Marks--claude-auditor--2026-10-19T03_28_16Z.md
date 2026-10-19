### A:abstract, A:ex:dealer, A:rem:regimes, A:sec5:overview: Dissertation.PaperSpec.A.ex55Marks
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 9be0f1e1fafbacc538907ec2c3b03cad (pl-fp-v1:b8f6d9575265010865f3b7973f9cc30255db087f3a73543ae21b15ae94a16699)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:28:16Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:19Z):
Reading of def:Dissertation.PaperSpec.A.ex55Marks.

Paper notion (Example 5.5, "Marks and activity" and "The interaction is active"): the mark space
E = {-1,+1} x (0,1], e = (varsigma, q) (side, size), with the sigma-finite intensity
  nu(d varsigma, dq) = c_varsigma q^{-1-rho} dq   on (0,1], for each side varsigma,
with constants c_varsigma > 0 and 0 < rho < 2; then nu(E) = infinity, int_E q^2 d nu < infinity,
h_c(varsigma,q) := varsigma q in L2(nu). In the active specialisation c_{+1} = c_{-1} = (2-rho)/2,
h_c(varsigma,q) = varsigma q, h_x(varsigma,q) = q, so ||h_c|| = ||h_x|| = 1 and <h_c,h_x> = 0
(computation: sum_varsigma c int_0^1 q^{1-rho} dq = 2 (2-rho)/2 / (2-rho) = 1; the cross term is
(c_{+1} - c_{-1})/(2-rho) = 0).

Faithful Lean definition: the measure nu on the mark type (DealerMark) equal to
sum over varsigma in {-1,+1} of c_varsigma * (Lebesgue restricted to (0,1] with density
q^{-1-rho}), i.e. withDensity of q^{-1-rho} on (0,1] (and 0 outside (0,1] if the type is larger),
with the paper's constants (general c_varsigma > 0, 0<rho<2, or the specialised
c = (2-rho)/2), and/or the mark functions h_c = varsigma q, h_x = q as elements of L2(nu). The
density exponent must be -1-rho (giving infinite activity), not e.g. -rho; the sigma-algebra on E
the product of the discrete one on the sides and Borel on (0,1] (countably generated). The
q^{-1-rho} density in ENNReal (ofReal) form is fine; junk Real.rpow at q <= 0 is harmless only if
(0,1] is enforced (q > 0).
Comparison (verdict recorded 2026-10-19T03:26:34Z):
def:Dissertation.PaperSpec.A.ex55Marks (Dissertation/PaperSpec/A/Sec5DealerActive.lean:42-46):
  ex55Marks ϱ := dealerMarks (fun _ => (2 - ϱ) / 2) ϱ,
dealerMarks c ϱ := (Measure.count.prod sizeLeb).withDensity (fun e => ofReal (c e.1 · e.2^(−1−ϱ)))
on DealerMark = Bool × Ioc 0 1 (Examples/Dealer/Marks.lean:87-122), sizeLeb = Lebesgue on (0,1].
Against the reading: ν(dς,dq) = c_ς q^{−1−ϱ} dq on {±1} × (0,1] with counting measure on the sides,
here with the specialisation's c_{+1} = c_{−1} = (2−ϱ)/2. Density exponent −1−ϱ ✓ (infinite
activity for ϱ ≥ 0, ∫q² dν < ∞ for ϱ < 2, proved nearby); Real.rpow evaluated only at q ∈ (0,1]
(subtype), so no junk at q ≤ 0; σ-algebra: discrete on Bool × Borel subtype of (0,1] ✓.
The mark functions h_c, h_x are not part of this definition (they appear where used, e.g.
ex55Linear writes ς q and q; dealerJump elsewhere). Representation choices: ϱ is an arbitrary real
(outside 0 < ϱ < 2 the constant (2−ϱ)/2 ≤ 0 is truncated to 0 by ofReal, giving the zero measure
for ϱ ≥ 2 — a junk range the claims must exclude by hypothesis); only the specialised constants,
not general c_ς > 0 (dealerMarks itself carries the general case).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — ex55Marks ϱ is the specialisation's mark measure ν(dς,dq) = ((2−ϱ)/2) q^{−1−ϱ} dq ⊗ counting on the
sides, on Bool × (0,1]. Choices: (1) the side ς ∈ {−1,+1} is Bool (true = +1), harmless; (2) ϱ is a
free real and the density passes through ENNReal.ofReal, so for ϱ ≥ 2 (outside the paper's
0 < ϱ < 2) the measure degenerates to 0; the claims must (and the paper does) restrict ϱ;
(3) it fixes c_{±1} = (2−ϱ)/2 of the active specialisation; the general c_ς is dealerMarks.
Disagreements with the author's review (shown 2026-10-19T03:27:50Z): No disagreement. One addition: ϱ is a free real, and the density c q^{−1−ϱ} passes through
ENNReal.ofReal, so for ϱ ≥ 2 (c = (2−ϱ)/2 ≤ 0) ex55Marks ϱ is the zero measure. That range lies
outside the paper's 0 < ϱ < 2 and has to be excluded by the propositions' hypotheses, as
ex_dealer_spec_marks does.
