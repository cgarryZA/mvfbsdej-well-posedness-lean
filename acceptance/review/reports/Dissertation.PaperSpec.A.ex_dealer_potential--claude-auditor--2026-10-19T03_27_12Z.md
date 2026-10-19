### A:ex:dealer: Dissertation.PaperSpec.A.ex_dealer_potential
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1c2e5952133294af3 (pl-fp-v1:a6f2a79442cfa0ceaab894f05b2eb9aac3458a22afc926b4b63f94990cdd7a52)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:12Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:11:31Z):
Reading of spec:Dissertation.PaperSpec.A.ex_dealer_potential (clause "the potential: even, convex,
its gradient, bounded and 1-Lipschitz" of Example 5.5, sections/05-examples.tex ~l.350-370).

Paper text: "V(w) := sqrt(1+||w||_{L2(nu)}^2) - 1 ... The potential V is even and convex, with
grad V(w) = w / sqrt(1+||w||^2), ||grad V(w)|| <= 1, Lip(grad V) <= 1, the last because the
second derivative of V has operator norm at most one."

Setting. L2(nu) = L^2(nu; R^m) for the sigma-finite mark measure nu of Section 2; in Example 5.5
(built on Ex. 5.1(i)) n = m = d = 1, so L2(nu) = L^2(nu; R), a real Hilbert space with
||w||^2 = int_E |w(e)|^2 nu(de). No other standing hypothesis matters: the claim is pure Hilbert-
space calculus and holds for every nu (no use of sigma-finiteness or countable generation).

A faithful formal statement must contain, for (every / the) nu and with V w := sqrt(1+||w||^2)-1
on L2(nu) (norm = the L^2(nu) norm, i.e. the Hilbert norm of Mathlib's Lp space with p=2):
 1. Even: for all w, V(-w) = V(w).
 2. Convex: V is convex on the whole space (ConvexOn R univ V).
 3. Gradient: for every w, V is (Frechet) differentiable at w with gradient
    gradV w = (1/sqrt(1+||w||^2)) • w, i.e. HasGradientAt V (gradV w) w, or equivalently
    HasFDerivAt V (innerSL R (gradV w)) w (Riesz identification of the derivative).
    The formula alone, without linking it to the derivative of V, would drop the "its gradient"
    content (narrower). The formula must be exactly w/sqrt(1+||w||^2) (not e.g. w/(1+||w||)).
 4. Bounded: for all w, ||gradV w|| <= 1.
 5. 1-Lipschitz: for all w, w', ||gradV w - gradV w'|| <= ||w - w'|| (LipschitzWith 1 gradV).
 The "second derivative has operator norm <= 1" is the paper's justification, not part of the
 claim; it need not appear.

Quantifiers: universally quantified over w (and w'); over the measure space (E, nu) either
universally (any measure, or any sigma-finite measure) or broader (any real inner-product /
Hilbert space, instance L2(nu;R) gives the printed claim; also L2(nu;R^m) for general m would be
a broader-than-needed but consistent instance). Restricting to the specific dealer mark measure of
"Marks and activity" only would be narrower than the printed generality of this sentence (the
potential is introduced before the marks are fixed), though harmless for the example's use.
No constants, no hypotheses beyond the setting; if the statement carries a hypothesis (e.g.
SigmaFinite nu), it is trivially satisfiable and a witness is immediate (e.g. any finite measure).
Junk values to watch: Real.sqrt is total (sqrt of negative = 0) but 1+||w||^2 > 0, so no junk;
division by sqrt(...) never divides by 0. The norm must be the L^2(nu) norm (not e.g. a sup norm
of some product representation).
Comparison (verdict recorded 2026-10-19T03:16:05Z):
Comparison for spec:Dissertation.PaperSpec.A.ex_dealer_potential
(Dissertation/PaperSpec/A/Sec5.lean:635-643; Mathlib-only statement, no `variable` context).

Item by item against my locked reading:
- Space: `Lp (EuclideanSpace ℝ (Fin 1)) 2 ν` = L^2(ν; R^1), the L2(nu) of Example 5.5
  (n = m = d = 1). Its norm is Mathlib's L^2 norm with the Euclidean norm on R^1 (= |.|), i.e.
  ||w||^2 = int |w(e)|^2 nu(de). Its inner product space structure (L2.innerProductSpace) is the
  L^2(ν) inner product, which is what HasGradientAt uses. Matches.
- V: `fun w => Real.sqrt (1 + ‖w‖ ^ 2) - 1` = sqrt(1+||w||^2) - 1. Matches; no sqrt junk since
  1 + ||w||^2 > 0.
- gradV: `(Real.sqrt (1 + ‖w‖ ^ 2))⁻¹ • w` = w / sqrt(1+||w||^2). Matches; the inverse is never of
  0 (sqrt >= 1), so the `0⁻¹ = 0` convention is not reached.
- Even: `∀ w, V (-w) = V w`. Matches.
- Convex: `ConvexOn ℝ Set.univ V`. Matches.
- Gradient: `∀ w, HasGradientAt V (gradV w) w` links the formula to the Frechet derivative of V
  via the Riesz identification on the Hilbert space L^2. This is the "its gradient" content.
- Bounded: `∀ w, ‖gradV w‖ ≤ 1`. Matches.
- 1-Lipschitz: `∀ w w', ‖gradV w - gradV w'‖ ≤ ‖w - w'‖`. Matches Lip(grad V) <= 1.
- Quantifiers: ∀ measurable space E (any universe) and ∀ measure ν, with no sigma-finiteness or
  countable generation. The paper's sentence sits in the standing setting (nu sigma-finite on a
  countably generated E); the Lean quantifies over all measures, so it is broader in the setting
  only. The claim does not use those standing hypotheses, so the extra generality is genuine but
  harmless; the printed claim is the instance at the paper's (E, nu).
- No hypotheses, so no vacuity question; the listed witness (ex_dealer_hypotheses) concerns the
  claim's other clauses and is not needed for this proposition.
- The mathematical content is true (D gradV(w) has eigenvalues 1/s and 1/s^3 with s >= 1, so
  operator norm <= 1, giving the Lipschitz bound by the mean-value inequality on the convex
  space), so nothing false is being stated.
- The proposition states exactly what the paper claims at f598204 in Example 5.5 ("The potential V
  is even and convex, with grad V(w) = w/sqrt(1+||w||^2), ||grad V(w)|| <= 1, Lip(grad V) <= 1");
  the paper's justification via the second derivative is not stated, correctly.

Verdict: broader (only by quantifying over every measure space instead of the paper's sigma-finite
countably generated one).
Witness: —
Verdict: broader — Broader only in the setting: the proposition quantifies over every measurable space E and every
measure ν (no σ-finiteness, no countable generation), whereas the paper's sentence lives in the
standing setting of §2. Instantiation giving the printed claim: take E the paper's countably
generated mark space and ν its σ-finite intensity (for the example's specialisation, the dealer
mark measure on {−1,+1}×(0,1]); with values in EuclideanSpace ℝ (Fin 1) = ℝ^1 (n = m = d = 1 of
Example 5.5) the five conjuncts are verbatim the paper's: V even, V convex, HasGradientAt V
(w/√(1+‖w‖²)) w for all w, ‖∇V(w)‖ ≤ 1, and ‖∇V(w)−∇V(w')‖ ≤ ‖w−w'‖.
Disagreements with the author's review (shown 2026-10-19T03:27:01Z): No disagreement on substance: I also find the proposition broader only in its setting, with the
five conjuncts verbatim the paper's. Two small precision points about the author's review:
1. The author describes the extra generality as "every σ-finite ν"; the Lean statement
   quantifies over every measurable space E and every measure ν, with no σ-finiteness or
   countable generation at all. Same direction, slightly broader than recorded.
2. The author lists ex_dealer_hypotheses as the witness for ex_dealer_potential too. The
   proposition has no hypotheses, so it needs no witness (listing one does no harm).
