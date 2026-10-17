### A:eq:coefmeas, A:sec2:coefmeas: Dissertation.WellPosedness.Existence.CoeffRegular
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash d55f353de2cd99bf9dda27c57cbbc263 (pl-fp-v1:2823e5843a6c6d86617992bb86d50e9fdefd79a829edee23d4da35c67c985079)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:33:27Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:31:28Z):
Unit: def Existence.CoeffRegular, used by the claim (2.5) eq:coefmeas / sec2:coefmeas:
"Consequently, along any diagonal input, (s,omega) |-> psi(s, Theta_s(omega), mu_s), psi in
{b, sigma, f}, is progressively measurable and (s,omega,e) |-> h(s, Theta_{s-}(omega), e, mu_s^-)
is predictable."

Paper: (2.5) is a consequence of the standing hypothesis "All coefficients are jointly Borel
measurable in their arguments; for the jump coefficient ... Borel measurability of the map
(t,theta,mu) |-> h(t,theta,.,mu) from [0,T] x H x P_2(H) to L^2(nu;R^n)" (eq:hborel, which follows
from joint pointwise measurability of (t,theta,e,mu) |-> h by Pettis), together with the Borel law
flow of Lemma A.1 and the Fubini isometry (2.4). No continuity or Lipschitz hypothesis is used for
(2.5).

So the notion "coefficients regular" in the sense needed for (2.5) is: b, sigma, f jointly Borel
on [0,T] x H x P_2(H) (H = R^n x R^m x R^{m x d} x L^2(nu;R^m), P_2(H) with the W_2 topology /
its Borel sigma-algebra), h Borel as a map into L^2(nu; R^n) (or jointly measurable in
(t,theta,e,mu)), and g Borel on R^n x P_2(R^n). A faithful Lean definition should be exactly such
a measurability condition. If CoeffRegular instead encodes a regularity of the coefficient
*processes* along a given tuple (e.g. that the evaluations are progressive / predictable), then it
is the conclusion of (2.5) and should be read as such: "progressive" relative to the standing
filtration and "predictable" for h (or a version good enough for the Poisson integral). If it
encodes more (continuity, Lipschitz), it is stronger than the paper's hypothesis and the claim
(2.5) would be narrower.
Comparison (verdict recorded 2026-10-17T12:33:16Z):
CoeffRegular F P T C := for every progressive tuple (X,Y,Z,U) (ProgTuple: X, Y adapted with
right-continuous paths; Z, U jointly measurable, (marked) progressive, finite energy on [0,T]),
there is gamma with CrossEval F P T C X Y Z U gamma: driftProc, diffusionProc, driverProc (the
evaluations psi(s, Theta_s(omega), lawP2 P Theta_s) cut off to [0,T]) jointly measurable and
progressive, and gamma jointly measurable, marked progressive, with
gamma(s,omega,.) = h(s, Theta_s(omega), ., lawP2 P Theta_s) nu-a.e., for a.e. s in [0,T], a.s.

Comparison with my reading. The unit is not the measurability hypothesis of §2 (that is
JointBorel) but the conclusion (2.5), used as such in PaperSpec eq_coefmeas
(JointBorel T C -> CoeffRegular F P T C). As a rendering of (2.5):
* b, sigma, f evaluations progressively measurable: present (b_prog, sigma_prog, f_prog), plus
  joint measurability (implied by progressivity anyway).
* "along any diagonal input": Lean quantifies over every progressive tuple, a class containing
  the paper's tuples (cadlag adapted X, Y; predictable Z, U with the integrability of H^2 or
  H-weak). So the Lean property is at least as strong as the paper's on the paper's tuples.
* laws: the true law at every time, lawP2 P Theta_s (image measure when Theta_s in L^2, junk
  Dirac 0 otherwise), not a Borel representative of the law flow. For tuples of the paper the
  two agree for a.e. s (Lemma A.1); the Lean form avoids choosing a representative and
  requires the true-law evaluation to be progressive, which is stronger. The junk value enters
  only on a measurable set of times that is Lebesgue-null for square-integrable tuples.
* h: the paper's (2.5) says the evaluation at the predictable tuple Theta_{s-}, mu_s^- is
  predictable. CoeffRegular asks only for a jointly measurable, marked progressive
  representative of the evaluation at Theta_s, mu_s (dt x dP x nu class). Theta_s and Theta_{s-}
  agree dt x dP-a.e. (the paper notes either may be used inside dt x dP integrals), and the
  library's compensated integral takes marked progressive integrands and depends only on the
  class; the predictability clause of (2.5) is stated separately (PaperSpec eq_coefmeas_jump).
  So as the first line of (2.5) this is a representation choice, not a loss: what the paper
  uses (2.5) for — making the Lebesgue, Ito and Poisson integrals of the evaluations defined —
  is exactly what CoeffRegular provides.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — 1. Quantifies over all Lean progressive tuples (right-continuous adapted X, Y; progressive Z,
   marked progressive U, finite energy), a superset of the paper's solution-space tuples: the
   property is at least as strong as (2.5) on the paper's tuples.
2. Evaluates along the true laws lawP2 P Theta_s (Dirac-0 junk off L^2) instead of the Borel
   representatives of Lemma A.1; they agree for a.e. s on square-integrable tuples, and the
   Lean form is the stronger requirement.
3. For h, asks for a jointly measurable, marked progressive representative gamma of
   e |-> h(s, Theta_s, e, mu_s) (nu-a.e., for a.e. s, a.s.) instead of predictability of the
   evaluation at (Theta_{s-}, mu_s^-): the two evaluations agree dt x dP-a.e., the library's
   Poisson integral depends only on the dt x dP x nu class and accepts marked progressive
   integrands, and the predictability statement of (2.5) is a separate clause
   (eq_coefmeas_jump).
Disagreements with the author's review (shown 2026-10-17T12:33:16Z): Agree with the author's one-line description. It omits that for h the definition asks only for
a marked progressive representative of the evaluation at Theta_s (not predictability of the
evaluation at Theta_{s-}, which is a separate clause), and that the laws are the true laws
lawP2 with a Dirac-0 junk value off L^2 rather than Borel representatives; both are harmless
but should be recorded.
