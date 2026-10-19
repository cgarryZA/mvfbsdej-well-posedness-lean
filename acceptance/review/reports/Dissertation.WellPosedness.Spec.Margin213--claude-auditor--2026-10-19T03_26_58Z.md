### A:conclusion, A:cor:robust, A:eq:monomarginu, A:ex:concrete, A:ex:fulllaw, A:rem:margin, A:rem:regimes, A:sec3:margin-paragraph: Dissertation.WellPosedness.Spec.Margin213
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 2ad64300a1211b964de2010be9bc24c1 (pl-fp-v1:398b904cb81b838e74fbcdb400013f73c7b17f25097bf736508fca6810d81142)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:26:58Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:07Z):
Reading of def:Dissertation.WellPosedness.Spec.Margin213.

The name refers to display (2.13) of the paper. Counting the numbered displays of section 2
(numbering within section): (2.1) eq:compid, (2.2) eq:zeromean, (2.3) eq:hborel,
(2.4) eq:fubiniiso, (2.5) eq:coefmeas, (2.6) eq:lipT, (2.7) eq:mono, (2.8) eq:coupling,
(2.9) eq:couplingT, (2.10) eq:lipfun, (2.11) eq:margproj, (2.12) eq:monomargin,
(2.13) eq:monomarginu.  So Margin213 is the UNWEIGHTED margin form (2.13) of Remark 2.11
(02-model-assumptions.tex:306-315), used by Corollary 3.6 (with margin c_diss > 0), by
Example 5.1(i)'s margin claim, Example 5.4, the paragraph after Cor 3.6 and the conclusion.

Paper notion: coefficients (b, sigma, h, f) (the interior coefficients, deterministic functions
[0,T] x H x P2(H) -> R^n, R^{n x d}, L2(nu;R^n), R^m), coupling matrix G in R^{m x n}, constants
beta_1, beta_2, and a margin c (> 0 in the paper's phrase "with margin c > 0") satisfy (2.13) iff
for a.e. t in [0,T] (Lebesgue) and all diagonal inputs (Theta, mu), (Theta', mu') in D_t, i.e.
Theta, Theta' in L2(Omega, F_t; H) on the standing basis with mu = Law(Theta), mu' = Law(Theta'):
  E[ <db, G^T dY> + <dsigma, G^T dZ>_F + <-df, G dX> + int_E <dh(e), G^T dU(e)> nu(de) ]
   <= -beta_1 E[ |G^T dY|^2 + |G^T dZ|_F^2 + ||G^T dU||^2 ] - beta_2 E|G dX|^2
      - c E[ |dY|^2 + |dZ|_F^2 + ||dU||^2 + |dX|^2 ],
where d psi = psi(t, Theta, mu) - psi(t, Theta', mu'), dX = X - X' etc., G^T dU is the fibrewise
image e |-> G^T dU(e) in L2(nu;R^n), and the nu-integral is the L2(nu;R^n) inner product of dh with
G^T dU.  The last bracket is UNWEIGHTED (no G), which distinguishes (2.13) from (2.12).

Faithful Lean definition must have: the same four coefficients evaluated at (t, Theta(omega), mu)
with mu the law of Theta (diagonal, never a free measure); the time quantifier "for a.e. t" in
[0,T] (or "for all t" would be a stronger, different notion - not faithful unless only used in a
direction where it is harmless); the input class: F_t-measurable square-integrable H-valued
random variables on the standing filtered space (F_t-measurability matters only as the class over
which the inequality is required; requiring it for a larger class, e.g. all F-measurable, would be
a stronger condition); the left side with the correct signs (minus df paired with G dX; G^T on
the backward-type differences, G on dX); the right side with beta_1 multiplying the three G^T
terms (Y, Z, U), beta_2 the G dX term, and c the unweighted sum of all four squared differences;
expectations of real integrands (Bochner; for square-integrable inputs and Lipschitz coefficients
all terms are integrable, so junk values do not arise in the paper's uses, but if the definition is
used without a Lipschitz hypothesis, non-integrable pairings would be read as 0).  The constants
beta_1, beta_2 are those of Assumption 2.4 (the paper's (2.13) is stated with the same
beta_1, beta_2 as (2.7)); whether c > 0 is built in or a separate hypothesis is a harmless choice.
Comparison (verdict recorded 2026-10-19T03:19:50Z):
Comparison for def:Dissertation.WellPosedness.Spec.Margin213 (Spec/CorollaryHyps.lean:54-69).

Lean: Margin213 F P T G beta1 beta2 c C :=
  for a.e. t wrt volume.restrict (Icc 0 T), for all p, p' in diagonalInputs nu n m d F P t:
    Integrable (pairing27 G C t (p.1 w) (p'.1 w) p.2 p'.2) P
    /\ E[pairing27 ...] <= -beta1 * E[|GX G^T dY|^2 + |GZ G^T dZ|^2 + ||GU G^T nu dU||^2]
                           - beta2 * E[|GX G dX|^2]
                           - c * E[|dY|^2 + |dZ|^2 + ||dU||^2 + |dX|^2].

Definitions used (read):
- diagonalInputs (System/DiagonalInputs.lean:44): pairs (Theta, mu) with Theta strongly
  F_t-measurable, MemLp Theta 2 P and mu = lawP2 P Theta. This is D_t of Definition 2.1 (on the
  filtration passed in; the propositions pass the standing enlarged filtration). Strong
  measurability = measurability here since TupleH is second countable under the instance
  hypotheses (sigma-finite nu, countably generated E).
- pairing27 (Spec/Assumptions.lean:165-170): <db, G^T dY> + <dsigma, G^T dZ> + <-df, G dX>
  + int_E <dh(e), G^T dU(e)> nu(de), with dpsi = psi(t, theta, mu) - psi(t, theta', mu') and the
  channel differences of theta - theta'. The nu-integral is taken pointwise on representatives of
  the L2 classes; since both factors are in L2(nu) the integrand is integrable and the integral is
  the L2(nu; R^n) inner product <dh, G^T dU> (no junk value).
- GX G = x |-> G x (R^n -> R^m), GX G^T = y |-> G^T y; GZ G^T = Kronecker (G^T (x) I_d) acting
  columnwise on R^{m x d} represented as EuclideanSpace on Fin m x Fin d (Frobenius norm and
  inner product); GU G^T nu = fibrewise G^T on L2(nu; R^m) (compLpL), a.e. equal to e |-> G^T u(e).
  (System/Operators.lean.)
- Coeffs: b, sigma, h, f functions of (t, theta in TupleH, mu in P2(TupleH)) into R^n, R^{n x d},
  L2(nu; R^n), R^m (System/Coefficients.lean:77-89).

Against my reading of (2.13):
- (2.13) is the unweighted margin form (my equation count): matches - the c-bracket is unweighted
  |dY|^2 + |dZ|_F^2 + ||dU||^2 + |dX|^2, the beta1-bracket has the three G^T terms, beta2 the G dX
  term. Signs (-df paired with G dX) correct.
- Time quantifier: a.e. t in [0, T] (Lebesgue). Matches.
- Diagonal inputs, never a free measure: matches.
- Expectations: Bochner integrals over P. Right-hand integrands are integrable for L2 inputs (G
  bounded), so no junk there.
- Integrability of the pairing is built in (Integrable /\ ...). The paper writes E[...] presupposing
  existence; in every use the coefficients are Lipschitz (Assumption 2.3), under which the pairing is
  integrable along diagonal inputs, so the two readings agree there. Without Lipschitz, requiring
  existence of the expectation is the natural reading. Harmless representation choice.
- c > 0 not built in: harmless (the propositions state c > 0, e.g. "margin c_diss > 0").
Representation choices: built-in integrability of the pairing; nu-pairing via pointwise
representatives (equal to the L2 inner product); matrices as Euclidean vectors with G acting by
Kronecker product (Frobenius structure exact); margin positivity left to the users.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — (1) "The expectation of the pairing exists" (Integrable) is built into the definition; the paper
presupposes it, and in all uses Assumption 2.3 makes the pairing integrable along diagonal inputs,
so nothing changes. (2) The jump pairing int_E <dh(e), G^T dU(e)> nu(de) is computed on pointwise
representatives of L2 classes; both factors are in L2(nu), so it is the L2(nu) inner product.
(3) R^{m x d} is EuclideanSpace on Fin m x Fin d (Frobenius norm/inner product) and G acts by the
Kronecker product G (x) I_d, i.e. columnwise, as in the paper. (4) c > 0 is not part of the
predicate; the propositions using it require c > 0 separately.
Disagreements with the author's review (shown 2026-10-19T03:26:48Z): none
