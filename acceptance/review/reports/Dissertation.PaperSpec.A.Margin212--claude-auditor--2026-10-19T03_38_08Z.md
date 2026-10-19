### A:eq:monomargin, A:rem:generalrank, A:rem:margin: Dissertation.PaperSpec.A.Margin212
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 2ad64300a1211b9647d3727884567824 (pl-fp-v1:61069a19a65f6fe5337c169b83b8bc3acca0b75970985f78cd2a0f99c552ab0a)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:38:08Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:18:01Z):
Reading of def:Dissertation.PaperSpec.A.Margin212 (eq. (2.12) eq:monomargin of Remark 2.11).

Paper notion: "(2.7) holds with margin c > 0" if, for a.e. t in [0,T] and all diagonal pairs
(Theta,mu),(Theta',mu') in D_t (the quantifiers of (2.7) in Assumption 2.5),
  E[ <db, G^T dY> + <dsigma, G^T dZ>_F + <-df, G dX> + int_E <dh(e), G^T dU(e)> nu(de) ]
  <= -beta1 E[|G^T dY|^2 + |G^T dZ|_F^2 + ||G^T dU||^2_{L^2(nu)}] - beta2 E|G dX|^2
     - c E[|G^T dY|^2 + |G^T dZ|_F^2 + ||G^T dU||^2 + |G dX|^2],
with dpsi = psi(t,Theta,mu) - psi(t,Theta',mu') (h as an element of L^2(nu;R^n) at the diagonal
input), dX = X - X', etc.; G in R^{m x n}; G^T acting on Y in R^m, column-wise on Z in R^{m x d},
pointwise in e on U(e).

A faithful Lean definition must contain: the same left side as (2.7) (signs, G vs G^T placement,
the L^2(nu) pairing for the jump channel), the beta1 and beta2 terms in the G-WEIGHTED quantities,
the extra margin term c times the sum of the four G-weighted squares (weighted, not unweighted
-- the unweighted one is (2.13)), the quantifiers "a.e. t" and "all diagonal pairs at t"
(diagonal: Theta in L^2(Omega,F_t;H), mu = Law(Theta)), expectations on both sides. Whether c > 0
is part of the definition or a separate hypothesis is a representation choice. Junk values:
expectation of a non-integrable pairing (Bochner 0) -- harmless for L^2 inputs and Lipschitz
coefficients, but the definition alone does not ensure integrability.
Comparison (verdict recorded 2026-10-19T03:34:55Z):
Comparison: def Margin212 F P T G beta1 beta2 c C (PaperSpec/A/Sec2Remarks.lean:199-218).
Lean: for a.e. t in [0,T], all p, p' in D_t: the pairing pairing27 G C t (p.1 w) (p'.1 w) p.2 p'.2
is integrable and
E[pairing] <= -beta1 E[|G^T dY|^2 + |G^T dZ|^2 + ||G^T dU||^2] - beta2 E|G dX|^2
              - c E[|G^T dY|^2 + |G^T dZ|^2 + ||G^T dU||^2 + |G dX|^2].
Reading: (2.12) = (2.7) plus the margin term in the G-WEIGHTED quantities, a.e. t, all diagonal
pairs, expectations on both sides; c > 0 either built in or separate.
- Left side: pairing27 is the left side of (2.7), with the f minus sign, G^T on Y, Z (GZ G^T =
  G^T (x) I_d, i.e. column-wise) and U (GX G^T applied pointwise to U(e) inside int_E ... nu(de)),
  and G on X. Matches.
- Right side: the beta1 term on G^T dY, G^T dZ, GU G^T dU (= e -> G^T dU(e) as an L^2(nu)
  element); the beta2 term on G dX; the margin term c times the SUM OF THE FOUR WEIGHTED squares.
  Weighted, not unweighted. Matches (2.12), and is distinct from Margin213 = (2.13).
- Quantifiers: a.e. t (volume restricted to Icc 0 T), all diagonal inputs (strongly F_t-measurable,
  L^2, with their laws). Matches Assumption 2.5's quantifiers, as (2.12) inherits them.
- Integrability of the pairing required; c not constrained to be > 0 (positivity is separate where
  used).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. The expectation of the pairing is required to exist, as in the formal Assumption 2.5
   (Mono27At). This excludes the Bochner junk value. For L^2 diagonal inputs and Lipschitz
   coefficients the pairing is integrable by Cauchy-Schwarz, so in every intended use the conjunct
   holds.
2. The margin c is a real parameter. The paper's "with margin c > 0" positivity is imposed
   separately wherever the definition is used (e.g. 0 < c in rem_margin_sharp and
   rem_margin_unweighted).
3. The jump-channel pairing is int_E <dh(e), G^T dU(e)> nu(de) over representatives of L^2(nu)
   classes. It does not depend on the representatives, and equals <dh, G^T dU>_{L^2(nu)}.
Disagreements with the author's review (shown 2026-10-19T03:37:56Z): none
