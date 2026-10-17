### A:rem:uniq-no-integ: Dissertation.WellPosedness.System.singularCoeffs
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 9cbaca3d28850a562cb0f143b2b54981 (pl-fp-v1:fcc8ca9df57698ede3bf5d1eb75d560606fe74d5db986d3e3cd83a7dfdda57d2)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:59:39Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:42:30Z):
Reading for def:Dissertation.WellPosedness.System.singularCoeffs (locked before seeing Lean).

Paper context: Remark 3.4 (rem:uniq-no-integ) says uniqueness (Thm 3.3) needs only Assumptions
2.3-2.5 (Lipschitz, coupling matrix, monotonicity), not Assumption 2.2 (origin integrability),
while existence needs 2.2. A definition named "singularCoeffs" in this context must be a
coefficient system that witnesses the remark: a genuine coefficient system of the paper's class
(deterministic b,sigma,h,f,g with the signatures of Sec. 2: b:[0,T]xHxP2(H)->R^n,
sigma:->R^{n x d}, h:->L^2(nu;R^n), f:->R^m, g:R^n x P2(R^n)->R^m; jointly Borel) which
satisfies Assumptions 2.3, 2.4, 2.5 with some constants L, G, alpha, beta1, beta2 (meeting the
constant constraints of 2.5), and FAILS Assumption 2.2 (e.g. an origin value b(.,0,delta_0)
not in L^2(0,T), such as a t^{-1/2} or t^{-1} singularity at t=0). The singular part must be
theta- and mu-independent (deterministic in t only) so that all diagonal differences are
unaffected and 2.3-2.5 are inherited from a regular base system.

What a faithful Lean definition must be: a coefficient system (of the same Coeffs type used by
the propositions) built from a regular base (e.g. Ex 5.1(i)-type affine system) by adding a
deterministic time-only singular term, whose origin value is not square-integrable on [0,T].
Edge cases to check: Lean's t^{-1} at t=0 is 0 and t^{-1/2} at 0 is 0 (rpow junk), which is
harmless (single time, measure zero); if the singular term is merely non-L^2 but L^1 (t^{-1/2}),
the Bochner integrals in the solution notion are genuine; if it is non-L^1 (t^{-1}), Lean's
Bochner integral returns 0 for non-integrable functions, which could make "solutions" exist
by junk - the meaning then depends on how the solution notion handles integrability.
Must check: is it in the paper's class (measurable, signature), does it satisfy 2.3-2.5, does
it violate 2.2.
Comparison (verdict recorded 2026-10-17T15:43:43Z):
Comparison for def:Dissertation.WellPosedness.System.singularCoeffs.

Lean: singularCoeffs : Coeffs nu 1 1 d := (affineCoeffs 1 0 0 0).addDrift singularDrift, with
affineCoeffs b1 b2 sc hc = (b = -(b1 y), sigma = sc - b1 z, h = hc - b1 u, f = b2 x, g x _ = x)
(Existence/AffineExample.lean), addDrift c adds c t to b only, singularDrift t = (sqrt t)^{-1}.
So: b(t,theta,mu) = t^{-1/2} - y, sigma = -z, h = -u, f = 0, g(x,rho) = x, n = m = 1, any d.

Against my reading:
- In the paper's class: a Coeffs value (deterministic functions with the paper's signatures);
  b is Borel (t^{-1/2} measurable, affine in theta). Yes.
- Built from a regular base (Ex 5.1(i) at beta1 = 1, beta2 = 0, sigma_c = 0, h_c = 0) plus a
  theta- and mu-independent time-only singular drift. Yes.
- Satisfies 2.3 (L = 1), 2.4 (G = 1), 2.5 (G = 1, alpha = 1, beta1 = 1, beta2 = 0; constants
  admissible at m = n: alpha+beta1 > 0, beta1+beta2 > 0): the file proves
  diagonalLipschitz_/terminalLipschitz_/diagonalMonotone_/terminalMonotone_/constants_singularCoeffs.
  The singular term cancels in all diagonal differences (diagDiff_addDrift).
- Fails 2.2: b(t,0,delta_0) = t^{-1/2}, int_0^T t^{-1} dt = infinity (not_coeffOrigin_singularCoeffs).
- Junk values: (sqrt 0)^{-1} = 0 and (sqrt t)^{-1} = 0 for t < 0; only t = 0 in [0,T] is affected,
  a Lebesgue-null time; harmless. t^{-1/2} is in L^1(0,T), so the forward ds-integral is a genuine
  Bochner integral (the file's solution X_t = 2 sqrt t - y_T t uses the true value), no junk-0
  integral is involved.
- Remark 3.4 does not print an example; this def is an auxiliary instance meeting 2.3-2.5 but
  not 2.2, which is exactly what is needed to witness that the uniqueness statement covers
  non-integrable systems. beta2 = 0 differs from Ex 5.1(i)'s beta2 > 0 but is admissible under 2.5
  at m = n.
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-17T15:59:33Z): none
