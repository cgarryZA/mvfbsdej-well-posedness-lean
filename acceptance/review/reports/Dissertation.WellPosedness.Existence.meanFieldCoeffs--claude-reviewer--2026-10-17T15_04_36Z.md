### A:ex:concrete: Dissertation.WellPosedness.Existence.meanFieldCoeffs
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash e170fd42ef8bf937a752d819f1e43056 (pl-fp-v1:455908fcb0dabe5bda9aa05cf4aad73633ad81518ce2f29a4670d0545a3cdc1d)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:04:36Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:34:53Z):
Unit: def Existence.meanFieldCoeffs (Example 5.1(ii)).
Paper: n = m = d = 1, G = 1, nu arbitrary sigma-finite. With theta = (x,y,z,u) and the marginal
means m_Psi(mu) = int_H pi_Psi(theta) mu(dtheta) (Bochner means; m_U(mu) in L^2(nu)) and the
barycentre b(rho) = int_{R^n} x rho(dx):
   b = -2y - m_Y(mu),  sigma = -2z - m_Z(mu),  h = -2u - m_U(mu)  (in L^2(nu)),
   f = 2x + m_X(mu),   g(x, rho) = 2x + barycentre(rho).
No time dependence. A faithful Lean definition: exactly these, with the means the genuine
Bochner integrals under mu in P_2(H) (well defined since second moments are finite, so no
junk from non-integrability), the U-mean as an element of L^2(nu) (Bochner mean of the
L^2(nu)-valued coordinate), signs and factors 2, 1 as printed (note the asymmetric signs: minus
for b, sigma, h, plus for f and g). A general-n version with n = m and d arbitrary is acceptable
if the n=m=d=1 instance is the paper's.
Comparison (verdict recorded 2026-10-17T12:40:38Z):
meanFieldCoeffs nu n d : Coeffs nu n n d (Examples/MeanField.lean:209):
  b = -(2 y) - (tupleMean mu).y, sigma = -(2 z) - (tupleMean mu).z, h = -(2 u) - (tupleMean mu).u,
  f = 2 x + (tupleMean mu).x, g x rho = 2 x + barycentre rho,
with tupleMean mu = Bochner integral of theta under mu.law in H (its components are the marginal
means m_Psi(mu), projections being continuous linear; the U-mean is the L^2(nu)-valued Bochner mean)
and barycentre rho = Bochner integral of x under rho.law.
Item by item with Example 5.1(ii): all signs and factors as printed (minus for b, sigma, h; plus for
f and g), no t dependence, means genuine for mu in P_2 (finite second moment implies integrability
of the identity on the separable H of the paper's setting; a Bochner junk 0 could only arise for a
non-separable L^2(nu), outside the paper's countably generated E). General n = m and d; the paper's
system is n = d = 1.
Verdict: broader (general dimension), instance n = d = 1 is the printed one.
Witness: —
Verdict: broader — Instantiation: n := 1, d := 1 (m = n = 1): b = -2y - m_Y(mu), sigma = -2z - m_Z(mu),
h = -2u - m_U(mu) in L^2(nu; R^1), f = 2x + m_X(mu), g(x,rho) = 2x + b(rho), exactly Example 5.1(ii).
Note: the definition carries no countable-generation hypothesis on E; the means are genuine when
L^2(nu) is separable (the paper's standing setting), which the statements assume.
Disagreements with the author's review (shown 2026-10-17T15:04:21Z): No disagreement on substance, but the author's review is an empty marker (only a section heading at
most): it does not record that the definition is broader than the printed system (general
dimensions) nor the instantiation that gives the printed one (n = d = 1, resp. d = 1), which the
review policy asks for a broader definition.
