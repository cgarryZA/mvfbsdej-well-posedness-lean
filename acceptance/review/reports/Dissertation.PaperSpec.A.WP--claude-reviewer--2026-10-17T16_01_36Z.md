### A:lem:cont, A:lem:small, A:sec4:WP-def: Dissertation.PaperSpec.A.WP
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 4c83187e460bc5017fcd19712e7de906 (pl-fp-v1:aa5f9b41b0d31ce061b748410eea221f317381d70282b20bbc1bd21bae7e651f)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:01:36Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:42:32Z):
Reading for def:Dissertation.PaperSpec.A.WP (locked before seeing Lean).

Paper notion (Sec 4): WP(lambda) holds if the lambda-scaled forced system (4.1) has a unique
solution in HH for EVERY square-integrable forcing q = (q^b, q^sigma, q^h, q^f, q^g_T) with
q^b in L^2(Omega x [0,T]; R^n), q^sigma in L^2(...; R^{n x d}), q^f in L^2(...; R^m) progressively
measurable, q^h predictable (P(x)E-measurable) in L^2(dP dt nu; R^n), q^g_T in L^2(Omega,F_T;R^m).
Fixed: the coefficient system, the initial datum xi_0 (in L^2(F_0)), lambda in [0,1].
Formally: for all admissible q, there exists Theta in HH solving (4.1)_{lambda,q} and any two
HH solutions coincide (as HH elements: X, Y indistinguishable, Z dt(x)dP-a.e., U
dt(x)dP(x)nu-a.e.; or E sup|dX|^2 = E sup|dY|^2 = E int(|dZ|^2+||dU||^2) = 0).
Points to check: quantifier over exactly the admissible forcings (not more, e.g. non-progressive,
not fewer); uniqueness among HH solutions (not Hweak); xi_0 fixed (a version quantifying over
all xi_0 in L^2(F_0) would be a stronger notion, changing the meaning of Lemmas 4.2/4.4 since WP
appears as hypothesis there); lambda a real parameter.
Comparison (verdict recorded 2026-10-17T15:55:54Z):
Comparison for def:Dissertation.PaperSpec.A.WP.

Lean (PaperSpec/A/Setting.lean): WP D hG0 hind0 T lam C xi0 := for all (qb, qsigma, qh, qf, qg) with
PredForcing over enlJoint (Forcing: qb, qsigma, qf jointly measurable, progressive, 0 off [0,T], finite
energy; qh jointly measurable, marked progressive, 0 off [0,T], finite marked energy; qg strongly
F_T-measurable, L^2; plus qh marked predictable): (∃ X Y Z U, ForcedSolution ... lam C xi0 q X Y Z U) ∧
any two ForcedSolutions have X, Y indistinguishable on [0,T] and zero energies of the differences of
Z and U.

Item by item against my reading:
- quantifier over every admissible forcing, exactly the paper's class: q^b, q^sigma, q^f progressive
  and square integrable over Omega x [0,T], q^h predictable (P(x)E-measurable) square integrable for
  dP dt nu, q^g_T in L^2(Omega, F_T): yes. Represented by their extensions by 0 off [0,T] (bijective
  with forcings on [0,T]; the equations only read [0,T]).
- existence of a solution in HH (ForcedSolution includes the HH conditions): yes.
- uniqueness among HH solutions, as HH elements (indistinguishable X, Y on [0,T]; Z dt(x)dP-a.e.,
  U dt(x)dP(x)nu-a.e. via vanishing energies): yes.
- coefficients, lambda and xi0 fixed (xi0 is a parameter, not quantified): yes, as in the paper.
- standing filtration (enlJoint, G0 independent of the driver): yes.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) forcings in coordinates and extended by 0 off [0,T] (each forcing on
[0,T] has exactly one such extension, and (4.1) reads only [0,T]); (2) q^h required jointly
measurable, marked progressive and marked predictable (the paper's P(x)E-measurability), the other
forcings jointly measurable and progressive; (3) uniqueness stated as indistinguishability of X, Y
on [0,T] and vanishing energies of the Z- and U-differences, i.e. equality in HH; (4) xi0 and lambda
are parameters, the coefficients a Coeffs value over the standing filtration enlJoint.
Disagreements with the author's review (shown 2026-10-17T16:01:31Z): The author's review entry is empty (no recorded reading). It should record: the quantifier over
PredForcing (the paper's class, q^h marked predictable) rather than the broader Forcing; xi0 and
lambda fixed parameters (not quantified); uniqueness among HH solutions stated as
indistinguishability of X, Y on [0,T] and vanishing energies of the Z- and U-differences; and the
extension-by-0 convention for forcings.
