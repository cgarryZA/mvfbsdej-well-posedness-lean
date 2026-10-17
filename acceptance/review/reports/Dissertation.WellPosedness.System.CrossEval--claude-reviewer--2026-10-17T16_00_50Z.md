### A:eq:coefmeas: Dissertation.WellPosedness.System.CrossEval
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash c32e743968a018740000000000000000 (pl-fp-v1:7da7095ff71fcad22444215e5622f225b575148af29e77b2341a322f849929fc)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:00:50Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:42:31Z):
Reading for def:Dissertation.WellPosedness.System.CrossEval (locked before seeing Lean).

Paper context (2.5, eq:coefmeas): along a diagonal input (process Theta with its law flow), the
coefficient processes (s,omega) |-> psi(s, Theta_s(omega), mu_s) (psi in {b, sigma, f}) are
progressively measurable and (s,omega,e) |-> h(s, Theta_{s-}(omega), e, mu^-_s) is predictable;
mu_s, mu^-_s are the Borel law flows of Lemma A.1. A def "CrossEval" presumably is the
evaluation of a coefficient along a tuple process and a law flow, where the law flow may be
supplied separately ("cross": e.g. the coefficients of system 1 along solution 2, as in the
delta psi of Thm 3.1, or a law flow not necessarily the tuple's own).

Faithful: CrossEval(coeff, Theta, mu)(s, omega) = coeff(s, Theta_s(omega), mu_s) (for h:
evaluated at the predictable tuple Theta^-_s = (X_{s-}, Y_{s-}, Z_s, U_s) and mu^-_s, or at
Theta_s with a stated a.e. agreement). If the law flow is a free argument the def is broader
than the diagonal evaluation; the paper's case is the instance mu = the tuple's own law flow
(Borel representative of Law(Theta_s)). The components must be evaluated at the right slots;
the h-evaluation must be in L^2(nu;R^n) (or its pointwise/P(x)E version).
Comparison (verdict recorded 2026-10-17T15:51:35Z):
Comparison for def:Dissertation.WellPosedness.System.CrossEval.

Lean (System/CrossEval.lean): structure CrossEval F P T C X Y Z U gamma : Prop:
 - jump_rep: for a.e. s in [0,T], a.s., e |-> gamma(s,omega,e) is nu-a.e. equal to
   C.h s (tupleAt X Y Z U s omega) (lawP2 P (tupleAt ... s)) (an L^2(nu) element);
 - driftProc, diffusionProc, driverProc of C along Theta (coefficient at (s, Theta_s(omega), lawP2 of
   Theta_s), cut off to [0,T]) jointly measurable and progressively measurable;
 - jumpProc gamma (cut off to [0,T]) jointly measurable and marked progressively measurable.
"Cross": C need not be the system the tuple solves; the law argument is the tuple's own law at each
time (diagonal), not a free law flow. Used in CoeffRegular (for every progressive tuple there is
such a gamma), which is the first line of (2.5) (eq_coefmeas); predictability of the jump
coefficient at a predictable tuple is a separate clause (eq_coefmeas_jump).

Against my reading:
- evaluation coefficient(s, Theta_s(omega), mu_s) with mu_s the tuple's own law: yes (diagonal; my
  reading allowed a free flow as a broader option - here it is the own law, matching the paper).
- b, sigma, f evaluations progressively measurable (and jointly measurable): yes, (2.5) line 1.
- h: evaluated at (Theta_s, mu_s), not at (Theta^-_s, mu^-_s), and asserted to have a jointly
  measurable marked progressive representative gamma, not to be predictable. The two evaluations
  agree dt(x)dP(x)nu-a.e. (cadlag paths jump countably often, mu^-_s = mu_s for a.e. s, Lemma A.1)
  and the library's compensated integral is L^2-isometric, so it depends only on that class; a
  marked progressive square-integrable process is a.e. equal to a P(x)E-measurable one. The
  paper itself reads Poisson integrands through P(x)E representatives modulo null sets (2.4). The
  predictability statement of (2.5) is formalised separately (eq_coefmeas_jump), so CrossEval is
  not the place where it is lost. Representation choice.
- junk: lawP2 is the Dirac mass at 0 when Theta_s is not in L^2, and tupleAt lifts U_s(omega,.) to 0
  when it is not in L^2(nu); for the tuples of interest (finite energy) these happen only on
  dt-null / dt(x)dP-null sets, which do not affect integrals; the measurability assertions are
  about the processes as defined (with the junk), which is stronger, not weaker.
- cut-off to [0,T] (0 off the horizon): convention.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) the jump coefficient is evaluated at (Theta_s, mu_s) instead of the
predictable (Theta^-_s, mu^-_s); they agree dt(x)dP(x)nu-a.e. (Lemma A.1) and the library's
compensated integral depends only on the L^2 class; (2) for h the def asserts a jointly measurable,
marked progressively measurable L^2(nu)-representative rather than predictability; such a process
is a.e. equal to a P(x)E-measurable one, and the predictability claim of (2.5) is a separate clause
(eq_coefmeas_jump); (3) processes extended by 0 off [0,T]; (4) the law flow is the tuple's own law
at every time, with the Dirac mass at 0 as junk where Theta_s is not square integrable, and the
U-channel lifted to 0 where U_s(omega,.) is not in L^2(nu): only null sets for finite-energy tuples.
Disagreements with the author's review (shown 2026-10-17T16:00:44Z): No disagreement with the description, but the review should record its relation to (2.5): the
paper's second line asserts predictability of h evaluated at the predictable tuple
(Theta^-_s, mu^-_s), while CrossEval evaluates h at (Theta_s, mu_s) and asks only for a marked
progressive representative. That is harmless (the two evaluations agree dt(x)dP(x)nu-a.e., the library
integral depends only on the L^2 class, and the predictability clause is the separate proposition
eq_coefmeas_jump), but it is a representation choice that a reader of the review should see; the
junk conventions (lawP2 = Dirac 0 off L^2, uLift = 0 off L^2(nu), cut-off to [0,T]) should also be
noted.
