### A:cor:robust, A:rem:generalrank, A:thm3.1:companion, A:thm:cwp, A:thm:stab: Dissertation.WellPosedness.Existence.coeffJump
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 90dd30b497d4dd12d6d4dda771a35c05 (pl-fp-v1:29fae3d5c341d5bfd94b1ca9e9852331540e6aa621b45fdf7ff46a7ce83300de)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:04:37Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:34:41Z):
Unit: def Existence.coeffJump (used by Thm 3.1, its companion paragraph, Thm 3.5, Cor 3.6,
Rem 3.7).
Paper notion: the jump coefficient evaluated along a tuple, (s, omega, e) |->
h(s, Theta_{s-}(omega), e, mu_s^-), an L^2(nu;R^n)-valued predictable process "read through a
P x E-measurable representative, unique up to dt x dP x nu-null sets" (eq:fubiniiso, (2.5)); in
Thm 3.1 the difference (delta h)(t) = h^1(t, Theta^{2,-}_t, ., mu^{2,-}_t) - h^2(...) is formed from
such evaluations, and in the solution notion the forward Poisson integral integrates it.
A faithful Lean definition: a function (coordinates i in Fin n) (s, omega, e) |-> R that is a
jointly measurable (and suitably progressive/predictable) representative of
e |-> h(s, Theta_s(omega), e, mu_s) in L^2(nu), for a.e. s in [0,T], a.s. (Theta_s in place of
Theta_{s-} is harmless, dt x dP-a.e. equal), with mu_s the law of Theta_s. Which representative
is chosen must not matter; the definition must give a genuine representative whenever the
coefficients are jointly measurable (in particular under the paper's joint Borel measurability),
and must not silently return a junk value (e.g. 0) on a set of positive dt x dP x nu measure
in the situations the statements use. Cut-off off [0,T] is a harmless normalisation.
Comparison (verdict recorded 2026-10-17T12:40:11Z):
coeffJump P T C X Y Z U i s omega e = lpRep nu R^n (1_{[0,T]}(s) h(s, Theta_s(omega), lawP2 P Theta_s), e)_i
(CoeffBorel.lean:106), where Theta_s = tupleAt nu X Y Z U s and lpRep : L^2(nu;V) x E -> V is a
jointly (strongly) measurable map with lpRep(u, .) = u nu-a.e. for every u and lpRep(0,.) = 0
(Law/LpRepresentative.lean:132, chosen from an existence lemma; genuine for every u).
Comparison with the reading:
* It is a representative of e |-> h(s, Theta_s(omega), e, mu_s) for EVERY s in [0,T] and omega (not
  only a.e.), canonical (independent of choices up to nu-null sets), jointly measurable whenever
  (s, omega) |-> h(s, Theta_s, mu_s) is measurable into L^2(nu) (composition with lpRep). No silent 0
  except the cut-off off [0,T] (normalisation: only [0,T] enters) and the junk values of the
  inputs themselves (lawP2's Dirac 0 off L^2, the L^2(nu) class of U when not square integrable),
  which occur only on dt x dP-null sets for tuples of finite energy.
* Evaluated at Theta_s and its true law instead of the predictable tuple Theta_{s-} and mu_s^-:
  for tuples with cadlag X, Y these agree dt x dP-a.e. (the paper says either may be used inside
  dt x dP integrals, §4 and Lemma A.1), and the compensated L^2 integral depends only on the
  dt x dP x nu class; the result is progressive rather than predictable, which the library's
  integral accepts.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — 1. Evaluation at Theta_s and lawP2 P Theta_s rather than at the predictable tuple Theta_{s-} and
   mu_s^-: a.e. equal in dt x dP for cadlag tuples, and the Poisson integral sees only the
   dt x dP x nu class; the process is progressive, not predictable, which the library integral
   accepts.
2. The representative is the canonical lpRep composition, a genuine nu-a.e. representative at
   every (s, omega); its joint measurability is inherited from the measurability of the
   L^2(nu)-valued evaluation.
3. Cut to 0 off [0,T]: normalisation.
Disagreements with the author's review (shown 2026-10-17T15:04:21Z): No disagreement on substance. The author's review is an empty marker with no recorded
comparison; the representation choices listed in my detail are not recorded there.
