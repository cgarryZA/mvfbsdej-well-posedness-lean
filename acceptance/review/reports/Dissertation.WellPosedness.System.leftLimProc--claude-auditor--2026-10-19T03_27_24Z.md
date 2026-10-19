### A:abstract, A:conclusion, A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:brownian, A:ex:concrete, A:ex:dealer, A:ex:fulllaw, A:intro:limin-comparison, A:intro:mvfbsdej, A:lem:cont, A:lem:lawflow, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:rem:regimes, A:rem:uniq-no-integ, A:sec3:one-null-set, A:sec4:WP-def, A:sec5:overview, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.System.leftLimProc
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash 9171262935c3b1fde4f555261cd0b9ba (pl-fp-v1:1ced7da3bb4fe58d54863ca0fec5bfa9cab6026e5d201d8f57d2308534ad8454)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:24Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:13:12Z):
Reading for def:Dissertation.WellPosedness.System.leftLimProc (locked before any Lean is shown).

Paper notion (sec 1, sec 2): the left-limit process of a cadlag process V (used for X, Y in the
predictable tuple Theta_t^- = (X_{t-}, Y_{t-}, Z_t, U_t)):
  V_{t-}(omega) = lim_{s -> t, s < t} V_s(omega)   for t > 0,
and at t = 0 the standard convention V_{0-} := V_0 (the paper does not discuss t=0 explicitly; at
t = 0 the value is irrelevant: a single time is Lebesgue-null and N({0} x E)=0 a.s.).
Properties used: V_- is predictable when V is cadlag adapted; V_- = V dt x dP-a.e.
A faithful Lean definition: the left limit along s < t (Filter nhdsWithin t (Iio t)) of the path,
e.g. via limUnder; for non-cadlag paths the junk value of limUnder is irrelevant provided the
process it is applied to is cadlag (as in the solution class). It must not be the right limit or
V itself. Whether it is defined on the whole tuple (Theta^-) or on a single component, the Z, U
components must be left untouched.
Comparison (verdict recorded 2026-10-19T03:25:28Z):
Comparison for def:Dissertation.WellPosedness.System.leftLimProc.

Lean: leftLimProc X i s omega = Function.leftLim (fun r => X i r omega) s. Mathlib's leftLim: the limit
along nhdsWithin s (Iio s) when it exists (on R, nhdsWithin s (Iio s) is never bot), and the value
f s itself when the left limit does not exist (junk).
- left limit X_{s-} for cadlag paths at s > 0: yes. Not the right limit, not V itself. OK.
- at s = 0: the value is the left limit of the path from negative times if it exists (X is
  unconstrained off [0,T] in PaperSolution) or X_0 otherwise; the paper's convention X_{0-} = X_0 may
  thus differ, but only at the single time 0, a Lebesgue-null time, and the jump integrand is
  required only for a.e. s (jump_rep) and enters only through its dt x dP x nu class. Harmless.
- non-cadlag paths: junk f s; irrelevant since solution paths have left limits on (0,T] (a.s. in
  PaperSolution, everywhere in Setting.Solution).
- applied per component family (X and Y separately); Z, U untouched in tupleAt
  (leftLimProc X) (leftLimProc Y) Z U. OK.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, harmless:
1. Function.leftLim falls back to the value f s where no left limit exists. Solution paths have
   left limits on (0,T], so this is irrelevant there.
2. At s = 0 the value comes from the (unconstrained) path at negative times, or is X_0, instead of
   the convention X_{0-} = X_0. This concerns a single, Lebesgue-null time, and the left-limit
   tuple enters only for a.e. s and through dt x dP x nu classes.
Disagreements with the author's review (shown 2026-10-19T03:25:40Z): none
