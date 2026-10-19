### A:ex:dealer: Dissertation.PaperSpec.A.ex_dealer_riccati
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba122071b255b506300 (pl-fp-v1:cc4f7c9f65263795d51a835db58b108e1bfd02e0fe6c833251a94e1bbe613580)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:19Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:07Z):
Reading of spec:Dissertation.PaperSpec.A.ex_dealer_riccati (Example 5.5, clause "the Riccati
function: p' = beta_1 p^2 - beta_2, p(T) = 1, p > 0 on [0, T], unique").

Paper (05-examples.tex:474-482): "for h_x = 0, with p the positive solution of
p' = beta_1 p^2 - beta_2, p(T) = 1, the tuple Y_t = p(t) X_t, ... solves the system".  The
definite article presupposes existence and uniqueness of such p on [0, T], and positivity.
Parameters: beta_1, beta_2 > 0 (Example 5.1(i), 05-examples.tex:30, which Ex. 5.5 builds on);
horizon T > 0 (standing setting).

Mathematical check: the equilibrium is p* = sqrt(beta_2/beta_1) > 0; backward from p(T) = 1 the
solution moves monotonically toward p* and stays between min(1,p*) and max(1,p*), so it exists on
(-infinity, T], is positive, and is unique (locally Lipschitz right side).

Faithful statement must contain:
- Quantifiers: for all beta_1 > 0, beta_2 > 0 (general, not only the later specialisation
  beta_1 = 1, beta_2 = 1/2; fixing those would be narrower), for all T > 0;
- existence of p with: p differentiable on [0, T] (derivative at interior points, one-sided at
  the endpoints, or two-sided on an open neighbourhood - harmless), p'(t) = beta_1 p(t)^2 - beta_2
  for t in [0, T], p(T) = 1, p(t) > 0 for every t in [0, T];
- uniqueness: any two functions with these properties agree on [0, T] (uniqueness must be modulo
  values outside [0, T] if p : R -> R; a literal "exists unique p : R -> R" with constraints only on
  [0, T] would be false, hence not the paper's claim).  Uniqueness may be among all solutions
  (positivity then automatic) or among positive ones; both readings give the printed "the positive
  solution".
- No constants.
Comparison (verdict recorded 2026-10-19T03:20:16Z):
Comparison for spec:Dissertation.PaperSpec.A.ex_dealer_riccati (Sec5DealerActive.lean:67-76).

Lean: forall beta1 beta2 T, 0 < beta1 -> 0 < beta2 -> 0 < T ->
  (exists p : R -> R, (forall t in [0,T], HasDerivAt p (beta1 * p t^2 - beta2) t) /\ p T = 1
     /\ forall t in [0,T], 0 < p t)
  /\ forall p q : R -> R, (ODE on [0,T]) -> p T = 1 -> (ODE on [0,T]) -> q T = 1 ->
     forall t in [0,T], p t = q t.

Against my reading:
- Quantifiers: general beta1 > 0, beta2 > 0 (not only the specialisation 1, 1/2), every T > 0.
  Matches.
- Existence with p' = beta1 p^2 - beta2 on [0,T], p(T) = 1, p > 0 on [0,T]. Matches.
- Uniqueness: on [0,T] (pointwise equality for t in [0,T]), so values outside [0,T] are not
  constrained - not the false "exists unique p : R -> R". Uniqueness is among ALL solutions with
  p(T) = 1 (positivity not assumed), which is stronger than uniqueness among positive solutions and
  implies the paper's "the positive solution". True (locally Lipschitz right side, solutions bounded
  on the compact interval).
- Derivatives: HasDerivAt (two-sided) at every t in [0, T], including the endpoints. For existence
  this is fine (the solution extends a little beyond both endpoints). For uniqueness the class is
  functions with two-sided derivatives at 0 and T; a solution with only one-sided derivatives at the
  endpoints can be extended beyond them by the local ODE solution to a function with two-sided
  derivatives, without changing it on [0,T], so the uniqueness statement covers that class too.
  Harmless.
- No constants. Hypotheses trivially satisfiable (any beta1, beta2, T > 0).
- The paper does claim this at the revision ("with p the positive solution of p' = beta1 p^2 -
  beta2, p(T) = 1").
Representation choices: p : R -> R with two-sided derivatives on the closed interval [0, T];
uniqueness stated as agreement on [0, T].
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — (1) p is a function R -> R and the ODE is required as HasDerivAt (two-sided) at every t in [0, T],
endpoints included; for existence the solution extends past both endpoints, and for uniqueness any
solution with one-sided endpoint derivatives extends to such a function without changing its
values on [0, T], so the class is effectively the paper's. (2) Uniqueness is stated as agreement on
[0, T] among all solutions with p(T) = 1, which implies uniqueness of "the positive solution".
Disagreements with the author's review (shown 2026-10-19T03:26:58Z): none
