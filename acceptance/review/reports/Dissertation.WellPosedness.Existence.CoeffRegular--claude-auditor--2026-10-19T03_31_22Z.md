### A:eq:coefmeas: Dissertation.WellPosedness.Existence.CoeffRegular
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash d55f353de2cd99bf9dda27c57cbbc263 (pl-fp-v1:2823e5843a6c6d86617992bb86d50e9fdefd79a829edee23d4da35c67c985079)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:31:22Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:16:08Z):
Reading of def CoeffRegular (used by eq:coefmeas).
Paper notion: "All coefficients are jointly Borel measurable in their arguments; for the jump coefficient
... Borel measurability of (t,theta,mu) |-> h(t,theta,.,mu) into L2(nu;R^n) (2.3)". So the regularity of a
coefficient system (b,sigma,h,f,g) is: b, sigma, f: [0,T] x H x P_2(H) -> R^n, R^{n x d}, R^m jointly Borel;
h: [0,T] x H x P_2(H) -> L2(nu;R^n) Borel; g: R^n x P_2(R^n) -> R^m jointly Borel. Sigma-algebras: Borel
on [0,T] (or R), on H, the Borel sigma-algebra of W_2 on P_2(H) and P_2(R^n), products thereof.
Faithful Lean def: a predicate on a coefficient record stating exactly these measurability conditions (it may
omit g if only b,sigma,f,h are concerned in (2.5); including more conditions such as Lipschitz bounds would
make it stronger than the paper's measurability notion and make (2.5) narrower).
Comparison (verdict recorded 2026-10-19T03:29:18Z):
Comparison, def CoeffRegular (WPZero.lean:92-102) vs reading.
My reading guessed (from the name) that CoeffRegular would be the standing joint Borel measurability of
the coefficients; in the Lean that role is JointBorel, and CoeffRegular is the property (2.5) itself:
"for every ProgTuple (X,Y,Z,U) there is γ with CrossEval ℱ P T C X Y Z U γ", i.e. the drift, diffusion and
driver processes along every progressive tuple, at the tuple's own law flow lawP2 P Θ_s, are jointly and
progressively measurable, and h along it has a jointly measurable marked progressive representative. Its
only use in the statements is as the conclusion of eq_coefmeas (first line of (2.5)).
Against the paper's notion (2.5): the b, σ, f part is the first line verbatim (plus joint measurability);
the law flow is the actual law at each time (a Borel version of the paper's flow); processes are 0 off
[0,T]; the jump part evaluates h at Θ_s (not Θ_{s-}) and asks marked progressive measurability, a weaker
form than the paper's second line (predictable at the left limits) -- irrelevant for the first-line clause
it serves, where it is an extra conclusion. The tuple class (ProgTuple) is broader than the paper's.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) CoeffRegular formalises the property (2.5) of a coefficient system (not the
joint Borel measurability, which is JointBorel); (2) it is quantified over all progressive tuples
(ProgTuple), a class containing the paper's tuples; (3) the law flow is lawP2 P Θ_s at every s (the true
law, itself Borel in s), the coefficient processes are set to 0 off [0,T]; (4) the jump channel is
recorded as a jointly measurable, marked progressively measurable representative of h(s,Θ_s,·,μ_s) --
weaker than the paper's second line of (2.5) (predictable, at Θ_{s-}), which matters for no statement
here since the only use is the first-line clause eq_coefmeas, where this is an extra conclusion. Caveat for
other users: CoeffRegular must not be read as the full second line of (2.5).
Disagreements with the author's review (shown 2026-10-19T03:29:28Z): none
