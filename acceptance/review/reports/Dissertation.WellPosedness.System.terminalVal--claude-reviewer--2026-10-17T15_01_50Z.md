### A:cor:robust, A:eq:forced, A:eq:mvfbsdej, A:ex:concrete, A:intro:mvfbsdej, A:lem:cont, A:lem:pert, A:lem:small, A:rem:cwp-class, A:rem:generalrank, A:sec3:one-null-set, A:sec4:WP-def, A:sec4:horizon-not-contractive, A:sec:examples, A:thm3.1:companion, A:thm:cwp, A:thm:stab, A:thm:uniq: Dissertation.WellPosedness.System.terminalVal
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash 553a1e2dd57f8bc4ed26c8f55d7a65f7 (pl-fp-v1:4ceefac89a87e5648d705976585881b1e1045892dff5958e37e6e3f192639e06)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T15:01:50Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:34:23Z):
Reading for def:Dissertation.WellPosedness.System.terminalVal (written before seeing any Lean).

Paper notion. The terminal condition of the backward equation in (eq:mvfbsdej) and the forced
system (eq:forced): g(X_T, Law(X_T)), a random variable omega |-> g(X_T(omega), rho) with
rho = Law(X_T) = P o X_T^{-1} in P_2(R^n) (the "induced terminal law"), g: R^n x P_2(R^n) ->
R^m deterministic. In the forced system it appears as lambda g(X_T, Law(X_T)) + q^g_T; the
scaling and forcing are separate from the terminal value itself.

A faithful Lean definition must:
- evaluate the forward component X at the horizon T (X_T, not X_{T-}, not at another time);
- use the law of X_T under the reference probability P (Measure.map (X T) P), i.e. the
  same law for every omega, not a conditional or empirical law; X_T must be (a.e.) measurable for
  Measure.map not to return junk 0, which is guaranteed for adapted processes; if the law is
  packaged as a probability measure / P_2 element, the underlying measure must be that pushforward;
- compose with the system's terminal function g exactly (no extra lambda or forcing inside);
- result valued in R^m (Euclidean).
Comparison (verdict recorded 2026-10-17T12:39:11Z):
Comparison for System.terminalVal.
Lean (Solves.lean): terminalVal P T C X (k : Fin m) (ω : Ω) : ℝ := C.g (toLp (fun i => X i T ω))
(lawP2 P (fun ω' => toLp (fun i => X i T ω'))) k, with C.g : ℝ^n → P2 ℝ^n → ℝ^m.
- X is evaluated at the horizon T, the value X_T(ω), not a left limit and not at another time.
  Matches.
- Law: lawP2 P X_T, which is the pushforward P.map X_T when X_T ∈ L²(P;ℝ^n) and the Dirac mass
  at 0 otherwise. When X_T ∈ L², this is exactly the paper's Law(X_T) ∈ P₂(ℝ^n), the same law for
  every ω, under the reference P. Matches.
- g is composed exactly. λ and the forcing q^g_T are not inside terminalVal. Coordinate k of
  the ℝ^m value: the vector is recovered from its coordinates. Representation choice.
- Junk: if X_T ∉ L², the law argument is δ₀ rather than undefined. The paper presupposes
  Law(X_T) ∈ P₂ ("As the terminal conditions presuppose Law(X^k_T) ∈ P_2(R^n), we have
  X^k_T ∈ L²", proof of Thm 3.3). So the junk lies outside the paper's domain. For S²-solutions,
  X_T ∈ L² automatically. A statement over the weak class H² that does not itself enforce
  X_T ∈ L² would, however, see g(X_T, δ₀) for such tuples. That should be checked at the spec
  level, for uniqueness over H².
- Euclidean ℝ^n/ℝ^m via WithLp.toLp 2. Matches.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices. (1) The ℝ^m-valued terminal value is given by its coordinates
k ↦ g(X_T(ω), Law X_T)_k, and the forward state by coordinate processes X i : ℝ → Ω → ℝ, assembled
into EuclideanSpace by WithLp.toLp 2. (2) The law is lawP2 P X_T. This is the pushforward P.map
X_T when X_T is square integrable, which is the paper's Law(X_T) ∈ P₂(ℝ^n), and the Dirac mass δ₀
otherwise. The second case is outside the paper's domain, because the paper presupposes
Law(X_T) ∈ P₂, so X_T ∈ L². Caveat for the statements that use terminalVal: when the solution
class does not force X_T ∈ L² (the weak class H² of Theorem 3.3), the junk branch g(X_T, δ₀) is
reachable, and the spec review should check that it does not change the claim.
Disagreements with the author's review (shown 2026-10-17T15:01:22Z): No disagreement on the substance. The author's entry (acceptance/review/definitions.md) records only the review marker and no comparison with the paper, so it does not state what I relied on: lawP2 returns δ₀ when X_T ∉ L². This is outside the paper's domain (the paper presupposes Law(X_T) ∈ P₂), but it is reachable in statements over the weak class H² that do not themselves force X_T ∈ L². The entry should mention this so the uniqueness spec review checks it.
