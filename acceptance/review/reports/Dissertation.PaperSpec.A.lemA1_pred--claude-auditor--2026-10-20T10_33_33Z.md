### A:lemA1:pettis: Dissertation.PaperSpec.A.lemA1_pred
Pins: manuscript A None; project 6d403c197bfb10fe8808933c6e525ee0ae544fb1; hash ed839d34f480cba136b795f0b638d045 (pl-fp-v1:e0770011789fa86d2d2a5d439a57dcece8ee52edefa3b10081fedbd54f66388f)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-20T10:33:33Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-20T10:21:55Z):
Reading of the clause (Lemma A.1, Step 1: "Theta^- is therefore a predictable, hence jointly measurable, H-valued field";
manuscript/paper/sections/09-appendix.tex lines 36-37).

Setting: standing filtered basis (usual conditions), T > 0, n, m, d >= 1, a countably generated (E, E) with sigma-finite
nu; H = R^n x R^m x R^{m x d} x L^2(nu; R^m) with its Hilbert norm (the type the paper's H is represented by).
Hypotheses of Lemma A.1: X (R^n) and Y (R^m) adapted with cadlag paths, Z a predictable R^{m x d}-valued process,
U a predictable (P (x) E-measurable) R^m-valued function of (t, omega, e), and
E int_0^T (|X_t|^2 + |Y_t|^2 + |Z_t|_F^2 + int_E |U_t(e)|^2 nu(de)) dt < infinity.
Conclusion: the field Theta^-_t(omega) = (X_{t-}(omega), Y_{t-}(omega), Z_t(omega), V_t(omega)), where V is the
predictable strongly measurable L^2(nu)-valued representative of (t, omega) -> U_t(omega, .) (the one of the previous
sentence of Step 1), is strongly measurable as a map [0,T] x Omega -> H for the predictable sigma-algebra.
Acceptable forms: "there is a representative V (agreeing with U's sections a.e.) for which the field is predictable"
(stronger, includes existence), or "for every predictable strongly measurable representative V the field is
predictable" (the "therefore" step). A version that leaves V unrelated to U (any V whatever) would not state the
paper's Theta^-. The left limits must be genuine left limits (convention at t = 0 harmless). The sigma-algebra must be
the predictable one of the standing filtration, the codomain H with its norm topology (strong measurability).
The paper's "hence jointly measurable" and "E int ||Theta^-||^2 < infinity" parts are not in this clause's text (other
clauses may state them).
Comparison (verdict recorded 2026-10-20T10:26:22Z):
Comparison of Dissertation.PaperSpec.A.lemA1_pred (Dissertation/PaperSpec/A/AppASteps.lean) with my locked reading.

Setting and hypotheses: identical to lemA1_leftlim / lemA1_U (arbitrary probability space and ℝ-indexed filtration,
sigma-finite nu on a countably generated E, arbitrary n, m, d, T, and `CadlagPredTuple`, i.e. Lemma A.1's hypotheses:
X, Y adapted with every path cadlag, Z predictable, U marked predictable, all of finite energy on [0,T]).

Conclusion: `Predictable ℱ (fun ω t => toL2 (tupleAt ν (leftLimProc X) (leftLimProc Y) Z U t ω))`.
 - `tupleAt` assembles (X_{t-}(omega), Y_{t-}(omega), Z_t(omega), uLift nu (U_t(omega, .))) with the Euclidean channels,
   the m x d channel as EuclideanSpace over Fin m x Fin d (Frobenius), and as U-channel `uLift`, the L^2(nu) class of
   e -> U_t(omega, e) when it is square integrable and 0 otherwise. `toL2` maps it to `TupleL2`, H with its Hilbert
   norm.
 - `Predictable` = strongly measurable for the predictable sigma-algebra of ℱ on ℝ x Omega.
So the statement is: the left-limit field Theta^- with U-coordinate the canonical section U_t(omega, .) in L^2(nu) is a
predictable, strongly measurable H-valued field. The canonical section is a representative of the paper's induced map
(it agrees with U_t(omega, .) wherever that section is in L^2(nu), i.e. dt (x) dP-a.e. under the energy hypothesis), and
it is the representative V that lemA1_U's proof exhibits; asserting predictability of this specific representative is
the "therefore" of the paper and includes the non-trivial part (measurability of the section map into L^2(nu)). [match]
The left limits are genuine left limits (Function.leftLim with existing limits on ℝ). "hence jointly measurable" and the
L^2 bound are in lemA1_L2, not here, as the clause text says.

Differences: generality (filtration arbitrary, no usual conditions; dimensions in ℕ; T arbitrary), and the version
convention of `MarkedPredictable` (U constant at times <= 0, so at t = 0 the U-channel is a constant class). For a paper U
whose time-0 slice is a nonconstant F_0 (x) E-measurable function, the statement is applied to U 1_{t>0}, whose canonical
section is another predictable representative of the induced map (it differs only at t = 0, a dt-null time), which is
all the paper's sentence asserts ("admits a predictable representative ... Theta^- is therefore predictable"). Harmless.

Witness: Dissertation.Acceptance.A.lemA1_coin_hypotheses (coin filtration, X = Y jumping at 1/2 so that X_- ≠ X,
Z = U = 1_{(0,1]} nonzero, nu = dirac 0): all four channels of Theta^- are nonzero somewhere, hypotheses met.

Coverage of the claim A:lemA1:pettis: as recorded in my decision on lemA1_leftlim: the clauses together state every
assertion of Step 1 (lines 25-51), this clause the predictability of Theta^- (lines 36-37); none states something the
passage does not claim; hypotheses are those of Lemma A.1 (plus the standing nu), minus unused structure; the scope_note is
accurate (it assigns "hence jointly measurable" to lemA1_L2, which states joint strong measurability). Witnesses exhibit
nonzero objects.
Witness: —
Verdict: broader — Broader only in generality: any probability space, any filtration indexed by ℝ (no usual conditions), any n, m, d, T. The
printed claim is the instance with the standing filtration extended by F_0 on (-inf, 0], X, Y extended by their initial
values before 0 (so X_{0-} = X_0), and U taken in its version U 1_{t>0} (a `MarkedPredictable` U is constant at times
<= 0); the U-channel of the Lean field is then the canonical L^2(nu) section of that version, which is a predictable
representative of the paper's induced map (t, omega) -> U_t(omega, .) (equal to it dt (x) dP-a.e.), so the Lean
conclusion is the paper's "Theta^- is a predictable H-valued field".
Disagreements with the author's review (shown 2026-10-20T10:33:11Z): Two points. (1) Label: the author records `faithful`; I record `broader`, for the same generality as in lemA1_leftlim
and lemA1_U (any ℝ-indexed filtration, no usual conditions, any n, m, d, T), with the printed claim as the instance.
(2) A small inaccuracy in the shared reading: it says the replacement of the paper's U_0 by the constant value forced by
`MarkedPredictable` "leaves every conclusion here unchanged" because the conclusions are a.e. statements or do not
involve U. For lemA1_pred that is not the reason: its conclusion is everywhere predictability of the field, and the
field at t = 0 does involve U_0. The replacement is still harmless, for a different reason: the paper asserts only that
the induced map admits a predictable representative and that Theta^- built with it is predictable, and the canonical
section of U 1_{t>0} is such a representative (equal to the paper's dt (x) dP-a.e.). The conclusion stands.
