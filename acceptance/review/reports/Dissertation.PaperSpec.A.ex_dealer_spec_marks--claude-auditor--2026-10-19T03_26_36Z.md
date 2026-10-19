### A:ex:dealer: Dissertation.PaperSpec.A.ex_dealer_spec_marks
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba1efd7d1ab7e3204fd (pl-fp-v1:b49ed2f109de40933d7123bc82e8264566e83ae09ff957fe357305348c0ef80e)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:26:36Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:07Z):
Reading of spec:Dissertation.PaperSpec.A.ex_dealer_spec_marks (Example 5.5, clause "the
specialisation: h_c, h_x in L2(nu), ||h_c|| = ||h_x|| = 1, <h_c, h_x> = 0").

Paper (05-examples.tex:464-486). Marks: E = {-1,+1} x (0,1], e = (s, q) (side s, size q);
nu(ds, dq) = c_s q^{-1-rho} dq, c_s > 0, 0 < rho < 2 (i.e. nu = sum over s in {+-1} of
c_s * (q^{-1-rho} dq restricted to (0,1]) on the copy {s} x (0,1]).  Specialisation:
c_{+1} = c_{-1} = (2 - rho)/2, h_c(s, q) = s q, h_x(s, q) = q.  Claim: "so that
||h_c||_{L2(nu)} = ||h_x||_{L2(nu)} = 1 and <h_c, h_x>_{L2(nu)} = 0", with h_c, h_x in L2(nu)
(earlier: "h_c(s,q) := s q lies in L2(nu)").
Check: ||h_c||^2 = sum_s c_s int_0^1 q^2 q^{-1-rho} dq = 2 * ((2-rho)/2) * 1/(2-rho) = 1; same
for h_x; <h_c,h_x> = sum_s s c_s/(2-rho) = 1/2 - 1/2 = 0.  True for every rho in (0,2).

Faithful statement must contain:
- Quantifier: for every rho with 0 < rho < 2 (rho is a free parameter of the example; fixing a
  single rho would be narrower).
- The mark space E = {-1,+1} x (0,1] (any faithful encoding, e.g. a two-point type or units of
  Z times reals restricted to (0,1], or {+-1} x R with nu carried by (0,1]); the measure nu with
  the density c_s q^{-1-rho} with respect to (counting on sides) x (Lebesgue on (0,1]), with
  c_s = (2-rho)/2 on both sides.
- h_c = (s, q) |-> s q and h_x = (s, q) |-> q (real-valued, m = 1), each square-integrable for nu
  (MemLp 2), so they define elements of L2(nu; R).
- Conclusions: ||h_c||_{L2(nu)} = 1, ||h_x||_{L2(nu)} = 1, <h_c, h_x>_{L2(nu)} = 0 (as norms and
  inner product of the L2 classes, or equivalently int |h_c|^2 dnu = 1 etc.).
- Optional: nu(E) = infinity and sigma-finiteness (those belong to the "marks and activity" clause,
  not this one; including them is harmless).
Representation issues to check: that nu is exactly this measure (density on (0,1] only, no mass
at q = 0 or outside (0,1]); that s ranges over {-1, +1} with s q the signed size; that the L2
space is the one with real (or R^1) values used by the dealer example; that norms are the L2 norm,
not the squared norm (both equal 1 here, but the inner product claim must be the L2 inner product).
Comparison (verdict recorded 2026-10-19T03:18:29Z):
Comparison for spec:Dissertation.PaperSpec.A.ex_dealer_spec_marks (Sec5DealerActive.lean:118-128).

Lean: forall rho, 0 < rho -> rho < 2 ->
  MemLp h_c 2 (ex55Marks rho) /\ MemLp h_x 2 (ex55Marks rho)
  /\ int h_c^2 d nu = 1 /\ int h_x^2 d nu = 1 /\ int h_c * h_x d nu = 0,
with h_c e = (if e.1 then 1 else -1) * e.2, h_x e = e.2 on DealerMark = Bool x Set.Ioc 0 1.

Definitions used:
- DealerMark (Examples/Dealer/Marks.lean:89) = Bool x (0,1] (subtype of R), true = +1, false = -1;
  measurable structure: discrete on Bool times the subtype Borel structure.
- ex55Marks rho = dealerMarks (fun _ => (2 - rho)/2) rho, and dealerMarks c rho
  (Marks.lean:119-121) = (Measure.count.prod sizeLeb).withDensity (ofReal (c s * q^(-1-rho))),
  with sizeLeb = Measure.comap Subtype.val volume, Lebesgue measure on (0,1]. This is exactly
  nu(ds, dq) = c_s q^{-1-rho} dq on {-1,+1} x (0,1] with c_{+-1} = (2-rho)/2 (positive for rho < 2,
  so ofReal does not truncate). No mass outside (0,1] (the size type is (0,1]).

Item by item:
- Quantifier over every rho in (0,2): present (not a fixed rho).  Matches.
- h_c(s, q) = s q, h_x(s, q) = q: present, real-valued (m = 1).  Matches.
- h_c, h_x in L2(nu): MemLp ... 2 (ex55Marks rho).  Matches.
- ||h_c|| = 1, ||h_x|| = 1: stated as int h^2 d nu = 1, i.e. ||h||^2 = 1, equivalent to ||h|| = 1
  for the L2 class (the integrand is integrable because MemLp is asserted in the same conjunction,
  so the Bochner integral is genuine, not a junk 0).  Matches.
- <h_c, h_x> = 0: stated as int h_c h_x d nu = 0; the product of two L2 functions is integrable
  (both MemLp conjuncts hold), so this is the genuine L2(nu; R) inner product, not the Bochner junk
  value.  Matches.
- Arithmetic check: int q^2 c q^{-1-rho} dq over (0,1] = c/(2-rho) = 1/2 per side; sum 1; signed
  version 1/2 - 1/2 = 0.  The proposition is true, as the paper says.
- Hypotheses (0 < rho < 2) trivially satisfiable (witness ex_dealer_spec_hypotheses).
Representation choices: (1) E = {-1,+1} x (0,1] encoded as Bool x (0,1] with true = +1;
(2) norms and inner product as integrals of real-valued functions (squared norm = 1 instead of
norm = 1) rather than norms of Lp (EuclideanSpace R (Fin 1)) classes; (3) real values instead of
R^1-valued (the example's fibre is Lp (EuclideanSpace R (Fin 1)) 2 nu; the classes of these
functions there have the same norms and inner product).
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — (1) The mark space {-1,+1} x (0,1] is Bool x Set.Ioc 0 1 with true = +1, and nu is
(count x Lebesgue on (0,1]).withDensity of c_s q^{-1-rho} with c = (2-rho)/2: the paper's measure.
(2) ||h|| = 1 and <h_c,h_x> = 0 are stated as int h^2 dnu = 1 and int h_c h_x dnu = 0 for the
real-valued functions; since MemLp 2 of both is asserted in the same conjunction, the integrands
are integrable and these are the genuine squared L2 norms and inner product (squared norm 1 iff norm
1). (3) Real-valued functions instead of R^1-valued Lp classes, which have the same norms.
Disagreements with the author's review (shown 2026-10-19T03:26:27Z): none
