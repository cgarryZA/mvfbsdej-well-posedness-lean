### A:ex:dealer, A:abstract: Dissertation.PaperSpec.A.ex_dealer_marks
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba140a65f520ffefa33 (pl-fp-v1:aba9ed43099ad9877b196be0fe2cff12547cfec4bc3fc30a8e2cff180e351093)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:26Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:14:28Z):
UNIT spec:Dissertation.PaperSpec.A.ex_dealer_marks

Paper passage: Example 5.5 (ex:dealer), paragraph "Marks and activity":
"Take E = {-1,+1} x (0,1], writing e = (vs, q) for side vs and size q, with
nu(d vs, dq) = c_vs q^{-1-rho} dq for constants c_vs > 0 and 0 < rho < 2: then nu(E) = infinity
while int_E q^2 nu(d vs, dq) < infinity, so h_c(vs, q) := vs q lies in L2(nu) - infinitely many
small tickets with square-integrable aggregate exposure."
(Later, in "The interaction is active", the specialisation c_{+-1} = (2 - rho)/2 is taken, so that
||h_c|| = ||h_x|| = 1 and <h_c, h_x> = 0; that is a different clause.)
Clause: "the mark measure: infinite mass, square-integrable size, h_c in L2(nu); the dealer mark
measure has infinite activity".

What a faithful formal statement must contain.
Setting: the mark space E = {-1,+1} x (0,1] with its Borel (product) sigma-algebra; nu is the
measure on E with nu({vs} x dq) = c_vs q^{-1-rho} dq on (0,1] for each side vs, i.e.
nu = sum_{vs in {-1,+1}} delta_vs (x) c_vs q^{-1-rho} 1_{(0,1]}(q) dq. (No probability space or
filtration is involved: this is a statement about a deterministic measure.)
Quantifiers: for all constants c_{-1} > 0, c_{+1} > 0 (a function c : {-1,+1} -> R with positive
values) and all rho with 0 < rho < 2. No other hypotheses. Order: c, rho universally quantified,
then the conclusion.
Conclusion (a conjunction):
 (1) nu(E) = infinity (infinite mass / infinite activity);
 (2) int_E q^2 nu(d vs, dq) < infinity (square-integrable size), as an ENNReal lintegral < top
     or as integrability of (vs,q) -> q^2;
 (3) h_c(vs,q) := vs q lies in L2(nu): Memℒp h_c 2 nu (MemLp), equivalently (2) since |h_c|^2 =
     q^2; real-valued (n = 1).
Possibly also (implicit in the paper's standing setting) nu sigma-finite; including it as an
extra conjunct is broader-conclusion and harmless; including it as a hypothesis would be
wrong (it is a property of this nu, not an assumption).
Constants: none.
Representation choices that are harmless: E encoded as a subset of R x R or as Bool x
Ioc 0 1 or as a subtype, provided nu is the same measure (in particular supported on sizes in
(0,1], density c_vs q^{-1-rho} with respect to Lebesgue in q, no mass at q <= 0 or q > 1, the two
sides weighted c_{-1}, c_{+1}); vs encoded as +-1 in R so that h_c = vs q. A statement with
c_{-1} = c_{+1} (a single constant) or a specific rho or the normalization c = (2 - rho)/2 only
would be narrower. A statement in which the density uses Real.rpow at q <= 0 without a
restriction to q > 0 would have junk values (rpow of 0 or negatives) and must be checked.
Witness: none needed (no hypotheses beyond c > 0, 0 < rho < 2, which are satisfiable).
The paper does claim this at this revision (Example 5.5, "Marks and activity").
Comparison (verdict recorded 2026-10-19T03:26:33Z):
Lean (Dissertation/PaperSpec/A/Sec5.lean:705-714):
  forall (c : Bool -> R), (forall b, 0 < c b) -> forall rho : R, 0 < rho -> rho < 2 ->
    let nu : Measure (Bool x Set.Ioc 0 1) :=
      (Measure.count.prod (Measure.comap Subtype.val volume)).withDensity
        (fun e => ENNReal.ofReal (c e.1 * (e.2 : R) ^ (-1 - rho)))
    nu univ = top /\ lintegral (ofReal ((e.2)^2)) dnu < top
      /\ MemLp (fun e => (if e.1 then 1 else -1) * (e.2 : R)) 2 nu.
Item by item against the locked reading:
 - Setting: E = {-1,+1} x (0,1] represented as Bool x Ioc 0 1 (true = +1, false = -1) with the
   product of the discrete sigma-algebra on Bool and the subtype Borel sigma-algebra on (0,1]:
   the Borel product sigma-algebra of the paper. nu = (counting on the sides) x (Lebesgue on
   (0,1], comap of volume along the subtype inclusion = restriction) with density
   c_vs q^{-1-rho}: nu({vs} x dq) = c_vs q^{-1-rho} dq, as printed. q ranges over (0,1] only,
   so the rpow q^{-1-rho} is evaluated at q > 0 only (no junk at q <= 0); the density is
   positive, ofReal exact.
 - Quantifiers: c : Bool -> R with c b > 0 for both sides (c_{-1}, c_{+1} > 0 independent), and
   rho with 0 < rho < 2, universally quantified, in the order of the paper; no extra hypotheses;
   no specialisation (not c = (2-rho)/2, not a single constant).
 - Conclusion: (1) nu(E) = infinity; (2) int_E q^2 dnu < infinity (ENNReal lintegral of q^2,
   finite); (3) h_c(vs,q) = vs q in L2(nu) (MemLp 2, real-valued since n = 1). All three, as
   printed. Clause from the abstract ("the dealer mark measure has infinite activity") = (1).
 - Constants: none.
 - Hypotheses can be met: witness ex_dealer_marks_hypotheses exhibits c = 1/2 (both sides),
   rho = 1, an instance the paper intends (it is the paper's normalisation c = (2 - rho)/2 at
   rho = 1). The proof ex_dealer_marks exists.
 - The paper claims this at revision f598204 (Example 5.5, "Marks and activity").
Representation choices (all harmless): Bool for the side {-1,+1} with h_c = (if side then 1 else
-1) * q; (0,1] as a subtype with comap-Lebesgue; the integral int q^2 dnu < infinity as an
ENNReal lintegral of ofReal q^2; L2(nu) with real values rather than EuclideanSpace R (Fin 1);
sigma-finiteness of nu not stated (not part of this clause).
Witness: —
Verdict: faithful with representation choices — Representation choices: (1) the side set {-1,+1} is Bool (true = +1, false = -1) and h_c(vs,q) is
written (if side then 1 else -1) * q - the same function; (2) (0,1] is the subtype Set.Ioc 0 1
with Lebesgue measure comap'd along the inclusion (= the restriction of Lebesgue measure), so the
density c_vs q^{-1-rho} is only evaluated at q > 0 (no rpow junk); nu is the counting measure on
the sides times this, with that density - the printed nu; (3) int_E q^2 dnu < infinity is stated
as an ENNReal lintegral of ofReal(q^2) < top, the same statement; (4) L2(nu) membership is MemLp 2
of a real-valued function rather than an element of L2(nu; R^1) - same condition for n = 1. No
hypothesis is added, no case lost (c_{-1}, c_{+1} > 0 independent, all 0 < rho < 2); the witness
c = 1/2, rho = 1 is an instance the paper intends.
Disagreements with the author's review (shown 2026-10-19T03:26:41Z): No substantive disagreement: the author's review covers the clause ("Marks and activity":
E = {-1,+1} x (0,1], nu(d vs, dq) = c_vs q^{-1-rho} dq, c_vs > 0, 0 < rho < 2: nu(E) = infinity,
int q^2 dnu < infinity, h_c in L2(nu)) with the witness ex_dealer_marks_hypotheses, and its overall
verdict is faithful. Classification: I record "faithful with representation choices" because the
proposition encodes the sides as Bool (h_c = (if side then 1 else -1) * q), (0,1] as a subtype with
comap-Lebesgue, the finiteness as an ENNReal lintegral and L2 membership as real-valued MemLp;
the author's review does not list these encodings for ex_dealer_marks. Note also that the author's
note "the other propositions hold for every sigma-finite nu: broader" does not apply to this
proposition, which fixes its own nu; it is neither broader nor narrower than the printed clause.
