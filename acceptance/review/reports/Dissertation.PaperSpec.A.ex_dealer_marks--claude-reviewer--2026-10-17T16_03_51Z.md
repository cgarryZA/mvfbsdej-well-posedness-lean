### A:ex:dealer, A:abstract: Dissertation.PaperSpec.A.ex_dealer_marks
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash ed839d34f480cba140a65f520ffefa33 (pl-fp-v1:aba9ed43099ad9877b196be0fe2cff12547cfec4bc3fc30a8e2cff180e351093)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T16:03:51Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T15:47:45Z):
Reading of spec ex_dealer_marks (Example 5.5, "Marks and activity"; and the abstract's "its
mark measure has infinite activity").

Setting (printed): E = {-1,+1} x (0,1], e = (s,q), nu(ds,dq) = c_s q^{-1-r} dq with constants
c_{-1}, c_{+1} > 0 and 0 < r < 2, i.e. nu = sum_{s=+-1} c_s delta_s (x) (q^{-1-r} Lebesgue on
(0,1]). E carries its Borel (product) sigma-algebra; countably generated.

A faithful statement must contain, for all c_{-1}, c_{+1} > 0 and all 0 < r < 2:
 1. nu(E) = infinity (infinite activity);
 2. int_E q^2 nu(de) < infinity;
 3. h_c(s,q) := s q is in L^2(nu) (measurable and square integrable: MemLp h_c 2 nu),
    so that h_c is an admissible baseline in the fibre L^2(nu;R) (n=1).
 Desirable (standing-setting membership, "admitted"): nu is sigma-finite (it is; q^{-1-r} is
 locally finite on (0,1]), so the measure is an instance of the standing setting. If the
 Lean omits sigma-finiteness this is a minor omission (the claim printed in the passage is
 items 1-3), but it is relevant for the abstract's clause that the example lies in the
 setting.
Quantifiers: universal over the constants; no further hypotheses. A statement with weaker
 ranges (e.g. r >= 0 for item 1, r < 2 for item 2) is broader and fine. A statement fixing
 particular c_s or r (e.g. c_s = 1, r = 1) is narrower.
Encoding choices acceptable: {-1,+1} as Bool/Fin 2/units of Z, (0,1] as Ioc 0 1 inside R
 (restricted Lebesgue measure with density), provided nu is the printed density measure.
Comparison (verdict recorded 2026-10-17T16:01:29Z):
Comparison, ex_dealer_marks (Sec5.lean:716-725).
Quantifiers: forall c : Bool -> R with c b > 0 for both b, forall r with 0 < r < 2 - the printed
c_{+-1} > 0, 0 < r < 2, universally. Matches.
Measure: nu := (count on Bool) (x) (Lebesgue on Ioc 0 1 via comap Subtype.val volume), with
density ofReal(c(e.1) * q^{-1-r}); this is sum_s c_s delta_s (x) q^{-1-r} dq on
{-1,+1} x (0,1], with Bool encoding the side (true = +1, false = -1). q > 0 on the subtype, so
q^{-1-r} (rpow) is the genuine power; ofReal of a positive number, no junk.
Conclusions: nu univ = infinity (item 1); lintegral of ofReal(q^2) < infinity (item 2);
MemLp ((if side then 1 else -1) * q) 2 nu (item 3: h_c(s,q) = s q in L^2(nu)). All present.
Abstract clause "the dealer mark measure has infinite activity": nu univ = infinity. Present.
Not stated: sigma-finiteness of nu (so that it is an instance of the standing setting). The
printed passage does not assert it explicitly; it is proved elsewhere (ex_dealer_hypotheses has
SigmaFinite (dealerMarks ...)). Harmless omission for this clause.
Representation choices: Bool for {-1,+1}; the subtype Ioc 0 1 with the comap of Lebesgue for
(0,1]; density via ENNReal.ofReal; the integral item 2 as a lintegral. All faithful encodings.
Witness ex_dealer_marks_hypotheses: c = 1/2, r = 1 - an intended instance.
Verdict: faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — Representation choices, each harmless:
1. The sides {-1,+1} are encoded as Bool (true = +1, false = -1), with counting measure; h_c is
   written (if side then 1 else -1) * q, i.e. s q.
2. (0,1] is the subtype Set.Ioc 0 1 of R with the comap of Lebesgue measure, i.e. Lebesgue
   measure on (0,1]; the density c_s q^{-1-r} enters through withDensity and ENNReal.ofReal of a
   positive real (no truncation occurs).
3. int_E q^2 dnu < infinity is stated as a lintegral of ofReal(q^2), the same quantity.
4. Sigma-finiteness of nu is not part of the statement; the passage's three conclusions do not
   assert it (it is proved separately in ex_dealer_hypotheses), so nothing printed is lost.
Disagreements with the author's review (shown 2026-10-17T16:01:35Z): Minor, on the verdict label and one correspondence remark of the shared Example 5.5 review (shown
under ex_dealer_potential): (1) I record "faithful with representation choices" rather than plain
"faithful": the sides are Bool (true = +1), (0,1] is the subtype Ioc 0 1 with the comap of
Lebesgue measure, the density enters through withDensity/ofReal, and item 2 is a lintegral - all
harmless encodings. (2) The review says "the same measure is dealerMarks"; the proposition does
not use dealerMarks but an inline measure (the same formula), and it does not state that nu is
sigma-finite (that is proved separately, in ex_dealer_hypotheses). Neither point changes the
meaning of the three printed conclusions.
