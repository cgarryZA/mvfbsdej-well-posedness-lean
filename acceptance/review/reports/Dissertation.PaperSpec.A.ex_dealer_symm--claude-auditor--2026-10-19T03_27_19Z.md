### A:ex:dealer: Dissertation.PaperSpec.A.ex_dealer_symm
Pins: manuscript A None; project 128888621847f17ef1e2e2351bf070ed392bad40; hash ed839d34f480cba11753a45d7d37cdc6 (pl-fp-v1:cf84db2ed7aecde0b37248c2626d7ab2adb54845263330ad760fec236bcbb27f)
Reviewer: claude-auditor (model, claude, self-declared); 2026-10-19T03:27:19Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-19T03:15:07Z):
Reading of spec:Dissertation.PaperSpec.A.ex_dealer_symm (Example 5.5, clause "the symmetrised
crowding pairing, positive unless lambda is a Dirac mass").

Paper (05-examples.tex:505-512): "For lambda in P2(L2(nu)) the symmetrisation above, under
lambda (x) lambda, gives
  int <A_lambda(u), u> lambda(du) = (1/2) iint ||u - v||^2 / sqrt(1 + ||u - v||^2) lambda(du) lambda(dv),
which is positive unless lambda is a Dirac mass".
A_lambda(u) = int grad V(u - v) lambda(dv), grad V(w) = w / sqrt(1 + ||w||^2), on L2(nu) = L2(nu; R)
(dealer example, m = 1).

Faithful statement:
- For every lambda in P2(L2(nu)) (Borel probability measure on the fibre with finite second
  moment; finite first moment suffices for integrability, so a broader class is harmless if the
  integrals are genuinely integrable there - with Bochner junk = 0 for non-integrable integrands a
  broader class could make the identity hold trivially or fail, so I will check);
- (identity) int <A_lambda(u), u> lambda(du) = (1/2) iint ||u-v||^2/sqrt(1+||u-v||^2) d(lambda x lambda);
- (positivity) if lambda is not a Dirac mass (there is no a with lambda = delta_a), then this
  value is > 0.  (The converse, = 0 at a Dirac mass, is immediate and harmless if included; "unless"
  is read as "if not Dirac then positive".)
- Setting: the standing mark space and sigma-finite nu (countably generated, so L2(nu) separable
  and the diagonal is measurable); any nu (for nu = 0 every lambda is Dirac and the claim is
  vacuous-true; fine).
Both the identity and the positivity are part of the clause ("the symmetrised ... pairing,
positive"); a statement with only one of them would be narrower.  The pairing must be the L2(nu)
inner product, A the paper's crowding correction.
Comparison (verdict recorded 2026-10-19T03:21:36Z):
Comparison for spec:Dissertation.PaperSpec.A.ex_dealer_symm (Sec5DealerActive.lean:174-183).

Lean: forall E nu [SigmaFinite] [CountablyGenerated] (Lam : P2 (Lp (EuclideanSpace R (Fin 1)) 2 nu)),
  int <ex55Crowd Lam.law u, u> dLam(u)
     = 1/2 * int_u int_v ||u - v||^2 / sqrt(1 + ||u - v||^2) dLam dLam
  /\ ((not exists u, Lam.law = dirac u) -> 0 < int <ex55Crowd Lam.law u, u> dLam(u)).

Against my reading:
- Laws: every lambda in P2(L2(nu)) (probability, finite second moment). Matches the printed class.
- Identity: present, with the paper's integrand ||u-v||^2/sqrt(1+||u-v||^2) and factor 1/2; the
  double integral under lambda (x) lambda is written as an iterated Bochner integral, which equals
  the product integral by Fubini because the integrand is integrable (bounded by ||u|| + ||v||,
  finite first moments). Left side integrable since |<A(u),u>| <= ||u||. So both sides are genuine
  values, not Bochner junk 0; the identity cannot hold vacuously.
- Positivity unless Dirac: (not exists a, lambda = delta_a) -> value > 0. Matches ("unless" read as
  "if not Dirac then positive").
- A is ex55Crowd, the paper's crowding correction; pairing the L2(nu) inner product. Fibre L2(nu; R^1).
- Setting: sigma-finite, countably generated nu (so L2(nu) separable, Borel structure fine).
  No other hypotheses; the class P2(L2(nu)) is nonempty (Dirac masses), and non-Dirac laws exist
  whenever the fibre is nontrivial (witness ex_dealer_unit_hypotheses gives a unit vector).
- Claimed by the paper at this revision (05-examples.tex:505-512).
Verdict: faithful.
Witness: —
Verdict: faithful
Disagreements with the author's review (shown 2026-10-19T03:26:58Z): none
