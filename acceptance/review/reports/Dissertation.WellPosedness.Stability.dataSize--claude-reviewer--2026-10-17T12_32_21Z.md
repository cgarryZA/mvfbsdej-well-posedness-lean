### A:cor:robust, A:lem:pert, A:rem:generalrank, A:thm3.1:companion, A:thm:cwp, A:thm:stab: Dissertation.WellPosedness.Stability.dataSize
Pins: manuscript A None; project 8b7dc67f842cfe4e558dbac79ab38a26a6d07eac; hash f5b22d1ca3f4de88514ab122da58813f (pl-fp-v1:a47c4b9c3651606c6c2b87324036ba082278fb7fff00f9cfd83fc660a79d3544)
Reviewer: claude-reviewer (model, claude, self-declared); 2026-10-17T12:32:21Z; same model family as the author: yes
Phase 1 specification (locked 2026-10-17T12:31:47Z):
Reading: dataSize = the data quantity on the right of (3.1) and (4.13), the P of the proof of
Lemma 4.3:

  P = E|delta xi_0|^2 + E|delta q^g_T|^2
      + E int_0^T ( |delta q^b_t|^2 + |delta q^sigma_t|_F^2 + ||delta q^h_t||_{L^2(nu)}^2
                    + |delta q^f_t|^2 ) dt,

for given (difference) data: initial datum in R^n, terminal forcing in R^m, drift forcing R^n,
diffusion forcing R^{n x d} (Frobenius), jump forcing L^2(nu;R^n) (i.e. int_E |q^h_t(e)|^2
nu(de)), driver forcing R^m, all with the Euclidean squared norms (sum of squared coordinates),
time integral over [0,T] w.r.t. Lebesgue, expectation over P. In Theorem 3.1 the forcings are the
coefficient differences along solution 2 and hat delta g_T. A faithful Lean definition must be
exactly this sum (values in [0, inf] are natural: an ENNReal lintegral form avoids junk values
for non-integrable data; a real Bochner form would need integrability to be meaningful). Any
constant factor or missing channel would be a mismatch (a constant factor would be harmless
only in statements with a free constant, but the definition should be the printed quantity).
Comparison (verdict recorded 2026-10-17T12:32:15Z):
dataSize P nu T xi0 qb qsigma qh qf qg : ENNReal =
  int^- esq(xi0(omega)) dP + int^- esq(qg(omega)) dP + sum_i energy(qb_i)
  + sum_{i,j} energy(qsigma_{ij}) + sum_i markedEnergy(qh_i) + sum_k energy(qf_k),
with esq x = sum_i |x_i|^2 (in ENNReal), energy H = int^- int^-_{[0,T]} |H|^2 ds dP and
markedEnergy phi = int^- int^-_{[0,T]} int^- |phi|^2 nu(de) ds dP.

Item by item: E|delta xi_0|^2 (sum of squared coordinates = Euclidean norm squared): present;
E|delta q^g_T|^2: present; E int_0^T |q^b|^2: sum over coordinates of the energies; |q^sigma|_F^2:
sum over (i,j) of the entries' energies = Frobenius; ||q^h||^2_{L^2(nu)} = sum_i int_E |q^h_i(e)|^2
nu(de), as sum of marked energies; |q^f|^2: present. Time domain [0,T] (closed; endpoints null).
No constant factor, no missing channel. Values in [0, inf]: no junk for non-integrable data;
the paper's quantity is finite exactly when all terms are finite.

Representation choices: coordinatewise sums of separate lintegrals instead of one integral of
the summed squared norm — equal by additivity of the lower integral for measurable integrands
(Tonelli), which is the case for every datum the paper considers; ENNReal value. The arguments
are the (difference) data themselves; callers pass delta xi_0 and delta q.
Faithful with representation choices.
Witness: —
Verdict: faithful with representation choices — (1) The squared norms are written coordinatewise (esq = sum of squared coordinates; Frobenius as
sum over (i,j) of entry energies; L^2(nu) norm of q^h as sum over coordinates of marked energies)
and each channel's E int_0^T is a separate lower integral, summed: equal to the printed
E int_0^T (...) dt by additivity of lintegral for measurable data (all data of the paper are
measurable; for non-measurable data lintegral is only superadditive, but such data never occur).
(2) Values in ENNReal, so the quantity is +inf rather than a junk real when some datum is not
square integrable; the printed P is the same element of [0, inf]. (3) The function takes the data
(xi0, q) as arguments; the paper's P uses differences delta xi_0, delta q, which callers pass.
Disagreements with the author's review (shown 2026-10-17T12:32:15Z): none (the author review shows only a marker, definitions.md:195, with no recorded reading).
