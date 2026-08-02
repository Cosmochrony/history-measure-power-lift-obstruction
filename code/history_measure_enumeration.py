#!/usr/bin/env python3
"""
Reproduction script for "Refinement Consistency Obstructs Nonlinear Power Lifts of
Finite History Measures".

Stdlib-only, exact arithmetic throughout (fractions.Fraction and the Q2 class below for
Q(sqrt(2))). No floating-point computation enters any claim of the paper.

Certifies:
  - exact row-stochasticity of P (Eq. P-exact);
  - the exact positive-cross-term proof of Proposition "Exact square-root failure on the
    shadow automaton" (Section 4.3), for all three rows of P;
  - exhaustive enumeration of all non-backtracking words of length n<=8 over the O12-native
    Heisenberg group Heis_3(Z/17Z), with exact endpoints and b-shadows;
  - both witnesses of the endpoint/shadow incomparability proposition (Section 5);
  - the exact cyclotomic-vanishing cancellation search (Section 6.3), for c=1 and for the
    conjugate c=16=q-c, confirming the predicted conjugate-covariance of the vanishing
    pattern (Proposition "Conjugate covariance");
  - the shadow invariance AND the exact endpoint transformation
    phi(a,b,gamma)=(-a,b,-gamma) of X<->X^{-1} relabelling (Proposition
    "Generator-relabelling covariance", parts ii-iii), over all enumerated words;
  - the exact coefficient symmetry coeffs[k]==coeffs[(Q-k)%Q] that certifies Corollary
    "Reality of co-b_n class sums" without evaluating any complex number.

Explicitly out of scope (unchanged from the paper): the D4/generic-probe residual-norm
channel of the trajectory-branching note is not recomputed; its cited equivalence to the
shadow quotient is imported, not re-derived.

No Born rule, no complex-carrier claim, and no publication step is taken by this script.
"""

from fractions import Fraction as F
import itertools

Q = 17          # prime modulus
N_MAX = 8       # maximal word length enumerated
C0 = 1          # primary central character
C0_CONJ = Q - C0  # conjugate character, for the covariance check


# ---------------------------------------------------------------------------
# Section A: exact arithmetic in Q(sqrt(2))
# ---------------------------------------------------------------------------

class Q2:
    """Exact element p + q*sqrt(2), p,q in Fraction. Stdlib-only exact arithmetic."""
    __slots__ = ("p", "q")

    def __init__(self, p=0, q=0):
        self.p = F(p)
        self.q = F(q)

    @staticmethod
    def coerce(x):
        return x if isinstance(x, Q2) else Q2(x)

    def __add__(self, other):
        o = Q2.coerce(other)
        return Q2(self.p + o.p, self.q + o.q)

    __radd__ = __add__

    def __sub__(self, other):
        o = Q2.coerce(other)
        return Q2(self.p - o.p, self.q - o.q)

    def __rsub__(self, other):
        return Q2.coerce(other) - self

    def __neg__(self):
        return Q2(-self.p, -self.q)

    def __mul__(self, other):
        o = Q2.coerce(other)
        return Q2(self.p * o.p + 2 * self.q * o.q, self.p * o.q + self.q * o.p)

    __rmul__ = __mul__

    def __truediv__(self, other):
        o = Q2.coerce(other)
        denom = o.p * o.p - 2 * o.q * o.q
        if denom == 0:
            raise ZeroDivisionError("division by zero in Q(sqrt(2))")
        num_p = self.p * o.p - 2 * self.q * o.q
        num_q = self.q * o.p - self.p * o.q
        return Q2(num_p / denom, num_q / denom)

    def __eq__(self, other):
        o = Q2.coerce(other)
        return self.p == o.p and self.q == o.q

    def __hash__(self):
        return hash((self.p, self.q))

    def sign(self):
        """Exact sign of p + q*sqrt(2), via p^2 vs 2 q^2 comparison (no float)."""
        if self.p == 0 and self.q == 0:
            return 0
        if self.q == 0:
            return 1 if self.p > 0 else -1
        if self.p == 0:
            return 1 if self.q > 0 else -1
        same_sign = (self.p > 0) == (self.q > 0)
        big = self.p * self.p - 2 * self.q * self.q  # sign of |p| vs |q|*sqrt(2)
        if same_sign:
            return 1 if self.p > 0 else -1
        if big > 0:
            return 1 if self.p > 0 else -1
        elif big < 0:
            return 1 if self.q > 0 else -1
        else:
            return 0

    def is_positive(self):
        return self.sign() > 0

    def to_float(self):
        return float(self.p) + float(self.q) * (2 ** 0.5)

    def __repr__(self):
        return f"({self.p}+{self.q}*sqrt2)"


ZERO2, ONE2 = Q2(0, 0), Q2(1, 0)


# ---------------------------------------------------------------------------
# Section B: O12-native Heisenberg group, generators, non-backtracking words
# (Eq. heis-law of the paper: (a,b,g)(a',b',g') = (a+a', b+b', g+g'+a*b') mod q)
# ---------------------------------------------------------------------------

def heis_mul(u, v, q=Q):
    a, b, g = u
    ap, bp, gp = v
    return ((a + ap) % q, (b + bp) % q, (g + gp + a * bp) % q)


def heis_inv(u, q=Q):
    a, b, g = u
    return ((-a) % q, (-b) % q, (a * b - g) % q)


GEN = {"X": (1, 0, 0), "Y": (0, 1, 0)}
GEN["x"] = heis_inv(GEN["X"])   # X^{-1}
GEN["y"] = heis_inv(GEN["Y"])   # Y^{-1}
INV = {"X": "x", "x": "X", "Y": "y", "y": "Y"}
SHADOW = {"X": "0", "x": "0", "Y": "+", "y": "-"}
LETTERS = ["X", "x", "Y", "y"]


def nonbacktracking_words(n):
    """All words of length n, g_{k+1} != inverse(g_k). Yields tuples of letters."""
    if n == 0:
        yield ()
        return
    for first in LETTERS:
        yield from _extend((first,), n)


def _extend(prefix, n):
    if len(prefix) == n:
        yield prefix
        return
    last = prefix[-1]
    for nxt in LETTERS:
        if nxt != INV[last]:
            yield from _extend(prefix + (nxt,), n)


def endpoint_of(word):
    u = (0, 0, 0)
    for g in word:
        u = heis_mul(u, GEN[g])
    return u


def shadow_of(word):
    return tuple(SHADOW[g] for g in word)


# ---------------------------------------------------------------------------
# Section C: H2 Parry kernel, stationary law, mu_n(h) (Eq. P-exact)
# ---------------------------------------------------------------------------

IDX = {"0": 0, "+": 1, "-": 2}
LAM = Q2(1, 1)
R = [Q2(0, 1), Q2(1, 0), Q2(1, 0)]
M = [[1, 1, 1], [1, 1, 0], [1, 0, 1]]

P = [[Q2(M[i][j]) * R[j] / (LAM * R[i]) if M[i][j] else ZERO2
      for j in range(3)] for i in range(3)]

PI = [F(1, 2), F(1, 4), F(1, 4)]  # stationary law, exact rational


def check_row_stochastic():
    for i in range(3):
        s = sum((P[i][j] for j in range(3)), ZERO2)
        assert s == ONE2, f"row {i} does not sum to 1: {s}"


def mu_n(shadow):
    """Exact mu_n(h) as a Q2 element, under the stationary initial law pi."""
    val = Q2(PI[IDX[shadow[0]]])
    for k in range(1, len(shadow)):
        val = val * P[IDX[shadow[k - 1]]][IDX[shadow[k]]]
    return val


# ---------------------------------------------------------------------------
# Section D: Proposition "Exact square-root failure on the shadow automaton"
# ---------------------------------------------------------------------------

def sqrt_failure_report():
    lines = []
    for i, row_state in enumerate("0+-"):
        nz = [j for j in range(3) if M[i][j]]
        cross_desc = []
        all_positive = True
        for a_, b_ in itertools.combinations(nz, 2):
            prod = P[i][a_] * P[i][b_]
            s = prod.sign()
            all_positive = all_positive and (s > 0)
            cross_desc.append(f"P[{row_state}][{'0+-'[a_]}]*P[{row_state}][{'0+-'[b_]}] sign={s}")
        strictly_exceeds_one = len(cross_desc) > 0 and all_positive
        lines.append(
            f"  row {row_state}: nonzero entries={len(nz)}, cross terms={cross_desc}, "
            f"=> sum_j sqrt(P_{row_state}j) {'>' if strictly_exceeds_one else '(undetermined)'} 1"
        )
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Section E: enumerate small histories
# ---------------------------------------------------------------------------

def enumerate_histories(n_max=N_MAX):
    records = []
    for n in range(1, n_max + 1):
        for w in nonbacktracking_words(n):
            ep = endpoint_of(w)
            sh = shadow_of(w)
            records.append({"word": w, "n": n, "endpoint": ep, "shadow": sh})
    return records


# ---------------------------------------------------------------------------
# Section F: Proposition "Incomparability" (endpoint pi_D1 vs shadow pi_shadow)
# ---------------------------------------------------------------------------

def quotient_comparability_witnesses(records):
    by_shadow = {}
    by_endpoint = {}
    for r in records:
        by_shadow.setdefault((r["n"], r["shadow"]), set()).add(r["endpoint"])
        by_endpoint.setdefault((r["n"], r["endpoint"]), set()).add(r["shadow"])

    same_shadow_diff_endpoint = None
    for key, endpoints in by_shadow.items():
        if len(endpoints) > 1:
            same_shadow_diff_endpoint = (key, endpoints)
            break

    same_endpoint_diff_shadow = None
    for key, shadows in by_endpoint.items():
        if len(shadows) > 1:
            same_endpoint_diff_shadow = (key, shadows)
            break

    return same_shadow_diff_endpoint, same_endpoint_diff_shadow


# ---------------------------------------------------------------------------
# Section G: uniform-probe phase label and exact cyclotomic cancellation test
# (Lemma "Cyclotomic vanishing over Q(sqrt(2)), q=17")
# ---------------------------------------------------------------------------

def cyclotomic_vanishes(coeffs):
    """coeffs: list of Q2, length q. Returns True iff sum coeffs[k]*zeta^k == 0 exactly."""
    first = coeffs[0]
    return all(c == first for c in coeffs)


def phase_cancellation_report(records, c):
    by_bn = {}
    for r in records:
        a, b, g = r["endpoint"]
        by_bn.setdefault((r["n"], b), []).append((g, mu_n(r["shadow"])))

    findings = []
    for (n, b), items in by_bn.items():
        if len(items) < 2:
            continue
        coeffs = [ZERO2] * Q
        for g, weight in items:
            k = (c * g) % Q
            coeffs[k] = coeffs[k] + weight
        distinct_gammas = len(set(g for g, _ in items))
        vanishes = cyclotomic_vanishes(coeffs) if distinct_gammas > 1 else False
        nontrivial_all_equal_nonzero = vanishes and coeffs[0] != ZERO2
        symmetric = all(coeffs[k] == coeffs[(Q - k) % Q] for k in range(Q))
        findings.append({
            "n": n, "b_n": b, "count": len(items),
            "distinct_gamma_labels": distinct_gammas,
            "exact_cancellation": nontrivial_all_equal_nonzero,
            "coeffs_symmetric": symmetric,
        })
    return findings


# ---------------------------------------------------------------------------
# Section H: Proposition "Generator-relabelling covariance" and Corollary
# "Reality of co-b_n class sums"
# ---------------------------------------------------------------------------

RELABEL = {"X": "x", "x": "X", "Y": "Y", "y": "y"}


def relabel_word(word):
    return tuple(RELABEL[g] for g in word)


def relabelling_covariance_report(records):
    """Certifies Proposition 'Generator-relabelling covariance', parts (ii)-(iii):
    shadow invariance AND the exact endpoint transformation
    phi(a,b,gamma) = (-a, b, -gamma)."""
    shadow_mismatches = 0
    endpoint_mismatches = 0
    checked = 0
    for r in records:
        w2 = relabel_word(r["word"])
        sh2 = shadow_of(w2)
        ep2 = endpoint_of(w2)
        a, b, g = r["endpoint"]
        predicted = ((-a) % Q, b % Q, (-g) % Q)
        checked += 1
        if sh2 != r["shadow"]:
            shadow_mismatches += 1
        if ep2 != predicted:
            endpoint_mismatches += 1
    return checked, shadow_mismatches, endpoint_mismatches


# ---------------------------------------------------------------------------
# Main: run all certifications and print a structured report
# ---------------------------------------------------------------------------

def main():
    print("=" * 78)
    print("Refinement Consistency Obstructs Nonlinear Power Lifts -- reproduction script")
    print(f"q={Q}, n_max={N_MAX}, c0={C0} (conjugate {C0_CONJ})")
    print("=" * 78)

    check_row_stochastic()
    print("\n[Eq. P-exact] P is exactly row-stochastic on Q(sqrt(2)). OK.")

    print("\n[Prop. 'Exact square-root failure'] sum_j sqrt(P_ij) vs 1, all three rows:")
    print(sqrt_failure_report())

    records = enumerate_histories(N_MAX)
    print(f"\n[Sec. 5-6 setup] Enumerated {len(records)} non-backtracking words, n=1..{N_MAX}.")

    same_sh, same_ep = quotient_comparability_witnesses(records)
    print("\n[Prop. 'Incomparability'] pi_D1 (endpoint) vs pi_shadow:")
    if same_sh:
        key, eps = same_sh
        print(f"  Witness: shadow {key} reached by {len(eps)} distinct endpoints "
              f"(e.g. {list(eps)[:2]}).")
    if same_ep:
        key, shs = same_ep
        print(f"  Witness: endpoint {key} reached by {len(shs)} distinct shadows "
              f"(e.g. {list(shs)[:2]}).")

    print("\n[Prop. 'Bounded negative search result'] Uniform-probe exact cancellation search (c=1):")
    findings = phase_cancellation_report(records, C0)
    any_cancel = [f for f in findings if f["exact_cancellation"]]
    multi_phase = [f for f in findings if f["distinct_gamma_labels"] > 1]
    print(f"  b_n-classes with >=2 histories: {len(findings)}")
    print(f"  classes with >1 distinct gamma-phase label: {len(multi_phase)}")
    print(f"  classes with EXACT cyclotomic cancellation: {len(any_cancel)}")

    print("\n[Cor. 'Reality of co-b_n class sums'] coeffs[k] == coeffs[(Q-k)%Q] for every class:")
    asymmetric = [f for f in findings if not f["coeffs_symmetric"]]
    print(f"  classes checked: {len(findings)}, asymmetric (S not real): {len(asymmetric)} (expect 0).")

    print("\n[Prop. 'Conjugate covariance'] c=1 vs c=q-c={}:".format(C0_CONJ))
    findings_conj = phase_cancellation_report(records, C0_CONJ)
    same_len = len(findings) == len(findings_conj)
    same_cancel_pattern = [f["exact_cancellation"] for f in findings] == \
                           [f["exact_cancellation"] for f in findings_conj]
    print(f"  class count matches: {same_len}; cancellation pattern matches: {same_cancel_pattern}")

    print("\n[Prop. 'Generator-relabelling covariance'] X<->X^{-1} shadow and endpoint transform:")
    checked, sh_mism, ep_mism = relabelling_covariance_report(records)
    print(f"  {checked} words checked, {sh_mism} shadow mismatches, "
          f"{ep_mism} endpoint-transform mismatches (both expected 0).")

    print("\n" + "=" * 78)
    print("End of run. No Born rule used. No publication step taken.")
    print("=" * 78)


if __name__ == "__main__":
    main()
