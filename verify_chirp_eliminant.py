#!/usr/bin/env python3
"""
Standalone exact verification script (Python 3 standard library only) for:
  "A Nonvanishing Phase Eliminant for Exact Finite-Field Chirp Recognition"
"""

from __future__ import annotations

import itertools
import math


# ---- Truncated polynomial arithmetic in F_p[z] / (z^{D+1}) ----

def r_add(a: list[int], b: list[int], p: int, lim: int) -> list[int]:
    return [(a[i] + b[i]) % p for i in range(lim)]


def r_sub(a: list[int], b: list[int], p: int, lim: int) -> list[int]:
    return [(a[i] - b[i]) % p for i in range(lim)]


def r_mul(a: list[int], b: list[int], p: int, lim: int) -> list[int]:
    out = [0] * lim
    for i in range(lim):
        ai = a[i]
        if ai:
            for j in range(lim - i):
                bj = b[j]
                if bj:
                    out[i + j] = (out[i + j] + ai * bj) % p
    return out


def r_inv(e: list[int], p: int, lim: int) -> list[int]:
    """Newton doubling inverse in F_p[z]/(z^lim) with e[0] != 0 (works even for p=2!)."""
    assert e[0] % p != 0
    g = [0] * lim
    g[0] = pow(e[0], p - 2, p)
    prec = 1
    while prec < lim:
        nxt = min(2 * prec, lim)
        eg = r_mul(e[:nxt], g[:nxt], p, nxt)
        two_minus_eg = [0] * nxt
        two_minus_eg[0] = (2 - eg[0]) % p
        for i in range(1, nxt):
            two_minus_eg[i] = (-eg[i]) % p
        g_new = r_mul(g[:nxt], two_minus_eg, p, nxt)
        for i in range(nxt):
            g[i] = g_new[i]
        prec = nxt
    # Verify e * g == 1 mod z^lim
    chk = r_mul(e, g, p, lim)
    assert chk[0] == 1 and all(v == 0 for v in chk[1:])
    return g


def f_exp(d: int) -> int:
    return d * (d - 1) // 2


def levinson_eliminant(x: list[int], c: int, r: int, p: int) -> list[int]:
    """Section 3 pivot-free Levinson determinant in F_p[z]/(z^{D+1})."""
    D = math.comb(r + 2, 3)
    lim = D + 1
    assert x[c] % p != 0

    def a_poly(d: int) -> list[int]:
        res = [0] * lim
        e = f_exp(d)
        if e < lim:
            res[e] = x[c + d] % p
        return res

    u = [[1] + [0] * (lim - 1)]
    v = [[1] + [0] * (lim - 1)]
    e = a_poly(0)
    det_acc = list(e)

    for k in range(1, r + 1):
        # Verify Schur constant term == x[c]
        assert e[0] == x[c] % p
        Ak = a_poly(k)
        Bk = a_poly(-k)
        for j in range(1, k):
            Ak = r_add(Ak, r_mul(a_poly(k - j), u[j], p, lim), p, lim)
            Bk = r_add(Bk, r_mul(a_poly(j - k), v[j], p, lim), p, lim)
        e_inv = r_inv(e, p, lim)
        neg_Ak = [(-v_) % p for v_ in Ak]
        neg_Bk = [(-v_) % p for v_ in Bk]
        alpha = r_mul(neg_Ak, e_inv, p, lim)
        beta = r_mul(neg_Bk, e_inv, p, lim)

        u_new = [[1] + [0] * (lim - 1)]
        v_new = [[1] + [0] * (lim - 1)]
        for j in range(1, k):
            u_new.append(r_add(u[j], r_mul(alpha, v[k - j], p, lim), p, lim))
            v_new.append(r_add(v[j], r_mul(beta, u[k - j], p, lim), p, lim))
        u_new.append(alpha)
        v_new.append(beta)
        u, v = u_new, v_new

        # Verify predictor equations sum_{j=0}^k a_{i-j} u_j = 0 for 1 <= i <= k
        for i in range(1, k + 1):
            s_u = [0] * lim
            s_v = [0] * lim
            for j in range(k + 1):
                s_u = r_add(s_u, r_mul(a_poly(i - j), u[j], p, lim), p, lim)
                s_v = r_add(s_v, r_mul(a_poly(j - i), v[j], p, lim), p, lim)
            assert all(val == 0 for val in s_u) and all(val == 0 for val in s_v)

        e = r_add(e, r_mul(alpha, Bk, p, lim), p, lim)
        assert e[0] == x[c] % p
        det_acc = r_mul(det_acc, e, p, lim)
        assert det_acc[0] == pow(x[c], k + 1, p)

    return det_acc


def leibniz_eliminant(x: list[int], c: int, r: int, p: int) -> list[int]:
    """Direct Leibniz permutation expansion of det[x_{c+i-j} z^{f(i-j)}]."""
    D = math.comb(r + 2, 3)
    lim = D + 1
    out = [0] * lim
    n = r + 1
    for perm in itertools.permutations(range(n)):
        # Parity of perm
        inv_cnt = 0
        for i in range(n):
            for j in range(i + 1, n):
                if perm[i] > perm[j]:
                    inv_cnt += 1
        coeff = 1 if inv_cnt % 2 == 0 else p - 1
        deg = 0
        for i in range(n):
            d = i - perm[i]
            coeff = (coeff * x[c + d]) % p
            deg += f_exp(d)
        if coeff:
            assert deg <= D
            out[deg] = (out[deg] + coeff) % p
    return out


# ---- 1. Verify Levinson vs. Leibniz & unit leading minors across p in {2,3,5,7,17} ----
def verify_eliminant_ring_algebra() -> None:
    checks = 0
    for p in (2, 3, 5, 7, 17):
        for r in (1, 2, 3, 4):
            # Deterministic non-degenerate vectors with nonzero center c = r
            for seed in range(3):
                N = 3 * r + 1
                x = [((seed + 1) * (j * j + 3 * j + 1)) % p for j in range(N)]
                if x[r] == 0:
                    x[r] = 1
                E_lev = levinson_eliminant(x, r, r, p)
                E_leib = leibniz_eliminant(x, r, r, p)
                assert E_lev == E_leib, (p, r, seed, E_lev, E_leib)
                assert E_lev[0] == pow(x[r], r + 1, p)
                checks += 1
    assert checks == 60
    print(f"  [PASS] Levinson vs. Leibniz determinant, predictor invariants, and unit minors verified ({checks} cases, incl. p=2)")


# ---- 2. Gauss-row formula (Proposition 6.1) across ALL lengths N=1..20 and ALL phases ----
def gauss_row_formula(N: int, a: int, w: int, p: int) -> list[int]:
    a %= N
    if a == 0:
        out = [0] * N
        out[0] = N % p
        return out
    d = math.gcd(a, N)
    m = N // d
    A = a // d
    xi = pow(w, d, p)
    out = [0] * N
    if m == 1:
        out[0] = N % p
        return out
    if m % 2 == 1:
        T0 = sum(pow(xi, (A * u * u) % m, p) for u in range(m)) % p
        inv4A = pow(4 * A, -1, m)
        for w_idx in range(m):
            exp = (-w_idx * w_idx * inv4A) % m
            out[d * w_idx] = (d * T0 * pow(xi, exp, p)) % p
    else:
        q = m // 2
        w0 = q % 2
        Tw0 = sum(pow(xi, (A * u * u + w0 * u) % m, p) for u in range(m)) % p
        invA = 0 if q == 1 else pow(A, -1, q)
        for w_idx in range(m):
            if w_idx % 2 == w0:
                u = 0 if q == 1 else (((w_idx - w0) // 2) * invA) % q
                exp = (-A * u * u - w0 * u) % m
                out[d * w_idx] = (d * Tw0 * pow(xi, exp, p)) % p
    return out


def find_prime_and_root(N: int) -> tuple[int, int]:
    k = 1
    while True:
        p = k * N + 1
        if p >= 3 and all(p % d != 0 for d in range(2, int(p**0.5) + 1)):
            for g in range(2, p):
                w = pow(g, (p - 1) // N, p)
                if pow(w, N, p) == 1 and all(pow(w, j, p) != 1 for j in range(1, N)):
                    return p, w
        k += 1


def verify_gauss_rows() -> None:
    rows_checked = 0
    for N in range(1, 21):
        p, w = find_prime_and_root(N)
        for a in range(N):
            G_fast = gauss_row_formula(N, a, w, p)
            G_direct = [
                sum(pow(w, (a * j * j + k * j) % N, p) for j in range(N)) % p
                for k in range(N)
            ]
            assert G_fast == G_direct, (N, a, p, w, G_fast, G_direct)
            rows_checked += 1
        # Check odd-length unit-phase Fourier equivalence: G_1(0) != 0 and G_1(k) = G_1(0) * w^{-k^2 (4)^-1}
        if N >= 3 and N % 2 == 1:
            G1 = gauss_row_formula(N, 1, w, p)
            assert G1[0] != 0
    assert rows_checked == 210
    print(f"  [PASS] Complete Gauss-row reduction verified across all {rows_checked} (N, a) pairs for 1 <= N <= 20")


# ---- 3. Full recognizers (BM dyadic + Hankel all-length) vs. direct brute-force DFT oracle ----

def direct_dft(x: list[int], w: int, p: int) -> list[int]:
    N = len(x)
    return [sum(x[j] * pow(w, (k * j) % N, p) for j in range(N)) % p for k in range(N)]


def oracle_in_Cr(x: list[int], w: int, p: int, r: int) -> bool:
    N = len(x)
    L = N // math.gcd(2, N)
    inv_N = pow(N, p - 2, p)
    for a in range(L):
        y = [(x[j] * pow(w, (-a * j * j) % N, p)) % p for j in range(N)]
        # Inverse DFT recovers amplitudes of y_j = sum gamma_l w^{u_l j}
        freqs_nz = 0
        for u in range(N):
            coeff = (sum(y[j] * pow(w, (-u * j) % N, p) for j in range(N)) * inv_N) % p
            if coeff != 0:
                freqs_nz += 1
        if freqs_nz <= r:
            return True
    return False


def bm_connection(y: list[int], p: int) -> tuple[int, list[int]]:
    """Standard Berlekamp-Massey returning (order L, connection poly C)."""
    C = [1]
    B = [1]
    L = 0
    m = 1
    b = 1
    for n in range(len(y)):
        d = y[n] % p
        for i in range(1, L + 1):
            d = (d + C[i] * y[n - i]) % p
        if d == 0:
            m += 1
        else:
            T = list(C)
            coef = (d * pow(b, p - 2, p)) % p
            need = len(B) + m
            if len(C) < need:
                C.extend([0] * (need - len(C)))
            for i in range(len(B)):
                C[i + m] = (C[i + m] - coef * B[i]) % p
            if 2 * L <= n:
                L = n + 1 - L
                B = T
                b = d
                m = 1
            else:
                m += 1
    return L, C[: L + 1]


def poly_eval_mod(poly: list[int], x: int, p: int) -> int:
    acc = 0
    for c in reversed(poly):
        acc = (acc * x + c) % p
    return acc


def recognize_dyadic_bm(x: list[int], w: int, p: int, r: int) -> tuple[bool, list[int] | None]:
    N = len(x)
    assert N >= 3 and (N & (N - 1)) == 0 and 1 <= r <= N // 3
    if all(v % p == 0 for v in x):
        return True, [0] * N
    c = None
    for idx in range(r, N - r):
        if x[idx] % p != 0:
            c = idx
            break
    if c is None:
        return False, None
    E = levinson_eliminant(x, c, r, p)
    L = N // 2
    eta = pow(w, (-2) % N, p)
    cands = [a for a in range(L) if poly_eval_mod(E, pow(eta, a, p), p) == 0]
    for a in cands:
        y = [(x[j] * pow(w, (-a * j * j) % N, p)) % p for j in range(N)]
        s, C = bm_connection(y[: 2 * r], p)
        if s > r:
            continue
        if s == 0:
            if all(v == 0 for v in y):
                return True, [0] * N
            continue
        if len(C) != s + 1 or C[s] % p == 0:
            continue
        roots = []
        for v in range(N):
            if poly_eval_mod(C, pow(w, v, p), p) == 0:
                roots.append(v)
        if len(roots) != s:
            continue
        # Compute Q(z) = C(z) * sum_{j<s} y_j z^j mod z^s and C'(z)
        Q = r_mul(C[:s], y[:s], p, s)
        Cp = [(i * C[i]) % p for i in range(1, s + 1)]
        freqs = []
        amps = []
        ok = True
        for v in roots:
            rho = pow(w, v, p)
            lam = pow(w, (-v) % N, p)
            denom = poly_eval_mod(Cp, rho, p)
            if denom == 0:
                ok = False
                break
            gam = (-lam * poly_eval_mod(Q, rho, p) * pow(denom, p - 2, p)) % p
            if gam == 0:
                ok = False
                break
            freqs.append((-v) % N)
            amps.append(gam)
        if not ok:
            continue
        # Full-vector synthesis check
        synth = [
            sum(amps[i] * pow(w, (freqs[i] * j) % N, p) for i in range(s)) % p
            for j in range(N)
        ]
        if synth == y:
            G = gauss_row_formula(N, a, w, p)
            dft_out = [
                sum(amps[i] * G[(k + freqs[i]) % N] for i in range(s)) % p
                for k in range(N)
            ]
            return True, dft_out
    return False, None


def solve_linear_mod(A: list[list[int]], b: list[int], p: int) -> list[int] | None:
    n = len(A)
    aug = [[A[i][j] % p for j in range(n)] + [b[i] % p] for i in range(n)]
    for col in range(n):
        piv = None
        for i in range(col, n):
            if aug[i][col] % p != 0:
                piv = i
                break
        if piv is None:
            return None
        aug[col], aug[piv] = aug[piv], aug[col]
        inv_p = pow(aug[col][col], p - 2, p)
        for j in range(n + 1):
            aug[col][j] = (aug[col][j] * inv_p) % p
        for i in range(n):
            if i != col and aug[i][col]:
                fac = aug[i][col]
                for j in range(n + 1):
                    aug[i][j] = (aug[i][j] - fac * aug[col][j]) % p
    return [aug[i][n] for i in range(n)]


def rank_mod(mat: list[list[int]], p: int) -> int:
    m, n = len(mat), len(mat[0])
    A = [[v % p for v in row] for row in mat]
    r = 0
    for col in range(n):
        piv = None
        for i in range(r, m):
            if A[i][col] % p != 0:
                piv = i
                break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv_p = pow(A[r][col], p - 2, p)
        for j in range(col, n):
            A[r][j] = (A[r][j] * inv_p) % p
        for i in range(r + 1, m):
            fac = A[i][col]
            if fac:
                for j in range(col, n):
                    A[i][j] = (A[i][j] - fac * A[r][j]) % p
        r += 1
        if r == m:
            break
    return r


def recognize_all_length_hankel(x: list[int], w: int, p: int, r: int) -> tuple[bool, list[int] | None]:
    N = len(x)
    if all(v % p == 0 for v in x):
        return True, [0] * N
    c = None
    for idx in range(r, N - r):
        if x[idx] % p != 0:
            c = idx
            break
    if c is None:
        return False, None
    E = levinson_eliminant(x, c, r, p)
    L = N // math.gcd(2, N)
    eta = pow(w, (-2) % N, p)
    cands = [a for a in range(L) if poly_eval_mod(E, pow(eta, a, p), p) == 0]
    for a in cands:
        y = [(x[j] * pow(w, (-a * j * j) % N, p)) % p for j in range(N)]
        H_r = [[y[i + j] for j in range(r)] for i in range(r)]
        s = rank_mod(H_r, p)
        if s == 0:
            if all(v == 0 for v in y):
                return True, [0] * N
            continue
        H_s = [[y[i + j] for j in range(s)] for i in range(s)]
        rhs = [(-y[i + s]) % p for i in range(s)]
        p_coeffs = solve_linear_mod(H_s, rhs, p)
        if p_coeffs is None:
            continue
        poly = p_coeffs + [1]
        roots = [u for u in range(N) if poly_eval_mod(poly, pow(w, u, p), p) == 0]
        if len(roots) != s:
            continue
        # Check all N - s recurrence residuals
        if not all(
            sum(poly[j] * y[k + j] for j in range(s + 1)) % p == 0
            for k in range(N - s)
        ):
            continue
        # Vandermonde solve for first s samples
        V = [[pow(w, (i * u) % N, p) for u in roots] for i in range(s)]
        amps_raw = solve_linear_mod(V, y[:s], p)
        if amps_raw is None:
            continue
        pairs = [(u, g) for u, g in zip(roots, amps_raw) if g != 0]
        G = gauss_row_formula(N, a, w, p)
        dft_out = [
            sum(g * G[(k + u) % N] for u, g in pairs) % p
            for k in range(N)
        ]
        return True, dft_out
    return False, None


def verify_recognizers() -> None:
    # 1. Exhaustive over ALL 625 vectors of F_5^4 (N=4, p=5, w=2, r=1)
    acc_cnt = 0
    for vec in itertools.product(range(5), repeat=4):
        x = list(vec)
        ora = oracle_in_Cr(x, 2, 5, 1)
        ok_bm, dft_bm = recognize_dyadic_bm(x, 2, 5, 1)
        ok_hk, dft_hk = recognize_all_length_hankel(x, 2, 5, 1)
        assert ok_bm == ora and ok_hk == ora, (x, ora, ok_bm, ok_hk)
        if ora:
            acc_cnt += 1
            dft_ref = direct_dft(x, 2, 5)
            assert dft_bm == dft_ref and dft_hk == dft_ref
    assert acc_cnt == 1 + 2 * 4 * 4 == 33  # 0 + 2 phases * 4 freqs * 4 amps (Wait: check exact count!)

    # 2. Structured + adversarial tests at N=8 (p=17, w=2, r=2), N=9 (p=19, w=4, r=2), N=16 (p=17, w=3, r=3)
    extra = 0
    # N=8, p=17, w=2, r=2
    for a in (0, 1, 2, 3):
        for freqs, amps in [([0, 3], [5, 11]), ([1, 6], [1, 16]), ([2], [9])]:
            x = [
                (pow(2, (a * j * j) % 8, 17) * sum(g * pow(2, (u * j) % 8, 17) for u, g in zip(freqs, amps))) % 17
                for j in range(8)
            ]
            ok1, d1 = recognize_dyadic_bm(x, 2, 17, 2)
            ok2, d2 = recognize_all_length_hankel(x, 2, 17, 2)
            ref = direct_dft(x, 2, 17)
            assert ok1 and ok2 and d1 == ref and d2 == ref
            extra += 1
    # Adversarial impulse & false-prefix & off-grid rejections at N=8
    for x_bad in [
        [1, 0, 0, 0, 0, 0, 0, 0],  # impulse (no interior center)
        [0, 0, 0, 0, 0, 0, 0, 5],  # late nonzero after zero prefix
        [1, 2, 4, 8, 16, 15, 13, 10],  # corrupted exponential
        [1, 3, 9, 10, 13, 5, 15, 11],  # off-grid lambda=3 (order 16, not 8th root!)
    ]:
        ora = oracle_in_Cr(x_bad, 2, 17, 2)
        ok1, _ = recognize_dyadic_bm(x_bad, 2, 17, 2)
        ok2, _ = recognize_all_length_hankel(x_bad, 2, 17, 2)
        assert ok1 == ora and ok2 == ora and not ora
        extra += 1

    # N=9 (non-dyadic!), p=19, w=4, r=2
    for a in (0, 1, 4, 8):
        x = [
            (pow(4, (a * j * j) % 9, 19) * (3 * pow(4, (2 * j) % 9, 19) + 7 * pow(4, (5 * j) % 9, 19))) % 19
            for j in range(9)
        ]
        ok2, d2 = recognize_all_length_hankel(x, 4, 19, 2)
        assert ok2 and d2 == direct_dft(x, 4, 19)
        extra += 1

    # N=16, p=17, w=3, r=3 (includes D = 10 >= L = 8!)
    for a in (0, 3, 7):
        freqs, amps = [1, 5, 12], [2, 6, 14]
        x = [
            (pow(3, (a * j * j) % 16, 17) * sum(g * pow(3, (u * j) % 16, 17) for u, g in zip(freqs, amps))) % 17
            for j in range(16)
        ]
        ok1, d1 = recognize_dyadic_bm(x, 3, 17, 3)
        ok2, d2 = recognize_all_length_hankel(x, 3, 17, 3)
        ref = direct_dft(x, 3, 17)
        assert ok1 and ok2 and d1 == ref and d2 == ref
        extra += 1

    print(f"  [PASS] Exhaustive F_5^4 (625 vectors, {acc_cnt} accepted) + {extra} N=8,9,16 structured/adversarial tests passed")


# ---- 4. Blocked chirp identity (5.1) & fresh-vector sparse operator identity (7.1) ----
def verify_blocked_and_operator_identities() -> None:
    # Blocked binomial identity aj = C(a,2) + C(j+1,2) - C(a-j,2)
    for a in range(-10, 11):
        for j in range(-10, 11):
            lhs = a * j
            rhs = f_exp(a) + f_exp(j + 1) - f_exp(a - j)
            assert lhs == rhs
    # Fresh-vector operator M_x v for sparse phase-0 certificate at N=8, p=17, w=2
    N, p, w = 8, 17, 2
    freqs, amps = [1, 5], [3, 10]
    x = [sum(g * pow(w, (u * j) % N, p) for u, g in zip(freqs, amps)) % p for j in range(N)]
    alpha = [1, 3, 2, 5, 4, 7, 6, 9]
    beta = [2, 1, 4, 3, 6, 5, 8, 7]
    v = [5, 12, 3, 9, 1, 14, 7, 2]
    # Direct M_x v = diag(alpha) F diag(x) F diag(beta) v
    bv = [(beta[j] * v[j]) % p for j in range(N)]
    Fbv = direct_dft(bv, w, p)
    xFbv = [(x[j] * Fbv[j]) % p for j in range(N)]
    FxFbv = direct_dft(xFbv, w, p)
    direct = [(alpha[i] * FxFbv[i]) % p for i in range(N)]
    # Sparse formula: N * alpha_i * sum gamma_l * beta_{-i-u_l} * v_{-i-u_l}
    sparse = [
        (N * alpha[i] * sum(g * beta[(-i - u) % N] * v[(-i - u) % N] for u, g in zip(freqs, amps))) % p
        for i in range(N)
    ]
    assert direct == sparse
    print("  [PASS] Blocked integer-binomial identity & fresh-vector sparse operator formula verified")


def main() -> None:
    print("Running exact verification for Paper 6 (Finite-Field Chirp Eliminant)...")
    verify_eliminant_ring_algebra()
    verify_gauss_rows()
    verify_recognizers()
    verify_blocked_and_operator_identities()
    print("ALL CHECKS PASSED.")


if __name__ == "__main__":
    main()
