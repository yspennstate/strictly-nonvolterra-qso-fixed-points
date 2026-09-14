"""Numerical companion to
    "Strictly non-Volterra quadratic stochastic operators in four or more types:
     the fixed point need not be unique"   (Rozikov's Problem 11)

What it does, in order:
  1. exact rational verification of the five-type operator W: symmetric, nonnegative, row-stochastic,
     strictly non-Volterra; W(p) = p and W(q) = q; Jacobians and their tangent-space eigenvalues;
  2. ALL fixed points of W on the affine hull of the simplex (Newton from many starts, deduplicated,
     then polished and classified as inside / on the boundary / outside the simplex), plus a Groebner-basis
     count when sympy manages it;
  3. the dynamics of W: orbits from random starts, their limit behaviour (fixed point, 2-cycle, other);
  4. the equiprobable family at m = 4: the coordinate-diameter contraction and convergence to the barycentre;
  5. a six-type operator with two disjoint invariant triples and its fixed points;
  6. random strictly non-Volterra operators at m = 4 and m = 5: the number of fixed points in the simplex.

Run: python qso_fixed_points.py   (writes results.md and figures/fixed_point_counts.pdf)
Dependencies: numpy, sympy, matplotlib.
"""
import numpy as np, sympy as sp, itertools, math, os, time
from fractions import Fraction as Fr
HERE = os.path.dirname(os.path.abspath(__file__)); FIG = os.path.normpath(os.path.join(HERE, "..", "figures")); os.makedirs(FIG, exist_ok=True)
out = []
def say(s=""): print(s); out.append(s)
rng = np.random.default_rng(20260914)

# ------------------------------------------------------------------------------------------------
# generic QSO machinery: P[i][j][k] with P symmetric in (i,j); V_k(x) = sum_{i,j} P_ijk x_i x_j
# ------------------------------------------------------------------------------------------------
def V_of(P):
    P = np.asarray(P, dtype=float); m = P.shape[0]
    return lambda x: np.einsum("ijk,i,j->k", P, x, x)
def jac_of(P):
    P = np.asarray(P, dtype=float)
    return lambda x: 2 * np.einsum("ijk,i->kj", P, x)   # dV_k/dx_j = 2 sum_i P_ijk x_i (symmetry in i,j)
def check_qso(P, strict=True, tol=1e-12):
    P = np.asarray(P, dtype=float); m = P.shape[0]
    sym = np.allclose(P, P.transpose(1, 0, 2))
    nonneg = (P >= -tol).all()
    rows = np.allclose(P.sum(axis=2), 1.0)
    snv = all(abs(P[i, j, k]) <= tol for i in range(m) for j in range(m) for k in (i, j))
    return sym, nonneg, rows, (snv if strict else None)

def fixed_points(P, starts=400, tol=1e-11):
    """Newton on the affine hull (sum x = 1) for V(x) = x; returns deduplicated solutions."""
    P = np.asarray(P, dtype=float); m = P.shape[0]; V = V_of(P); J = jac_of(P)
    sols = []
    for s in range(starts):
        x = rng.dirichlet(np.ones(m)) if s % 2 == 0 else rng.normal(size=m); x = x / x.sum() if abs(x.sum()) > 1e-9 else rng.dirichlet(np.ones(m))
        for it in range(60):
            F = np.append(V(x) - x, x.sum() - 1.0)
            A = np.vstack([J(x) - np.eye(m), np.ones(m)])
            try: dx = np.linalg.lstsq(A, -F, rcond=None)[0]
            except np.linalg.LinAlgError: break
            x = x + dx
            if np.linalg.norm(dx) < 1e-14: break
            if np.linalg.norm(x) > 1e3: break
        if np.linalg.norm(V(x) - x) < tol and abs(x.sum() - 1) < tol:
            if not any(np.linalg.norm(x - y) < 1e-7 for y in sols): sols.append(x)
    return sols
def in_simplex(x, tol=1e-9): return bool((x >= -tol).all())

# ------------------------------------------------------------------------------------------------
# 1. the five-type operator W
# ------------------------------------------------------------------------------------------------
def five_type():
    m = 5; F = [0, 1, 2]; P = [[[Fr(0)] * m for _ in range(m)] for _ in range(m)]
    def setP(i, j, k, v): P[i][j][k] = v; P[j][i][k] = v
    for i in F:
        for k in F:
            if k != i: setP(i, i, k, Fr(1, 2))
    for i, j in itertools.combinations(F, 2):
        k = [t for t in F if t not in (i, j)][0]; setP(i, j, k, Fr(1))
    for i in F: setP(i, 3, 4, Fr(1)); setP(i, 4, 3, Fr(1))
    setP(3, 3, 4, Fr(1)); setP(4, 4, 3, Fr(1))
    for k in F: setP(3, 4, k, Fr(1, 3))
    return P
def exact_V(P, x):
    m = len(P); return [sum(P[i][j][k] * x[i] * x[j] for i in range(m) for j in range(m)) for k in range(m)]

def section1():
    say("## 1. The five-type operator W, exactly")
    P = five_type(); m = 5
    sym = all(P[i][j][k] == P[j][i][k] for i in range(m) for j in range(m) for k in range(m))
    nonneg = all(P[i][j][k] >= 0 for i in range(m) for j in range(m) for k in range(m))
    rows = all(sum(P[i][j][k] for k in range(m)) == 1 for i in range(m) for j in range(m))
    snv = all(P[i][j][k] == 0 for i in range(m) for j in range(m) for k in (i, j))
    p = [Fr(1, 3)] * 3 + [Fr(0)] * 2; q = [Fr(1, 9)] * 3 + [Fr(1, 3)] * 2
    say(f"symmetric {sym}; nonnegative {nonneg}; row sums one {rows}; strictly non-Volterra {snv}")
    say(f"W(p) = p: {exact_V(P, p) == p};  W(q) = q: {exact_V(P, q) == q}")
    xs = sp.symbols("x0:5"); Vs = [sum(sp.Rational(P[i][j][k]) * xs[i] * xs[j] for i in range(m) for j in range(m)) for k in range(m)]
    say("coordinates: " + "; ".join(f"W_{k} = {sp.factor(Vs[k])}" for k in range(m)))
    J = sp.Matrix(Vs).jacobian(xs)
    B = sp.Matrix([[1 if r == i else (-1 if r == 4 else 0) for i in range(4)] for r in range(5)])
    for name, pt in (("p", p), ("q", q)):
        Jp = J.subs(dict(zip(xs, [sp.Rational(v) for v in pt])))
        T = (B.T * B).inv() * B.T * Jp * B
        ev = T.eigenvals(); idx = sp.sign(sp.prod([(1 - lam) ** mult for lam, mult in ev.items()]))
        say(f"at {name}: full-space eigenvalues {Jp.eigenvals()}; tangent eigenvalues {ev}; sign det(I - DW_T) = {idx}; spectral radius on the tangent space {max(abs(l) for l in ev)}")
    say(f"trace of DW is identically zero: {sp.simplify(J.trace()) == 0}")
    return P

def section2(P):
    say("\n## 2. All fixed points of W on the affine hull")
    Pf = np.array([[[float(v) for v in row] for row in mat] for mat in P])
    sols = fixed_points(Pf, starts=3000)
    sols.sort(key=lambda x: (not in_simplex(x), tuple(np.round(x, 6))))
    for x in sols:
        say(f"  {np.round(x, 8).tolist()}  in simplex: {in_simplex(x)}")
    say(f"solutions found: {len(sols)}; in the simplex: {sum(in_simplex(x) for x in sols)}")
    # Groebner count of the full complex solution set, if sympy manages it in reasonable time
    try:
        xs = sp.symbols("x0:5"); m = 5
        Vs = [sum(sp.Rational(P[i][j][k]) * xs[i] * xs[j] for i in range(m) for j in range(m)) for k in range(m)]
        eqs = [Vs[k] - xs[k] for k in range(m - 1)] + [sum(xs) - 1]
        t0 = time.time(); G = sp.groebner(eqs, *xs, order="lex");
        last = G.exprs[-1]; deg = sp.Poly(last, xs[-1]).degree() if last.free_symbols <= {xs[-1]} else None
        say(f"Groebner basis (lex) computed in {time.time()-t0:.1f} s; last polynomial in x4 of degree {deg}: {sp.factor(last)}")
    except Exception as e:
        say(f"Groebner step skipped: {type(e).__name__}")
    return sols

def section3(P):
    say("\n## 3. Dynamics of W from random starts")
    Pf = np.array([[[float(v) for v in row] for row in mat] for mat in P]); V = V_of(Pf)
    kinds = {}
    def step(x):
        y = V(x); return y / y.sum()      # renormalise: sum V = (sum x)^2, so rounding error would otherwise compound
    for s in range(300):
        x = rng.dirichlet(np.ones(5))
        for _ in range(4000): x = step(x)
        # classify by the smallest period up to 12, else "other"
        orbit = [x]
        for _ in range(12): orbit.append(step(orbit[-1]))
        per = next((r for r in range(1, 13) if np.linalg.norm(orbit[r] - x) < 1e-8), None)
        if per == 1: k = "fixed point " + str(np.round(x, 4).tolist())
        elif per == 2: k = "2-cycle {" + str(np.round(x, 4).tolist()) + ", " + str(np.round(orbit[1], 4).tolist()) + "}"
        elif per: k = f"{per}-cycle"
        else: k = "other (no period <= 12 after 4000 steps; largest coordinate range " + str(np.round(max(o.max() for o in orbit) - min(o.min() for o in orbit), 3)) + ")"
        kinds[k] = kinds.get(k, 0) + 1
    for k, c in sorted(kinds.items(), key=lambda kv: -kv[1]): say(f"  {c:4d} orbits -> {k}")
    return kinds

def equiprobable(m):
    P = np.zeros((m, m, m))
    for i in range(m):
        for j in range(m):
            for k in range(m):
                if k in (i, j): continue
                P[i, j, k] = 1.0 / (m - 1) if i == j else 1.0 / (m - 2)
    return P
def section4():
    say("\n## 4. The equiprobable family at m = 4: global attraction")
    m = 4; P = equiprobable(m); V = V_of(P)
    say(f"equiprobable m=4 is a strictly non-Volterra QSO: {check_qso(P)}")
    xs = sp.symbols("x0:4"); Vs = [sum(sp.Rational(P[i, j, k]).limit_denominator(100) * xs[i] * xs[j] for i in range(m) for j in range(m)) for k in range(m)]
    S = sum(xs)
    diff = sp.simplify(Vs[0] - Vs[1] - (xs[1] - xs[0]) * (2 * S - sp.Rational(m, m - 1) * (xs[0] + xs[1])) / (m - 2))
    say(f"V_k - V_l = (x_l - x_k)[2 S - m(x_k+x_l)/(m-1)]/(m-2) with S = sum x holds symbolically: {diff == 0}")
    worst = 0.0
    for s in range(200):
        x = rng.dirichlet(np.ones(m) * 0.3)
        for _ in range(500):
            x = V(x); x = x / x.sum()
        worst = max(worst, np.abs(x - 0.25).max())
    say(f"after 500 iterations from 200 random starts, max distance to the barycentre: {worst:.2e}; contraction factor bound (2m-1)/(m-1)^2 = {(2*m-1)/(m-1)**2:.4f}")

def six_type(symmetric_cross=True):
    """two invariant triples F = {0,1,2}, G = {3,4,5}: the symmetric three-type operator inside each triple.
    Cross pairs {i, j}, i in F, j in G: either the symmetric rule (land on the four types of (F minus i) and
    (G minus j) equally) or random Dirichlet weights over those four targets."""
    m = 6; P = np.zeros((m, m, m)); F = [0, 1, 2]; G = [3, 4, 5]
    for T in (F, G):
        for i in T:
            for k in T:
                if k != i: P[i, i, k] = 0.5
        for i, j in itertools.combinations(T, 2):
            k = [t for t in T if t not in (i, j)][0]; P[i, j, k] = P[j, i, k] = 1.0
    for i in F:
        for j in G:
            targets = [t for t in F if t != i] + [t for t in G if t != j]
            w = np.ones(len(targets)) / len(targets) if symmetric_cross else rng.dirichlet(np.ones(len(targets)))
            for t, wt in zip(targets, w): P[i, j, t] = P[j, i, t] = wt
    return P
def section5():
    say("\n## 5. Six-type operators with two disjoint invariant triples")
    # (a) the symmetric cross rule: on the line x = (a,a,a,b,b,b), 3a + 3b = 1, one has V_k = 3a^2 + 3ab = a for
    #     k in F and likewise b on G, so the whole segment is fixed. Check the identity symbolically.
    P = six_type(True); say(f"(a) symmetric cross rule: symmetric, nonnegative, row-stochastic, strictly non-Volterra: {check_qso(P)}")
    a = sp.symbols("a"); b = sp.Rational(1, 3) - a; x = [a, a, a, b, b, b]
    Vsym = [sp.expand(sum(sp.nsimplify(P[i, j, k]) * x[i] * x[j] for i in range(6) for j in range(6))) for k in range(6)]
    say(f"    on the segment (a,a,a,1/3-a,1/3-a,1/3-a): V = {Vsym}; identically fixed: {all(sp.simplify(Vsym[k] - x[k]) == 0 for k in range(6))}")
    # (b) random cross weights: isolated fixed points; the two face points must be among them
    P = six_type(False); say(f"(b) random cross weights: symmetric, nonnegative, row-stochastic, strictly non-Volterra: {check_qso(P)}")
    sols = fixed_points(P, starts=1500)
    for x in sols: say(f"    {np.round(x, 6).tolist()}  in simplex: {in_simplex(x)}")
    say(f"    fixed points in the simplex: {sum(in_simplex(x) for x in sols)}; the two face points present: "
        f"{any(np.allclose(x,[1/3,1/3,1/3,0,0,0]) for x in sols) and any(np.allclose(x,[0,0,0,1/3,1/3,1/3]) for x in sols)}")
    np.save(os.path.join(HERE, "six_type_random_cross_P.npy"), P)

def random_snv(m, conc=1.0):
    P = np.zeros((m, m, m))
    for i in range(m):
        for j in range(i, m):
            targets = [k for k in range(m) if k not in (i, j)]
            w = rng.dirichlet(np.ones(len(targets)) * conc)
            for t, wt in zip(targets, w): P[i, j, t] = P[j, i, t] = wt
    return P
def section6():
    say("\n## 6. Random strictly non-Volterra operators: number of fixed points in the simplex")
    table = {}
    for m, n, conc in ((4, 300, 1.0), (4, 200, 0.1), (5, 200, 1.0), (5, 100, 0.1), (6, 60, 1.0)):
        counts = {}
        for s in range(n):
            P = random_snv(m, conc); sols = fixed_points(P, starts=120)
            c = sum(in_simplex(x) for x in sols); counts[c] = counts.get(c, 0) + 1
        table[(m, conc)] = counts
        say(f"m = {m}, Dirichlet concentration {conc}, {n} operators: counts of fixed points in the simplex {dict(sorted(counts.items()))}")
    import matplotlib; matplotlib.use("Agg"); import matplotlib.pyplot as plt
    fig, ax = plt.subplots(figsize=(5.2, 3.2)); labels = []; vals = []
    for (m, conc), counts in table.items():
        for c, n in sorted(counts.items()): labels.append(f"m={m}, c={conc}: {c} fp"); vals.append(n)
    ax.barh(labels, vals); ax.set_xlabel("operators"); ax.set_title("fixed points in the simplex, random strictly non-Volterra operators"); fig.tight_layout()
    fig.savefig(os.path.join(FIG, "fixed_point_counts.pdf")); fig.savefig(os.path.join(FIG, "fixed_point_counts.png"), dpi=150)

def section7():
    """all vertex operators on four types: every pair sends its whole mass to one admissible target
    (3^4 * 2^6 = 5184 operators); count the fixed points in the simplex of each."""
    say("\n## 7. All 5184 four-type vertex operators")
    m = 4; pairs = [(i, j) for i in range(m) for j in range(i, m)]
    choices = [[k for k in range(m) if k not in (i, j)] for (i, j) in pairs]
    counts = {}; worst = None
    for combo in itertools.product(*choices):
        P = np.zeros((m, m, m))
        for (i, j), k in zip(pairs, combo): P[i, j, k] = P[j, i, k] = 1.0
        sols = fixed_points(P, starts=40); c = sum(in_simplex(x) for x in sols)
        counts[c] = counts.get(c, 0) + 1
        if c != 1 and worst is None: worst = (combo, [np.round(x, 5).tolist() for x in sols if in_simplex(x)])
    say(f"fixed points in the simplex over all 5184 vertex operators: {dict(sorted(counts.items()))}" + (f"; first exception {worst}" if worst else ""))

def section8():
    """the swap extension of Theorem: random three-type operators U and random rho give exactly two fixed points."""
    say("\n## 8. Swap extensions of random three-type operators")
    counts = {}
    for s in range(200):
        U = random_snv(3); rho = rng.dirichlet(np.ones(3)); m = 5; P = np.zeros((m, m, m))
        P[:3, :3, :3] = U
        for i in range(3): P[i, 3, 4] = P[3, i, 4] = 1.0; P[i, 4, 3] = P[4, i, 3] = 1.0
        P[3, 3, 4] = 1.0; P[4, 4, 3] = 1.0
        for k in range(3): P[3, 4, k] = P[4, 3, k] = rho[k]
        assert all(v for v in check_qso(P))
        sols = fixed_points(P, starts=150); c = sum(in_simplex(x) for x in sols)
        ok = all(abs(x[3] - x[4]) < 1e-8 and (abs(x[3]) < 1e-8 or abs(x[3] - 1/3) < 1e-8) for x in sols if in_simplex(x))
        counts[(c, ok)] = counts.get((c, ok), 0) + 1
    say(f"200 random swap extensions: (number of fixed points in the simplex, all with x4 = x5 in {{0, 1/3}}) -> {counts}")

def main():
    t0 = time.time(); say("# Numerical companion: results\n")
    P = section1(); section2(P); section3(P); section4(); section5(); section6(); section7(); section8()
    say(f"\nelapsed {time.time()-t0:.0f} s")
    open(os.path.join(HERE, "results.md"), "w", encoding="utf-8").write("\n".join(out) + "\n")

if __name__ == "__main__":
    main()
