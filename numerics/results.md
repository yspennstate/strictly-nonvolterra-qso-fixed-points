# Numerical companion: results

## 1. The five-type operator W, exactly
symmetric True; nonnegative True; row sums one True; strictly non-Volterra True
W(p) = p: True;  W(q) = q: True
coordinates: W_0 = (3*x1**2 + 12*x1*x2 + 3*x2**2 + 4*x3*x4)/6; W_1 = (3*x0**2 + 12*x0*x2 + 3*x2**2 + 4*x3*x4)/6; W_2 = (3*x0**2 + 12*x0*x1 + 3*x1**2 + 4*x3*x4)/6; W_3 = x4*(2*x0 + 2*x1 + 2*x2 + x4); W_4 = x3*(2*x0 + 2*x1 + 2*x2 + x3)
at p: full-space eigenvalues {2: 2, -1: 2, -2: 1}; tangent eigenvalues {2: 1, -1: 2, -2: 1}; sign det(I - DW_T) = -1; spectral radius on the tangent space 2
at q: full-space eigenvalues {2: 1, -4/3: 1, -1/3: 2, 0: 1}; tangent eigenvalues {-1/3: 2, 0: 1, -4/3: 1}; sign det(I - DW_T) = 1; spectral radius on the tangent space 4/3
trace of DW is identically zero: True

## 2. All fixed points of W on the affine hull
  [0.11111111, 0.11111111, 0.11111111, 0.33333333, 0.33333333]  in simplex: True
  [0.33333333, 0.33333333, 0.33333333, 0.0, 0.0]  in simplex: True
  [-2.0, -0.0, 0.0, -0.79128785, 3.79128785]  in simplex: False
  [-2.0, -0.0, 0.0, 3.79128785, -0.79128785]  in simplex: False
  [-1.0, -1.0, 3.0, 0.0, 0.0]  in simplex: False
  [-1.0, 3.0, -1.0, -0.0, -0.0]  in simplex: False
  [-0.77777778, -0.77777778, 1.88888889, 0.33333333, 0.33333333]  in simplex: False
  [-0.77777778, 1.88888889, -0.77777778, 0.33333333, 0.33333333]  in simplex: False
  [-0.66666667, -0.66666667, -0.66666667, -0.79128785, 3.79128785]  in simplex: False
  [-0.66666667, -0.66666667, -0.66666667, 3.79128785, -0.79128785]  in simplex: False
  [-0.0, -2.0, -0.0, -0.79128785, 3.79128785]  in simplex: False
  [-0.0, -2.0, -0.0, 3.79128785, -0.79128785]  in simplex: False
  [0.0, -0.0, -2.0, -0.79128785, 3.79128785]  in simplex: False
  [0.0, 0.0, -2.0, 3.79128785, -0.79128785]  in simplex: False
  [1.88888889, -0.77777778, -0.77777778, 0.33333333, 0.33333333]  in simplex: False
  [3.0, -1.0, -1.0, 0.0, 0.0]  in simplex: False
solutions found: 16; in the simplex: 2
Groebner basis (lex) computed in 0.0 s; last polynomial in x4 of degree 4: x4*(3*x4 - 1)*(x4**2 - 3*x4 - 3)/3

## 3. Dynamics of W from random starts
   164 orbits -> 2-cycle {[0.0, 0.0, 0.0, 1.0, 0.0], [0.0, 0.0, 0.0, 0.0, 1.0]}
   136 orbits -> 2-cycle {[0.0, 0.0, 0.0, 0.0, 1.0], [0.0, 0.0, 0.0, 1.0, 0.0]}

## 4. The equiprobable family at m = 4: global attraction
equiprobable m=4 is a strictly non-Volterra QSO: (True, np.True_, True, True)
V_k - V_l = (x_l - x_k)[2 S - m(x_k+x_l)/(m-1)]/(m-2) with S = sum x holds symbolically: True
after 500 iterations from 200 random starts, max distance to the barycentre: 0.00e+00; contraction factor bound (2m-1)/(m-1)^2 = 0.7778

## 5. Six-type operators with two disjoint invariant triples
(a) symmetric cross rule: symmetric, nonnegative, row-stochastic, strictly non-Volterra: (True, np.True_, True, True)
    on the segment (a,a,a,1/3-a,1/3-a,1/3-a): V = [a, a, a, 1/3 - a, 1/3 - a, 1/3 - a]; identically fixed: True
(b) random cross weights: symmetric, nonnegative, row-stochastic, strictly non-Volterra: (True, np.True_, True, True)
    [0.333333, 0.333333, 0.333333, 0.0, 0.0, 0.0]  in simplex: True
    [0.632468, 0.036066, 0.38512, -0.998059, 1.940677, -0.996272]  in simplex: False
    [-1.0, -1.0, 3.0, 0.0, 0.0, 0.0]  in simplex: False
    [0.0, 0.0, 0.0, 0.333333, 0.333333, 0.333333]  in simplex: True
    [3.0, -1.0, -1.0, 0.0, 0.0, 0.0]  in simplex: False
    [0.542678, 0.425233, 0.597104, 0.134687, -0.324148, -0.375554]  in simplex: False
    [0.0, -0.0, -0.0, -1.0, -1.0, 3.0]  in simplex: False
    [0.181501, -0.837184, -0.869767, 1.171854, 0.660813, 0.692783]  in simplex: False
    [-0.0, -0.0, 0.0, -1.0, 3.0, -1.0]  in simplex: False
    [-2.199549, 0.431958, -0.912809, 1.424158, 1.455949, 0.800293]  in simplex: False
    [-1.207308, -6.881099, 0.001028, 5.196062, 0.693651, 3.197666]  in simplex: False
    [-1.0, 3.0, -1.0, -0.0, 0.0, 0.0]  in simplex: False
    [-0.0, 0.0, -0.0, 3.0, -1.0, -1.0]  in simplex: False
    [-1.915551, 6.903069, -1.809079, -2.958349, -2.079983, 2.859893]  in simplex: False
    [-1.396809, -6.818301, 0.240645, 3.596744, -0.667291, 6.045011]  in simplex: False
    [-4.483662, 4.685727, 11.833165, -1.719669, -15.103395, 5.787835]  in simplex: False
    fixed points in the simplex: 2; the two face points present: True

## 6. Random strictly non-Volterra operators: number of fixed points in the simplex
m = 4, Dirichlet concentration 1.0, 300 operators: counts of fixed points in the simplex {1: 300}
m = 4, Dirichlet concentration 0.1, 200 operators: counts of fixed points in the simplex {1: 200}
m = 5, Dirichlet concentration 1.0, 200 operators: counts of fixed points in the simplex {1: 200}
m = 5, Dirichlet concentration 0.1, 100 operators: counts of fixed points in the simplex {1: 100}
m = 6, Dirichlet concentration 1.0, 60 operators: counts of fixed points in the simplex {1: 60}

## 7. All 5184 four-type vertex operators
fixed points in the simplex over all 5184 vertex operators: {1: 5184}

## 8. Swap extensions of random three-type operators
200 random swap extensions: (number of fixed points in the simplex, all with x4 = x5 in {0, 1/3}) -> {(2, True): 200}

elapsed 310 s
