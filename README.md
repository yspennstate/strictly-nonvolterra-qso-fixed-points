# Strictly non-Volterra quadratic stochastic operators: the fixed point need not be unique

Companion material for the paper of the same title (Y. Shmalo, September 2026), which answers Problem 11
of Ganikhodzhaev and Rozikov, *Quadratic stochastic operators: results and open problems* (2009): Theorem 6
(unique, non-attractive fixed point of a strictly non-Volterra operator on three types) does not extend to
four or more types. Non-attractiveness fails from four types (the equiprobable family of Jamilov, Ladra
and Mukhitdinov, 2017); uniqueness fails from five types, by a rational operator with two fixed points
studied by Jamilov (Uzbek Math. J., 2017), which the paper shows to be one member of a family in which
the count is always exactly two, and a six-type operator has a whole segment of fixed points. Uniqueness
at four types is left open and reduced to one determinant inequality by an index count.

Contents

- `paper/` the LaTeX source and the compiled PDF.
- `numerics/qso_fixed_points.py` the numerical companion: exact verification of the five-type operator, all
  its fixed points (Newton and an exact Groebner solve), its dynamics, the equiprobable family, six-type
  operators with two invariant triples, and fixed-point counts for random operators on four to six types;
  `numerics/results.md` is its output.
- `figures/` the figure produced by the script.
- `lean/QSOFixedPoints.lean` the Lean 4 verification (operator and Jacobian for any number of types; Euler's
  identity, zero trace, the invariant-face lemma, the four-type face observation; the five-type operator's
  conditions, fixed points, Jacobians and complete spectra; the equiprobable four-type Jacobian at the
  barycentre; the six-type segment of fixed points), with the build log and axiom report. It compiles
  against Mathlib with Lean 4.33.1 (`lean/lean-toolchain`, `lean/lake-manifest.json`).
- `lean/QSOFourTypeUnique.lean` the Lean 4 proof of the four-type uniqueness theorem (`QSO4.unique_fixed_point`):
  for any coefficient table on four types that is symmetric, nonnegative, stochastic and strictly non-Volterra,
  two fixed points in the simplex coincide. `lean/build_four_type.log` is its build and axiom report.

To reproduce the numerics: `python numerics/qso_fixed_points.py` (numpy, sympy, matplotlib). To check the
Lean file: put it in a Lake project depending on Mathlib at the pinned commit and run `lake env lean QSOFixedPoints.lean`.
