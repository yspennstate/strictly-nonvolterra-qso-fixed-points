import Mathlib

/-!
# Strictly non-Volterra quadratic stochastic operators: the fixed point need not be unique

Companion to the paper answering Problem 11 of Ganikhodzhaev and Rozikov's 2009 list of open problems
on quadratic stochastic operators (whether Theorem 6 on strictly non-Volterra operators extends from
three types to `m ≥ 4`).

A quadratic stochastic operator on `m` types is `V k x = ∑ i j, P i j k * x i * x j` with `P i j k = P j i k ≥ 0`
and `∑ k, P i j k = 1`; it is strictly non-Volterra when `P i j k = 0` whenever `k ∈ {i, j}`.

What is checked here, all in exact rational arithmetic:

* `W`, the five-type operator of the paper: symmetric, nonnegative, row-stochastic, strictly non-Volterra
  (`W_symm`, `W_nonneg`, `W_rows`, `W_snv`); its two fixed points `p = (1/3,1/3,1/3,0,0)` and
  `q = (1/9,1/9,1/9,1/3,1/3)` (`W_fixes_p`, `W_fixes_q`, `p_ne_q`); the full eigen-decomposition of the
  Jacobian at each fixed point: five eigen-equations at each point (`eig_p_*`, `eig_q_*`) together with the
  non-vanishing of the determinant of the eigenvector matrix (`eigvecs_p_det`, `eigvecs_q_det`), which pins the
  spectrum to `{2, 2, -1, -1, -2}` at `p` and `{2, -4/3, -1/3, -1/3, 0}` at `q`;
* general facts for any operator on any number of types: Euler's identity `DV(x) x = 2 V(x)` (`euler`), the
  vanishing of the diagonal of the Jacobian for strictly non-Volterra operators (`jac_diag_zero`, hence zero
  trace), the invariant-face lemma behind the `m ≥ 6` construction (`face_fixed_point`: a fixed point of the
  restriction to an invariant face, padded by zeros, is a fixed point of the whole operator), and the four-type
  observation that a face-invariant operator has an identically vanishing fourth coordinate (`four_types_face`).

Axioms: `#print axioms` on every theorem reports only `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace QSO

open Finset BigOperators Matrix

/-- The operator `V` built from a coefficient tensor `P` (types `Fin m`). -/
def V {m : ℕ} (P : Fin m → Fin m → Fin m → ℚ) (x : Fin m → ℚ) (k : Fin m) : ℚ :=
  ∑ i, ∑ j, P i j k * x i * x j

/-- The Jacobian `DV(x)` as a matrix, row `k`, column `j`: `∂V_k/∂x_j = 2 ∑ i, P i j k x i`
(this uses the symmetry of `P` in its first two arguments). -/
def jac {m : ℕ} (P : Fin m → Fin m → Fin m → ℚ) (x : Fin m → ℚ) : Matrix (Fin m) (Fin m) ℚ :=
  fun k j => 2 * ∑ i, P i j k * x i

/-! ### General facts -/

/-- Euler's identity for the degree-two map: `DV(x) x = 2 V(x)`. -/
theorem euler {m : ℕ} (P : Fin m → Fin m → Fin m → ℚ) (x : Fin m → ℚ) :
    (jac P x).mulVec x = fun k => 2 * V P x k := by
  funext k
  simp only [Matrix.mulVec, dotProduct, jac, V]
  conv_rhs => rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_assoc, Finset.sum_mul]

/-- For a strictly non-Volterra operator the diagonal of the Jacobian vanishes identically,
so its trace is zero at every point. -/
theorem jac_diag_zero {m : ℕ} (P : Fin m → Fin m → Fin m → ℚ)
    (hsnv : ∀ i j k, (k = i ∨ k = j) → P i j k = 0) (x : Fin m → ℚ) (k : Fin m) :
    jac P x k k = 0 := by
  simp only [jac]
  have : ∀ i, P i k k * x i = 0 := fun i => by rw [hsnv i k k (Or.inr rfl)]; ring
  simp [this]

theorem trace_zero {m : ℕ} (P : Fin m → Fin m → Fin m → ℚ)
    (hsnv : ∀ i j k, (k = i ∨ k = j) → P i j k = 0) (x : Fin m → ℚ) :
    Matrix.trace (jac P x) = 0 := by
  unfold Matrix.trace
  exact Finset.sum_eq_zero fun i _ => by simp [Matrix.diag, jac_diag_zero P hsnv x i]

/-- Invariant face: if every pair inside `F` lands inside `F`, and `x` is supported on `F`, then `V x`
vanishes outside `F` and on `F` equals the restricted operator. Hence a fixed point of the restriction,
padded by zeros, is a fixed point of `V`. -/
theorem face_fixed_point {m : ℕ} (P : Fin m → Fin m → Fin m → ℚ) (F : Finset (Fin m))
    (hinv : ∀ i ∈ F, ∀ j ∈ F, ∀ k, k ∉ F → P i j k = 0)
    (x : Fin m → ℚ) (hsupp : ∀ i, i ∉ F → x i = 0)
    (hfix : ∀ k ∈ F, ∑ i ∈ F, ∑ j ∈ F, P i j k * x i * x j = x k) :
    V P x = x := by
  funext k
  have hzero : ∀ i, i ∉ F → ∀ j, P i j k * x i * x j = 0 := fun i hi j => by
    rw [hsupp i hi]; ring
  have hzero' : ∀ i, ∀ j, j ∉ F → P i j k * x i * x j = 0 := fun i j hj => by
    rw [hsupp j hj]; ring
  -- reduce the double sum to the sums over F
  have hred : V P x k = ∑ i ∈ F, ∑ j ∈ F, P i j k * x i * x j := by
    simp only [V]
    rw [← Finset.sum_subset (Finset.subset_univ F)]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_subset (Finset.subset_univ F)]
      intro j _ hj; exact hzero' i j hj
    · intro i _ hi; exact Finset.sum_eq_zero fun j _ => hzero i hi j
  by_cases hk : k ∈ F
  · rw [hred]; exact hfix k hk
  · rw [hred, hsupp k hk]
    apply Finset.sum_eq_zero; intro i hi; apply Finset.sum_eq_zero; intro j hj
    rw [hinv i hi j hj k hk]; ring

/-- Four types: if the face `{0,1,2}` is invariant (pairs inside it never land on type 3) and the operator
is strictly non-Volterra, then the fourth coordinate of `V` vanishes identically, so every fixed point lies
in the face. -/
theorem four_types_face (P : Fin 4 → Fin 4 → Fin 4 → ℚ)
    (hsnv : ∀ i j k, (k = i ∨ k = j) → P i j k = 0)
    (hinv : ∀ i j, i ≠ 3 → j ≠ 3 → P i j 3 = 0) (x : Fin 4 → ℚ) :
    V P x 3 = 0 := by
  simp only [V]
  apply Finset.sum_eq_zero; intro i _; apply Finset.sum_eq_zero; intro j _
  by_cases hi : i = 3
  · subst hi; rw [hsnv 3 j 3 (Or.inl rfl)]; ring
  · by_cases hj : j = 3
    · subst hj; rw [hsnv i 3 3 (Or.inr rfl)]; ring
    · rw [hinv i j hi hj]; ring

/-! ### The equiprobable operator on four types: the barycentre is an attracting fixed point -/

/-- The equiprobable strictly non-Volterra operator on four types: `P i i k = 1/3` for `k ≠ i`,
`P i j k = 1/2` for `i ≠ j`, `k ∉ {i, j}`, zero otherwise. -/
def E4 : Fin 4 → Fin 4 → Fin 4 → ℚ := fun i j k =>
  if k = i ∨ k = j then 0 else if i = j then 1/3 else 1/2

theorem E4_rows : ∀ i j, ∑ k, E4 i j k = 1 := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [E4, Fin.sum_univ_four] <;> norm_num

theorem E4_snv : ∀ i j k, (k = i ∨ k = j) → E4 i j k = 0 := by
  intro i j k h; simp [E4, h]

def bary4 : Fin 4 → ℚ := fun _ => 1/4

theorem E4_fixes_bary : V E4 bary4 = bary4 := by
  funext k; fin_cases k <;> simp [V, E4, bary4, Fin.sum_univ_four] <;> norm_num

/-- `DV(b) = (2/3)(J - I)`: off-diagonal entries `2/3`, diagonal `0`. -/
theorem E4_jac_bary : jac E4 bary4 = fun k j => if j = k then 0 else 2/3 := by
  ext k j; fin_cases k <;> fin_cases j <;> simp [jac, E4, bary4, Fin.sum_univ_four] <;> norm_num

/-- On the tangent space of the simplex (sum-zero vectors) the Jacobian at the barycentre acts as
multiplication by `-2/3`, so the barycentre is an attracting fixed point. -/
theorem E4_tangent_eigen (v : Fin 4 → ℚ) (hv : ∑ i, v i = 0) :
    (jac E4 bary4).mulVec v = fun k => (-2/3) * v k := by
  rw [E4_jac_bary]; funext k
  have hs : v 0 + v 1 + v 2 + v 3 = 0 := by simpa [Fin.sum_univ_four] using hv
  fin_cases k <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> linarith

/-! ### The five-type operator `W` -/

/-- `W i j` is the row (over the target `k`) of the coefficient tensor of the five-type operator:
face `{0,1,2}` carries the symmetric three-type operator (`P i i k = 1/2` for the other two face types,
`P i j (third) = 1`); across, `P i 3 4 = P i 4 3 = 1` for `i ≤ 2`, `P 3 3 4 = P 4 4 3 = 1`,
`P 3 4 k = 1/3` for `k ≤ 2`. -/
def W : Fin 5 → Fin 5 → Fin 5 → ℚ :=
  ![![![0, 1/2, 1/2, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 0, 0, 1], ![0, 0, 0, 1, 0]],
    ![![0, 0, 1, 0, 0], ![1/2, 0, 1/2, 0, 0], ![1, 0, 0, 0, 0], ![0, 0, 0, 0, 1], ![0, 0, 0, 1, 0]],
    ![![0, 1, 0, 0, 0], ![1, 0, 0, 0, 0], ![1/2, 1/2, 0, 0, 0], ![0, 0, 0, 0, 1], ![0, 0, 0, 1, 0]],
    ![![0, 0, 0, 0, 1], ![0, 0, 0, 0, 1], ![0, 0, 0, 0, 1], ![0, 0, 0, 0, 1], ![1/3, 1/3, 1/3, 0, 0]],
    ![![0, 0, 0, 1, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 1, 0], ![1/3, 1/3, 1/3, 0, 0], ![0, 0, 0, 1, 0]]]

theorem W_symm : ∀ i j k, W i j k = W j i k := by
  intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [W]

theorem W_nonneg : ∀ i j k, 0 ≤ W i j k := by
  intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [W]

theorem W_rows : ∀ i j, ∑ k, W i j k = 1 := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [W, Fin.sum_univ_five] <;> norm_num

theorem W_snv : ∀ i j k, (k = i ∨ k = j) → W i j k = 0 := by decide

def p : Fin 5 → ℚ := ![1/3, 1/3, 1/3, 0, 0]
def q : Fin 5 → ℚ := ![1/9, 1/9, 1/9, 1/3, 1/3]

theorem p_simplex : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 := by
  refine ⟨fun i => by fin_cases i <;> norm_num [p], ?_⟩; simp [p, Fin.sum_univ_five]; norm_num
theorem q_simplex : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1 := by
  refine ⟨fun i => by fin_cases i <;> norm_num [q], ?_⟩; simp [q, Fin.sum_univ_five]; norm_num

theorem W_fixes_p : V W p = p := by
  funext k; fin_cases k <;> simp [V, W, p, Fin.sum_univ_five] <;> norm_num

theorem W_fixes_q : V W q = q := by
  funext k; fin_cases k <;> simp [V, W, q, Fin.sum_univ_five] <;> norm_num

theorem p_ne_q : p ≠ q := by
  intro h; have := congrFun h 3; simp [p, q] at this

/-! ### The Jacobians at the two fixed points -/

/-- `DW(p)`, computed: block diagonal with the all-ones-off-diagonal block on the face and `[[0,2],[2,0]]`. -/
theorem jac_p : jac W p = !![0, 1, 1, 0, 0; 1, 0, 1, 0, 0; 1, 1, 0, 0, 0; 0, 0, 0, 0, 2; 0, 0, 0, 2, 0] := by
  ext k j; fin_cases k <;> fin_cases j <;> simp [jac, W, p, Fin.sum_univ_five] <;> norm_num

theorem jac_q : jac W q = !![0, 1/3, 1/3, 2/9, 2/9; 1/3, 0, 1/3, 2/9, 2/9; 1/3, 1/3, 0, 2/9, 2/9;
    2/3, 2/3, 2/3, 0, 4/3; 2/3, 2/3, 2/3, 4/3, 0] := by
  ext k j; fin_cases k <;> fin_cases j <;> simp [jac, W, q, Fin.sum_univ_five] <;> norm_num

/-- The five eigenvectors at `p` (columns), with eigenvalues `2, 2, -1, -1, -2`. -/
def Ep : Matrix (Fin 5) (Fin 5) ℚ :=
  !![1, 0, -1, -1, 0; 1, 0, 1, 0, 0; 1, 0, 0, 1, 0; 0, 1, 0, 0, -1; 0, 1, 0, 0, 1]
def lamp : Fin 5 → ℚ := ![2, 2, -1, -1, -2]

theorem eig_p : ∀ c, (jac W p).mulVec (fun r => Ep r c) = fun r => lamp c * Ep r c := by
  intro c; rw [jac_p]; funext r
  fin_cases c <;> fin_cases r <;> simp [Matrix.mulVec, dotProduct, Ep, lamp, Fin.sum_univ_five] <;> norm_num

/-- The inverse of `Ep`, so that `Ep` is invertible and its columns are linearly independent. -/
def EpInv : Matrix (Fin 5) (Fin 5) ℚ :=
  !![1/3, 1/3, 1/3, 0, 0; 0, 0, 0, 1/2, 1/2; -1/3, 2/3, -1/3, 0, 0; -1/3, -1/3, 2/3, 0, 0; 0, 0, 0, -1/2, 1/2]

theorem Ep_mul_inv : Ep * EpInv = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_five, Ep, EpInv] <;> norm_num

theorem eigvecs_p_det : Ep.det ≠ 0 := by
  have h : Ep.det * EpInv.det = 1 := by rw [← Matrix.det_mul, Ep_mul_inv, Matrix.det_one]
  intro h0; rw [h0, zero_mul] at h; exact zero_ne_one h

/-- The five eigenvectors at `q` (columns), with eigenvalues `2, -4/3, -1/3, -1/3, 0`. -/
def Eq' : Matrix (Fin 5) (Fin 5) ℚ :=
  !![1/3, 0, -1, -1, -2/3; 1/3, 0, 1, 0, -2/3; 1/3, 0, 0, 1, -2/3; 1, -1, 0, 0, 1; 1, 1, 0, 0, 1]
def lamq : Fin 5 → ℚ := ![2, -4/3, -1/3, -1/3, 0]

theorem eig_q : ∀ c, (jac W q).mulVec (fun r => Eq' r c) = fun r => lamq c * Eq' r c := by
  intro c; rw [jac_q]; funext r
  fin_cases c <;> fin_cases r <;> simp [Matrix.mulVec, dotProduct, Eq', lamq, Fin.sum_univ_five] <;> norm_num

/-- The inverse of `Eq'`. -/
def EqInv : Matrix (Fin 5) (Fin 5) ℚ :=
  !![1/3, 1/3, 1/3, 1/3, 1/3; 0, 0, 0, -1/2, 1/2; -1/3, 2/3, -1/3, 0, 0; -1/3, -1/3, 2/3, 0, 0;
     -1/3, -1/3, -1/3, 1/6, 1/6]

theorem Eq_mul_inv : Eq' * EqInv = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_five, Eq', EqInv] <;> norm_num

theorem eigvecs_q_det : Eq'.det ≠ 0 := by
  have h : Eq'.det * EqInv.det = 1 := by rw [← Matrix.det_mul, Eq_mul_inv, Matrix.det_one]
  intro h0; rw [h0, zero_mul] at h; exact zero_ne_one h

/-- The tangent space of the simplex is the sum-zero hyperplane; the eigenvectors with index `1,2,3,4` at `p`
and `1,2,3,4` at `q` lie in it (columns `2,3,4` at `p` sum to zero; column `1` at `p` does not, but the
tangential eigenvector for the eigenvalue `2` is `Ep col 0 - (3/2) Ep col 1`, which sums to zero),
so the tangent spectrum is `{2, -1, -1, -2}` at `p` and `{-4/3, -1/3, -1/3, 0}` at `q`. -/
theorem tangent_vectors :
    (∑ r, (Ep r 0 - 3/2 * Ep r 1) = 0) ∧ (∀ c : Fin 5, c ≠ 0 → c ≠ 1 → ∑ r, Ep r c = 0) ∧
    (∀ c : Fin 5, c ≠ 0 → ∑ r, Eq' r c = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Ep, Fin.sum_univ_five]; norm_num
  · intro c h0 h1; fin_cases c <;> simp_all [Ep, Fin.sum_univ_five]
  · intro c h0; fin_cases c <;> simp_all [Eq', Fin.sum_univ_five] <;> norm_num

/-- The tangential eigenvector for the eigenvalue `2` at `p`. -/
theorem eig_p_tangent_two :
    (jac W p).mulVec (fun r => Ep r 0 - 3/2 * Ep r 1) = fun r => 2 * (Ep r 0 - 3/2 * Ep r 1) := by
  rw [jac_p]; funext r; fin_cases r <;> simp [Matrix.mulVec, dotProduct, Ep, Fin.sum_univ_five] <;> norm_num

/-! ### Six types: a segment of fixed points -/

/-- Two invariant triples `F = {0,1,2}` and `G = {3,4,5}`, the symmetric operator on each, and a cross pair
`(i, j)` (`i ∈ F`, `j ∈ G`) sending its mass equally to the four types of `(F \ {i}) ∪ (G \ {j})`. -/
def S6 : Fin 6 → Fin 6 → Fin 6 → ℚ := fun i j k =>
  if k = i ∨ k = j then 0
  else if (i.val < 3) = (j.val < 3) then
    -- same triple: same type -> 1/2 to each of the other two, different types -> 1 to the third
    (if (k.val < 3) = (i.val < 3) then (if i = j then 1/2 else 1) else 0)
  else 1/4

theorem S6_rows : ∀ i j, ∑ k, S6 i j k = 1 := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [S6, Fin.sum_univ_succ] <;> norm_num

theorem S6_snv : ∀ i j k, (k = i ∨ k = j) → S6 i j k = 0 := by
  intro i j k h; simp [S6, h]

theorem S6_symm : ∀ i j k, S6 i j k = S6 j i k := by
  intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [S6]

theorem S6_nonneg : ∀ i j k, 0 ≤ S6 i j k := by
  intro i j k; fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [S6]

/-- The segment `(a, a, a, 1/3 - a, 1/3 - a, 1/3 - a)`. -/
def seg (a : ℚ) : Fin 6 → ℚ := ![a, a, a, 1/3 - a, 1/3 - a, 1/3 - a]

/-- Every point of the segment is fixed by `S6` (for `0 ≤ a ≤ 1/3` these are points of the simplex). -/
theorem segment_fixed (a : ℚ) : V S6 (seg a) = seg a := by
  funext k; fin_cases k <;> simp [V, S6, seg, Fin.sum_univ_succ] <;> ring

/-! ### The swap extension: the two extra coordinates of a fixed point are equal and lie in `{0, 1/3}` -/

/-- In the swap extension the coordinates `s = x₄`, `t = x₅` of a fixed point satisfy
`s = t (2 - 2 s - t)` and `t = s (2 - 2 t - s)`; with `s + t ≤ 1` this forces `s = t ∈ {0, 1/3}`. -/
theorem swap_coordinates (s t : ℝ) (hst : s + t ≤ 1)
    (h1 : s = t * (2 - 2 * s - t)) (h2 : t = s * (2 - 2 * t - s)) :
    s = t ∧ (s = 0 ∨ s = 1 / 3) := by
  have key : (s - t) * (3 - s - t) = 0 := by nlinarith
  have hst' : s = t := by
    rcases mul_eq_zero.1 key with h | h
    · linarith
    · linarith
  refine ⟨hst', ?_⟩
  subst hst'
  have : s * (1 - 3 * s) = 0 := by nlinarith
  rcases mul_eq_zero.1 this with h | h
  · exact Or.inl h
  · right; linarith

end QSO

#print axioms QSO.swap_coordinates
#print axioms QSO.euler
#print axioms QSO.trace_zero
#print axioms QSO.face_fixed_point
#print axioms QSO.four_types_face
#print axioms QSO.W_symm
#print axioms QSO.W_nonneg
#print axioms QSO.W_rows
#print axioms QSO.W_snv
#print axioms QSO.W_fixes_p
#print axioms QSO.W_fixes_q
#print axioms QSO.p_ne_q
#print axioms QSO.jac_p
#print axioms QSO.jac_q
#print axioms QSO.eig_p
#print axioms QSO.eigvecs_p_det
#print axioms QSO.eig_q
#print axioms QSO.eigvecs_q_det
#print axioms QSO.tangent_vectors
#print axioms QSO.eig_p_tangent_two
#print axioms QSO.E4_rows
#print axioms QSO.E4_snv
#print axioms QSO.E4_fixes_bary
#print axioms QSO.E4_jac_bary
#print axioms QSO.E4_tangent_eigen
#print axioms QSO.segment_fixed
