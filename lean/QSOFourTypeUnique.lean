import Mathlib

/-!
Uniqueness of the fixed point of a strictly non-Volterra quadratic stochastic operator
on four types.

`V P x k = ∑ i j, P i j k * x i * x j` with `P` symmetric, nonnegative, stochastic in `k`
and `P i j k = 0` whenever `k ∈ {i, j}`.  The theorem `unique_fixed_point` says that two
fixed points of `V P` in the simplex coincide.

The argument: every coordinate of a fixed point is at most `2/5`; the difference `z` of two
fixed points has exactly two positive and two negative coordinates; the polarisation
identity `V x - V y = 2 A(m) z` with `m = (x+y)/2` and the transfer inequality
`∑_{r ∈ G} (A(m)(e_i - e_j))_r ≤ max (m i) (m j)` for `i ∈ G`, `j ∈ H` give
`h ≤ 2 · (2/5) · h` for `h = ∑_{r ∈ G} z r > 0`.
-/

open Finset

namespace QSO4

noncomputable section

/-- The quadratic stochastic operator with coefficient table `P`. -/
def V (P : Fin 4 → Fin 4 → Fin 4 → ℝ) (x : Fin 4 → ℝ) (k : Fin 4) : ℝ :=
  ∑ i, ∑ j, P i j k * x i * x j

/-- Strictly non-Volterra coefficient tables. -/
structure IsSNV (P : Fin 4 → Fin 4 → Fin 4 → ℝ) : Prop where
  symm : ∀ i j k, P i j k = P j i k
  nonneg : ∀ i j k, 0 ≤ P i j k
  stoch : ∀ i j, ∑ k, P i j k = 1
  snv : ∀ i j k, k = i ∨ k = j → P i j k = 0

/-- The simplex of probability vectors. -/
def InSimplex (x : Fin 4 → ℝ) : Prop := (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1

variable {P : Fin 4 → Fin 4 → Fin 4 → ℝ}

lemma P_le_one (h : IsSNV P) (i j k : Fin 4) : P i j k ≤ 1 := by
  have := h.stoch i j
  have hle : P i j k ≤ ∑ k', P i j k' :=
    Finset.single_le_sum (fun k' _ => h.nonneg i j k') (Finset.mem_univ k)
  linarith

/-- A sum over `Fin 4` is the sum over any four distinct elements. -/
lemma sum_four {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) (f : Fin 4 → ℝ) :
    ∑ a, f a = f i + f j + f k + f l := by
  have hj' : j ∉ ({k, l} : Finset (Fin 4)) := by simp [hjk, hjl]
  have hi' : i ∉ ({j, k, l} : Finset (Fin 4)) := by simp [hij, hik, hil]
  have huniv : ({i, j, k, l} : Finset (Fin 4)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem hi', Finset.card_insert_of_notMem hj', Finset.card_pair hkl]
    simp
  rw [← huniv, Finset.sum_insert hi', Finset.sum_insert hj', Finset.sum_pair hkl]
  ring

/-- Every coordinate of a fixed point is at most `2/5`. -/
lemma coord_le (h : IsSNV P) {x : Fin 4 → ℝ} (hx : InSimplex x)
    (hfx : ∀ r, V P x r = x r) (k : Fin 4) : x k ≤ 2 / 5 := by
  obtain ⟨y, hy⟩ : ∃ y : Fin 4 → ℝ, ∀ i, y i = if i = k then 0 else x i :=
    ⟨fun i => if i = k then 0 else x i, fun i => rfl⟩
  have hy0 : ∀ i, 0 ≤ y i := by
    intro i; rw [hy]; split_ifs
    · exact le_refl 0
    · exact hx.1 i
  have hsum : ∑ i, y i = 1 - x k := by
    have : ∀ i, y i = x i - (if i = k then x k else 0) := by
      intro i; rw [hy]; split_ifs with hik
      · rw [hik]; ring
      · ring
    simp_rw [this, Finset.sum_sub_distrib, Finset.sum_ite_eq' Finset.univ k]
    simp [hx.2]
  have hterm : ∀ i j, P i j k * x i * x j ≤ y i * y j := by
    intro i j
    by_cases hi : i = k
    · rw [h.snv i j k (Or.inl hi.symm), zero_mul, zero_mul]
      exact mul_nonneg (hy0 i) (hy0 j)
    · by_cases hj : j = k
      · rw [h.snv i j k (Or.inr hj.symm), zero_mul, zero_mul]
        exact mul_nonneg (hy0 i) (hy0 j)
      · have e1 : y i = x i := by rw [hy, if_neg hi]
        have e2 : y j = x j := by rw [hy, if_neg hj]
        rw [e1, e2]
        have h1 := P_le_one h i j k
        have h0 := h.nonneg i j k
        have hxx := mul_nonneg (hx.1 i) (hx.1 j)
        have := mul_le_mul_of_nonneg_right h1 hxx
        nlinarith
  have hV : V P x k ≤ (1 - x k) ^ 2 := by
    unfold V
    calc ∑ i, ∑ j, P i j k * x i * x j ≤ ∑ i, ∑ j, y i * y j :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      _ = (∑ i, y i) * (∑ j, y j) := by rw [Finset.sum_mul_sum]
      _ = (1 - x k) ^ 2 := by rw [hsum]; ring
  rw [hfx k] at hV
  have h0 := hx.1 k
  have h1 : x k ≤ 1 := by
    have := Finset.single_le_sum (fun i _ => hx.1 i) (Finset.mem_univ k)
    linarith [hx.2]
  by_contra hcon
  have hcon' : 2 / 5 < x k := lt_of_not_ge hcon
  nlinarith [mul_nonneg (le_of_lt (sub_pos.mpr hcon')) (sub_nonneg.mpr h1)]

/-- `V_i` is monotone in the coordinates other than `i`. -/
lemma mono (h : IsSNV P) {x y : Fin 4 → ℝ} (hx0 : ∀ j, 0 ≤ x j)
    (i : Fin 4) (hle : ∀ j, j ≠ i → x j ≤ y j) : V P x i ≤ V P y i := by
  unfold V
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  by_cases ha : a = i
  · simp [h.snv a b i (Or.inl ha.symm)]
  · by_cases hb : b = i
    · simp [h.snv a b i (Or.inr hb.symm)]
    · have h0 := h.nonneg a b i
      have hxa := hle a ha
      have hxb := hle b hb
      have hya : 0 ≤ y a := le_trans (hx0 a) hxa
      have hxy : x a * x b ≤ y a * y b := mul_le_mul hxa hxb (hx0 b) hya
      have := mul_le_mul_of_nonneg_left hxy h0
      nlinarith

/-- Polarisation: `V x - V y = 2 A(m) (x - y)` with `m = (x + y)/2`. -/
lemma polar (h : IsSNV P) (x y : Fin 4 → ℝ) (r : Fin 4) :
    V P x r - V P y r
      = 2 * ∑ b, (∑ a, P a b r * ((x a + y a) / 2)) * (x b - y b) := by
  unfold V
  have key : ∀ a b, P a b r * x a * x b - P a b r * y a * y b
      = P a b r * ((x a + y a) / 2) * (x b - y b)
        + P a b r * (x a - y a) * ((x b + y b) / 2) := by
    intro a b; ring
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, key, Finset.sum_add_distrib]
  have h2 : ∑ a, ∑ b, P a b r * (x a - y a) * ((x b + y b) / 2)
      = ∑ a, ∑ b, P a b r * ((x a + y a) / 2) * (x b - y b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [h.symm b a r]; ring
  rw [h2]
  have h3 : ∑ b, (∑ a, P a b r * ((x a + y a) / 2)) * (x b - y b)
      = ∑ a, ∑ b, P a b r * ((x a + y a) / 2) * (x b - y b) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
  rw [h3]; ring

/-- The transfer bound for one pair `(i, j)` with `i ∈ G = {i, k}`, `j ∈ H = {j, l}`:
the coefficients `q a b = P a b i + P a b k` carry the mass sent into `G`. -/
lemma bracket_le {q : Fin 4 → Fin 4 → ℝ} {m : Fin 4 → ℝ} {i j k l : Fin 4}
    (hq0 : ∀ a b, 0 ≤ q a b) (hq1 : ∀ a b, q a b ≤ 1) (hqs : ∀ a b, q a b = q b a)
    (hm0 : ∀ a, 0 ≤ m a) (hm1 : ∀ a, m a ≤ 2 / 5)
    (hki : q k i = 0) (hlj : q l j = 1) :
    m i * (q i i - q i j) + m j * (q j i - q j j) + m k * (q k i - q k j)
      + m l * (q l i - q l j) ≤ 2 / 5 := by
  rw [hki, hlj, hqs j i]
  nlinarith [mul_nonneg (hm0 i) (sub_nonneg.mpr (hq1 i i)),
    mul_nonneg (hm0 j) (hq0 j j), mul_nonneg (hm0 k) (hq0 k j),
    mul_nonneg (hm0 l) (sub_nonneg.mpr (hq1 l i)),
    mul_nonneg (sub_nonneg.mpr (hm1 i)) (sub_nonneg.mpr (hq1 i j)),
    mul_nonneg (sub_nonneg.mpr (hm1 j)) (hq0 i j)]

/-- The core estimate: two fixed points whose difference is positive on `{i, k}` and
negative on `{j, l}` cannot exist. -/
lemma core (h : IsSNV P) {x y : Fin 4 → ℝ} (hx : InSimplex x) (hy : InSimplex y)
    (hfx : ∀ r, V P x r = x r) (hfy : ∀ r, V P y r = y r)
    {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hi : 0 < x i - y i) (hk : 0 < x k - y k) (hj : x j - y j < 0) (hl : x l - y l < 0) :
    False := by
  -- the midpoint `m`, the mass `q` sent into `G = {i, k}`, and the column sums `ap`
  obtain ⟨m, hm⟩ : ∃ m : Fin 4 → ℝ, ∀ a, m a = (x a + y a) / 2 :=
    ⟨fun a => (x a + y a) / 2, fun a => rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : Fin 4 → Fin 4 → ℝ, ∀ a b, q a b = P a b i + P a b k :=
    ⟨fun a b => P a b i + P a b k, fun a b => rfl⟩
  obtain ⟨ap, hap⟩ : ∃ ap : Fin 4 → ℝ, ∀ b, ap b = ∑ a, q a b * m a :=
    ⟨fun b => ∑ a, q a b * m a, fun b => rfl⟩
  -- the coordinate caps
  have hxc := coord_le h hx hfx
  have hyc := coord_le h hy hfy
  have hm0 : ∀ a, 0 ≤ m a := fun a => by rw [hm]; linarith [hx.1 a, hy.1 a]
  have hm1 : ∀ a, m a ≤ 2 / 5 := fun a => by rw [hm]; linarith [hxc a, hyc a]
  -- properties of q
  have hq0 : ∀ a b, 0 ≤ q a b := fun a b => by
    rw [hq]; linarith [h.nonneg a b i, h.nonneg a b k]
  have hqs : ∀ a b, q a b = q b a := fun a b => by rw [hq, hq, h.symm a b i, h.symm a b k]
  have hstoch : ∀ a b, P a b i + P a b j + P a b k + P a b l = 1 := fun a b => by
    have := h.stoch a b
    rwa [sum_four hij hik hil hjk hjl hkl] at this
  have hq1 : ∀ a b, q a b ≤ 1 := fun a b => by
    rw [hq]; linarith [hstoch a b, h.nonneg a b j, h.nonneg a b l]
  have hki : q k i = 0 := by
    rw [hq, h.snv k i i (Or.inr rfl), h.snv k i k (Or.inl rfl)]; ring
  have hik' : q i k = 0 := by rw [hqs]; exact hki
  have hlj : q l j = 1 := by
    have := hstoch l j
    rw [h.snv l j j (Or.inr rfl), h.snv l j l (Or.inl rfl)] at this
    rw [hq]; linarith
  have hjl' : q j l = 1 := by rw [hqs]; exact hlj
  -- polarisation at the two fixed points
  have hpol : ∀ r, x r - y r = 2 * ∑ b, (∑ a, P a b r * m a) * (x b - y b) := by
    intro r
    have := polar h x y r
    rw [hfx r, hfy r] at this
    simp only [← hm] at this
    exact this
  have hsumz : (x i - y i) + (x j - y j) + (x k - y k) + (x l - y l) = 0 := by
    have hx2 := hx.2; have hy2 := hy.2
    rw [sum_four hij hik hil hjk hjl hkl] at hx2 hy2
    linarith
  have hh : (x i - y i) + (x k - y k) = 2 * ∑ b, ap b * (x b - y b) := by
    rw [hpol i, hpol k, ← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hap, ← add_mul, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hq]; ring
  -- expand the sums over the four indices
  have hapb : ∀ b, ap b = q i b * m i + q j b * m j + q k b * m k + q l b * m l := fun b => by
    rw [hap, sum_four hij hik hil hjk hjl hkl]
  have hS : ∑ b, ap b * (x b - y b)
      = ap i * (x i - y i) + ap j * (x j - y j) + ap k * (x k - y k) + ap l * (x l - y l) :=
    sum_four hij hik hil hjk hjl hkl _
  rw [hS] at hh
  -- the four transfer bounds
  have Bij : ap i - ap j ≤ 2 / 5 := by
    rw [hapb i, hapb j]
    have := bracket_le (i := i) (j := j) (k := k) (l := l) hq0 hq1 hqs hm0 hm1 hki hlj
    linarith
  have Bil : ap i - ap l ≤ 2 / 5 := by
    rw [hapb i, hapb l]
    have := bracket_le (i := i) (j := l) (k := k) (l := j) hq0 hq1 hqs hm0 hm1 hki hjl'
    linarith
  have Bkj : ap k - ap j ≤ 2 / 5 := by
    rw [hapb k, hapb j]
    have := bracket_le (i := k) (j := j) (k := i) (l := l) hq0 hq1 hqs hm0 hm1 hik' hlj
    linarith
  have Bkl : ap k - ap l ≤ 2 / 5 := by
    rw [hapb k, hapb l]
    have := bracket_le (i := k) (j := l) (k := i) (l := j) hq0 hq1 hqs hm0 hm1 hik' hjl'
    linarith
  -- combine: name the four differences
  obtain ⟨zi, hzi'⟩ : ∃ t, t = x i - y i := ⟨_, rfl⟩
  obtain ⟨zj, hzj'⟩ : ∃ t, t = x j - y j := ⟨_, rfl⟩
  obtain ⟨zk, hzk'⟩ : ∃ t, t = x k - y k := ⟨_, rfl⟩
  obtain ⟨zl, hzl'⟩ : ∃ t, t = x l - y l := ⟨_, rfl⟩
  rw [← hzi', ← hzj', ← hzk', ← hzl'] at hh hsumz
  rw [← hzi'] at hi
  rw [← hzk'] at hk
  rw [← hzj'] at hj
  rw [← hzl'] at hl
  have hpos : 0 < zi + zk := by linarith
  have hneg : -zj - zl = zi + zk := by linarith
  have ident : (zi + zk) * (ap i * zi + ap j * zj + ap k * zk + ap l * zl)
      = zi * (-zj) * (ap i - ap j) + zi * (-zl) * (ap i - ap l)
        + zk * (-zj) * (ap k - ap j) + zk * (-zl) * (ap k - ap l) := by
    linear_combination (ap i * zi + ap k * zk) * hsumz
  have e1 := mul_le_mul_of_nonneg_left Bij (mul_nonneg hi.le (neg_nonneg.mpr hj.le))
  have e2 := mul_le_mul_of_nonneg_left Bil (mul_nonneg hi.le (neg_nonneg.mpr hl.le))
  have e3 := mul_le_mul_of_nonneg_left Bkj (mul_nonneg hk.le (neg_nonneg.mpr hj.le))
  have e4 := mul_le_mul_of_nonneg_left Bkl (mul_nonneg hk.le (neg_nonneg.mpr hl.le))
  have e5 : zi * (-zj) + zi * (-zl) + zk * (-zj) + zk * (-zl) = (zi + zk) * (zi + zk) := by
    calc zi * (-zj) + zi * (-zl) + zk * (-zj) + zk * (-zl) = (zi + zk) * (-zj - zl) := by ring
      _ = (zi + zk) * (zi + zk) := by rw [hneg]
  have hbound : (zi + zk) * (ap i * zi + ap j * zj + ap k * zk + ap l * zl)
      ≤ 2 / 5 * ((zi + zk) * (zi + zk)) := by
    rw [ident, ← e5]; linarith
  have hsq : (zi + zk) * (zi + zk)
      = 2 * ((zi + zk) * (ap i * zi + ap j * zj + ap k * zk + ap l * zl)) := by
    calc (zi + zk) * (zi + zk)
        = (zi + zk) * (2 * (ap i * zi + ap j * zj + ap k * zk + ap l * zl)) := by rw [← hh]
      _ = 2 * ((zi + zk) * (ap i * zi + ap j * zj + ap k * zk + ap l * zl)) := by ring
  have hpp : 0 < (zi + zk) * (zi + zk) := mul_pos hpos hpos
  linarith

/-- Every strictly non-Volterra quadratic stochastic operator on four types has at most one
fixed point in the simplex. -/
theorem unique_fixed_point (h : IsSNV P) {x y : Fin 4 → ℝ}
    (hx : InSimplex x) (hy : InSimplex y)
    (hfx : ∀ r, V P x r = x r) (hfy : ∀ r, V P y r = y r) : x = y := by
  by_contra hne
  set G : Finset (Fin 4) := Finset.univ.filter (fun a => 0 < x a - y a) with hG
  set H : Finset (Fin 4) := Finset.univ.filter (fun a => x a - y a < 0) with hH
  have hsum : ∑ a, (x a - y a) = 0 := by rw [Finset.sum_sub_distrib, hx.2, hy.2]; ring
  -- G and H are nonempty
  have hGne : G.Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hcon
    have hle : ∀ a ∈ Finset.univ, x a - y a ≤ 0 := fun a ha => not_lt.mp (hcon ha)
    have := (Finset.sum_eq_zero_iff_of_nonpos hle).mp hsum
    exact hne (funext fun a => by linarith [this a (Finset.mem_univ a)])
  have hHne : H.Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hcon
    have hle : ∀ a ∈ Finset.univ, 0 ≤ x a - y a := fun a ha => not_lt.mp (hcon ha)
    have := (Finset.sum_eq_zero_iff_of_nonneg hle).mp hsum
    exact hne (funext fun a => by linarith [this a (Finset.mem_univ a)])
  -- neither is a singleton
  have hG1 : G.card ≠ 1 := by
    intro hc
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    have haG : a ∈ G := by rw [ha]; exact Finset.mem_singleton_self a
    have hapos : 0 < x a - y a := (Finset.mem_filter.mp haG).2
    have hle : ∀ b, b ≠ a → x b ≤ y b := by
      intro b hb
      have : b ∉ G := by rw [ha]; simpa using hb
      have := fun hp => this (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hp⟩)
      linarith [not_lt.mp this]
    have := mono h hx.1 a hle
    rw [hfx a, hfy a] at this
    linarith
  have hH1 : H.card ≠ 1 := by
    intro hc
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    have haH : a ∈ H := by rw [ha]; exact Finset.mem_singleton_self a
    have haneg : x a - y a < 0 := (Finset.mem_filter.mp haH).2
    have hle : ∀ b, b ≠ a → y b ≤ x b := by
      intro b hb
      have : b ∉ H := by rw [ha]; simpa using hb
      have := fun hp => this (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hp⟩)
      linarith [not_lt.mp this]
    have := mono h hy.1 a hle
    rw [hfx a, hfy a] at this
    linarith
  -- so both have exactly two elements
  have hdisj : Disjoint G H := by
    rw [Finset.disjoint_filter]
    intro a _ h1 h2; linarith
  have hcard : G.card + H.card ≤ 4 := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact (Finset.card_le_univ _).trans (by simp)
  have hG2 : G.card = 2 := by
    have := hGne.card_pos; have := hHne.card_pos; omega
  have hH2 : H.card = 2 := by
    have := hGne.card_pos; have := hHne.card_pos; omega
  obtain ⟨i, k, hik, hGik⟩ := Finset.card_eq_two.mp hG2
  obtain ⟨j, l, hjl, hHjl⟩ := Finset.card_eq_two.mp hH2
  have hi : 0 < x i - y i := (Finset.mem_filter.mp (by rw [hGik]; simp : i ∈ G)).2
  have hk : 0 < x k - y k := (Finset.mem_filter.mp (by rw [hGik]; simp : k ∈ G)).2
  have hj : x j - y j < 0 := (Finset.mem_filter.mp (by rw [hHjl]; simp : j ∈ H)).2
  have hl : x l - y l < 0 := (Finset.mem_filter.mp (by rw [hHjl]; simp : l ∈ H)).2
  have hij : i ≠ j := fun e => by subst e; linarith
  have hil : i ≠ l := fun e => by subst e; linarith
  have hjk : j ≠ k := fun e => by subst e; linarith
  have hkl : k ≠ l := fun e => by subst e; linarith
  exact core h hx hy hfx hfy hij hik hil hjk hjl hkl hi hk hj hl

end

end QSO4

#print axioms QSO4.unique_fixed_point
