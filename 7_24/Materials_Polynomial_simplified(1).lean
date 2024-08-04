import Mathlib

open Finset Polynomial BigOperators
set_option maxHeartbeats 0

theorem support_tetranomial' (k m n l : ℕ) (x y z w : ℤ) : support (C x * X ^ k + C y * X ^ m + C z * X ^ n + C w * X ^ l) ⊆ {k, m, n, l} := by
  have h₁: support (C x * X ^ k + C y * X ^ m) ⊆ support (C x * X ^ k) ∪ support (C y * X ^ m) := support_add
  have h₂: support (C x * X ^ k + C y * X ^ m + C z * X ^ n) ⊆ support (C x * X ^ k + C y * X ^ m) ∪ support (C z * X ^ n) := support_add
  have h₃: support (C x * X ^ k + C y * X ^ m + C z * X ^ n + C w * X ^ l) ⊆ support (C x * X ^ k + C y * X ^ m + C z * X ^ n) ∪ support (C w * X ^ l) := support_add
  exact Subset.trans (Subset.trans h₃ (union_subset_union_left (Subset.trans h₂ (union_subset_union_left h₁)))) (union_subset (union_subset (union_subset ((support_C_mul_X_pow' k x).trans (singleton_subset_iff.mpr (mem_insert_self k {m, n, l}))) ((support_C_mul_X_pow' m y).trans (singleton_subset_iff.mpr (mem_insert_of_mem (mem_insert_self m {n, l}))))) ((support_C_mul_X_pow' n z).trans (by simp only [mem_singleton, mem_insert, singleton_subset_iff, true_or, or_true]))) ((support_C_mul_X_pow' l w).trans (by simp only [mem_singleton, mem_insert, singleton_subset_iff, true_or, or_true])))

theorem support_tetranomial {k m n l: ℕ} (hkm : k < m) (hmn : m < n) (hnl : n < l) {x y z w : ℤ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0) : support (C x * X ^ k + C y * X ^ m + C z * X ^ n + C w * X ^ l) = {k, m, n, l} := by
  apply subset_antisymm (support_tetranomial' k m n l x y z w)
  simp_rw [insert_subset_iff, singleton_subset_iff, mem_support_iff, coeff_add, coeff_C_mul, coeff_X_pow_self, mul_one, coeff_X_pow, if_neg hkm.ne, if_neg hkm.ne', if_neg hmn.ne, if_neg hmn.ne', if_neg hnl.ne, if_neg hnl.ne', if_neg (hkm.trans hmn).ne, if_neg (hkm.trans hmn).ne', if_neg (hmn.trans hnl).ne, if_neg (hmn.trans hnl).ne', if_neg ((hkm.trans hmn).trans hnl).ne, if_neg ((hkm.trans hmn).trans hnl).ne',mul_zero, add_zero, zero_add]
  tauto

theorem experiment_non_zero: (1 + X + X ^ 2 + X ^ 4: ℤ[X]) ≠ 0 := by
  let poly := (1 + X + X ^ 2 + X ^ 4 : ℤ[X])
  let poly' := (1 * X ^ 0 + 1 * X ^ 1 + 1 * X ^ 2 + 1 * X ^ 4 : ℤ[X])
  have support_det: poly'.support = {0, 1, 2, 4} := by
    apply support_tetranomial
    <;> norm_num
  have: poly.support = poly'.support := by congr; ring
  by_contra eq_zero
  have support_non_empty: poly.support = ∅ := Polynomial.support_eq_empty.mpr eq_zero
  rw [this, support_det] at support_non_empty
  contradiction

theorem experiment_non_one: (1 + X + X ^ 2 + X ^ 4: ℤ[X]) ≠ 1 := by
  let poly := (1 + X + X ^ 2 + X ^ 4 : ℤ[X])
  let poly' := (1 * X ^ 0 + 1 * X ^ 1 + 1 * X ^ 2 + 1 * X ^ 4 : ℤ[X])
  have support_det: poly'.support = {0, 1, 2, 4} := by
    apply support_tetranomial
    <;> norm_num
  have: poly.support = poly'.support := by congr; ring
  by_contra eq_one
  have eq_support: poly.support = (1 : ℤ[X]).support := by rw [← eq_one]
  have support_one: (1 : ℤ[X]).support = {0} := by
    have one_non_triv: 1 = (X ^ 0: ℤ[X]) := by simp only [pow_zero]
    rw [one_non_triv]
    apply support_X_pow
    simp only [one_ne_zero, not_false_eq_true]
  rw [this, support_det, support_one] at eq_support
  contradiction

theorem experiment_nat_deg_tetra: (1 + X + X ^ 2 + X ^ 4 : ℤ[X]).natDegree = 4 := by
  let poly' := (1 * X ^ 0 + 1 * X ^ 1 + 1 * X ^ 2 + 1 * X ^ 4 : ℤ[X])
  have support_det: poly'.support = {0, 1, 2, 4} := by
    apply support_tetranomial
    <;> norm_num
  have non_zero: poly' ≠ 0 := by
    by_contra eq_zero
    have support_non_empty: poly'.support = ∅ := Polynomial.support_eq_empty.mpr eq_zero
    rw [support_det] at support_non_empty
    contradiction
  have deg_eq_support_max': poly'.natDegree = poly'.support.max' (nonempty_support_iff.mpr non_zero) := natDegree_eq_support_max' non_zero
  have poly_support_max'_eq_max: (poly'.support.max' (nonempty_support_iff.mpr non_zero): WithBot ℕ) = ((poly'.support).max: WithBot ℕ) := by apply Finset.coe_max'
  have support_max'_eq_max: ({0, 1, 2, 4}: Finset ℕ).max' (insert_nonempty 0 {1, 2, 4}) = ({0, 1, 2, 4}: Finset ℕ).max := by apply Finset.coe_max'
  have poly_support_max'_eq_support_max': (poly'.support.max' (nonempty_support_iff.mpr non_zero): WithBot ℕ) = (({0, 1, 2, 4}: Finset ℕ).max' (insert_nonempty 0 {1, 2, 4}): WithBot ℕ) := by rw [poly_support_max'_eq_max, support_max'_eq_max, support_det]
  have poly_support_max'_WithBot_eq_max': (poly'.support.max' (nonempty_support_iff.mpr non_zero): WithBot ℕ) = (poly'.support.max' (nonempty_support_iff.mpr non_zero): ℕ) := rfl
  have support_max'_WithBot_eq_support_max': (({0, 1, 2, 4}: Finset ℕ).max' (insert_nonempty 0 {1, 2, 4}): WithBot ℕ) = (({0, 1, 2, 4}: Finset ℕ).max' (insert_nonempty 0 {1, 2, 4}): ℕ) := rfl
  rw [poly_support_max'_WithBot_eq_max', support_max'_WithBot_eq_support_max'] at poly_support_max'_eq_support_max'
  simp only [Finset.mem_singleton, Finset.mem_insert, Nat.cast_inj] at poly_support_max'_eq_support_max'
  have poly_support_max'_eq_four: (poly'.support.max' (nonempty_support_iff.mpr non_zero): ℕ) = 4 := by rw [poly_support_max'_eq_support_max']; rfl
  have natDegree_eq_four: poly'.natDegree = 4 := by rw [deg_eq_support_max']; exact poly_support_max'_eq_four
  simp only [pow_zero, mul_one, pow_one, one_mul, ne_eq] at non_zero
  simp only [pow_zero, mul_one, pow_one, one_mul] at natDegree_eq_four
  have: (1 + X + X ^ 2 + X ^ 4 : ℤ[X]).natDegree = poly'.natDegree := by unfold_let; simp only [pow_zero, mul_one, pow_one, one_mul]
  rw [this]
  exact natDegree_eq_four

theorem experiment_deg_tetra: (1 + X + X ^ 2 + X ^ 4 : ℤ[X]).degree = 4 := by
  let poly := (1 + X + X ^ 2 + X ^ 4 : ℤ[X])
  have natDegree_eq_four: (1 + X + X ^ 2 + X ^ 4 : ℤ[X]).natDegree = 4 := experiment_nat_deg_tetra
  have non_zero: (1 + X + X ^ 2 + X ^ 4 : ℤ[X]) ≠ 0 := experiment_non_zero
  have deg_eq_four: poly.degree = poly.natDegree := degree_eq_natDegree non_zero
  rw [natDegree_eq_four] at deg_eq_four
  exact deg_eq_four

theorem experiment_not_unit: ¬ IsUnit (1 + X + X ^ 2 + X ^ 4 : ℤ[X]) := by
  let poly := (1 + X + X ^ 2 + X ^ 4 : ℤ[X])
  have deg_eq_four: poly.degree = 4 := experiment_deg_tetra
  by_contra poly_is_unit'
  have poly_is_unit: ∃ (Poly : ℤ[X]), poly * Poly = 1 := isUnit_iff_exists_inv.mp poly_is_unit'
  rcases poly_is_unit with ⟨Poly, poly_is_unit⟩
  have poly_is_unit_deg: (poly * Poly).degree = poly.degree + Poly.degree := by simp only [degree_mul]
  rw [poly_is_unit, deg_eq_four] at poly_is_unit_deg
  simp only [degree_one] at poly_is_unit_deg
  by_cases Poly_eq_zero : Poly = 0
  rw [Poly_eq_zero] at poly_is_unit_deg
  contradiction
  have: Poly.degree < 0 := by
    by_contra p
    push_neg at p
    have: 4 + Poly.degree > 0 := by
      refine Left.add_pos_of_pos_of_nonneg ?ha p
      norm_num
    rw [← poly_is_unit_deg] at this
    exact (lt_self_iff_false 0).mp this
  absurd this
  simp only [Nat.WithBot.lt_zero_iff, degree_eq_bot]
  exact Poly_eq_zero

theorem experiment_monic: Monic (1 + X + X ^ 2 + X ^ 4 : ℤ[X]) := by
  let poly := (1 + X + X ^ 2 + X ^ 4 : ℤ[X])
  have natDegree_eq_four: poly.natDegree = 4 := experiment_nat_deg_tetra
  unfold Monic leadingCoeff
  rw [natDegree_eq_four]
  simp only [coeff_add, coeff_X_pow, ite_false, add_zero, ite_true, add_left_eq_self]
  have coeff₁: (coeff 1 4 : ℤ) = 0 := by apply coeff_one
  have coeff₂: (coeff X 4 : ℤ) = 0 := by apply coeff_X
  rw [coeff₁, coeff₂]
  simp only [add_zero, Nat.reduceEqDiff, ↓reduceIte]

theorem experiment_deg_zero_form {Polya: ℤ[X]} (deg_eq_zero: Polya.natDegree = 0) (Polya_monic : Monic Polya) : Polya = 1 := by
  unfold Monic leadingCoeff at Polya_monic
  rw [deg_eq_zero] at Polya_monic
  apply Polynomial.ext_iff.mpr
  intro n
  by_cases n_eq_zero: n = 0
  rw [n_eq_zero, Polya_monic, coeff_one_zero]
  have support_one: (1 : ℤ[X]).support = {0} := by
    have one_non_triv: 1 = (X ^ 0: ℤ[X]) := by simp only [pow_zero]
    rw [one_non_triv]
    apply support_X_pow
    simp only [one_ne_zero, not_false_eq_true]
  have coeff_one_eq_zero: coeff (1 :ℤ[X]) n = 0 := by
    apply not_mem_support_iff.mp
    rw [support_one, mem_singleton]
    exact n_eq_zero
  have coeff_Polya_eq_zero: coeff Polya n = 0 := by
    apply (degree_le_iff_coeff_zero Polya 0).mp
    exact natDegree_eq_zero_iff_degree_le_zero.mp deg_eq_zero
    by_contra leq
    simp only [Nat.cast_pos, not_lt, nonpos_iff_eq_zero] at leq
    contradiction
  rw [coeff_one_eq_zero, coeff_Polya_eq_zero]

theorem expreriment_deg_one_form {Polya: ℤ[X]} (deg_eq_one: Polya.natDegree = 1) (Polya_monic : Monic Polya): Polya = C (coeff Polya 0) + X := by
  have Polyb_eq: Polya = ∑ x in range (Polya.natDegree).succ, (C (coeff Polya x) * (X ^ x) : ℤ[X]) := as_sum_range_C_mul_X_pow Polya
  nth_rw 1 [Polyb_eq, deg_eq_one]
  have : range (Nat.succ 1) = {0, 1} := rfl
  rw [this]
  simp only [mem_singleton, mem_insert, eq_intCast, not_false_eq_true, sum_insert, pow_zero, mul_one, pow_one, sum_singleton]
  unfold Monic leadingCoeff at Polya_monic
  rw [deg_eq_one] at Polya_monic
  rw [Polya_monic]
  ring

theorem experiment_minus_one {x : ℕ} (sum : 4 = 1 + x) : x = 3 := by
  have succ_three: 4 = Nat.succ 3 := by simp only
  have succ_one: 1 + (x : ℕ) = Nat.succ (x : ℕ) := (Nat.succ_eq_one_add (x : ℕ)).symm
  rw [succ_three, succ_one] at sum
  simp only [Nat.succ.injEq] at sum
  exact sum.symm

theorem experiment_monic_neq_zero {Poly: ℤ[X]} (Ponic: Monic Poly) : Poly ≠ 0 := by
  apply Monic.ne_zero_of_ne
  norm_num
  exact Ponic

theorem experiment_deg_three_form {Polyb: ℤ[X]} (deg_eq_three: Polyb.natDegree = 3) (Polyb_monic : Monic Polyb): Polyb = C (coeff Polyb 0) + C (coeff Polyb 1) * X + C (coeff Polyb 2) * X ^ 2 + X ^ 3 := by
  have Polyb_eq: Polyb = ∑ x in range (Polyb.natDegree).succ, (C (coeff Polyb x) * (X ^ x) : ℤ[X]) := as_sum_range_C_mul_X_pow Polyb
  nth_rw 1 [Polyb_eq, deg_eq_three]
  have : range (Nat.succ 3) = {0, 1, 2, 3} := rfl
  rw [this]
  simp only [mem_singleton, mem_insert, eq_intCast, not_false_eq_true, sum_insert, pow_zero, mul_one, pow_one, sum_singleton]
  unfold Monic leadingCoeff at Polyb_monic
  rw [deg_eq_three] at Polyb_monic
  simp only [mem_insert, zero_ne_one, OfNat.zero_ne_ofNat, mem_singleton, or_self, not_false_eq_true, sum_insert, pow_zero, mul_one, OfNat.one_ne_ofNat, pow_one, Nat.reduceEqDiff, sum_singleton, Polyb_monic]
  ring

theorem experiment_deg_two_form {Polyb: ℤ[X]} (deg_eq_two: Polyb.natDegree = 2) (Polyb_monic : Monic Polyb): Polyb = C (coeff Polyb 0) + C (coeff Polyb 1) * X + X ^ 2 := by
  have Polyb_eq: Polyb = ∑ x in range (Polyb.natDegree).succ, (C (coeff Polyb x) * (X ^ x) : ℤ[X]) := as_sum_range_C_mul_X_pow Polyb
  nth_rw 1 [Polyb_eq, deg_eq_two]
  have : range (Nat.succ 2) = {0, 1, 2} := rfl
  rw [this]
  simp only [mem_singleton, mem_insert, eq_intCast, not_false_eq_true, sum_insert, pow_zero, mul_one, pow_one, sum_singleton]
  unfold Monic leadingCoeff at Polyb_monic
  rw [deg_eq_two] at Polyb_monic
  simp only [mem_insert, zero_ne_one, mem_singleton, OfNat.zero_ne_ofNat, or_self, not_false_eq_true, sum_insert, pow_zero, mul_one, OfNat.one_ne_ofNat, pow_one, sum_singleton, Polyb_monic]
  ring

theorem experiment_mul {Polya Polyb : ℤ[X]} : (C (coeff Polya 0) + X) * (C (coeff Polyb 0) + C (coeff Polyb 1) * X + C (coeff Polyb 2) * X ^ 2 + X ^ 3) = C ((coeff Polya 0) * (coeff Polyb 0)) + C ((coeff Polya 0) * (coeff Polyb 1) + (coeff Polyb 0)) * X + C ((coeff Polya 0) * (coeff Polyb 2) + (coeff Polyb 1)) * X ^ 2 + C ((coeff Polya 0) + (coeff Polyb 2)) * X ^ 3 + X ^ 4 := by
  ring_nf
  simp only [eq_intCast, map_add, map_mul]
  ring

theorem experiment_coeff_one {Polya Polyb : ℤ[X]}: coeff (C ((coeff Polya 0) * (coeff Polyb 0)) + C ((coeff Polya 0) * (coeff Polyb 1) + (coeff Polyb 0)) * X + C ((coeff Polya 0) * (coeff Polyb 2) + (coeff Polyb 1)) * X ^ 2 + C ((coeff Polya 0) + (coeff Polyb 2)) * X ^ 3 + X ^ 4 : ℤ[X]) 1 = (coeff Polya 0) * (coeff Polyb 1) + (coeff Polyb 0) := by
  repeat rw [coeff_add]
  repeat rw [coeff_C]
  repeat rw [coeff_C_mul_X_pow]
  simp only [ite_false, map_add, map_mul, coeff_mul_X, coeff_add, zero_add, add_zero, ite_true, coeff_X_pow, add_left_eq_self]
  rw [← C_mul]
  repeat rw [coeff_C]
  simp only [↓reduceIte, OfNat.one_ne_ofNat, add_zero]

theorem experiment_coeff_two {Polya Polyb : ℤ[X]}: coeff (C ((coeff Polya 0) * (coeff Polyb 0)) + C ((coeff Polya 0) * (coeff Polyb 1) + (coeff Polyb 0)) * X + C ((coeff Polya 0) * (coeff Polyb 2) + (coeff Polyb 1)) * X ^ 2 + C ((coeff Polya 0) + (coeff Polyb 2)) * X ^ 3 + X ^ 4 : ℤ[X]) 2 = (coeff Polya 0) * (coeff Polyb 2) + (coeff Polyb 1) := by
  repeat rw [coeff_add]
  repeat rw [coeff_C]
  repeat rw [coeff_C_mul_X_pow]
  simp only [ite_false, map_add, map_mul, coeff_mul_X, coeff_add, zero_add, add_zero, ite_true, coeff_X_pow, add_left_eq_self]
  rw [← C_mul]
  repeat rw [coeff_C]
  simp only [one_ne_zero, ↓reduceIte, add_zero, zero_add, Nat.reduceEqDiff]

theorem experiment_coeff_three {Polya Polyb : ℤ[X]}: coeff (C ((coeff Polya 0) * (coeff Polyb 0)) + C ((coeff Polya 0) * (coeff Polyb 1) + (coeff Polyb 0)) * X + C ((coeff Polya 0) * (coeff Polyb 2) + (coeff Polyb 1)) * X ^ 2 + C ((coeff Polya 0) + (coeff Polyb 2)) * X ^ 3 + X ^ 4 : ℤ[X]) 3 = (coeff Polya 0) + (coeff Polyb 2) := by
  repeat rw [coeff_add]
  repeat rw [coeff_C]
  repeat rw [coeff_C_mul_X_pow]
  simp only [ite_false, map_add, map_mul, coeff_mul_X, coeff_add, zero_add, add_zero, ite_true, coeff_X_pow, add_left_eq_self]
  rw [← C_mul]
  repeat rw [coeff_C]
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, add_zero, Nat.succ_ne_self, zero_add, Nat.reduceEqDiff]

theorem experiment_minus_four {x : ℕ} (sum : 4 = 4 + x) : x = 0 := by omega

theorem experiment_mul' {Polya Polyb : ℤ[X]} : (C (coeff Polya 0) + C (coeff Polya 1) * X + X ^ 2) * (C (coeff Polyb 0) + C (coeff Polyb 1) * X + X ^ 2) = C ((coeff Polya 0) * (coeff Polyb 0)) + C ((coeff Polya 0) * (coeff Polyb 1) + (coeff Polya 1) * (coeff Polyb 0)) * X + C ((coeff Polya 0) + (coeff Polya 1) * (coeff Polyb 1) + (coeff Polyb 0)) * X ^ 2 + C ((coeff Polya 1) + (coeff Polyb 1)) * X ^ 3 + X ^ 4 := by
  ring_nf
  simp only [eq_intCast, map_add, map_mul]
  ring

theorem experiment_coeff_one' {Polya Polyb : ℤ[X]}: coeff (C ((coeff Polya 0) * (coeff Polyb 0)) + C ((coeff Polya 0) * (coeff Polyb 1) + (coeff Polya 1) * (coeff Polyb 0)) * X + C ((coeff Polya 0) + (coeff Polya 1) * (coeff Polyb 1) + (coeff Polyb 0)) * X ^ 2 + C ((coeff Polya 1) + (coeff Polyb 1)) * X ^ 3 + X ^ 4 : ℤ[X]) 1 = (coeff Polya 0) * (coeff Polyb 1) + (coeff Polya 1) * (coeff Polyb 0) := by
  repeat rw [coeff_add]
  repeat rw [coeff_C]
  repeat rw [coeff_C_mul_X_pow]
  simp only [ite_false, map_add, map_mul, coeff_mul_X, coeff_add, zero_add, add_zero, ite_true, coeff_X_pow, add_left_eq_self]
  rw [← C_mul]
  repeat rw [coeff_C]
  simp only [↓reduceIte, eq_intCast, mul_coeff_zero, intCast_coeff_zero, Int.cast_id,
    OfNat.one_ne_ofNat, add_zero]

theorem experiment_coeff_two' {Polya Polyb : ℤ[X]}: coeff (C ((coeff Polya 0) * (coeff Polyb 0)) + C ((coeff Polya 0) * (coeff Polyb 1) + (coeff Polya 1) * (coeff Polyb 0)) * X + C ((coeff Polya 0) + (coeff Polya 1) * (coeff Polyb 1) + (coeff Polyb 0)) * X ^ 2 + C ((coeff Polya 1) + (coeff Polyb 1)) * X ^ 3 + X ^ 4 : ℤ[X]) 2 = (coeff Polya 0) + (coeff Polya 1) * (coeff Polyb 1) + (coeff Polyb 0) := by
  repeat rw [coeff_add]
  repeat rw [coeff_C]
  repeat rw [coeff_C_mul_X_pow]
  simp only [ite_false, map_add, map_mul, coeff_mul_X, coeff_add, zero_add, add_zero, ite_true, coeff_X_pow, add_left_eq_self]
  repeat rw [← C_mul]
  repeat rw [coeff_C]
  simp only [one_ne_zero, ↓reduceIte, add_zero, zero_add, Nat.reduceEqDiff]

theorem experiment_coeff_three' {Polya Polyb : ℤ[X]}: coeff (C ((coeff Polya 0) * (coeff Polyb 0)) + C ((coeff Polya 0) * (coeff Polyb 1) + (coeff Polya 1) * (coeff Polyb 0)) * X + C ((coeff Polya 0) + (coeff Polya 1) * (coeff Polyb 1) + (coeff Polyb 0)) * X ^ 2 + C ((coeff Polya 1) + (coeff Polyb 1)) * X ^ 3 + X ^ 4 : ℤ[X]) 3 = (coeff Polya 1) + (coeff Polyb 1) := by
  repeat rw [coeff_add]
  repeat rw [coeff_C]
  repeat rw [coeff_C_mul_X_pow]
  simp only [ite_false, map_add, map_mul, coeff_mul_X, coeff_add, zero_add, add_zero, ite_true, coeff_X_pow, add_left_eq_self]
  repeat rw [← C_mul]
  repeat rw [coeff_C]
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, add_zero, Nat.succ_ne_self, zero_add,
    Nat.reduceEqDiff]

theorem experiment_irreducible: Irreducible (1 + X + X ^ 2 + X ^ 4 : ℤ[X]) := by
  let poly := (1 + X + X ^ 2 + X ^ 4 : ℤ[X])
  apply (irreducible_of_monic experiment_monic experiment_non_one).mpr
  intro Polya Polyb Polya_monic Polyb_monic fac
  by_cases Polya_natDegree_eq_zero : Polya.natDegree = 0
  left; exact experiment_deg_zero_form Polya_natDegree_eq_zero Polya_monic
  by_cases Polya_natDegree_eq_one: Polya.natDegree = 1
  have natDegree_sum: (Polya * Polyb).natDegree = Polya.natDegree + Polyb.natDegree := natDegree_mul (experiment_monic_neq_zero Polya_monic) (experiment_monic_neq_zero Polyb_monic)
  rw [fac, experiment_nat_deg_tetra, Polya_natDegree_eq_one] at natDegree_sum
  have Polyb_natDegree_eq_three: Polyb.natDegree = 3 := by omega
  rw [expreriment_deg_one_form Polya_natDegree_eq_one Polya_monic, experiment_deg_three_form Polyb_natDegree_eq_three Polyb_monic, experiment_mul] at fac
  have eq₁: coeff (C ((coeff Polya 0) * (coeff Polyb 0)) + C ((coeff Polya 0) * (coeff Polyb 1) + (coeff Polyb 0)) * X + C ((coeff Polya 0) * (coeff Polyb 2) + (coeff Polyb 1)) * X ^ 2 + C ((coeff Polya 0) + (coeff Polyb 2)) * X ^ 3 + X ^ 4) 0 = coeff poly 0 := congrFun (congrArg coeff fac) 0
  have eq₁': coeff (C ((coeff Polya 0) * (coeff Polyb 0)) + C ((coeff Polya 0) * (coeff Polyb 1) + (coeff Polyb 0)) * X + C ((coeff Polya 0) * (coeff Polyb 2) + (coeff Polyb 1)) * X ^ 2 + C ((coeff Polya 0) + (coeff Polyb 2)) * X ^ 3 + X ^ 4) 0 = (coeff Polya 0) * (coeff Polyb 0) := by
    unfold_let
    simp only [map_mul, eq_intCast, map_add, coeff_add, mul_coeff_zero, intCast_coeff_zero, Int.cast_id, coeff_X_zero, mul_zero, add_zero, coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte]
  have eq₁'': coeff poly 0 = 1 := by
    unfold_let
    simp only [coeff_add, coeff_one_zero, coeff_X_zero, add_zero, coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte]
  rw [eq₁', eq₁''] at eq₁
  have eq₂: coeff (C ((coeff Polya 0) * (coeff Polyb 0)) + C ((coeff Polya 0) * (coeff Polyb 1) + (coeff Polyb 0)) * X + C ((coeff Polya 0) * (coeff Polyb 2) + (coeff Polyb 1)) * X ^ 2 + C ((coeff Polya 0) + (coeff Polyb 2)) * X ^ 3 + X ^ 4) 1 = coeff poly 1 := congrFun (congrArg coeff fac) 1
  have eq₂'': coeff poly 1 = 1 := by
    unfold_let
    simp only [coeff_add, coeff_X_one, coeff_X_pow, OfNat.one_ne_ofNat, ↓reduceIte, add_zero, add_left_eq_self]
    apply coeff_C
  have eq₃: coeff (C ((coeff Polya 0) * (coeff Polyb 0)) + C ((coeff Polya 0) * (coeff Polyb 1) + (coeff Polyb 0)) * X + C ((coeff Polya 0) * (coeff Polyb 2) + (coeff Polyb 1)) * X ^ 2 + C ((coeff Polya 0) + (coeff Polyb 2)) * X ^ 3 + X ^ 4) 2 = coeff poly 2 := congrFun (congrArg coeff fac) 2
  have eq₃'': coeff poly 2 = 1 := by
    unfold_let
    simp only [coeff_add, coeff_X_pow, ↓reduceIte, Nat.reduceEqDiff, add_zero, add_left_eq_self]
    have: coeff (@OfNat.ofNat ℤ[X] 1 One.toOfNat1) 2 = 0 := coeff_C
    rw [this, zero_add]
    apply coeff_X
  have eq₄: coeff (C ((coeff Polya 0) * (coeff Polyb 0)) + C ((coeff Polya 0) * (coeff Polyb 1) + (coeff Polyb 0)) * X + C ((coeff Polya 0) * (coeff Polyb 2) + (coeff Polyb 1)) * X ^ 2 + C ((coeff Polya 0) + (coeff Polyb 2)) * X ^ 3 + X ^ 4) 3 = coeff poly 3 := congrFun (congrArg coeff fac) 3
  have eq₄'': coeff poly 3 = 0 := by
    unfold_let
    simp only [coeff_add, coeff_X_pow, Nat.succ_ne_self, ↓reduceIte, add_zero, Nat.reduceEqDiff]
    have: coeff (@OfNat.ofNat ℤ[X] 1 One.toOfNat1) 3 = 0 := coeff_C
    rw [this, zero_add]
    apply coeff_X
  rw [experiment_coeff_one, eq₂''] at eq₂
  rw [experiment_coeff_two, eq₃''] at eq₃
  rw [experiment_coeff_three, eq₄''] at eq₄
  obtain ⟨Polya_one_eq_one, Polyb_one_eq_one⟩ | ⟨Polya_one_eq_one, Polyb_one_eq_one⟩ := Iff.mp Int.mul_eq_one_iff_eq_one_or_neg_one eq₁
  rw [Polya_one_eq_one] at eq₂ eq₃ eq₄
  rw [Polyb_one_eq_one] at eq₂
  linarith
  rw [Polya_one_eq_one] at eq₂ eq₃ eq₄
  rw [Polyb_one_eq_one] at eq₂
  linarith
  by_cases Polya_natDegree_eq_two: Polya.natDegree = 2
  have natDegree_sum: (Polya * Polyb).natDegree = Polya.natDegree + Polyb.natDegree := natDegree_mul (experiment_monic_neq_zero Polya_monic) (experiment_monic_neq_zero Polyb_monic)
  rw [fac, experiment_nat_deg_tetra, Polya_natDegree_eq_two] at natDegree_sum
  have Polyb_natDegree_eq_two: Polyb.natDegree = 2 := by omega
  rw [experiment_deg_two_form Polya_natDegree_eq_two Polya_monic, experiment_deg_two_form Polyb_natDegree_eq_two Polyb_monic, experiment_mul'] at fac
  have eq₁: coeff (C ((coeff Polya 0) * (coeff Polyb 0)) + C ((coeff Polya 0) * (coeff Polyb 1) + (coeff Polya 1) * (coeff Polyb 0)) * X + C ((coeff Polya 0) + (coeff Polya 1) * (coeff Polyb 1) + (coeff Polyb 0)) * X ^ 2 + C ((coeff Polya 1) + (coeff Polyb 1)) * X ^ 3 + X ^ 4) 0 = coeff poly 0 := congrFun (congrArg coeff fac) 0
  have eq₁': coeff (C ((coeff Polya 0) * (coeff Polyb 0)) + C ((coeff Polya 0) * (coeff Polyb 1) + (coeff Polya 1) * (coeff Polyb 0)) * X + C ((coeff Polya 0) + (coeff Polya 1) * (coeff Polyb 1) + (coeff Polyb 0)) * X ^ 2 + C ((coeff Polya 1) + (coeff Polyb 1)) * X ^ 3 + X ^ 4) 0 = (coeff Polya 0) * (coeff Polyb 0) := by
    unfold_let
    simp only [map_mul, eq_intCast, map_add, coeff_add, mul_coeff_zero, intCast_coeff_zero, Int.cast_id, coeff_X_zero, mul_zero, add_zero, coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte]
  have eq₁'': coeff poly 0 = 1 := by
    unfold_let
    simp only [coeff_add, coeff_one_zero, coeff_X_zero, add_zero, coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte]
  rw [eq₁', eq₁''] at eq₁
  have eq₂: coeff (C ((coeff Polya 0) * (coeff Polyb 0)) + C ((coeff Polya 0) * (coeff Polyb 1) + (coeff Polya 1) * (coeff Polyb 0)) * X + C ((coeff Polya 0) + (coeff Polya 1) * (coeff Polyb 1) + (coeff Polyb 0)) * X ^ 2 + C ((coeff Polya 1) + (coeff Polyb 1)) * X ^ 3 + X ^ 4) 1 = coeff poly 1 := congrFun (congrArg coeff fac) 1
  have eq₂'': coeff poly 1 = 1 := by
    unfold_let
    simp only [coeff_add, coeff_X_one, coeff_X_pow, OfNat.one_ne_ofNat, ↓reduceIte, add_zero, add_left_eq_self]
    apply coeff_C
  have eq₃: coeff (C ((coeff Polya 0) * (coeff Polyb 0)) + C ((coeff Polya 0) * (coeff Polyb 1) + (coeff Polya 1) * (coeff Polyb 0)) * X + C ((coeff Polya 0) + (coeff Polya 1) * (coeff Polyb 1) + (coeff Polyb 0)) * X ^ 2 + C ((coeff Polya 1) + (coeff Polyb 1)) * X ^ 3 + X ^ 4) 2 = coeff poly 2 := congrFun (congrArg coeff fac) 2
  have eq₃'': coeff poly 2 = 1 := by
    unfold_let
    simp only [coeff_add, coeff_X_pow, ↓reduceIte, Nat.reduceEqDiff, add_zero, add_left_eq_self]
    have: coeff (@OfNat.ofNat ℤ[X] 1 One.toOfNat1) 2 = 0 := coeff_C
    rw [this, zero_add]
    apply coeff_X
  have eq₄: coeff (C ((coeff Polya 0) * (coeff Polyb 0)) + C ((coeff Polya 0) * (coeff Polyb 1) + (coeff Polya 1) * (coeff Polyb 0)) * X + C ((coeff Polya 0) + (coeff Polya 1) * (coeff Polyb 1) + (coeff Polyb 0)) * X ^ 2 + C ((coeff Polya 1) + (coeff Polyb 1)) * X ^ 3 + X ^ 4) 3 = coeff poly 3 := congrFun (congrArg coeff fac) 3
  have eq₄'': coeff poly 3 = 0 := by
    unfold_let
    simp only [coeff_add, coeff_X_pow, Nat.succ_ne_self, ↓reduceIte, add_zero, Nat.reduceEqDiff]
    have: coeff (@OfNat.ofNat ℤ[X] 1 One.toOfNat1) 3 = 0 := coeff_C
    rw [this, zero_add]
    apply coeff_X
  rw [experiment_coeff_one', eq₂''] at eq₂
  rw [experiment_coeff_two', eq₃''] at eq₃
  rw [experiment_coeff_three', eq₄''] at eq₄
  obtain ⟨Polya_one_eq_one, Polyb_one_eq_one⟩ | ⟨Polya_one_eq_one, Polyb_one_eq_one⟩ := Iff.mp Int.mul_eq_one_iff_eq_one_or_neg_one eq₁
  rw [Polya_one_eq_one, Polyb_one_eq_one] at eq₂ eq₃
  linarith
  rw [Polya_one_eq_one, Polyb_one_eq_one] at eq₂ eq₃
  linarith
  by_cases Polya_natDegree_eq_three: Polya.natDegree = 3
  have natDegree_sum: (Polya * Polyb).natDegree = Polya.natDegree + Polyb.natDegree := natDegree_mul (experiment_monic_neq_zero Polya_monic) (experiment_monic_neq_zero Polyb_monic)
  rw [fac, experiment_nat_deg_tetra, Polya_natDegree_eq_three] at natDegree_sum
  have Polyb_natDegree_eq_one: Polyb.natDegree = 1 := by omega
  rw [mul_comm, experiment_deg_three_form Polya_natDegree_eq_three Polya_monic, expreriment_deg_one_form Polyb_natDegree_eq_one Polyb_monic, experiment_mul] at fac
  have eq₁: coeff (C ((coeff Polyb 0) * (coeff Polya 0)) + C ((coeff Polyb 0) * (coeff Polya 1) + (coeff Polya 0)) * X + C ((coeff Polyb 0) * (coeff Polya 2) + (coeff Polya 1)) * X ^ 2 + C ((coeff Polyb 0) + (coeff Polya 2)) * X ^ 3 + X ^ 4) 0 = coeff poly 0 := congrFun (congrArg coeff fac) 0
  have eq₁': coeff (C ((coeff Polyb 0) * (coeff Polya 0)) + C ((coeff Polyb 0) * (coeff Polya 1) + (coeff Polya 0)) * X + C ((coeff Polyb 0) * (coeff Polya 2) + (coeff Polya 1)) * X ^ 2 + C ((coeff Polyb 0) + (coeff Polya 2)) * X ^ 3 + X ^ 4) 0 = (coeff Polyb 0) * (coeff Polya 0) := by
    unfold_let
    simp only [map_mul, eq_intCast, map_add, coeff_add, mul_coeff_zero, intCast_coeff_zero, Int.cast_id, coeff_X_zero, mul_zero, add_zero, coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte]
  have eq₁'': coeff poly 0 = 1 := by
    unfold_let
    simp only [coeff_add, coeff_one_zero, coeff_X_zero, add_zero, coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte]
  rw [eq₁', eq₁''] at eq₁
  have eq₂: coeff (C ((coeff Polyb 0) * (coeff Polya 0)) + C ((coeff Polyb 0) * (coeff Polya 1) + (coeff Polya 0)) * X + C ((coeff Polyb 0) * (coeff Polya 2) + (coeff Polya 1)) * X ^ 2 + C ((coeff Polyb 0) + (coeff Polya 2)) * X ^ 3 + X ^ 4) 1 = coeff poly 1 := congrFun (congrArg coeff fac) 1
  have eq₂'': coeff poly 1 = 1 := by
    unfold_let
    simp only [coeff_add, coeff_X_one, coeff_X_pow, OfNat.one_ne_ofNat, ↓reduceIte, add_zero, add_left_eq_self]
    apply coeff_C
  have eq₃: coeff (C ((coeff Polyb 0) * (coeff Polya 0)) + C ((coeff Polyb 0) * (coeff Polya 1) + (coeff Polya 0)) * X + C ((coeff Polyb 0) * (coeff Polya 2) + (coeff Polya 1)) * X ^ 2 + C ((coeff Polyb 0) + (coeff Polya 2)) * X ^ 3 + X ^ 4) 2 = coeff poly 2 := congrFun (congrArg coeff fac) 2
  have eq₃'': coeff poly 2 = 1 := by
    unfold_let
    simp only [coeff_add, coeff_X_pow, ↓reduceIte, Nat.reduceEqDiff, add_zero, add_left_eq_self]
    have: coeff (@OfNat.ofNat ℤ[X] 1 One.toOfNat1) 2 = 0 := coeff_C
    rw [this, zero_add]
    apply coeff_X
  have eq₄: coeff (C ((coeff Polyb 0) * (coeff Polya 0)) + C ((coeff Polyb 0) * (coeff Polya 1) + (coeff Polya 0)) * X + C ((coeff Polyb 0) * (coeff Polya 2) + (coeff Polya 1)) * X ^ 2 + C ((coeff Polyb 0) + (coeff Polya 2)) * X ^ 3 + X ^ 4) 3 = coeff poly 3 := congrFun (congrArg coeff fac) 3
  have eq₄'': coeff poly 3 = 0 := by
    unfold_let
    simp only [coeff_add, coeff_X_pow, Nat.succ_ne_self, ↓reduceIte, add_zero, Nat.reduceEqDiff]
    have: coeff (@OfNat.ofNat ℤ[X] 1 One.toOfNat1) 3 = 0 := coeff_C
    rw [this, zero_add]
    apply coeff_X
  rw [experiment_coeff_one, eq₂''] at eq₂
  rw [experiment_coeff_two, eq₃''] at eq₃
  rw [experiment_coeff_three, eq₄''] at eq₄
  obtain ⟨Polyb_one_eq_one, Polya_one_eq_one⟩ | ⟨Polyb_one_eq_one, Polya_one_eq_one⟩ := Iff.mp Int.mul_eq_one_iff_eq_one_or_neg_one eq₁
  rw [Polyb_one_eq_one] at eq₂ eq₃ eq₄
  rw [Polya_one_eq_one] at eq₂
  linarith
  rw [Polyb_one_eq_one] at eq₂ eq₃ eq₄
  rw [Polya_one_eq_one] at eq₂
  linarith
  by_cases Polya_natDegree_eq_four : Polya.natDegree = 4
  have natDegree_sum: (Polya * Polyb).natDegree = Polya.natDegree + Polyb.natDegree := natDegree_mul (experiment_monic_neq_zero Polya_monic) (experiment_monic_neq_zero Polyb_monic)
  rw [fac, experiment_nat_deg_tetra, Polya_natDegree_eq_four] at natDegree_sum
  right; exact experiment_deg_zero_form (experiment_minus_four natDegree_sum) Polyb_monic
  have natDegree_sum: (Polya * Polyb).natDegree = Polya.natDegree + Polyb.natDegree := natDegree_mul (experiment_monic_neq_zero Polya_monic) (experiment_monic_neq_zero Polyb_monic)
  rw [fac, experiment_nat_deg_tetra] at natDegree_sum
  have deg_Polya_ge_four: 4 < Polya.natDegree := by omega
  linarith
