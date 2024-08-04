import Mathlib

open Finset
open Polynomial
open BigOperators
set_option maxHeartbeats 0

variable (n : ℕ) {R : Type*}

theorem general_form_of_polynomials [Semiring R] (poly: R[X]) : poly = ∑ x in range (poly.natDegree).succ, (C (coeff poly x) * (X ^ x) : R[X]) := as_sum_range_C_mul_X_pow poly

theorem experiment_deg_two_form {Polyb: ℤ[X]} (deg_eq_two: Polyb.natDegree = 2) : Polyb = C (coeff Polyb 0) + C (coeff Polyb 1) * X + C (coeff Polyb 2) * X ^ 2 := by
  nth_rw 1 [as_sum_range_C_mul_X_pow Polyb, deg_eq_two]
  have : range (Nat.succ 2) = {0, 1, 2} := rfl
  simp only [this, eq_intCast, mem_insert, zero_ne_one, mem_singleton, OfNat.zero_ne_ofNat, or_self, not_false_eq_true, sum_insert, pow_zero, mul_one, OfNat.one_ne_ofNat, pow_one, sum_singleton]
  ring

theorem experiment_deg_two_form_monic {Polyb: ℤ[X]} (deg_eq_two: Polyb.natDegree = 2) (MONIC: Monic Polyb): Polyb = C (coeff Polyb 0) + C (coeff Polyb 1) * X + X ^ 2 := by
  nth_rw 1 [as_sum_range_C_mul_X_pow Polyb, deg_eq_two]
  have : range (Nat.succ 2) = {0, 1, 2} := rfl
  unfold Monic leadingCoeff at MONIC
  rw [deg_eq_two] at MONIC
  simp only [this, MONIC, eq_intCast, mem_insert, zero_ne_one, mem_singleton, OfNat.zero_ne_ofNat, or_self, not_false_eq_true, sum_insert, pow_zero, mul_one, OfNat.one_ne_ofNat, pow_one, sum_singleton]
  ring

theorem experiment_deg_three_form_monic {Polyb: ℤ[X]} (deg_eq_three: Polyb.natDegree = 3) (Polyb_monic: Monic Polyb): Polyb = C (coeff Polyb 0) + C (coeff Polyb 1) * X + C (coeff Polyb 2) * X ^ 2 + X ^ 3 := by
  nth_rw 1 [as_sum_range_C_mul_X_pow Polyb, deg_eq_three]
  have : range (Nat.succ 3) = {0, 1, 2, 3} := rfl
  unfold Monic leadingCoeff at Polyb_monic
  rw [deg_eq_three] at Polyb_monic
  simp only [this, Polyb_monic, eq_intCast, mem_insert, zero_ne_one, OfNat.zero_ne_ofNat, mem_singleton, or_self, not_false_eq_true, sum_insert, pow_zero, mul_one, OfNat.one_ne_ofNat, pow_one, Nat.reduceEqDiff, sum_singleton]
  ring

theorem experiment_deg_n_form_monic {Polya: ℤ[X]} (deg_eq_one: Polya.natDegree = 1) (Polya_monic: Monic Polya): Polya = C (coeff Polya 0) + X := by
  unfold Monic leadingCoeff at Polya_monic
  rw [deg_eq_one] at Polya_monic
  nth_rw 1 [as_sum_range_C_mul_X_pow Polya, deg_eq_one]
  have : range (Nat.succ 1) = {0, 1} := rfl
  simp only [this, mem_singleton, mem_insert, eq_intCast, not_false_eq_true, sum_insert, pow_zero, mul_one, pow_one, sum_singleton, Polya_monic]
  ring

theorem coeff_of_polynomials [Semiring R] (poly: R[X]) {u: ℕ} : coeff (∑ x in range (poly.natDegree).succ, (C (coeff poly x) * (X ^ x) : R[X])) u = coeff poly u := by
  simp only [finset_sum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero, sum_ite_eq, mem_range, ite_eq_left_iff, not_lt]
  intro y
  apply (coeff_eq_zero_of_natDegree_lt y).symm

theorem experiment_coeff_three {Polya Polyb : ℤ[X]}: coeff (C ((coeff Polya 0) * (coeff Polyb 0)) + C ((coeff Polya 0) * (coeff Polyb 1) + (coeff Polyb 0)) * X + C ((coeff Polya 0) * (coeff Polyb 2) + (coeff Polyb 1)) * X ^ 2 + C ((coeff Polya 0) + (coeff Polyb 2)) * X ^ 3 + X ^ 4 : ℤ[X]) 3 = (coeff Polya 0) + (coeff Polyb 2) := by
  repeat rw [coeff_add]
  repeat rw [coeff_C]
  repeat rw [coeff_C_mul_X_pow]
  simp only [ite_false, map_add, map_mul, coeff_mul_X, coeff_add, zero_add, add_zero, ite_true, coeff_X_pow, add_left_eq_self]
  rw [← C_mul]
  repeat rw [coeff_C]
  simp only [ite_false, add_zero, Nat.succ_ne_self, ↓reduceIte, zero_add, Nat.reduceEqDiff]

#check coeff_sum
