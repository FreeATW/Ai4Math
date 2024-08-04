import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Combinatorics.Enumerative.Partition

/-!
=============
  SymmGroup
=============

Definition of Symmetry Group
============================

-/

open Equiv.Perm
open Multiset

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev SymmGroup (n : ℕ) := Equiv.Perm <| Fin n

lemma Equiv.Perm.orderOf_swap : ∀ (n : ℕ) (i j : Fin n), orderOf (Equiv.swap i j) <= 2 := by
  intros n i j
  exact orderOf_le_of_pow_eq_one (by decide)
    (by rw [pow_two, ext_iff]; intro x; rw [mul_apply (Equiv.swap i j) (Equiv.swap i j) x]; simp)


instance : Setoid (SymmGroup n) := IsConj.setoid (SymmGroup n)

instance : Fintype (SymmGroup n) := inferInstance

namespace SymmGroup
/- Example 1.29 -/

namespace List

theorem cycleType_formPerm (l : List (Fin n)) (hl : l.Nodup) (hn : 2 ≤ l.length) :
    l.formPerm.cycleType = [l.length] := by
    rw [cycleType_eq [l.formPerm]]
    . simp
      rw [List.support_formPerm_of_nodup _ hl, List.card_toFinset, List.dedup_eq_self.mpr hl]
      simp; intro x h; simp [h, Nat.succ_le_succ_iff] at hn;
    . simp;
    . simpa using List.isCycle_formPerm hl hn
    simp;

lemma Nodup.take {α : Type*} (l : List α) (hl : l.Nodup) (n : ℕ) : (l.take n).Nodup :=
  List.Nodup.sublist (List.take_sublist n l) hl

lemma Nodup.drop {α : Type*} (l : List α) (hl : l.Nodup) (n : ℕ) : (l.drop n).Nodup :=
  List.Nodup.sublist (List.drop_sublist n l) hl

lemma subset_of_take_add {α : Type*} (l : List α) (m n : ℕ) : l.take m ⊆ l.take (m + n) := by
  rw [List.take_add]; exact List.subset_append_left _ _



end List


def partition (σ : SymmGroup n) : n.Partition where
  parts := σ.cycleType + Multiset.replicate (Fintype.card (Fin n) - σ.support.card) 1
  parts_pos {n hn} := by
    cases' mem_add.mp hn with hn hn
    · exact zero_lt_one.trans (one_lt_of_mem_cycleType hn)
    · exact lt_of_lt_of_le zero_lt_one (ge_of_eq (Multiset.eq_of_mem_replicate hn))
  parts_sum := by
    rw [sum_add, sum_cycleType, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, mul_one,
      add_tsub_cancel_of_le σ.support.card_le_univ, Fintype.card_fin]

theorem parts_partition {σ : SymmGroup n} :
    σ.partition.parts = σ.cycleType + Multiset.replicate (Fintype.card (Fin n) - σ.support.card) 1 :=
  rfl

theorem filter_parts_partition_eq_cycleType {σ : SymmGroup n} :
    (partition σ).parts.filter (2 <= ·) = σ.cycleType := by
  rw [parts_partition, filter_add, Multiset.filter_eq_self.2 fun _ => two_le_of_mem_cycleType,
    Multiset.filter_eq_nil.2 fun a h => ?_, add_zero]
  rw [Multiset.eq_of_mem_replicate h]
  decide

lemma card_support_le_card {σ : SymmGroup n} : σ.support.card ≤ n := by
  suffices h : σ.support.card ≤ Fintype.card (Fin n) by rw [Fintype.card_fin n] at h; exact h
  exact σ.support.card_le_univ

theorem partition_eq_of_isConj {σ τ : SymmGroup n} : IsConj σ τ ↔ σ.partition = τ.partition := by
  rw [@isConj_iff_cycleType_eq _ _ _ σ τ]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Nat.Partition.ext_iff, parts_partition, parts_partition, ← sum_cycleType, ← sum_cycleType, h]
  · rw [← filter_parts_partition_eq_cycleType, ← filter_parts_partition_eq_cycleType, h]

/- This is an aux fcn so so that the ones are filtered -/
def cananical_perm_of_parts (parts : List ℕ) (cann : List (Fin n)) : SymmGroup n :=
  match parts with
  | [] => 1
  | ph :: pt => (cann.take ph).formPerm * (cananical_perm_of_parts pt (cann.drop ph))


lemma List.formPerm_disjoint_of_subset {σ : Equiv.Perm α} (l₁ l₂ : List α) (h : l₁ ⊆ l₂) (hl₁ : l₁.Nodup) (hl₂ : l₂.Nodup):
  l₂.formPerm.Disjoint σ → l₁.formPerm.Disjoint σ := by
  intro hd
  sorry

lemma cycleType_eq_of_cananical_perm (p : List ℕ) (cann : List (Fin n)) (hp : ∀ x ∈ p, 2 <= x)
  (hsum : p.sum <= cann.length) (hnd : cann.Nodup) : (cananical_perm_of_parts p cann).cycleType = p := by
  induction' p with ph pt ih generalizing cann
  . simp [cananical_perm_of_parts]
  . simp [cananical_perm_of_parts]
    simp only [List.sum_cons] at hsum; rw [add_comm] at hsum;
    have h_tk_l : (cann.take ph).length = ph := by
      rw [List.length_take];exact min_eq_left (le_of_add_le_right hsum)
    have h_disj: (cann.take ph).formPerm.Disjoint (cananical_perm_of_parts pt (cann.drop ph)) := by
      induction' pt with pth ptt tih generalizing ph
      . simp [cananical_perm_of_parts]
      simp [cananical_perm_of_parts];
      apply Equiv.Perm.Disjoint.mul_right
      . rw [List.formPerm_disjoint_iff]
        . exact List.disjoint_of_subset_right (List.take_subset pth _)
            (List.disjoint_take_drop hnd (by linarith))
        . exact List.Nodup.take cann hnd ph
        . exact List.Nodup.take _ (List.Nodup.drop cann hnd _) pth
        . rw [h_tk_l]; exact hp ph (List.mem_cons_self ph _)
        simp only [List.length_take, List.length_drop, le_min_iff];
        simp only [List.sum_cons] at hsum;
        have h2le : 2 <= pth := hp pth (List.mem_cons_of_mem ph (List.mem_cons_self pth _))
        nth_rw 2 [add_comm] at hsum; rw [add_assoc] at hsum
        exact ⟨h2le, Nat.le_sub_of_add_le (add_le_of_add_le_right (le_of_add_le_right hsum) h2le)⟩
      rw [add_comm]; apply List.formPerm_disjoint_of_subset _ _ (List.subset_of_take_add _ _ _)
        (List.Nodup.take _ hnd _) _ (tih (ph + pth) ?_ ?_ ?_ ?_)
      . exact List.Nodup.take cann hnd (ph + pth)
      . sorry
      . intro x hx; rw [List.mem_cons] at hx; rcases hx with hx1 | hx2
        . rw [hx1]; exact Nat.le_trans (hp ph (List.mem_cons_self ph _)) (Nat.le_add_right _ _)
        exact hp x (List.mem_cons_of_mem ph (List.mem_cons_of_mem pth hx2))
      . simp at hsum; rw [←add_assoc, add_comm, ←add_assoc]; exact hsum
      simp; simp at hsum; rw [add_comm, ←add_assoc] at hsum; exact le_trans (Nat.le_add_right _ _) hsum
    have h_sgt : (cann.take ph).formPerm.cycleType = [ph] := by
      rw [List.cycleType_formPerm]
      . rw [h_tk_l]
      . exact List.Nodup.take cann hnd ph
      rw [h_tk_l]; exact hp ph (List.mem_cons_self ph pt)
    rw [Disjoint.cycleType h_disj, h_sgt]
    nth_rw 2 [← Multiset.cons_coe]
    nth_rw 1 [← singleton_add]
    congr 1
    have hpi : ∀ x ∈ pt, 2 <= x := fun x hx => hp x (List.mem_cons_of_mem ph hx)
    have hsumi : pt.sum ≤ (List.drop ph cann).length := by

      simp only [List.length_drop]; exact Nat.le_sub_of_add_le hsum;
    exact ih (cann.drop ph) hpi hsumi (List.Nodup.drop cann hnd ph)

lemma partition_eq_of_cananical_perm (p : n.Partition) :
  (cananical_perm_of_parts (p.parts.toList.filter (2 <= ·)) (List.finRange n)).partition = p := by
  simp_rw [Nat.Partition.ext_iff, parts_partition, ← sum_cycleType, Fintype.card_fin]
  have hp : ∀ x ∈ p.parts.toList.filter (2 <= ·), 2 <= x := fun x =>
    by rw [List.mem_filter]; intro h; exact of_decide_eq_true h.2
  have hsum : (p.parts.toList.filter (2 <= ·)).sum <= (List.finRange n).length := by
    rw [List.length_finRange];
    have h_le : (p.parts.toList.filter (2 <= ·)).sum <= p.parts.toList.sum :=
      List.Sublist.sum_le_sum (List.filter_sublist p.parts.toList)
        (fun x hx => le_of_lt <| p.parts_pos <| mem_toList.mp hx)
    rw [sum_toList, p.parts_sum] at h_le; exact h_le
  simp_rw [cycleType_eq_of_cananical_perm _ _ hp hsum (List.nodup_finRange n), ← p.parts_sum];
  simp_rw [← Multiset.filter_coe, Multiset.coe_toList];
  have h_sum : p.parts = (filter (2 <= ·) p.parts) + (filter (· < 2) p.parts) := by
    nth_rw 1 [← Multiset.filter_add_not (2 <= ·) p.parts]; congr 2; simp;
  have h : (filter (· < 2) p.parts) = replicate (filter (· < 2) p.parts).sum 1 := by
    ext pt;
    rw [count_filter, count_replicate];
    match pt with
    | 0 =>
      rw [if_pos (by linarith), if_neg (by linarith)];
      simp only [count_eq_zero]; by_contra hn; exact Eq.not_lt (rfl) (p.parts_pos (hn))
    | 1 =>
      rw [if_pos (by linarith), if_pos (rfl)];
      have : p.parts.filter (· < 2) = p.parts.filter (· = 1) := by
        calc
          p.parts.filter (· < 2) = p.parts.filter fun x => x = 1 ∨ x = 0 := filter_congr (fun x _ => by {
            exact not_iff_not.mp (by push_neg; rw [and_comm]; exact Nat.two_le_iff x)})
          _ = p.parts.filter (fun x => x = 1 ∨ x = 0) + p.parts.filter fun x => x = 1 ∧ x = 0 := by
            nth_rw 3 [filter_eq_nil.mpr (fun a _ => by by_contra ha; nth_rw 2 [ha.1] at ha; linarith)]; simp;
          _ = p.parts.filter (· = 1) + p.parts.filter (· = 0) := by rw [Eq.comm, filter_add_filter (· = 1) (· = 0) p.parts]
          _ = p.parts.filter (· = 1) := by
            simp only [add_right_eq_self]; rw [filter_eq_nil]; intro a ha; by_contra hn; rw [hn] at ha;
            exact Eq.not_lt (rfl) (p.parts_pos (ha))
      rw [this, filter_eq', sum_replicate, smul_eq_mul, mul_one]
    | n + 2 =>
      rw [if_neg (by linarith), if_neg (by linarith)]
  nth_rw 4 [h_sum]; congr; rw [h]; congr;
  rw [Nat.sub_eq_iff_eq_add, add_comm, ← Multiset.sum_add]; congr;
  nth_rw 2 [h_sum]; simp_rw [Multiset.sum_add]; simp


lemma bij_conjClasses_partition : ∃ f : ConjClasses (SymmGroup n) → n.Partition, Function.Bijective f := by
  constructor; swap;
  . exact fun c => c.out.partition
  constructor;
  . intro c1 c2 h; simp only at h;
    rw [← @Quotient.out_eq _ _ c1, ← @Quotient.out_eq _ _ c2, ConjClasses.quotient_mk_eq_mk, ConjClasses.quotient_mk_eq_mk,
       @ConjClasses.mk_eq_mk_iff_isConj _ _ c1.out c2.out]
    exact partition_eq_of_isConj.mpr h
  intro p; let gt := (cananical_perm_of_parts (p.parts.toList.filter (· >= 2)) (List.finRange n))
  use ⟦gt⟧; simp
  have h_pconj : gt.partition = ⟦gt⟧.out.partition := by
    rw [← partition_eq_of_isConj, ← ConjClasses.mk_eq_mk_iff_isConj];
    nth_rw 2 [ConjClasses.mk]; simp only [Quotient.out_eq]; rfl
  suffices hn : gt.partition = p by exact h_pconj.symm.trans hn
  exact partition_eq_of_cananical_perm p



end SymmGroup
