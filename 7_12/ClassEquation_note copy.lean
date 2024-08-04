import Mathlib.Algebra.Group.ConjFinite
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.ClassEquation
import Mathlib.GroupTheory.GroupAction.ConjAct
/-!
########################################################
  Group Actions, Conjugacy Classes, and Class Equation
########################################################

- Basic API of Group Actions
- Construct of Sum Type and lemmas
- Multiset.card and Finset.card, and card
- Summation of Finset
- Proof of Class Equation

-/

/-!
=======================
  Finset and Multiset
=======================

Some basic lemmas about Finset and Multiset are provided here.

-/

section MulAction

variable {G : Type} [Group G]

/- Left Action by Group Multiplication -/

/- Trivial Action on Group -/

/- Natural Action for Symmetric Group -/

/- Conjugacy Action for Group -/

end MulAction

section Conj

#check IsConj.setoid

end Conj

/-!
=======================
  Sigma Type in Lean
=======================

-/
section SigmaType

#check Sigma

/-! A basic equivalence for Sigma Type-/
def sigmaFiberEquiv' {α β : Type*} (f : α → β) : (Σ y : β, { x // f x = y }) ≃ α := sorry
namespace Finset

lemma sum_const' {α : Type*} (s : Finset α) (n : ℕ) : ∑ _x ∈ s, n = card s • n := sorry

lemma card_eq_sum_ones' {α : Type*} (s : Finset α) : card s = ∑ x ∈ s, 1 := sorry

end Finset

#check Sigma.instFintype
end SigmaType

section card

end card

/-!
===========================
  Proof of Class Equation
===========================

Class equation is stated as cardinality of a group is equal to the size of its center plus the sum of the size of all its nontrivial conjugacy classes.

.. default-role:: lean4

-/

/-! **Mathlib Version** of ``ClassEquation`` -/
#check Group.nat_card_center_add_sum_card_noncenter_eq_card

/-!
Class Equation theorem should be proved in the scope of ``Classical``. In this circumstance, every proposition is decidable. To avoid unnecessary coersion, we use ``Fintype.card`` to measure the size of a ``Fintype``.
-/
open ConjClasses Fintype Classical

#check Fintype.card

/-! **Statement** ``G`` is a ``Group`` -/
variable (G : Type*) [Group G]

/-!
Partition of Group by Conjugacy Classes
=======================================

Conjugacy classes form a partition of G, stated in terms of cardinality. -/
theorem sum_conjClasses_card_eq_card'  [Fintype G] :
    ∑ x : ConjClasses G, card x.carrier = card G := sorry
  -- simpa [carrier_eq_preimage_mk] using Equiv.sigmaFiberEquiv ConjClasses.mk

/-!
Class Equation for Finite Groups
================================

The cardinality of a group is equal to the size of its center plus the sum of the size of all its nontrivial conjugacy classes. -/
theorem Group.nat_card_center_add_sum_card_noncenter_eq_card' [Fintype G]:
  card (Subgroup.center G) + ∑ x ∈ noncenter G, card x.carrier = card G := by
  /- Rewrite `G` as partitioned by its conjugacy classes -/
  nth_rw 2 [← sum_conjClasses_card_eq_card']
  /- Cancel out nontrivial conjugacy classes from summation -/
  rw [← Finset.sum_sdiff (ConjClasses.noncenter G).toFinset.subset_univ]; congr 1
  /- Now we can obtain the result by calculation -/
  sorry
