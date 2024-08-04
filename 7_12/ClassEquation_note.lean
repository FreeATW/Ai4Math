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
#synth SMul G G
instance : MulAction G G where
  one_smul := one_mul
  mul_smul := mul_assoc

-- variable {M : Type} [Fintype M]
-- #synth SMul (Equiv.Perm M) M

/- Trivial Action on Group -/
variable {G α : Type} [Group G]
-- #synth SMul G α
instance trivial_smul {G α : Type} [Group G] : SMul G α where
  smul := fun _ a => a

-- #synth SMul G α

instance trivial_mul_action {G α : Type} [Group G] : MulAction G α where
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl

/- Natural Action for Symmetric Group -/
variable {M : Type} [Fintype M]

-- #synth SMul (Equiv.Perm M) M
instance PermSmul : SMul (Equiv.Perm M) M where
  smul := fun g a => g a

instance PermNaturalAction : MulAction (Equiv.Perm M) M where
  one_smul := Equiv.Perm.one_apply
  mul_smul := Equiv.Perm.mul_apply

def MulAction.IsTransitive (G α : Type) [Group G] [MulAction G α] :=
  ∃ a : α, orbit G a = Set.univ

open MulAction

instance IsTrans.IsPretrans (h : IsTransitive G α) : IsPretransitive G α where
  exists_smul_eq := by
    intro x y
    simp [IsTransitive] at h
    obtain ⟨a,ha⟩ := h
    have hx : x ∈ orbit G a := (eq_comm.1 ha) ▸ (Set.mem_univ x)
    have hy : y ∈orbit G a := (eq_comm.1 ha) ▸ (Set.mem_univ x)
    rw [MulAction.mem_orbit_iff] at hx hy
    obtain ⟨gx,hx⟩ := hx
    obtain ⟨gy,hy⟩ := hy
    use gy*gx⁻¹
    rw [←hx, ←mul_smul, mul_assoc]
    simp only [mul_left_inv, mul_one, hy]

lemma IsTrans_of_IsPretrans [h : IsPretransitive G α] [hne : Nonempty α]: IsTransitive G α := by
  have := h.exists_smul_eq
  simp [IsTransitive]
  rcases hne with ⟨x⟩
  have := this x
  use x
  ext y
  constructor
  · intro; simp
  · intro; exact MulAction.mem_orbit_iff.2 (this y)

instance Equiv.Perm.IsPretransitive : IsPretransitive (Equiv.Perm (Fin n)) (Fin n) where
  exists_smul_eq := by
    intro x y
    use Equiv.swap x y
    rw [Equiv.Perm.smul_def (Equiv.swap x y) x]
    simp only [Equiv.Perm.smul_def, Equiv.swap_apply_left]

/- Conjugacy Action for Group -/
#check ConjAct

end MulAction

section Conj

#check IsConj.setoid

end Conj

/-!
=============================
  Review in Finset and Card
=============================
-/
section card

#check Fintype.card
#check Finset.card
#check Nat.card
#check Multiset.card

end card

/-!
=======================
  Sigma Type in Lean
=======================

-/
section SigmaType

#check Sigma

/-! A basic equivalence for Sigma Type-/
def sigmaFiberEquiv' {α β : Type*} (f : α → β) : (Σ y : β, { x // f x = y }) ≃ α where
  toFun := fun ⟨_, a, _⟩ => a
  invFun a := ⟨f a, a, rfl⟩
  left_inv := by
    rintro ⟨b, a, rfl⟩;
    simp only [Sigma.mk.inj_iff];
  right_inv := by intro x; simp
  -- fun _ => by rfl

namespace Finset

lemma sum_const' {α : Type*} (s : Finset α) (n : ℕ) : ∑ _x ∈ s, n = card s • n := by
  rw [← Multiset.sum_replicate s.card n, Finset.card_def, ← s.val.map_const n]; congr;

lemma card_eq_sum_ones' {α : Type*} (s : Finset α) : card s = ∑ x ∈ s, 1 := by
  simp only [sum_const, smul_eq_mul, mul_one]

end Finset

#check Sigma.instFintype
end SigmaType

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
open ConjClasses Fintype Classical BigOperators

#check Fintype.card

/-! **Statement** ``G`` is a ``Group`` -/
variable (G : Type*) [Group G]

/-!
Partition of Group by Conjugacy Classes
=======================================

Conjugacy classes form a partition of G, stated in terms of cardinality. -/
theorem sum_conjClasses_card_eq_card'  [Fintype G] :
    ∑ x : ConjClasses G, card x.carrier = card G := by
  /- To prove the lemma, it suffices to show that conjugacy classes do form a partition of G -/
  suffices h_equiv : (Σ x : ConjClasses G, x.carrier) ≃ G by
    rw [←Fintype.card_sigma]
    exact card_congr h_equiv
  -- simpa using (card_congr h_equiv)
  /- The proof of the equivalence is based on the bijection between the carrier of a conjugacy class and the conjugacy class itself -/
  simp only [carrier_eq_preimage_mk]
  exact Equiv.sigmaFiberEquiv ConjClasses.mk
  -- simpa [carrier_eq_preimage_mk] using Equiv.sigmaFiberEquiv ConjClasses.mk

/-!
Class Equation for Finite Groups
================================

The cardinality of a group is equal to the size of its center plus the sum of the size of all its nontrivial conjugacy classes. -/

#check mk_bijOn
theorem Group.nat_card_center_add_sum_card_noncenter_eq_card' [Fintype G]:
  card (Subgroup.center G) + ∑ x ∈ noncenter G, card x.carrier = card G := by
  /- Rewrite `G` as partitioned by its conjugacy classes -/
  nth_rw 2 [← sum_conjClasses_card_eq_card']
  /- Cancel out nontrivial conjugacy classes from summation -/
  rw [← Finset.sum_sdiff (ConjClasses.noncenter G).toFinset.subset_univ]; congr 1
  /- Now we can obtain the result by calculation -/
  calc
    _ = card ((noncenter G)ᶜ : Set (ConjClasses G)) :=
      card_congr ((mk_bijOn G).equiv _)
    _ = Finset.card (Finset.univ \ (noncenter G).toFinset) := by
      rw [← Set.toFinset_card, Set.toFinset_compl, Finset.compl_eq_univ_sdiff]
    _ = ∑ x ∈ Finset.univ \ (noncenter G).toFinset, 1 :=
      Finset.card_eq_sum_ones _
    _ = ∑ x ∈ Finset.univ \ (noncenter G).toFinset, card x.carrier := by
      rw [Finset.sum_congr rfl _];
      rintro ⟨g⟩ hg; simp at hg
      rw [← Set.toFinset_card, eq_comm, Finset.card_eq_one]
      exact ⟨g, by
        rw [← Set.toFinset_singleton];
        exact Set.toFinset_congr (Set.Subsingleton.eq_singleton_of_mem hg mem_carrier_mk)⟩
