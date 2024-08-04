import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!

============================
  Notes for Symmetry Group
============================

-/

/-!
Quotient Type
-------------
A typical idea to construct new map.
Example: Coset, ℤ/nℤ, ConjClasses, G-orbit etc.

-/
namespace Quotient

variable (G : Type*) (X : Type*) [Group G] [MulAction G X]

def orbit_setoid : Setoid X where
  r := fun x y => ∃ g : G, g • x = y
  iseqv := by
    constructor
    . exact fun x => ⟨1, MulAction.one_smul x⟩
    . intro x y ⟨g, hg⟩; exact ⟨g⁻¹, by rw [←hg, inv_smul_smul]⟩
    intro x y z ⟨g, hg⟩ ⟨h, hh⟩;
    exact ⟨h * g, by rw [mul_smul, ←hh, ←hg, smul_smul]⟩

def orbit_coset := Quotient (orbit_setoid G X : Setoid X)

end Quotient

/-!

Lean's Characterization of Finiteness
-------------------------------------

1. Decidability and Representation
2. List -> Multiset -> Finset

-/
namespace List

#check List

def l1 : List ℕ := [2, 5, 3, 3, 5, 8, 11]
def l1' : List ℕ := [5, 2, 3, 3, 5, 8, 11]

#eval l1
#eval l1 = l1'

#check Multiset
/-! Use Quotient type to achive -/
#check Multiset.ofList
#check Multiset.toList

def ml1 := Multiset.ofList l1

#eval ml1
#eval Multiset.ofList l1 = Multiset.ofList l1'

#check Finset
def fml1 := ml1.toFinset

/-! Derivation of Partition of ℕ  -/
@[ext]
structure MyPartition (n : ℕ) where
  parts : Multiset ℕ
  parts_pos : ∀ p ∈ parts, 0 < p
  parts_sum : parts.sum = n

instance : DecidableEq (MyPartition n) := fun p1 p2 =>
  decidable_of_iff _ (MyPartition.ext_iff p1 p2).symm

unsafe instance : Repr (MyPartition n) where
  reprPrec := fun p _ => repr (Multiset.sort (· >= ·) p.parts)
    ++ " Partition of " ++ repr n

def partition1 : MyPartition 7 where
  parts := [2, 2, 3]
  parts_pos := by decide
  parts_sum := by decide

def partition2 : MyPartition 7 := ⟨[3, 2, 2], by decide, by decide⟩

#eval partition1
#eval partition1 = partition2

end List



/-!
Symmetry Group by Equivalence
-----------------------------
-/
def MySymmGroup (n : ℕ) := Equiv (Fin n) (Fin n)

namespace MySymmGroup

variable {n : ℕ}

instance : Mul (MySymmGroup n) where
  mul σ τ := τ.trans σ

instance : Group (MySymmGroup n) where
  mul_assoc σ τ μ := (Equiv.trans_assoc μ τ σ).symm
  one_mul σ := Equiv.trans_refl σ
  mul_one σ := Equiv.refl_trans σ
  mul_left_inv σ := Equiv.self_trans_symm σ

instance : SMul (MySymmGroup n) (Fin n) where
  smul σ i := σ.toFun i

instance : MulAction (MySymmGroup n) (Fin n) where
  one_smul := Equiv.refl_apply
  mul_smul _ _ := Equiv.trans_apply _ _

end MySymmGroup


open Equiv.Perm
abbrev SymmGroup (n : ℕ) := Equiv.Perm <| Fin n
variable {n : ℕ}

def toPerm (σ : SymmGroup n) : Equiv.Perm (Fin n) := σ

instance : Setoid (SymmGroup n) := IsConj.setoid (SymmGroup n)

instance : Fintype (SymmGroup n) := inferInstance

instance : MulAction (SymmGroup n) (Fin n) where
  one_smul := Equiv.Perm.one_apply
  mul_smul := Equiv.Perm.mul_apply

/-!
Repr of Symmetry Group
----------------------
Cycle Notation
-/

namespace ConcreteSymmGroup

#check Cycle
#eval ([1, 2, 3, 4] : Cycle ℕ)
#eval ([1, 2, 3, 4] : Cycle ℕ) = ([2, 3, 4, 1] : Cycle ℕ)

def p1 : SymmGroup 3 := ⟨![1, 2, 0], ![2, 0, 1], by decide, by decide⟩
def p2 : SymmGroup 3 := ⟨![0, 2, 1], ![0, 2, 1], by decide, by decide⟩
def p12 : SymmGroup 4 := c[0, 3, 1]
def p21 : SymmGroup 4 := c[2, 1]

#check repr_perm
#check Fintype.decidableEqEquivFintype


#eval p12 * p21
#eval (@Finset.univ (SymmGroup 3) _).image fun σ => σ.partition.parts
#eval (Subgroup.center (SymmGroup 3)).carrier.toFinset
#eval @decomposeFin 3 p12

end ConcreteSymmGroup

/-! Small Lemma -/
lemma Equiv.Perm.orderOf_swap : ∀ (n : ℕ) (i j : Fin n), orderOf (Equiv.swap i j) <= 2 := by
  intros n i j
  exact orderOf_le_of_pow_eq_one (by decide)
    (by rw [pow_two, ext_iff]; intro x; rw [mul_apply (Equiv.swap i j) (Equiv.swap i j) x]; simp)

/-!
Exercises for Symmetry Groups
-----------------------------
-/
namespace Exercise

#check Nat.card_eq_fintype_card
#check Fintype.card_perm
#check Fintype.card_fin

/- Example 1.33(2) A Demonstration for case-by-case proof -/
lemma S3_not_cyclic : ¬ IsCyclic (SymmGroup 3) := by
  intro h
  rw [isCyclic_iff_exists_ofOrder_eq_natCard] at h
  have symm3_card : Nat.card (SymmGroup 3) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  rw [symm3_card] at h
  contrapose! h
  intro g
  fin_cases g
  . simp
  . simp; sorry
  . simp; sorry
  . simp; sorry
  . simp; sorry
  simp; sorry

/- Example 1.33(2) Genralized version -/
lemma S3_not_cyclic' : ¬ IsCyclic (SymmGroup 3) := by
  intro h
  let h_comm : CommGroup (SymmGroup 3) := @IsCyclic.commGroup _ _ h
  let x1 : SymmGroup 3 := c[0, 1]
  let x2 : SymmGroup 3 := c[1, 2]
  have h_eq : x1 * x2 = x2 * x1 := mul_comm x1 x2
  have h_ne : x1 * x2 ≠ x2 * x1 := by unfold_let; decide
  exact h_ne h_eq

/- Example 1.12(2) Computational verification -/
#eval @Finset.univ (MulAction.stabilizer (SymmGroup 4) (0 : Fin 4)).carrier _
#eval @Finset.univ (SymmGroup 3) _

/- Example 1.12(2) Generalized version -/
def Fin_of_Fin_succ_stablizer : MulAction.stabilizer (SymmGroup n.succ) (0 : Fin n.succ) ≃ SymmGroup n where
  toFun s := (decomposeFin s.1).2
  invFun σ := ⟨decomposeFin.symm (0, σ),
    by rw [MulAction.mem_stabilizer_iff]; simp;⟩
  left_inv s := by
    have : (decomposeFin s.1).1 = 0 := by
      simp [decomposeFin]; let h := s.2; rw [MulAction.mem_stabilizer_iff] at h; exact h
    simp_rw [← this, Prod.eta, Equiv.symm_apply_apply]
  right_inv σ := by simp_rw [Equiv.apply_symm_apply]

/- Example 1.12(2) Proof by generalizarion-/
def S4_stablizer_eq_S3 : MulAction.stabilizer (SymmGroup 4) (0 : Fin 4) ≃ SymmGroup 3 :=
  Fin_of_Fin_succ_stablizer

end Exercise

/-!
Induction Techniques for Symmetry Groups
-/
namespace CycleInduction

open Equiv
variable {α : Type*} [Fintype α] [DecidableEq α]

#check Perm.cycle_induction_on
#check Perm.IsCycle.conj
#check Perm.Disjoint.conj
#check Perm.Disjoint.cycleType
#check Perm.Disjoint.card_support_mul

theorem cycleType_conj {σ τ : Perm α} : (τ * σ * τ⁻¹).cycleType = σ.cycleType := by
  induction' σ using Perm.cycle_induction_on with σ hσ σ π hσπ hσ h1 h2
  . simp
  . rw [Perm.IsCycle.cycleType hσ, (Perm.IsCycle.conj hσ).cycleType]; simp;
  . rw [← conj_mul, Perm.Disjoint.cycleType hσπ, (Perm.Disjoint.conj hσπ _).cycleType];
    rw [h1, h2]

theorem cycleType_sum {σ : Perm α} : σ.cycleType.sum = σ.support.card := by
  induction' σ using Perm.cycle_induction_on with σ hσ σ π hσπ hσ h1 h2
  . simp
  . rw [Perm.IsCycle.cycleType hσ, Multiset.coe_singleton, Multiset.sum_singleton];
  rw [hσπ.cycleType, Multiset.sum_add, h1, h2, hσπ.card_support_mul]

end CycleInduction

/-!
Correspondence between Conjugacy Classes and Partitions
-------------------------------------------------------
-/
section ConjPartition

#check Equiv.Perm.cycleType_conj
#check isConj_of_cycleType_eq
#check isConj_iff_cycleType_eq
#check partition_eq_of_isConj

lemma bij_conjClasses_partition : ∃ f : ConjClasses (SymmGroup n) → n.Partition, Function.Bijective f := sorry

end ConjPartition
