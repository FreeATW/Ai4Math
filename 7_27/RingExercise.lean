import Mathlib

/-- Suppose $R$ is a ring with unity and $I, J, K$ are ideals of $R$.  Prove that $I \subseteq J \cup K \iff I \subseteq J \vee I \subseteq K$.-/
theorem Ideal.subset_union₁ {R : Type*} [CommRing R] {I J K : Ideal R} :
    (I : Set R) ⊆ J ∪ K ↔ I ≤ J ∨ I ≤ K := by
    constructor
    -- To prove $I \subseteq J \cup K \implies I \subseteq J \vee I \subseteq K$
    -- We just need to prove if $I \subsetneq J$, then $I \subseteq K$, which means if there exists $x \in I$ while $x \notin J$, then $\forall y \in I, y\in K$.
    · intro h
      rw [or_iff_not_imp_left, SetLike.not_le_iff_exists]
      intro ⟨x, xi, xnj⟩ y yi
      -- Since $x, y\in I$, $x+y\in I$. By $I \subseteq J \cup K$, we can deduce that $x + y \in J$ or $x + y \in K$.
      have : x + y ∈ I := (Submodule.add_mem_iff_right I xi).mpr yi
      rcases h this with h' | h'
      -- If $x + y \in J$, we prove by contradiction. If $y \notin K$, then $y \in J$, which leads to $x \in J$ since $x + y \in J$. That contradicts with the hypothesis $x\notin J$.
      · by_contra ynk
        have yj : y ∈ J := (h yi).resolve_right ynk
        have xj : x ∈ J := (add_mem_cancel_right yj).mp h'
        exact xnj xj
      -- If $x + y \in K$, since $x \in K$, we have $y \in K$.
      · have xk : x ∈ K := (h xi).resolve_left xnj
        exact (add_mem_cancel_left xk).mp h'
    -- $I\subseteq J \vee I \subseteq K\implies I \subseteq J \cup K$ is trivial since $I$ is a subset of one member of the union.
    · intro h
      rcases h with ij | ik
      · exact Set.subset_union_of_subset_left ij K
      · exact Set.subset_union_of_subset_right ik J

/-- Suppose $R$ is a commutative ring with unity. $I, A, B$ are ideals of $R$. $\{P_{i}\}_{i\in \Lambda}$ are a finite set of prime ideals of $R$. Prove that $I \subseteq A\cup B \cup \bigcup\limits_{i\in \Lambda}P_{i}\iff I\subseteq A \vee I \subseteq B \vee \exists i\in \Lambda, I\subseteq P_{i}$.-/
theorem subset_union_prime'₀ {R : Type*} [CommRing R] {s : Finset ι} {f : ι → Ideal R} {a b : ι}
    (hp : ∀ i ∈ s, Ideal.IsPrime (f i)) {I : Ideal R} :
    ((I : Set R) ⊆ f a ∪ f b ∪ ⋃ i ∈ s, f i) ↔ I ≤ f a ∨ I ≤ f b ∨ ∃ i ∈ s, I ≤ f i := by
    -- $I\subseteq A \vee I \subseteq B \vee \exists i\in \Lambda, I\subseteq P_{i}$ implies $\subseteq A\cup B \cup \bigcup\limits_{i\in \Lambda}P_{i}$ since $I$ is a subset of one member of the union. So we only need to prove $I \subseteq A\cup B \cup \bigcup\limits_{i\in \Lambda}P_{i}\implies I\subseteq A \vee I \subseteq B \vee \exists i\in \Lambda, I\subseteq P_{i}$.
    suffices ((I : Set R) ⊆ f a ∪ f b ∪ ⋃ i ∈ (↑s : Set ι), f i) → I ≤ f a ∨ I ≤ f b ∨ ∃ i ∈ s, I ≤ f i from ⟨this, by
      intro h
      rcases h with h | h | h
      · apply Set.Subset.trans h
        apply Set.Subset.trans (Set.subset_union_left _ (f b))
        apply Set.subset_union_left
      · apply Set.Subset.trans h
        apply Set.Subset.trans (Set.subset_union_right (f a) _)
        apply Set.subset_union_left
      · refine Set.Subset.trans ?_ (Set.subset_union_right _ _)
        rcases h with ⟨i, is, ih⟩
        exact Set.subset_iUnion₂_of_subset i is ih
    ⟩
    -- We do induction on the cardinality of the finite set $\Lambda$. When $\Lambda$ is an empty set, the situation is the same with Ideal.subset_union.
    generalize hn : s.card = n
    intro h
    induction' n with n ih generalizing a b s
    · rw [Finset.card_eq_zero] at hn
      subst hn
      clear hp
      simp only [Finset.coe_empty, Set.mem_empty_iff_false, Set.iUnion_of_empty, Set.iUnion_empty,
        Set.union_empty, Finset.not_mem_empty, false_and, exists_false, or_false] at h ⊢
      exact Ideal.subset_union.mp h
    -- Suppose for any $n(n\ge 1)$ prime ideals the hypothesis holds true, then for $\{P_{i}\}_{i=1}^{n+1}$, we take a subset $\{P_{i}'\}_{i=1}^{n}$ with $n$ elements. Then we do some case analysis.
    · classical
      replace hn : ∃ (i : ι) (t : Finset ι), i ∉ t ∧ insert i t = s ∧ t.card = n := Finset.card_eq_succ.mp hn
      rcases hn with ⟨i, t, int, rfl, ht⟩
      replace hp : (f i).IsPrime ∧ ∀ j ∈ t, (f j).IsPrime:= (t.forall_mem_insert _ _).mp hp
      rcases hp with ⟨ip, hp⟩
      --  If $\exists 1\le j\le n, P_{j}'\subseteq P_{n+1}'$, then $\bigcup\limits_{1\le i\le n+1}P_{i}=\bigcup\limits_{1\le i \le n+1, i\ne j}P_{i}'$. We prove it by inductive hypothesis.
      by_cases Ht : ∃ j ∈ t, f j ≤ f i
      · rcases Ht with ⟨j, jt, hj⟩
        obtain ⟨u, jnu, rfl⟩ : ∃ (u : Finset ι), j ∉ u ∧ insert j u = t  := by
          use t.erase j
          simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true,
            true_and]
          exact Finset.insert_erase jt
        have hp' : ∀ k ∈ insert i u, (f k).IsPrime := by
          simp only [Finset.mem_insert, forall_eq_or_imp]
          constructor
          · exact ip
          · exact fun a au => hp _ (Finset.mem_insert_of_mem au)
        have inu : i ∉ u := fun iu => int (Finset.mem_insert_of_mem iu)
        have iun : (insert i u).card = n := by
          rw [Finset.card_insert_of_not_mem, ht.symm]
          symm
          apply Finset.card_insert_of_not_mem jnu
          exact inu
        have h' : (I : Set R) ⊆ (f a) ∪ (f b) ∪ ⋃ k ∈ (insert i u), (f k) := by
          simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe,
            Set.iUnion_iUnion_eq_or_left, Finset.mem_insert] at h ⊢
          rw [← Set.union_assoc (f i : Set R)] at h
          erw [Set.union_eq_self_of_subset_right hj] at h
          exact h
        specialize ih hp' iun h'
        rcases ih with ih | ih | ⟨k, ik, hk⟩
        · left; exact ih
        · right; left; exact ih
        · right; right
          use k
          constructor
          · apply Finset.mem_insert.mpr
            rw [Finset.mem_insert] at ik
            rcases ik with ik | ik
            · left; exact ik
            · right; exact Finset.mem_insert_of_mem ik
          · exact hk
      -- Else if $A \subseteq P_{n+1}'$, then we have $I \subseteq P_{n+1}'\cup B \cup \bigcup\limits_{1\le i \le n}P_{i}'$. For the generality of $A$ in the inductive hypothesis, we have $I \subseteq P_{n+1}'\vee I\subseteq B \vee \exists 1\le i\le n, I \subseteq P_{i}'$, which directly leads to $I\subseteq A \vee I \subseteq B \vee \exists 1 \le i \le n+1, I \subseteq P_{i}$.
      by_cases Ha : f a ≤ f i
      · have h' : (I : Set R) ⊆ f i ∪ f b ∪ ⋃ j ∈ (t : Set ι), f j := by
          rw [Finset.coe_insert, Set.biUnion_insert, ← Set.union_assoc,
            Set.union_right_comm (f a : Set R)] at h
          rw [Set.union_eq_self_of_subset_left Ha] at h
          exact h
        specialize ih hp ht h'
        rcases ih with ih | ih | ⟨i, it, hit⟩
        · right; right
          use i
          exact ⟨Finset.mem_insert_self i t, ih⟩
        · right; left
          exact ih
        · right; right
          use i
          exact ⟨Finset.mem_insert_of_mem it, hit⟩
      -- Else if $B \subseteq P_{n+1}'$, the proof is the same.
      by_cases Hb : f b ≤ f i
      · have h' : (I : Set R) ⊆ f a ∪ f i ∪ ⋃ j ∈ (t : Set ι), f j := by
          rw [Finset.coe_insert, Set.biUnion_insert, ← Set.union_assoc,
            Set.union_right_comm (f a : Set R)] at h
          rw [Set.union_assoc (f a : Set R), Set.union_eq_self_of_subset_right Hb] at h
          exact h
        specialize ih hp ht h'
        rcases ih with ih | ih | ⟨i, it, hit⟩
        · left
          exact ih
        · right; right
          use i
          exact ⟨Finset.mem_insert_self i t, ih⟩
        · right; right
          use i
          exact ⟨Finset.mem_insert_of_mem it, hit⟩
      -- Else if $I \subseteq P_{n+1}'$, we get $\exists 1\le i\le n+1, I \subseteq P_{i}= P_{n+1}'$.
      by_cases Hi : I ≤ f i
      · right; right
        use i
        exact ⟨Finset.mem_insert_self i t, Hi⟩
      -- Else, we have $I \subsetneq A \land I \subsetneq B \land I \subsetneq P_{n+1}' \land A \subsetneq P_{n+1}' \land B\subsetneq P_{n+1}' \land \forall 1\le i \le n, P_{i}'\subsetneq P_{n+1}'$. Since $P_{n+1}'$ is a prime ideal, we can deduce that $\lnot I\cap A\cap B \cap \bigcap_\limits{1\le i \le n}P_{i}'\subseteq P_{n+1}'$, which means there exists $r\in I\cap A\cap B \cap \bigcap\limits_{1\le i \le n}P_{i}'$ and $r \notin P_{n+1}'$.
      have : ¬I ⊓ f a ⊓ f b ⊓ t.inf f ≤ f i := by
        simp only [ip.inf_le, ip.inf_le', not_or]
        exact ⟨⟨⟨Hi, Ha⟩, Hb⟩, Ht⟩
      rcases Set.not_subset.mp this with ⟨r, ⟨⟨⟨hrI, hra⟩, hrb⟩, hr⟩, hrn⟩
      -- If $I \subseteq A\cup B \cup \bigcup\limits_{1\le i\le n}P_{i}'$, it is just the case of the inductive hypothesis. We will prove that this is the only reasonable case, otherwise we will end up with contradiction.
      by_cases HI : (I : Set R) ⊆ f a ∪ f b ∪ ⋃ j ∈ t, f j
      · specialize ih hp ht HI
        rcases ih with ih | ih | ⟨k, kt, hkt⟩
        · left
          exact ih
        · right; left
          exact ih
        · right; right
          use k
          exact ⟨Finset.mem_insert_of_mem kt, hkt⟩
      exfalso
      -- If $I \subsetneq A\cup B \cup \bigcup\limits_{1\le i\le n}P_{i}'$, we have $s\in I$ while $s\notin A \land s \notin B \land \forall 1\le i \le n, s \notin P_{i}'$. Since $I$ is contained in the union, $s \in P_{n+1}'$.
      rcases Set.not_subset.mp HI with ⟨s, hsI, hs⟩
      rw [Finset.coe_insert, Set.biUnion_insert] at h
      have hsi : s ∈ f i := ((h hsI).resolve_left (mt Or.inl hs)).resolve_right (mt Or.inr hs)
      -- Now we get $r + s \in I$. Clearly $r + s\notin A\land r+s\notin B\land \forall 1\le i \le n, r+s \notin P_{i}'$, so $r +s \in P_{n+1}'$, which leads to $r\in P_{n+1}'$ since $s \in P_{n+1}'$. That contradicts with $r \notin P_{n+1}'$.
      have rsI : r + s ∈ I := I.add_mem hrI hsI
      simp only [Set.mem_union, SetLike.mem_coe, Set.mem_iUnion, exists_prop, not_or, not_exists,
        not_and] at hs
      rcases h rsI with (⟨ha | hb⟩ | hi | ht)
      · exact hs.1.1 ((Submodule.add_mem_iff_right (f a) hra).mp ha)
      · exact hs.1.2 ((Submodule.add_mem_iff_right (f b) hrb).mp hb)
      · exact hrn ((Submodule.add_mem_iff_left (f i) hsi).mp hi)
      · simp only [Finset.mem_coe, Set.mem_iUnion, SetLike.mem_coe, exists_prop] at ht
        rcases ht with ⟨k, ik, rsk⟩
        simp only [Submodule.finset_inf_coe, Set.mem_iInter, SetLike.mem_coe] at hr
        exact hs.2 k ik ((Submodule.add_mem_iff_right (f k) (hr k ik)).mp rsk)

example {R : Type*} [CommRing R] {A : Ideal R} {s : Finset ι} (hs : s.card ≥ 1) {P : ι → Ideal R} (hp : ∀ i ∈ s, (P i).IsPrime) : (A : Set R) ⊆ ⋃ i ∈ (s : Finset ι), (P i) → ∃ i ∈ s, A ≤ P i := by
  by_cases Hn : s.card = 1
  · rw [Finset.card_eq_one] at Hn
    rcases Hn with ⟨a, ha⟩
    subst ha
    simp only [Finset.card_singleton, ge_iff_le, le_refl, Finset.mem_singleton, forall_eq,
      Finset.coe_singleton, Set.mem_singleton_iff, Set.iUnion_iUnion_eq_left,
      SetLike.coe_subset_coe, exists_eq_left, imp_self]
  replace hn : s.card >= 2 := Nat.lt_of_le_of_ne hs fun a => Hn (id (Eq.symm a))
  classical
  sorry


example {R : Type*} [CommRing R] {A : Ideal R} {s : Finset ι} (hs : s.card ≥ 1) {P : ι → Ideal R} (hp : ∀ i ∈ s, (P i).IsPrime) : (A : Set R) ⊆ ⋃ i ∈ (s : Finset ι), (P i) → ∃ i ∈ s, A ≤ P i := by
  intro h
  generalize hn : s.card = n
  induction' n with n ih generalizing s
  · linarith
  · classical
    have ht : ∃ (i : ι) (t : Finset ι), i ∉ t ∧ insert i t = s ∧ t.card = n := Finset.card_eq_succ.mp hn
    rcases ht with ⟨i, t, int, rfl, tcn⟩
    simp only [Finset.mem_insert, forall_eq_or_imp, Set.iUnion_iUnion_eq_or_left,
      exists_eq_or_imp] at hp h ⊢
    by_cases Htc : t.card < 1
    · sorry
    push_neg at Htc
    by_cases Hi : A ≤ P i
    · left; exact Hi
    by_cases Hn : ∃ j ∈ t, P j ≤ P i
    · sorry
    have : ¬A ⊓ t.inf P ≤ P i := by
      sorry
    rcases Set.not_subset.mp this with ⟨r, hr₁, hr₂⟩
    simp only [Submodule.inf_coe, Submodule.finset_inf_coe, Set.mem_inter_iff, SetLike.mem_coe,
      Set.mem_iInter] at hr₁
    by_cases Ht : (A : Set R) ⊆ ⋃ j ∈ t, P j
    · right
      specialize ih Htc hp.2 Ht tcn
      exact ih
    exfalso
    sorry


theorem Ideal.subset_union_prime₀ {R : Type*} [CommRing R] {s : Finset ι} {f : ι → Ideal R} (a b : ι)
    (hp : ∀ i ∈ s, i ≠ a → i ≠ b → IsPrime (f i)) {I : Ideal R} :
    ((I : Set R) ⊆ ⋃ i ∈ (↑s : Set ι), f i) ↔ ∃ i ∈ s, I ≤ f i := sorry
