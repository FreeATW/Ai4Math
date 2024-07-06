import Mathlib.Tactic

-- informal answer

/-
Proof:
1. It suffice to show that, under the setup of this exercise, the order of $ba$ is less or equal to the order of $ab$. Apply this result for $a$ and $b$ once and for $b$ and $a$ once, we will get the desired equality.
2. First we show that $(ba) ^ {k+1} = b (ab)^k a$ by induction. The case $k = 0$ is trivial, and the case of $k + 1$ is a direct calculation $(ba) ^ {k+2} = (ba) ^ {k+1} ba = (b (ab)^k a) b a = b (ab)^{k+1} a$.
3. Now suppose the order of $ab$ is $n$, then $a (b (ab)^{n-1}) = (ab)^n = 1$.
4. Thus $(ba)^n = (b (ab)^{n-1}) a = 1$, since the left inverse is also the right inverse.
5. So order of $ba$ is less or equal to $n$. This finishes the proof.
-/

-- formal answer

/-
Let $a$ and $b$ be two elements of a finite group $G$. Show that the order of $ab$ equals to the order of $ba$.
-/
theorem GroupEx1 {G : Type u} [Group G] [Fintype G] (a b : G) : orderOf (a * b) = orderOf (b * a) := by
  -- It suffice to show that, under the setup of this exercise, the order of $ba$ is less or equal to the order of $ab$.
  suffices ∀ {G : Type u} [Group G] [Fintype G] (a b : G), orderOf (b * a) ≤ orderOf (a * b) by
    -- Apply this result for $a$ and $b$ once and for $b$ and $a$ once, we will get the desired equality.
    exact le_antisymm (this b a) (this a b)
  intro G _ _ a b
  -- First we show that $(ba) ^ {k+1} = b (ab)^k a$ by induction.
  have h1 : ∀ k, (b * a) ^ (k + 1) = b * (a * b) ^ k * a := by
    intro k
    induction k with
    -- The case $k = 0$ is trivial,
    | zero => group
    -- and the case of $k + 1$ is a direct calculation $(ba) ^ {k+2} = (ba) ^ {k+1} ba = (b (ab)^k a) b a = b (ab)^{k+1} a$.
    | succ k hk =>
      calc
      _ = (b * a) ^ (k + 1) * b * a := by
        rw [pow_succ, mul_assoc]
      _ = b * (a * b) ^ k * a * b * a := by rw [hk]
      _ = _ := by
        rw [pow_succ]
        group
  -- Suppose the order of $ab$ is $n$, then $a (b (ab)^{n-1}) = (ab)^n = 1$.
  have h : a * (b * (a * b) ^ (orderOf (a * b) - 1)) = 1 := by
    calc
    _ = (a * b) ^ (orderOf (a * b)) := by
      group
      congr
      norm_cast
      exact Nat.add_sub_of_le <| orderOf_pos (a * b)
    _ = 1 := by
      exact pow_orderOf_eq_one (a * b)
  -- Thus $(ba)^n = (b (ab)^{n-1}) a = 1$,
  have h' : (b * a) ^ (orderOf (a * b)) = 1 := by
    calc
    _ = (b * (a * b) ^ (orderOf (a * b) - 1)) * a := by
      simpa [Nat.sub_add_cancel <| orderOf_pos (a * b)] using h1 (orderOf (a * b) - 1)
    -- since the left inverse is also the right inverse.
    _ = 1 := by
      simp [← mul_eq_one_iff_inv_eq.mp h]
  -- So order of $ba$ is less or equal to $n$. This finishes the proof.
  exact orderOf_le_of_pow_eq_one (orderOf_pos (a * b)) h'
