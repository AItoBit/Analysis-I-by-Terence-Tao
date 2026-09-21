namespace Tao

/-- Peano naturals: `zero` is 0 and `succ n` is `n++`. -/
inductive N where
  | zero : N
  | succ : N → N

open N

/-- Definition 2.2.1:  0 + m = m  and  (n++) + m = (n + m)++ -/
def add : N → N → N
  | zero,   m => m
  | succ n, m => succ (add n m)

instance : Add N := ⟨add⟩

/-- 0 + m = m, by definition of addition -/
theorem zero_add' (m : N) : zero + m = m := rfl

/-- (n++) + m = (n + m)++, by definition of addition -/
theorem succ_add' (n m : N) : succ n + m = succ (n + m) := rfl

/-- Exercise 2.2.1: addition is associative. -/
theorem add_assoc (a b c : N) : (a + b) + c = a + (b + c) := by
  -- induction on a, keeping b and c fixed
  induction a with
  | zero =>
    -- Base case: (0 + b) + c = 0 + (b + c)
    calc (zero + b) + c = b + c := by rw [zero_add']        -- (0 + b) = b
      _ = zero + (b + c)        := by rw [zero_add']        -- 0 + (b + c) = b + c
  | succ a ih =>
    -- Inductive step: ((a++) + b) + c = (a++) + (b + c)
    calc (succ a + b) + c
        = (succ (a + b)) + c        := by rw [succ_add']    -- (a++ + b) = (a + b)++
      _ = succ ((a + b) + c)        := by rw [succ_add']    -- ((a + b)++ + c) = ((a + b) + c)++
      _ = succ (a + (b + c))        := by rw [ih]           -- inductive hypothesis
      _ = succ a + (b + c)          := by rw [succ_add']    -- right-hand side, definition of +

end Tao
