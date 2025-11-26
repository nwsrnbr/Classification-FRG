import Mathlib

variable (a : ℕ → ℝ)
variable (p q A B: ℝ)

variable (h0 : a 0 = 1)
variable (h1 : a 1 = 2)
variable (hrec : ∀ n, a (n+2) = 2 * a (n+1) - a n)

theorem recurrence_induction (h0 : a 0 = 1) (h1 : a 1 = 2)
    (hrec : ∀ n, a (n+2) = 2 * a (n+1) - a n) : ∀ n, a n = n + 1 := by
  intro n
  induction' n using Nat.strongRec with n ih
  cases n with
  | zero => simpa
  | succ n =>
      cases n with
      | zero =>
          simp [h1]; norm_num
      | succ n =>
          -- use recurrence + ih n + ih (n+1)
          have h₁ := ih (n) (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
          have h₂ := ih (n+1) (Nat.lt_succ_self _)
          · simp [hrec, h₂, h₁]
            ring
