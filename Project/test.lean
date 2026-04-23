import Mathlib.Data.Matrix.Cartan

open CartanMatrix

def a' (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if h : i < n ∧ j < n then (A n) (i.castLT h.1) (j.castLT h.2)
    else if i = j then 2
    else if i = 0 ∧ j = n ∨ j = 0 ∧ i = n then -1
    else 0

theorem det_a' (n : ℕ) (h0 : ¬n = 0) (h1 : ¬n = 1) (v : Fin (n + 1) → ℤ := fun x ↦ 1) :
    (a' n).det = 0 := by
  sorry
