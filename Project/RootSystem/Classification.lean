/-

import Mathlib.Tactic
import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Project.ReflectionGroup.Basic
import Project.ReflectionGroup.CartanMatrix
import Project.ReflectionGroup.Determinant
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.Algebra.Lie.CartanMatrix
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 1000000

variable {ι E F : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] [SeminormedAddCommGroup F]
  [InnerProductSpace ℝ F] (Φ : RootSystem ι ℝ E F) [Φ.IsReduced]

variable [Φ.IsCrystallographic]

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable (P : RootPairing ι R M N) [P.IsCrystallographic] {b : P.Base}

universe u

namespace MyCartanMatrix

open Matrix

section SubGraph

variable {n : ℕ}

/-- n 次正方行列 C から最後の行と列を取り除いた n 次正方行列 -/
def PrincipalSubmatrix (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) :=
  C.submatrix (fun i => Fin.castSucc i) (fun j => Fin.castSucc j)

def LowerLabel (C : Matrix (Fin n) (Fin n) ℤ) :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
    else
      match C i j with
      | -1 => -1
      | -2 => -1
      | -3 => -2
      | _ => 0

theorem sub_of_pos_def (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) (h : (SymmMatrix C).PosDef) :
    (SymmMatrix (PrincipalSubmatrix C)).PosDef := by
  contrapose! h
  simp [PosDef] at *
  intro h'
  have : (SymmMatrix (PrincipalSubmatrix C)).IsHermitian := by
    simp [IsHermitian, SymmMatrix_trans_rfl]
  rcases h this with ⟨x, xnz, hx⟩
  let y : Fin (n + 1) → ℝ := fun i ↦ if h : i < n then |(x (i.castLT h))| else 0
  use y
  split_ands
  · contrapose! xnz
    simp [funext_iff]
    intro i
    rw [← abs_eq_zero]
    calc
      _ = y (i.castLT (by omega)) := by simp [y]; aesop
      _ = 0 := by simp [xnz]
  · calc
      _ = ∑ i, ∑ j, y i * (SymmMatrix C i j * y j) := by
        simp [mulVec, dotProduct, Finset.mul_sum]
      _ = ∑ (i : Fin n), ∑ (j : Fin n),
          |x i| * (SymmMatrix C (i.castLE (by omega)) (j.castLE (by omega)) * |x j|) := by
        simp [Fin.sum_univ_succAbove (x := Fin.last n)]
        simp [Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.castLT, y]
      _ = ∑ (i : Fin n), ∑ (j : Fin n),
          SymmMatrix C (i.castLE (by omega)) (j.castLE (by omega)) * |x i * x j| := by
        simp [abs_mul, ← mul_assoc, mul_comm]
      _ ≤ ∑ (i : Fin n), ∑ (j : Fin n),
          SymmMatrix C (i.castLE (by omega)) (j.castLE (by omega)) * (x i * x j) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        by_cases hij : i = j
        · simp [hij]
        · apply mul_le_mul_of_nonpos_left
          · apply le_abs_self
          · simp [SymmMatrix]
            split_ifs
            · simp
      _ = ∑ (i : Fin n), ∑ (j : Fin n),
          x i * (SymmMatrix C (i.castLE (by omega)) (j.castLE (by omega)) * x j) := by
        simp [← mul_assoc, mul_comm]
      _ = x ⬝ᵥ SymmMatrix (PrincipalSubmatrix C) *ᵥ x := by
        simp [mulVec, dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _
        apply Finset.sum_congr rfl; intro j _
        congr 1
        congr 1
        simp [SymmMatrix, PrincipalSubmatrix, Fin.castSucc, Fin.castAdd, Fin.castLE]
        grind
      _ ≤ 0 := by assumption

theorem sub_of_pos_def' (C : Matrix (Fin n) (Fin n) ℤ) (h : (SymmMatrix C).PosDef) :
    (SymmMatrix (LowerLabel C)).PosDef := by
  contrapose! h
  simp [PosDef] at *
  intro h'
  have : (SymmMatrix (LowerLabel C)).IsHermitian := by
    simp [IsHermitian, SymmMatrix_trans_rfl]
  rcases h this with ⟨x, xnz, hx⟩
  let y : Fin n → ℝ := fun i ↦ |x i|
  use y
  split_ands
  · contrapose! xnz
    simp [funext_iff]
    intro i
    rw [← abs_eq_zero]
    calc
      _ = y i := by simp [y]
      _ = 0 := by simp [xnz]
  · calc
      _ = ∑ i, ∑ j, y i * (SymmMatrix C i j * y j) := by
        simp [mulVec, dotProduct, Finset.mul_sum]
      _ = ∑ (i : Fin n), ∑ (j : Fin n), |x i| * (SymmMatrix C i j * |x j|) := by
        simp [y]
      _ ≤ ∑ (i : Fin n), ∑ (j : Fin n), |x i| * (SymmMatrix (LowerLabel C) i j * |x j|) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        apply mul_le_mul_of_nonneg_left
        apply mul_le_mul_of_nonneg_right
        · simp [SymmMatrix, LowerLabel]
          split_ifs
          · rfl
          · aesop
          · have : √2 * √3 = √6 := by rw [← Real.sqrt_mul zero_le_two]; norm_num
            split
            <;> split
            <;> simp [*, mul_comm]
            <;> norm_num
        all_goals apply abs_nonneg
      _ = ∑ (i : Fin n), ∑ (j : Fin n), SymmMatrix (LowerLabel C) i j * |x i * x j| := by
        simp [abs_mul, ← mul_assoc, mul_comm]
      _ ≤ ∑ (i : Fin n), ∑ (j : Fin n), SymmMatrix (LowerLabel C) i j * (x i * x j) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        by_cases hij : i = j
        · simp [hij]
        · apply mul_le_mul_of_nonpos_left
          · apply le_abs_self
          · simp [SymmMatrix]
            split_ifs
            · simp
      _ = ∑ (i : Fin n), ∑ (j : Fin n), x i * (SymmMatrix (LowerLabel C) i j * x j) := by
        simp [← mul_assoc, mul_comm]
      _ ≤ x ⬝ᵥ SymmMatrix (LowerLabel C) *ᵥ x := by
        simp [mulVec, dotProduct, Finset.mul_sum]
      _ ≤ 0 := by assumption

end SubGraph

namespace RootPairing

variable {ι E F : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] [SeminormedAddCommGroup F]
  [InnerProductSpace ℝ F]

theorem classification (Φ : RootSystem ι ℝ E F) {b : Φ.Base} [Φ.IsCrystallographic] (h_irred : Φ.IsIrreducible) :
  (∃ (n : ℕ) (σ : Fin n ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((Aₙ n).reindex σ σ)) ∨
  (∃ (n : ℕ) (σ : Fin n ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((Bₙ n).reindex σ σ)) ∨
  (∃ (n : ℕ) (σ : Fin n ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((Cₙ n).reindex σ σ)) ∨
  (∃ (n : ℕ) (σ : Fin n ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((Dₙ n).reindex σ σ)) ∨
  (∃ (σ : Fin 6 ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((E₆).reindex σ σ)) ∨
  (∃ (σ : Fin 7 ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((E₇).reindex σ σ)) ∨
  (∃ (σ : Fin 8 ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((E₈).reindex σ σ)) ∨
  (∃ (σ : Fin 4 ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((F₄).reindex σ σ)) ∨
  (∃ (σ : Fin 2 ≃ {x // x ∈ b.support}),
    b.cartanMatrix = ((G₂).reindex σ σ)) := by
  sorry

end RootPairing
end MyCartanMatrix

-/
