import Mathlib.Tactic
import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Project.ReflectionGroup.Basic
import Project.ReflectionGroup.CartanMatrix
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

namespace RootPairing

variable {T : Type u} [Zero T] [DecidableEq T]
variable {n : Type*} [Fintype n] [DecidableEq n]

end RootPairing

variable {n : Type*} [Fintype n] [DecidableEq n]

def cartanToCoxeter (A : Matrix n n ℤ) : Matrix n n ℕ :=
  fun i j =>
    if i = j then 1
    else
      let prod := A i j * A j i
      match prod with
      | 0 => 2
      | 1 => 3
      | 2 => 4
      | 3 => 6
      | _ => 0   -- 本来 ∞ だが，ℕ からはみ出さないよう 0 にしている．

example : cartanToCoxeter (CartanMatrix.E₈) = CoxeterMatrix.E₈.M := by
  decide

namespace MyCartanMatrix
open Matrix
section Positive

variable {n : ℕ}

/-- Coxeter グラフの正定値性を定義する対称行列 (x2) -/
noncomputable def SymmMatrix (C : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
    else -√(C i j * C j i)

variable (n : ℕ)

def ind_matrix (Y : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if h : i < n ∧ j < n then Y (i.castLT h.1) (j.castLT h.2)
    else if i = j then 2
    else if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then c
    else 0

/-- n 次正方行列 C から最後の行と列を取り除いた (n - 1) 次正方行列 -/
def PrincipalSubmatrix (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) :=
  C.submatrix (fun i => Fin.castSucc i) (fun j => Fin.castSucc j)

def isTopLeftBlock (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :=
  Y.submatrix (fun i => Fin.castSucc i) (fun j => Fin.castSucc j)

theorem ind_det (X : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℝ)
    (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Z : Matrix (Fin n) (Fin n) ℝ)
    (c : ℝ)
    (hX : X = ind_matrix (n + 1) Y c)
    (hY : isTopLeftBlock n Y = Z) :
  X.det = 2 * Y.det - c ^ 2 * Z.det := by
    have h_col : ∀ (j : Fin n), ind_matrix (n + 1) Y c (Fin.last (n + 1)) j.castSucc.castSucc = 0 := by
      intro j
      simp [ind_matrix]
      split_ifs with h1 h2
      · apply Fin.val_eq_of_eq at h1
        simp at h1
        apply Fin.is_le' at j
        linarith
      · omega
      · rfl
    have h_row : ∀ (i : Fin n), ind_matrix (n + 1) Y c i.castSucc.castSucc (Fin.last (n + 1)) = 0 := by
      intro i
      simp [ind_matrix]
      intro h
      omega
    rw [X.det_succ_row (Fin.last (n + 1)), hX]
    rw [Fin.sum_univ_succAbove (x := Fin.last (n + 1)), Fin.sum_univ_succAbove (x := Fin.last n)]
    simp
    simp [h_col]
    congr 1
    · simp [ind_matrix, Fin.castLT]
      congr 1
      ext i j
      simp
    · rw [det_succ_column (j := Fin.last n), Fin.sum_univ_succAbove (x := Fin.last n)]
      simp
      simp [h_row]
      rw [← mul_assoc]--, mul_comm 2, mul_assoc (c ^ 2)]
      congr 1
      · rw [pow_two]
        congr
        · simp [ind_matrix, Fin.last]
        · simp [ind_matrix]
      · simp [ind_matrix, Fin.castLT]
        congr 1
        ext i j
        simp
        simp [← hY, isTopLeftBlock]
        split_ifs with h1 h2 h3
        · congr
        repeat'
          omega

/-
lemma Aₙ_submatrix : PrincipalSubmatrix n hn (Aₙ n) = Aₙ (n - 1) := by
  ext i j
  simp [Aₙ]

lemma Bₙ_submatrix (hn : 1 ≤ n) : PrincipalSubmatrix n hn (Bₙ n) = Aₙ (n - 1) := by
  ext i j
  simp [Bₙ, Aₙ]
  grind

lemma Cₙ_submatrix (hn : 1 ≤ n) : PrincipalSubmatrix n hn (Cₙ n) = Aₙ (n - 1) := by
  ext i j
  simp [Cₙ, Aₙ]
  omega

lemma Dₙ_submatrix (hn : 5 ≤ n) : PrincipalSubmatrix n (by linarith) (Dₙ n) = Dₙ (n - 1) := by
  ext i j
  simp [Dₙ, Dₙ]

lemma D₄_submatrix : PrincipalSubmatrix 4 (by linarith) (Dₙ 4) = Aₙ 3 := by
  ext i j
  simp [Dₙ, Aₙ]
  grind

lemma F₄_submatrix : PrincipalSubmatrix 4 (by linarith) F₄ = Bₙ 3 := by
  ext i j
  simp [F₄, Bₙ]
  --grind
  sorry
-/

theorem det_Aₙ : (SymmMatrix (Aₙ n)).det = (n : ℝ) + 1 := by
  induction' n using Nat.strongRec with n ih
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp [SymmMatrix]; norm_num
    | succ n =>
      have h1 := ih (n) (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      have h2 := ih (n+1) (Nat.lt_succ_self _)
      rw [ind_det n (SymmMatrix (Aₙ (n + 1 + 1))) (SymmMatrix (Aₙ (n + 1))) (SymmMatrix (Aₙ n)) (-1 : ℝ)]
      · simp [h1, h2]; ring
      · ext i j
        simp [SymmMatrix, ind_matrix, Aₙ, Fin.castLT]
        grind
      · ext i j
        simp [isTopLeftBlock, SymmMatrix, Aₙ]


theorem det_Bₙ : (SymmMatrix (Bₙ n)).det = if n = 0 then 1 else 2 := by
  induction' n using Nat.strongRec with n ih
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp [SymmMatrix]
    | succ n =>
      have h1 := ih (n) (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      have h2 := ih (n+1) (Nat.lt_succ_self _)
      rw [ind_det n (SymmMatrix (Bₙ (n + 1 + 1))) (SymmMatrix (Aₙ (n + 1))) (SymmMatrix (Aₙ n)) (-√2 : ℝ)]
      · simp [det_Aₙ]; ring
      · ext i j
        simp [SymmMatrix, ind_matrix, Aₙ, Bₙ, Fin.castLT]
        by_cases hi : i < n + 1
        by_cases hj : j < n + 1
        · grind
        · grind
        · grind
      · ext i j
        simp [isTopLeftBlock, SymmMatrix, Aₙ]

theorem det_Cₙ : (SymmMatrix (Cₙ n)).det = if n = 0 then 1 else 2 := by
  induction' n using Nat.strongRec with n ih
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp [SymmMatrix]
    | succ n =>
      have h1 := ih (n) (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      have h2 := ih (n+1) (Nat.lt_succ_self _)
      rw [ind_det n (SymmMatrix (Cₙ (n + 1 + 1))) (SymmMatrix (Aₙ (n + 1))) (SymmMatrix (Aₙ n)) (-√2 : ℝ)]
      · simp [det_Aₙ]; ring
      · ext i j
        simp [SymmMatrix, ind_matrix, Aₙ, Cₙ, Fin.castLT]
        by_cases hi : i < n + 1
        by_cases hj : j < n + 1
        · simp [hi, hj]
          grind
        · grind
        · grind
      · ext i j
        simp [isTopLeftBlock, SymmMatrix, Aₙ]

theorem det_Dₙ : (SymmMatrix (Dₙ n)).det =
    if n = 0 then 1
    else if n = 1 then 2
    else 4 := by
  induction' n using Nat.strongRec with n ih
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp [SymmMatrix]
    | succ n =>
      have h1 := ih (n) (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      have h2 := ih (n+1) (Nat.lt_succ_self _)
      by_cases hn : n = 0
      · rw [hn]
        have : SymmMatrix (Dₙ 2) = !![2, 0; 0, 2] := by
          simp [SymmMatrix, Dₙ]
          ext i j
          fin_cases i
          <;> fin_cases j
          <;> simp
        simp [this]
        norm_num
      by_cases hn' : n = 1
      · rw [hn']
        simp
        have : SymmMatrix (Dₙ 3) = !![2, 0, -1; 0, 2, -1; -1, -1, 2] := by
          simp [SymmMatrix, Dₙ]
          ext i j
          fin_cases i
          <;> fin_cases j
          <;> simp
        simp [this, Matrix.det_fin_three]
        norm_num
      · rw [ind_det n (SymmMatrix (Dₙ (n + 1 + 1))) (SymmMatrix (Dₙ (n + 1))) (SymmMatrix (Dₙ n)) (-1 : ℝ)]
        · simp [h1, h2]
          split_ifs
          norm_num
        · ext i j
          simp [SymmMatrix, ind_matrix, Dₙ, Fin.castLT]
          by_cases hi : i < n + 1
          by_cases hj : j < n + 1
          · simp [hi, hj]
            grind
          · simp [hi, hj]
            have : j = n + 1 := by omega
            split_ifs
            <;> simp
            <;> aesop
          · simp [hi]
            have : i = n + 1 := by omega
            split_ifs
            <;> simp
            <;> aesop
        · ext i j
          simp [isTopLeftBlock, SymmMatrix, Dₙ, Fin.castSucc, Fin.castAdd, Fin.castLE]
          grind

/-
noncomputable def D'ₙ :=
  let e := Equiv.ofBijective (fun i : Fin n ↦ i.rev) Fin.rev_bijective
  (reindex e e) (Dₙ n)
-/

def D'ₙ : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
      else (if i = n - 1 ∧ j = n - 3 ∨ j = n - 1 ∧ i = n - 3 then -1
        else(if i = n - 1 ∧ j = n - 2 ∨ j = n - 1 ∧ i = n - 2 then 0
          else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then -1 else 0)))

lemma det_Dₙ_eq_det_D'ₙ5 :(SymmMatrix (D'ₙ 5)).det = (SymmMatrix (Dₙ 5)).det := by
  let e := Equiv.ofBijective (fun i : Fin 5 ↦ i.rev) Fin.rev_bijective
  rw [← det_reindex_self e]
  congr 1
  ext i j
  calc
    _ = (SymmMatrix (D'ₙ 5)) i.rev j.rev := by
      simp
      congr
      · nth_rw 1 [← i.rev_rev]; rw [Equiv.ofBijective_symm_apply_apply]
      · nth_rw 1 [← j.rev_rev]; rw [Equiv.ofBijective_symm_apply_apply]
    _ = SymmMatrix (Dₙ 5) i j := by
      fin_cases i
      <;> fin_cases j
      <;> rfl

theorem det_E₆ : (SymmMatrix E₆).det = 3 := by
  rw [ind_det 4 (SymmMatrix E₆) (SymmMatrix (D'ₙ (4 + 1))) (SymmMatrix (Aₙ 4)) (-1 : ℝ)]
  · simp [det_Dₙ_eq_det_D'ₙ5, det_Dₙ, det_Aₙ]; norm_num
  · ext i j
    simp [SymmMatrix, ind_matrix, E₆, D'ₙ, Fin.castLT]
    fin_cases i
    <;> fin_cases j
    <;> simp
  · ext i j
    simp [isTopLeftBlock, SymmMatrix, D'ₙ, Aₙ]
    fin_cases i
    <;> fin_cases j
    <;> simp


theorem det_E₇ : (SymmMatrix E₇).det = 2 := by
  rw [ind_det 5 (SymmMatrix E₇) (SymmMatrix E₆) (SymmMatrix (D'ₙ 5)) (-1 : ℝ)]
  · simp [det_E₆, det_Dₙ_eq_det_D'ₙ5, det_Dₙ]; norm_num
  · ext i j
    simp [SymmMatrix, ind_matrix, E₇, E₆, Fin.castLT]
    fin_cases i
    <;> fin_cases j
    <;> simp
  · ext i j
    simp [isTopLeftBlock, SymmMatrix, E₆, D'ₙ]
    fin_cases i
    <;> fin_cases j
    <;> simp

theorem det_E₈ : (SymmMatrix E₈).det = 1 := by
  rw [ind_det 6 (SymmMatrix E₈) (SymmMatrix E₇) (SymmMatrix E₆) (-1 : ℝ)]
  · simp [det_E₇, det_E₆]; norm_num
  · ext i j
    simp [SymmMatrix, ind_matrix, E₈, E₇, Fin.castLT]
    fin_cases i
    <;> fin_cases j
    <;> simp
  · ext i j
    simp [isTopLeftBlock, SymmMatrix, E₇, E₆]
    fin_cases i
    <;> fin_cases j
    <;> simp

theorem det_F₄ : (SymmMatrix F₄).det = 1 := by
  rw [ind_det 2 (SymmMatrix F₄) (SymmMatrix (Bₙ (2 + 1))) (SymmMatrix (Aₙ 2)) (-1 : ℝ)]
  · simp [det_Aₙ, det_Bₙ]
    norm_num
  · ext i j
    simp [SymmMatrix, ind_matrix, F₄, Bₙ, Fin.castLT]
    fin_cases i
    <;> fin_cases j
    <;> simp
  · ext i j
    simp [isTopLeftBlock, SymmMatrix, Bₙ, Aₙ]
    fin_cases i
    <;> fin_cases j
    <;> simp

theorem det_G₂ : (SymmMatrix G₂).det = 1 := by
  have : SymmMatrix G₂ = !![2, -√3; -√3, 2] := by
    simp [G₂, SymmMatrix]
    ext i j
    fin_cases i
    <;> fin_cases j
    <;> simp
  rw [this]
  simp; norm_num

end Positive

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
