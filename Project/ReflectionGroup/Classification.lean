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

namespace MyCartanMatrix
open Matrix
section Determinant

variable {n : ℕ}

/-- Coxeter グラフの正定値性を定義する対称行列 (x2) -/
noncomputable def SymmMatrix (C : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
    else -√(C i j * C j i)

lemma SymmMatrix_trans_rfl (C : Matrix (Fin n) (Fin n) ℤ) : (SymmMatrix C)ᵀ = SymmMatrix C := by
  ext i j
  simp [SymmMatrix, mul_comm]
  aesop

def ind_matrix (Y : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if h : i < n ∧ j < n then Y (i.castLT h.1) (j.castLT h.2)
    else if i = j then 2
    else if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then c
    else 0

def isTopLeftBlock (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :=
  Y.submatrix (fun i => Fin.castSucc i) (fun j => Fin.castSucc j)

lemma ind_det (X : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℝ)
    (Y : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Z : Matrix (Fin n) (Fin n) ℝ)
    (c : ℝ)
    (hX : X = ind_matrix Y c)
    (hY : isTopLeftBlock Y = Z) :
  X.det = 2 * Y.det - c ^ 2 * Z.det := by
    have h_col : ∀ (j : Fin n), ind_matrix Y c (Fin.last (n + 1)) j.castSucc.castSucc = 0 := by
      intro j
      simp [ind_matrix]
      split_ifs with h1 h2
      · apply Fin.val_eq_of_eq at h1
        simp at h1
        apply Fin.is_le' at j
        linarith
      · omega
      · rfl
    have h_row : ∀ (i : Fin n), ind_matrix Y c i.castSucc.castSucc (Fin.last (n + 1)) = 0 := by
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

variable (n : ℕ)

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
      rw [ind_det (SymmMatrix (Aₙ (n + 1 + 1))) (SymmMatrix (Aₙ (n + 1))) (SymmMatrix (Aₙ n)) (-1 : ℝ)]
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
      rw [ind_det (SymmMatrix (Bₙ (n + 1 + 1))) (SymmMatrix (Aₙ (n + 1))) (SymmMatrix (Aₙ n)) (-√2 : ℝ)]
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
      rw [ind_det (SymmMatrix (Cₙ (n + 1 + 1))) (SymmMatrix (Aₙ (n + 1))) (SymmMatrix (Aₙ n)) (-√2 : ℝ)]
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
      · rw [ind_det (SymmMatrix (Dₙ (n + 1 + 1))) (SymmMatrix (Dₙ (n + 1))) (SymmMatrix (Dₙ n)) (-1 : ℝ)]
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
            <;> aesop
          · simp [hi]
            have : i = n + 1 := by omega
            split_ifs
            <;> aesop
        · ext i j
          simp [isTopLeftBlock, SymmMatrix, Dₙ, Fin.castSucc, Fin.castAdd, Fin.castLE]
          grind

/-
noncomputable def Dₙ_rev :=
  let e := Equiv.ofBijective (fun i : Fin n ↦ i.rev) Fin.rev_bijective
  (reindex e e) (Dₙ n)
-/

def Dₙ_rev : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
      else (if i = n - 1 ∧ j = n - 3 ∨ j = n - 1 ∧ i = n - 3 then -1
        else(if i = n - 1 ∧ j = n - 2 ∨ j = n - 1 ∧ i = n - 2 then 0
          else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then -1 else 0)))

lemma det_Dₙ_eq_det_Dₙ_rev5 :(SymmMatrix (Dₙ_rev 5)).det = (SymmMatrix (Dₙ 5)).det := by
  let e := Equiv.ofBijective (fun i : Fin 5 ↦ i.rev) Fin.rev_bijective
  rw [← det_reindex_self e]
  congr 1
  ext i j
  calc
    _ = (SymmMatrix (Dₙ_rev 5)) i.rev j.rev := by
      simp
      congr
      · nth_rw 1 [← i.rev_rev]; rw [Equiv.ofBijective_symm_apply_apply]
      · nth_rw 1 [← j.rev_rev]; rw [Equiv.ofBijective_symm_apply_apply]
    _ = SymmMatrix (Dₙ 5) i j := by
      fin_cases i
      <;> fin_cases j
      <;> rfl

theorem det_E₆ : (SymmMatrix E₆).det = 3 := by
  rw [ind_det (SymmMatrix E₆) (SymmMatrix (Dₙ_rev (4 + 1))) (SymmMatrix (Aₙ 4)) (-1 : ℝ)]
  · simp [det_Dₙ_eq_det_Dₙ_rev5, det_Dₙ, det_Aₙ]; norm_num
  · ext i j
    simp [SymmMatrix, ind_matrix, E₆, Dₙ_rev, Fin.castLT]
    fin_cases i
    <;> fin_cases j
    <;> simp
  · ext i j
    simp [isTopLeftBlock, SymmMatrix, Dₙ_rev, Aₙ]
    fin_cases i
    <;> fin_cases j
    <;> simp

theorem det_E₇ : (SymmMatrix E₇).det = 2 := by
  rw [ind_det (SymmMatrix E₇) (SymmMatrix E₆) (SymmMatrix (Dₙ_rev 5)) (-1 : ℝ)]
  · simp [det_E₆, det_Dₙ_eq_det_Dₙ_rev5, det_Dₙ]; norm_num
  · ext i j
    simp [SymmMatrix, ind_matrix, E₇, E₆, Fin.castLT]
    fin_cases i
    <;> fin_cases j
    <;> simp
  · ext i j
    simp [isTopLeftBlock, SymmMatrix, E₆, Dₙ_rev]
    fin_cases i
    <;> fin_cases j
    <;> simp

theorem det_E₈ : (SymmMatrix E₈).det = 1 := by
  rw [ind_det (SymmMatrix E₈) (SymmMatrix E₇) (SymmMatrix E₆) (-1 : ℝ)]
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
  rw [ind_det (SymmMatrix F₄) (SymmMatrix (Bₙ (2 + 1))) (SymmMatrix (Aₙ 2)) (-1 : ℝ)]
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

/-
theorem det_B'ₙ : (SymmMatrix (B'ₙ n)).det = if n = 0 ∨ n = 1 ∨ n = 2 then 2 else 0 := by
  induction' n using Nat.strongRec with n ih
  cases n with
  | zero => simp [SymmMatrix]
  | succ n =>
    cases n with
    | zero =>
      have : SymmMatrix (B'ₙ 1) = !![2, -√2; -√2, 2] := by
        simp [SymmMatrix, B'ₙ]
        ext i j
        fin_cases i
        <;> fin_cases j
        <;> simp
      simp [this]; norm_num
    | succ n =>
      have h1 := ih (n) (Nat.lt_succ_of_lt (Nat.lt_succ_self _))
      have h2 := ih (n+1) (Nat.lt_succ_self _)
      by_cases hn : n = 0
      · rw [hn]
        have : SymmMatrix (B'ₙ 2) = !![2, 0, -1; 0, 2, -√2; -1, -√2, 2] := by
          simp [SymmMatrix, B'ₙ]
          ext i j
          fin_cases i
          <;> fin_cases j
          <;> simp
        simp [this, Matrix.det_fin_three]
        ring_nf
        rw [Real.sq_sqrt zero_le_two]
        norm_num
      · rw [ind_det (SymmMatrix (B'ₙ (n + 1 + 1))) (SymmMatrix (Dₙ (n  + 1 + 1))) (SymmMatrix (Dₙ (n + 1))) (-√2 : ℝ)]
        · simp [det_Dₙ]
          split_ifs
          norm_num
        · ext i j
          simp [SymmMatrix, ind_matrix, B'ₙ, Dₙ, Fin.castLT]
          by_cases hi : i < n + 1 + 1
          by_cases hj : j < n + 1 + 1
          · simp [hi, hj]
            split_ifs
            repeat'
              grind
            congr
            · grind
            · split_ifs
              repeat'
                grind

          · simp [hi, hj]
            have : j = n + 1 + 1 := by omega
            split_ifs
            <;> aesop
          · simp [hi]
            have : i = n + 1 + 1 := by omega
            split_ifs
            <;> aesop
        · ext i j
          simp [isTopLeftBlock, SymmMatrix, Dₙ, Fin.castSucc, Fin.castAdd, Fin.castLE]
          grind
-/

end Determinant

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
