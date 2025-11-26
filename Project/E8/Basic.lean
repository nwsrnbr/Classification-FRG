/-
Copyright (c) 2024 Erik van der Plas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik van der Plas
2025-02-26 10:09:13
E8 格子のために借用
-/

import Mathlib.Data.Matrix.Basic
import Project.IntegralLattice.Equiv
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Lie.CartanMatrix
import Mathlib.Analysis.InnerProductSpace.Projection

#check Submodule.reflection

universe u

open Module
open InnerProductSpace
open IntegralLattice
open FiniteDimensional

/--
The E8 lattice is the unique even, unimodular integral lattice of rank 8
-/
class E8Lattice (Λ : Type*) extends IntegralLattice Λ where
  (even : IsEven Λ)
  (unimodular : IsUnimodular Λ)
  (rank_eq_8 : finrank ℤ Λ = 8)


namespace E8Lattice

variable (Λ : Type*) [E8Lattice Λ]

theorem unique (Λ₁ Λ₂ : Type*) [E8Lattice Λ₁] [E8Lattice Λ₂]:
  Nonempty (Λ₁ ≃ₗ Λ₂) := sorry

#check E8Lattice.unique

def B := Matrix.toBilin' CartanMatrix.E₈

def intMatrixToRat {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Matrix (Fin m) (Fin n) ℚ :=
  A.map (↑)

lemma intDetToRat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) : A.det = (intMatrixToRat A).det := by
  exact RingHom.map_det (Int.castRingHom ℚ) A

def M0 := intMatrixToRat CartanMatrix.E₈
def M1 := Matrix.updateRow M0 2 (M0 2 + (1/2 : ℚ) • M0 0)
def M2 := Matrix.updateRow M1 3 (M1 3 + (1/2 : ℚ) • M1 1)
def M3 := Matrix.updateRow M2 3 (M2 3 + (2/3 : ℚ) • M2 2)
def M4 := Matrix.updateRow M3 4 (M3 4 + (6/5 : ℚ) • M3 3)
def M5 := Matrix.updateRow M4 5 (M4 5 + (5/4 : ℚ) • M4 4)
def M6 := Matrix.updateRow M5 6 (M5 6 + (4/3 : ℚ) • M5 5)
def M7 := Matrix.updateRow M6 7 (M6 7 + (3/2 : ℚ) • M6 6)

#eval M0
#eval M1
#eval M2
#eval M3
#eval M4
#eval M5
#eval M6
#eval M7

lemma M7_upperTrianglar : Matrix.BlockTriangular M7 id := by
  rw [Matrix.BlockTriangular]
  intro i j hij
  fin_cases i
  <;> fin_cases j
  <;> simp at *
  repeat'
    rfl'

-- Matrix.det_of_upperTriangular でエラーが出る
-- でなくなった！
lemma M7_det : M7.det = 1 := by
  rw [Matrix.det_of_upperTriangular M7_upperTrianglar]
  calc
    _ = M7 0 0 * M7 1 1 * M7 2 2 * M7 3 3 * M7 4 4 * M7 5 5 * M7 6 6 * M7 7 7 := by rfl'
    _ = 2 * 2 * (3 / 2) * (5 / 6) * (4 / 5) * (3 / 4) * (2 / 3) * (1 / 2) := by
      congr
      <;> rfl'
    _ = 1 := by norm_num

-- Matrix.det_updateRow_add_smul_self でエラーが出る
theorem E8_det : ((CartanMatrix.E₈).det : ℚ) = 1 := by
  sorry
  /-
  calc
    _ = M0.det := by
      rw [M0, intDetToRat]
    _ = M1.det := by
      rw [M1, Matrix.det_updateRow_add_smul_self]
      decide
    _ = M2.det := by
      rw [M2, Matrix.det_updateRow_add_smul_self]
      decide
    _ = M3.det := by
      rw [M3, Matrix.det_updateRow_add_smul_self]
      decide
    _ = M4.det := by
      rw [M4, Matrix.det_updateRow_add_smul_self]
      decide
    _ = M5.det := by
      rw [M5, Matrix.det_updateRow_add_smul_self]
      decide
    _ = M6.det := by
      rw [M6, Matrix.det_updateRow_add_smul_self]
      decide
    _ = M7.det := by
      rw [M7, Matrix.det_updateRow_add_smul_self]
      decide
    _ = 1 := by
      rw [M7_det]
  -/

-- 自身との bilinear form を具体的に計算．
lemma inner_self_calc (x : Fin 8 → ℤ) : (B x) x =
  2 * ((x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 + (x 3) ^ 2 + (x 4) ^ 2 + (x 5) ^ 2 + (x 6) ^ 2 + (x 7) ^ 2
  - ((x 0 * x 2) + (x 1 * x 3) + (x 2 * x 3) + (x 3 * x 4) + (x 4 * x 5) + (x 5 * x 6) + (x 6 * x 7))) := by
    rw [B]
    rw [Matrix.toBilin'_apply', CartanMatrix.E₈] -- bilinear form を内積の形に展開(x ⬝ (Ay) = x^t A y)
    simp
    simp [Matrix.vecHead, Matrix.vecTail, Fin.succ] -- 内積を力技で計算
    ring_nf

-- 自身との bilinear form を平方完成
lemma inner_self_comp_sq (x : Fin 8 → ℤ) : (B x) x =
  (√2 * x 0 - √(1 / 2) * x 2) ^ 2 + (√2 * x 1 - √(1 / 2) * x 3) ^ 2 + (√(3 / 2) * x 2 - √(2 / 3) * x 3) ^ 2 +
  (√(5 / 6) * x 3 - √(6 / 5) * x 4) ^ 2 + (√(4 / 5) * x 4 - √(5 / 4) * x 5) ^ 2 +
  (√(3 / 4) * x 5 - √(4 / 3) * x 6) ^ 2 + (√(2 / 3) * x 6 - √(3 / 2) * x 7) ^ 2 + (1 / 2) * x 7 ^ 2 := by
    rw [inner_self_calc]
    ring_nf
    simp
    ring_nf
    simp [mul_inv_cancel]
    ring

theorem AddInner (x y z : Fin 8 → ℤ) : (B (x + y)) z = (B x) z + (B y) z := by
  rw [B]
  simp

theorem InnerSym (x y : Fin 8 → ℤ) : (B x) y = (B y) x := by
  rw [B]
  simp [Matrix.toBilin'_apply']
  rw [CartanMatrix.E₈]
  simp -- 力技で計算
  ring

theorem InnerSelf (x : Fin 8 → ℤ) : (B x) x ≥ 0 := by
  simp [inner]
  have (a : ℤ) : (0 : ℤ) ≤ a ↔ (0 : ℝ) ≤ (a : ℝ) := by simp -- (整数) ≤ (整数) ↔ (実数) ≤ (実数) の変換
  rw [this, inner_self_comp_sq]
  repeat'
    apply add_nonneg
  repeat'
    apply sq_nonneg
  apply mul_nonneg
  · apply div_nonneg
    <;> norm_num
  · apply sq_nonneg

theorem InnerEven (x : Fin 8 → ℤ) : Even ((B x) x) := by
  rw [Even]
  rw [inner_self_calc]
  use (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 + (x 3) ^ 2 + (x 4) ^ 2 + (x 5) ^ 2 + (x 6) ^ 2 + (x 7) ^ 2
    - ((x 0 * x 2) + (x 1 * x 3) + (x 2 * x 3) + (x 3 * x 4) + (x 4 * x 5) + (x 5 * x 6) + (x 6 * x 7))
  ring

theorem InnerSelfEqZero (x : Fin 8 → ℤ) : (B x) x = 0 → x = 0 := by
  intro h
  have coe (a : ℤ) : a = (0 : ℤ) ↔ (a : ℝ) = (0 : ℝ) := by simp -- (整数) = (整数) ↔ (実数) = (実数) の変換
  rw [coe, inner_self_comp_sq] at h -- B x x を平方完成した形にする
  -- f₀ + ... + f₇ = 0 ↔ f₀ = ... = f₇ = 0
  rw [add_eq_zero_iff_of_nonneg] at h
  rw [add_eq_zero_iff_of_nonneg] at h
  rw [add_eq_zero_iff_of_nonneg] at h
  rw [add_eq_zero_iff_of_nonneg] at h
  rw [add_eq_zero_iff_of_nonneg] at h
  rw [add_eq_zero_iff_of_nonneg] at h
  rw [add_eq_zero_iff_of_nonneg] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
  have H (a b : ℤ) (s t : ℝ) : (s * a - t * b) ^ 2 = 0 → s * a = t * b := by
    intro h
    rw [sq_eq_zero_iff, sub_eq_zero] at h
    assumption
  have H' (a : ℤ) (s : ℝ) (hs : s ≠ 0) : s * a ^ 2 = 0 → a = 0 := by
    intro h
    rw [mul_eq_zero] at h
    rcases h with (h | h)
    · contradiction
    · rw [sq_eq_zero_iff, ← coe] at h
      assumption
  apply H at h0
  apply H at h1
  apply H at h2
  apply H at h3
  apply H at h4
  apply H at h5
  apply H at h6
  apply H' at h7
  simp [h7] at h6
  simp [h6] at h5
  simp [h5] at h4
  simp [h4] at h3
  simp [h3] at h2
  simp [h3] at h1
  simp [h2] at h0
  ext i -- 各 i : Fin 8 について証明する
  simp -- 0 i = 0
  fin_cases i -- i = 0, ..., 7 でしらみつぶし
  repeat'
    simp
  repeat'
    assumption
  repeat'
    apply sq_nonneg
  repeat'
    apply add_nonneg
  repeat'
    apply sq_nonneg

instance exampleE8 : E8Lattice (Fin 8 → ℤ) where
  inner := fun x y => B x y
  add := Pi.addCommGroup.add
  add_assoc := Pi.addCommGroup.add_assoc
  zero := Pi.addCommGroup.zero
  zero_add := Pi.addCommGroup.zero_add
  add_zero := Pi.addCommGroup.add_zero
  nsmul := Pi.addCommGroup.nsmul
  nsmul_zero := Pi.addCommGroup.nsmul_zero
  nsmul_succ := Pi.addCommGroup.nsmul_succ
  neg := Pi.addCommGroup.neg
  sub := Pi.addCommGroup.sub
  sub_eq_add_neg := Pi.addCommGroup.sub_eq_add_neg
  zsmul := Pi.addCommGroup.zsmul
  zsmul_zero' := Pi.addCommGroup.zsmul_zero'
  zsmul_succ' := Pi.addCommGroup.zsmul_succ'
  zsmul_neg' := Pi.addCommGroup.zsmul_neg'
  neg_add_cancel := Pi.addCommGroup.neg_add_cancel
  add_comm := Pi.addCommGroup.add_comm
  free := by exact Module.Free.function (Fin 8) ℤ ℤ
  finite := by exact Module.Finite.pi
  add_inner := by apply AddInner
  inner_sym := by apply InnerSym
  inner_self := by apply InnerSelf
  inner_self_eq_zero := by apply InnerSelfEqZero
  even := by apply InnerEven
  unimodular := by
    rw [IsUnimodular, determinant]
    --determinant, Matrix.det_apply']
    sorry
  rank_eq_8 := by exact finrank_fin_fun ℤ


-- Type u だとできない．
theorem exists_E8 : ∃ (Λ : Type u), Nonempty (E8Lattice Λ) := sorry

-- Type 0 ならできる．
theorem exists_E8' : ∃ (Λ : Type), Nonempty (E8Lattice Λ) := by
  use (Fin 8 → ℤ)
  exact ⟨E8Lattice.exampleE8⟩

instance (n : ℕ) : Finite {x: Λ | ⟪x, x⟫_ℤ = n} := sorry
instance (n : ℕ) : Finite {x: Λ // ⟪x, x⟫_ℤ = n} := sorry

-- Lemma's about cardinality of vectors of norms 2, 4, 6 and 8:


lemma card_norm_2 : Nat.card {x: Λ | ⟪x, x⟫_ℤ = 2} = 240 := sorry

end E8Lattice
