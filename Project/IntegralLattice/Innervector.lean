import Mathlib

open Matrix

-- 階数 2 の自由 ℤ 加群
def R2 := Fin 2 → ℤ

-- 内積, というか対称双線形形式の定義

def H := !![(0:ℤ), (1:ℤ);(1:ℤ), (0:ℤ)] -- 2x2行列


def B := Matrix.toBilin' H

theorem is_even (x : R2) : ∃ (n : ℤ), B x x = 2*n := by
  use x 0 * x 1
  rw [B]
  rw [Matrix.toBilin'_apply H x x]
  simp
  ring_nf
  have aux1 : H 0 0 = 0 := by rfl
  have aux2 : H 1 1 = 0 := by rfl
  have aux3 : H 0 1 = 1 := by rfl
  have aux4 : H 1 0 = 1 := by rfl
  rw [aux1, aux2,aux3,aux4]
  ring_nf

theorem unimodular : (det H = -1) ∨ (det H = 1):= by
  left
  rw [det_fin_two]
  have aux1 : H 0 0 = 0 := by rfl
  have aux2 : H 1 1 = 0 := by rfl
  have aux3 : H 0 1 = 1 := by rfl
  have aux4 : H 1 0 = 1 := by rfl
  rw [aux1, aux2,aux3,aux4]
  ring_nf
