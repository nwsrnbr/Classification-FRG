import Mathlib.Data.Real.basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant

set_option maxRecDepth 1000

-- Leech lattice は s1 * B 1 + ... + s24 * B 24 たちの集合(B i は基底．この後で定義してる)
@[ext]
structure Leech where
  s1 : ℤ
  s2 : ℤ
  s3 : ℤ
  s4 : ℤ
  s5 : ℤ
  s6 : ℤ
  s7 : ℤ
  s8 : ℤ
  s9 : ℤ
  s10 : ℤ
  s11 : ℤ
  s12 : ℤ
  s13 : ℤ
  s14 : ℤ
  s15 : ℤ
  s16 : ℤ
  s17 : ℤ
  s18 : ℤ
  s19 : ℤ
  s20 : ℤ
  s21 : ℤ
  s22 : ℤ
  s23 : ℤ
  s24 : ℤ

namespace Leech

-- 基底の係数たち
def b (i : ℕ) : Leech :=
  match i with
  | 1  => ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 2  => ⟨0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 3  => ⟨0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 4  => ⟨0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 5  => ⟨0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 6  => ⟨0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 7  => ⟨0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 8  => ⟨0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 9  => ⟨0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 10 => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 11 => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 12 => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 13 => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 14 => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 15 => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 16 => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 17 => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0⟩
  | 18 => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0⟩
  | 19 => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0⟩
  | 20 => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0⟩
  | 21 => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0⟩
  | 22 => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0⟩
  | 23 => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0⟩
  | 24 => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1⟩
  | _  => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

-- Leech lattice の基底たち(√8倍してる)
def B (i : ℕ) : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ :=
  match i with
  | 1  => ⟨8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 2  => ⟨4, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 3  => ⟨4, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 4  => ⟨4, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 5  => ⟨4, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 6  => ⟨4, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 7  => ⟨4, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 8  => ⟨2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 9  => ⟨4, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 10 => ⟨4, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 11 => ⟨4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 12 => ⟨2, 2, 2, 2, 0, 0, 0, 0, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 13 => ⟨4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 14 => ⟨2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 15 => ⟨2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 16 => ⟨2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0⟩
  | 17 => ⟨4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0⟩
  | 18 => ⟨2, 0, 2, 0, 2, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0⟩
  | 19 => ⟨2, 0, 0, 2, 2, 2, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0⟩
  | 20 => ⟨2, 2, 0, 0, 2, 0, 2, 0, 2, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0⟩
  | 21 => ⟨0, 2, 2, 2, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0⟩
  | 22 => ⟨0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0, 2, 2, 0, 0⟩
  | 23 => ⟨0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0⟩
  | 24 => ⟨-3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1⟩
  | _  => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

-- B i の第j成分を取り出す関数(例えば，(B i).2 だと ℝ^23という型を持つからこう書く必要がある)
def B_comp (i : ℕ) (j : ℕ) : ℝ :=
  match j with
  | 1  => (B i).1
  | 2  => (B i).2.1
  | 3  => (B i).2.2.1
  | 4  => (B i).2.2.2.1
  | 5  => (B i).2.2.2.2.1
  | 6  => (B i).2.2.2.2.2.1
  | 7  => (B i).2.2.2.2.2.2.1
  | 8  => (B i).2.2.2.2.2.2.2.1
  | 9  => (B i).2.2.2.2.2.2.2.2.1
  | 10 => (B i).2.2.2.2.2.2.2.2.2.1
  | 11 => (B i).2.2.2.2.2.2.2.2.2.2.1
  | 12 => (B i).2.2.2.2.2.2.2.2.2.2.2.1
  | 13 => (B i).2.2.2.2.2.2.2.2.2.2.2.2.1
  | 14 => (B i).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | 15 => (B i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | 16 => (B i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | 17 => (B i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | 18 => (B i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | 19 => (B i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | 20 => (B i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | 21 => (B i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | 22 => (B i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | 23 => (B i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | 24 => (B i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  | _  => 0

-- Leech lattice を ℝ^24 の部分空間と見たときのの任意の縦ベクトルの各成分を取り出す写像(√8倍してる)
noncomputable def coor (x : Leech) (i : ℕ) : ℝ :=
  match i with
  | 1  => x.s1 * B_comp 1 1 + x.s2 * B_comp 2 1 + x.s3 * B_comp 3 1 + x.s4 * B_comp 4 1 + x.s5 * B_comp 5 1 + x.s6 * B_comp 6 1 + x.s7 * B_comp 7 1 + x.s8 * B_comp 8 1 + x.s9 * B_comp 9 1 + x.s10 * B_comp 10 1 + x.s11 * B_comp 11 1 + x.s12 * B_comp 12 1 + x.s13 * B_comp 13 1 + x.s14 * B_comp 14 1 + x.s15 * B_comp 15 1 + x.s16 * B_comp 16 1 + x.s17 * B_comp 17 1 + x.s18 * B_comp 18 1 + x.s19 * B_comp 19 1 + x.s20 * B_comp 20 1 + x.s21 * B_comp 21 1 + x.s22 * B_comp 22 1 + x.s23 * B_comp 23 1 + x.s24 * B_comp 24 1
  | 2  => x.s1 * B_comp 1 2 + x.s2 * B_comp 2 2 + x.s3 * B_comp 3 2 + x.s4 * B_comp 4 2 + x.s5 * B_comp 5 2 + x.s6 * B_comp 6 2 + x.s7 * B_comp 7 2 + x.s8 * B_comp 8 2 + x.s9 * B_comp 9 2 + x.s10 * B_comp 10 2 + x.s11 * B_comp 11 2 + x.s12 * B_comp 12 2 + x.s13 * B_comp 13 2 + x.s14 * B_comp 14 2 + x.s15 * B_comp 15 2 + x.s16 * B_comp 16 2 + x.s17 * B_comp 17 2 + x.s18 * B_comp 18 2 + x.s19 * B_comp 19 2 + x.s20 * B_comp 20 2 + x.s21 * B_comp 21 2 + x.s22 * B_comp 22 2 + x.s23 * B_comp 23 2 + x.s24 * B_comp 24 2
  | 3  => x.s1 * B_comp 1 3 + x.s2 * B_comp 2 3 + x.s3 * B_comp 3 3 + x.s4 * B_comp 4 3 + x.s5 * B_comp 5 3 + x.s6 * B_comp 6 3 + x.s7 * B_comp 7 3 + x.s8 * B_comp 8 3 + x.s9 * B_comp 9 3 + x.s10 * B_comp 10 3 + x.s11 * B_comp 11 3 + x.s12 * B_comp 12 3 + x.s13 * B_comp 13 3 + x.s14 * B_comp 14 3 + x.s15 * B_comp 15 3 + x.s16 * B_comp 16 3 + x.s17 * B_comp 17 3 + x.s18 * B_comp 18 3 + x.s19 * B_comp 19 3 + x.s20 * B_comp 20 3 + x.s21 * B_comp 21 3 + x.s22 * B_comp 22 3 + x.s23 * B_comp 23 3 + x.s24 * B_comp 24 3
  | 4  => x.s1 * B_comp 1 4 + x.s2 * B_comp 2 4 + x.s3 * B_comp 3 4 + x.s4 * B_comp 4 4 + x.s5 * B_comp 5 4 + x.s6 * B_comp 6 4 + x.s7 * B_comp 7 4 + x.s8 * B_comp 8 4 + x.s9 * B_comp 9 4 + x.s10 * B_comp 10 4 + x.s11 * B_comp 11 4 + x.s12 * B_comp 12 4 + x.s13 * B_comp 13 4 + x.s14 * B_comp 14 4 + x.s15 * B_comp 15 4 + x.s16 * B_comp 16 4 + x.s17 * B_comp 17 4 + x.s18 * B_comp 18 4 + x.s19 * B_comp 19 4 + x.s20 * B_comp 20 4 + x.s21 * B_comp 21 4 + x.s22 * B_comp 22 4 + x.s23 * B_comp 23 4 + x.s24 * B_comp 24 4
  | 5  => x.s1 * B_comp 1 5 + x.s2 * B_comp 2 5 + x.s3 * B_comp 3 5 + x.s4 * B_comp 4 5 + x.s5 * B_comp 5 5 + x.s6 * B_comp 6 5 + x.s7 * B_comp 7 5 + x.s8 * B_comp 8 5 + x.s9 * B_comp 9 5 + x.s10 * B_comp 10 5 + x.s11 * B_comp 11 5 + x.s12 * B_comp 12 5 + x.s13 * B_comp 13 5 + x.s14 * B_comp 14 5 + x.s15 * B_comp 15 5 + x.s16 * B_comp 16 5 + x.s17 * B_comp 17 5 + x.s18 * B_comp 18 5 + x.s19 * B_comp 19 5 + x.s20 * B_comp 20 5 + x.s21 * B_comp 21 5 + x.s22 * B_comp 22 5 + x.s23 * B_comp 23 5 + x.s24 * B_comp 24 5
  | 6  => x.s1 * B_comp 1 6 + x.s2 * B_comp 2 6 + x.s3 * B_comp 3 6 + x.s4 * B_comp 4 6 + x.s5 * B_comp 5 6 + x.s6 * B_comp 6 6 + x.s7 * B_comp 7 6 + x.s8 * B_comp 8 6 + x.s9 * B_comp 9 6 + x.s10 * B_comp 10 6 + x.s11 * B_comp 11 6 + x.s12 * B_comp 12 6 + x.s13 * B_comp 13 6 + x.s14 * B_comp 14 6 + x.s15 * B_comp 15 6 + x.s16 * B_comp 16 6 + x.s17 * B_comp 17 6 + x.s18 * B_comp 18 6 + x.s19 * B_comp 19 6 + x.s20 * B_comp 20 6 + x.s21 * B_comp 21 6 + x.s22 * B_comp 22 6 + x.s23 * B_comp 23 6 + x.s24 * B_comp 24 6
  | 7  => x.s1 * B_comp 1 7 + x.s2 * B_comp 2 7 + x.s3 * B_comp 3 7 + x.s4 * B_comp 4 7 + x.s5 * B_comp 5 7 + x.s6 * B_comp 6 7 + x.s7 * B_comp 7 7 + x.s8 * B_comp 8 7 + x.s9 * B_comp 9 7 + x.s10 * B_comp 10 7 + x.s11 * B_comp 11 7 + x.s12 * B_comp 12 7 + x.s13 * B_comp 13 7 + x.s14 * B_comp 14 7 + x.s15 * B_comp 15 7 + x.s16 * B_comp 16 7 + x.s17 * B_comp 17 7 + x.s18 * B_comp 18 7 + x.s19 * B_comp 19 7 + x.s20 * B_comp 20 7 + x.s21 * B_comp 21 7 + x.s22 * B_comp 22 7 + x.s23 * B_comp 23 7 + x.s24 * B_comp 24 7
  | 8  => x.s1 * B_comp 1 8 + x.s2 * B_comp 2 8 + x.s3 * B_comp 3 8 + x.s4 * B_comp 4 8 + x.s5 * B_comp 5 8 + x.s6 * B_comp 6 8 + x.s7 * B_comp 7 8 + x.s8 * B_comp 8 8 + x.s9 * B_comp 9 8 + x.s10 * B_comp 10 8 + x.s11 * B_comp 11 8 + x.s12 * B_comp 12 8 + x.s13 * B_comp 13 8 + x.s14 * B_comp 14 8 + x.s15 * B_comp 15 8 + x.s16 * B_comp 16 8 + x.s17 * B_comp 17 8 + x.s18 * B_comp 18 8 + x.s19 * B_comp 19 8 + x.s20 * B_comp 20 8 + x.s21 * B_comp 21 8 + x.s22 * B_comp 22 8 + x.s23 * B_comp 23 8 + x.s24 * B_comp 24 8
  | 9  => x.s1 * B_comp 1 9 + x.s2 * B_comp 2 9 + x.s3 * B_comp 3 9 + x.s4 * B_comp 4 9 + x.s5 * B_comp 5 9 + x.s6 * B_comp 6 9 + x.s7 * B_comp 7 9 + x.s8 * B_comp 8 9 + x.s9 * B_comp 9 9 + x.s10 * B_comp 10 9 + x.s11 * B_comp 11 9 + x.s12 * B_comp 12 9 + x.s13 * B_comp 13 9 + x.s14 * B_comp 14 9 + x.s15 * B_comp 15 9 + x.s16 * B_comp 16 9 + x.s17 * B_comp 17 9 + x.s18 * B_comp 18 9 + x.s19 * B_comp 19 9 + x.s20 * B_comp 20 9 + x.s21 * B_comp 21 9 + x.s22 * B_comp 22 9 + x.s23 * B_comp 23 9 + x.s24 * B_comp 24 9
  | 10 => x.s1 * B_comp 1 10 + x.s2 * B_comp 2 10 + x.s3 * B_comp 3 10 + x.s4 * B_comp 4 10 + x.s5 * B_comp 5 10 + x.s6 * B_comp 6 10 + x.s7 * B_comp 7 10 + x.s8 * B_comp 8 10 + x.s9 * B_comp 9 10 + x.s10 * B_comp 10 10 + x.s11 * B_comp 11 10 + x.s12 * B_comp 12 10 + x.s13 * B_comp 13 10 + x.s14 * B_comp 14 10 + x.s15 * B_comp 15 10 + x.s16 * B_comp 16 10 + x.s17 * B_comp 17 10 + x.s18 * B_comp 18 10 + x.s19 * B_comp 19 10 + x.s20 * B_comp 20 10 + x.s21 * B_comp 21 10 + x.s22 * B_comp 22 10 + x.s23 * B_comp 23 10 + x.s24 * B_comp 24 10
  | 11 => x.s1 * B_comp 1 11 + x.s2 * B_comp 2 11 + x.s3 * B_comp 3 11 + x.s4 * B_comp 4 11 + x.s5 * B_comp 5 11 + x.s6 * B_comp 6 11 + x.s7 * B_comp 7 11 + x.s8 * B_comp 8 11 + x.s9 * B_comp 9 11 + x.s10 * B_comp 10 11 + x.s11 * B_comp 11 11 + x.s12 * B_comp 12 11 + x.s13 * B_comp 13 11 + x.s14 * B_comp 14 11 + x.s15 * B_comp 15 11 + x.s16 * B_comp 16 11 + x.s17 * B_comp 17 11 + x.s18 * B_comp 18 11 + x.s19 * B_comp 19 11 + x.s20 * B_comp 20 11 + x.s21 * B_comp 21 11 + x.s22 * B_comp 22 11 + x.s23 * B_comp 23 11 + x.s24 * B_comp 24 11
  | 12 => x.s1 * B_comp 1 12 + x.s2 * B_comp 2 12 + x.s3 * B_comp 3 12 + x.s4 * B_comp 4 12 + x.s5 * B_comp 5 12 + x.s6 * B_comp 6 12 + x.s7 * B_comp 7 12 + x.s8 * B_comp 8 12 + x.s9 * B_comp 9 12 + x.s10 * B_comp 10 12 + x.s11 * B_comp 11 12 + x.s12 * B_comp 12 12 + x.s13 * B_comp 13 12 + x.s14 * B_comp 14 12 + x.s15 * B_comp 15 12 + x.s16 * B_comp 16 12 + x.s17 * B_comp 17 12 + x.s18 * B_comp 18 12 + x.s19 * B_comp 19 12 + x.s20 * B_comp 20 12 + x.s21 * B_comp 21 12 + x.s22 * B_comp 22 12 + x.s23 * B_comp 23 12 + x.s24 * B_comp 24 12
  | 13 => x.s1 * B_comp 1 13 + x.s2 * B_comp 2 13 + x.s3 * B_comp 3 13 + x.s4 * B_comp 4 13 + x.s5 * B_comp 5 13 + x.s6 * B_comp 6 13 + x.s7 * B_comp 7 13 + x.s8 * B_comp 8 13 + x.s9 * B_comp 9 13 + x.s10 * B_comp 10 13 + x.s11 * B_comp 11 13 + x.s12 * B_comp 12 13 + x.s13 * B_comp 13 13 + x.s14 * B_comp 14 13 + x.s15 * B_comp 15 13 + x.s16 * B_comp 16 13 + x.s17 * B_comp 17 13 + x.s18 * B_comp 18 13 + x.s19 * B_comp 19 13 + x.s20 * B_comp 20 13 + x.s21 * B_comp 21 13 + x.s22 * B_comp 22 13 + x.s23 * B_comp 23 13 + x.s24 * B_comp 24 13
  | 14 => x.s1 * B_comp 1 14 + x.s2 * B_comp 2 14 + x.s3 * B_comp 3 14 + x.s4 * B_comp 4 14 + x.s5 * B_comp 5 14 + x.s6 * B_comp 6 14 + x.s7 * B_comp 7 14 + x.s8 * B_comp 8 14 + x.s9 * B_comp 9 14 + x.s10 * B_comp 10 14 + x.s11 * B_comp 11 14 + x.s12 * B_comp 12 14 + x.s13 * B_comp 13 14 + x.s14 * B_comp 14 14 + x.s15 * B_comp 15 14 + x.s16 * B_comp 16 14 + x.s17 * B_comp 17 14 + x.s18 * B_comp 18 14 + x.s19 * B_comp 19 14 + x.s20 * B_comp 20 14 + x.s21 * B_comp 21 14 + x.s22 * B_comp 22 14 + x.s23 * B_comp 23 14 + x.s24 * B_comp 24 14
  | 15 => x.s1 * B_comp 1 15 + x.s2 * B_comp 2 15 + x.s3 * B_comp 3 15 + x.s4 * B_comp 4 15 + x.s5 * B_comp 5 15 + x.s6 * B_comp 6 15 + x.s7 * B_comp 7 15 + x.s8 * B_comp 8 15 + x.s9 * B_comp 9 15 + x.s10 * B_comp 10 15 + x.s11 * B_comp 11 15 + x.s12 * B_comp 12 15 + x.s13 * B_comp 13 15 + x.s14 * B_comp 14 15 + x.s15 * B_comp 15 15 + x.s16 * B_comp 16 15 + x.s17 * B_comp 17 15 + x.s18 * B_comp 18 15 + x.s19 * B_comp 19 15 + x.s20 * B_comp 20 15 + x.s21 * B_comp 21 15 + x.s22 * B_comp 22 15 + x.s23 * B_comp 23 15 + x.s24 * B_comp 24 15
  | 16 => x.s1 * B_comp 1 16 + x.s2 * B_comp 2 16 + x.s3 * B_comp 3 16 + x.s4 * B_comp 4 16 + x.s5 * B_comp 5 16 + x.s6 * B_comp 6 16 + x.s7 * B_comp 7 16 + x.s8 * B_comp 8 16 + x.s9 * B_comp 9 16 + x.s10 * B_comp 10 16 + x.s11 * B_comp 11 16 + x.s12 * B_comp 12 16 + x.s13 * B_comp 13 16 + x.s14 * B_comp 14 16 + x.s15 * B_comp 15 16 + x.s16 * B_comp 16 16 + x.s17 * B_comp 17 16 + x.s18 * B_comp 18 16 + x.s19 * B_comp 19 16 + x.s20 * B_comp 20 16 + x.s21 * B_comp 21 16 + x.s22 * B_comp 22 16 + x.s23 * B_comp 23 16 + x.s24 * B_comp 24 16
  | 17 => x.s1 * B_comp 1 17 + x.s2 * B_comp 2 17 + x.s3 * B_comp 3 17 + x.s4 * B_comp 4 17 + x.s5 * B_comp 5 17 + x.s6 * B_comp 6 17 + x.s7 * B_comp 7 17 + x.s8 * B_comp 8 17 + x.s9 * B_comp 9 17 + x.s10 * B_comp 10 17 + x.s11 * B_comp 11 17 + x.s12 * B_comp 12 17 + x.s13 * B_comp 13 17 + x.s14 * B_comp 14 17 + x.s15 * B_comp 15 17 + x.s16 * B_comp 16 17 + x.s17 * B_comp 17 17 + x.s18 * B_comp 18 17 + x.s19 * B_comp 19 17 + x.s20 * B_comp 20 17 + x.s21 * B_comp 21 17 + x.s22 * B_comp 22 17 + x.s23 * B_comp 23 17 + x.s24 * B_comp 24 17
  | 18 => x.s1 * B_comp 1 18 + x.s2 * B_comp 2 18 + x.s3 * B_comp 3 18 + x.s4 * B_comp 4 18 + x.s5 * B_comp 5 18 + x.s6 * B_comp 6 18 + x.s7 * B_comp 7 18 + x.s8 * B_comp 8 18 + x.s9 * B_comp 9 18 + x.s10 * B_comp 10 18 + x.s11 * B_comp 11 18 + x.s12 * B_comp 12 18 + x.s13 * B_comp 13 18 + x.s14 * B_comp 14 18 + x.s15 * B_comp 15 18 + x.s16 * B_comp 16 18 + x.s17 * B_comp 17 18 + x.s18 * B_comp 18 18 + x.s19 * B_comp 19 18 + x.s20 * B_comp 20 18 + x.s21 * B_comp 21 18 + x.s22 * B_comp 22 18 + x.s23 * B_comp 23 18 + x.s24 * B_comp 24 18
  | 19 => x.s1 * B_comp 1 19 + x.s2 * B_comp 2 19 + x.s3 * B_comp 3 19 + x.s4 * B_comp 4 19 + x.s5 * B_comp 5 19 + x.s6 * B_comp 6 19 + x.s7 * B_comp 7 19 + x.s8 * B_comp 8 19 + x.s9 * B_comp 9 19 + x.s10 * B_comp 10 19 + x.s11 * B_comp 11 19 + x.s12 * B_comp 12 19 + x.s13 * B_comp 13 19 + x.s14 * B_comp 14 19 + x.s15 * B_comp 15 19 + x.s16 * B_comp 16 19 + x.s17 * B_comp 17 19 + x.s18 * B_comp 18 19 + x.s19 * B_comp 19 19 + x.s20 * B_comp 20 19 + x.s21 * B_comp 21 19 + x.s22 * B_comp 22 19 + x.s23 * B_comp 23 19 + x.s24 * B_comp 24 19
  | 20 => x.s1 * B_comp 1 20 + x.s2 * B_comp 2 20 + x.s3 * B_comp 3 20 + x.s4 * B_comp 4 20 + x.s5 * B_comp 5 20 + x.s6 * B_comp 6 20 + x.s7 * B_comp 7 20 + x.s8 * B_comp 8 20 + x.s9 * B_comp 9 20 + x.s10 * B_comp 10 20 + x.s11 * B_comp 11 20 + x.s12 * B_comp 12 20 + x.s13 * B_comp 13 20 + x.s14 * B_comp 14 20 + x.s15 * B_comp 15 20 + x.s16 * B_comp 16 20 + x.s17 * B_comp 17 20 + x.s18 * B_comp 18 20 + x.s19 * B_comp 19 20 + x.s20 * B_comp 20 20 + x.s21 * B_comp 21 20 + x.s22 * B_comp 22 20 + x.s23 * B_comp 23 20 + x.s24 * B_comp 24 20
  | 21 => x.s1 * B_comp 1 21 + x.s2 * B_comp 2 21 + x.s3 * B_comp 3 21 + x.s4 * B_comp 4 21 + x.s5 * B_comp 5 21 + x.s6 * B_comp 6 21 + x.s7 * B_comp 7 21 + x.s8 * B_comp 8 21 + x.s9 * B_comp 9 21 + x.s10 * B_comp 10 21 + x.s11 * B_comp 11 21 + x.s12 * B_comp 12 21 + x.s13 * B_comp 13 21 + x.s14 * B_comp 14 21 + x.s15 * B_comp 15 21 + x.s16 * B_comp 16 21 + x.s17 * B_comp 17 21 + x.s18 * B_comp 18 21 + x.s19 * B_comp 19 21 + x.s20 * B_comp 20 21 + x.s21 * B_comp 21 21 + x.s22 * B_comp 22 21 + x.s23 * B_comp 23 21 + x.s24 * B_comp 24 21
  | 22 => x.s1 * B_comp 1 22 + x.s2 * B_comp 2 22 + x.s3 * B_comp 3 22 + x.s4 * B_comp 4 22 + x.s5 * B_comp 5 22 + x.s6 * B_comp 6 22 + x.s7 * B_comp 7 22 + x.s8 * B_comp 8 22 + x.s9 * B_comp 9 22 + x.s10 * B_comp 10 22 + x.s11 * B_comp 11 22 + x.s12 * B_comp 12 22 + x.s13 * B_comp 13 22 + x.s14 * B_comp 14 22 + x.s15 * B_comp 15 22 + x.s16 * B_comp 16 22 + x.s17 * B_comp 17 22 + x.s18 * B_comp 18 22 + x.s19 * B_comp 19 22 + x.s20 * B_comp 20 22 + x.s21 * B_comp 21 22 + x.s22 * B_comp 22 22 + x.s23 * B_comp 23 22 + x.s24 * B_comp 24 22
  | 23 => x.s1 * B_comp 1 23 + x.s2 * B_comp 2 23 + x.s3 * B_comp 3 23 + x.s4 * B_comp 4 23 + x.s5 * B_comp 5 23 + x.s6 * B_comp 6 23 + x.s7 * B_comp 7 23 + x.s8 * B_comp 8 23 + x.s9 * B_comp 9 23 + x.s10 * B_comp 10 23 + x.s11 * B_comp 11 23 + x.s12 * B_comp 12 23 + x.s13 * B_comp 13 23 + x.s14 * B_comp 14 23 + x.s15 * B_comp 15 23 + x.s16 * B_comp 16 23 + x.s17 * B_comp 17 23 + x.s18 * B_comp 18 23 + x.s19 * B_comp 19 23 + x.s20 * B_comp 20 23 + x.s21 * B_comp 21 23 + x.s22 * B_comp 22 23 + x.s23 * B_comp 23 23 + x.s24 * B_comp 24 23
  | 24 => x.s1 * B_comp 1 24 + x.s2 * B_comp 2 24 + x.s3 * B_comp 3 24 + x.s4 * B_comp 4 24 + x.s5 * B_comp 5 24 + x.s6 * B_comp 6 24 + x.s7 * B_comp 7 24 + x.s8 * B_comp 8 24 + x.s9 * B_comp 9 24 + x.s10 * B_comp 10 24 + x.s11 * B_comp 11 24 + x.s12 * B_comp 12 24 + x.s13 * B_comp 13 24 + x.s14 * B_comp 14 24 + x.s15 * B_comp 15 24 + x.s16 * B_comp 16 24 + x.s17 * B_comp 17 24 + x.s18 * B_comp 18 24 + x.s19 * B_comp 19 24 + x.s20 * B_comp 20 24 + x.s21 * B_comp 21 24 + x.s22 * B_comp 22 24 + x.s23 * B_comp 23 24 + x.s24 * B_comp 24 24
  | _  => 0

instance : Zero Leech :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

-- (∑ x.si * B i) + (∑ y.si * B i) = ∑ (x.si + y.si) * B i
instance : Add Leech :=
  ⟨fun x y ↦ ⟨x.s1 + y.s1, x.s2 + y.s2, x.s3 + y.s3, x.s4 + y.s4, x.s5 + y.s5, x.s6 + y.s6, x.s7 + y.s7,
  x.s8 + y.s8, x.s9 + y.s9, x.s10 + y.s10, x.s11 + y.s11, x.s12 + y.s12, x.s13 + y.s13, x.s14 + y.s14,
  x.s15 + y.s15, x.s16 + y.s16, x.s17 + y.s17, x.s18 + y.s18, x.s19 + y.s19, x.s20 + y.s20, x.s21 + y.s21,
  x.s22 + y.s22, x.s23 + y.s23, x.s24 + y.s24⟩⟩

-- -(∑ x.si * B i) = ∑ (-x.si) * B i
instance : Neg Leech :=
  ⟨fun x ↦ ⟨-x.s1, -x.s2, -x.s3, -x.s4, -x.s5, -x.s6, -x.s7, -x.s8,
  -x.s9, -x.s10, -x.s11, -x.s12, -x.s13, -x.s14, -x.s15,
  -x.s16, -x.s17, -x.s18, -x.s19, -x.s20, -x.s21, -x.s22,
  -x.s23, -x.s24⟩⟩

theorem zero_def : (0 : Leech) = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ :=
  rfl

theorem add_def (x y : Leech) : x + y = ⟨x.s1 + y.s1, x.s2 + y.s2, x.s3 + y.s3, x.s4 + y.s4, x.s5 + y.s5, x.s6 + y.s6, x.s7 + y.s7,
  x.s8 + y.s8, x.s9 + y.s9, x.s10 + y.s10, x.s11 + y.s11, x.s12 + y.s12, x.s13 + y.s13, x.s14 + y.s14,
  x.s15 + y.s15, x.s16 + y.s16, x.s17 + y.s17, x.s18 + y.s18, x.s19 + y.s19, x.s20 + y.s20, x.s21 + y.s21,
  x.s22 + y.s22, x.s23 + y.s23, x.s24 + y.s24⟩ :=
  rfl

theorem neg_def (x : Leech) : -x = ⟨-x.s1, -x.s2, -x.s3, -x.s4, -x.s5, -x.s6, -x.s7, -x.s8,
  -x.s9, -x.s10, -x.s11, -x.s12, -x.s13, -x.s14, -x.s15,
  -x.s16, -x.s17, -x.s18, -x.s19, -x.s20, -x.s21, -x.s22,
  -x.s23, -x.s24⟩ :=
  rfl

@[simp]
theorem zero_s1 : (0 : Leech).s1 = 0 := rfl

@[simp]
theorem zero_s2 : (0 : Leech).s2 = 0 := rfl

@[simp]
theorem zero_s3 : (0 : Leech).s3 = 0 := rfl

@[simp]
theorem zero_s4 : (0 : Leech).s4 = 0 := rfl

@[simp]
theorem zero_s5 : (0 : Leech).s5 = 0 := rfl

@[simp]
theorem zero_s6 : (0 : Leech).s6 = 0 := rfl

@[simp]
theorem zero_s7 : (0 : Leech).s7 = 0 := rfl

@[simp]
theorem zero_s8 : (0 : Leech).s8 = 0 := rfl

@[simp]
theorem zero_s9 : (0 : Leech).s9 = 0 := rfl

@[simp]
theorem zero_s10 : (0 : Leech).s10 = 0 := rfl

@[simp]
theorem zero_s11 : (0 : Leech).s11 = 0 := rfl

@[simp]
theorem zero_s12 : (0 : Leech).s12 = 0 := rfl

@[simp]
theorem zero_s13 : (0 : Leech).s13 = 0 := rfl

@[simp]
theorem zero_s14 : (0 : Leech).s14 = 0 := rfl

@[simp]
theorem zero_s15 : (0 : Leech).s15 = 0 := rfl

@[simp]
theorem zero_s16 : (0 : Leech).s16 = 0 := rfl

@[simp]
theorem zero_s17 : (0 : Leech).s17 = 0 := rfl

@[simp]
theorem zero_s18 : (0 : Leech).s18 = 0 := rfl

@[simp]
theorem zero_s19 : (0 : Leech).s19 = 0 := rfl

@[simp]
theorem zero_s20 : (0 : Leech).s20 = 0 := rfl

@[simp]
theorem zero_s21 : (0 : Leech).s21 = 0 := rfl

@[simp]
theorem zero_s22 : (0 : Leech).s22 = 0 := rfl

@[simp]
theorem zero_s23 : (0 : Leech).s23 = 0 := rfl

@[simp]
theorem zero_s24 : (0 : Leech).s24 = 0 := rfl

@[simp]
theorem add_s1 (x y : Leech) : (x + y).s1 = x.s1 + y.s1 := rfl

@[simp]
theorem add_s2 (x y : Leech) : (x + y).s2 = x.s2 + y.s2 := rfl

@[simp]
theorem add_s3 (x y : Leech) : (x + y).s3 = x.s3 + y.s3 := rfl

@[simp]
theorem add_s4 (x y : Leech) : (x + y).s4 = x.s4 + y.s4 := rfl

@[simp]
theorem add_s5 (x y : Leech) : (x + y).s5 = x.s5 + y.s5 := rfl

@[simp]
theorem add_s6 (x y : Leech) : (x + y).s6 = x.s6 + y.s6 := rfl

@[simp]
theorem add_s7 (x y : Leech) : (x + y).s7 = x.s7 + y.s7 := rfl

@[simp]
theorem add_s8 (x y : Leech) : (x + y).s8 = x.s8 + y.s8 := rfl

@[simp]
theorem add_s9 (x y : Leech) : (x + y).s9 = x.s9 + y.s9 := rfl

@[simp]
theorem add_s10 (x y : Leech) : (x + y).s10 = x.s10 + y.s10 := rfl

@[simp]
theorem add_s11 (x y : Leech) : (x + y).s11 = x.s11 + y.s11 := rfl

@[simp]
theorem add_s12 (x y : Leech) : (x + y).s12 = x.s12 + y.s12 := rfl

@[simp]
theorem add_s13 (x y : Leech) : (x + y).s13 = x.s13 + y.s13 := rfl

@[simp]
theorem add_s14 (x y : Leech) : (x + y).s14 = x.s14 + y.s14 := rfl

@[simp]
theorem add_s15 (x y : Leech) : (x + y).s15 = x.s15 + y.s15 := rfl

@[simp]
theorem add_s16 (x y : Leech) : (x + y).s16 = x.s16 + y.s16 := rfl

@[simp]
theorem add_s17 (x y : Leech) : (x + y).s17 = x.s17 + y.s17 := rfl

@[simp]
theorem add_s18 (x y : Leech) : (x + y).s18 = x.s18 + y.s18 := rfl

@[simp]
theorem add_s19 (x y : Leech) : (x + y).s19 = x.s19 + y.s19 := rfl

@[simp]
theorem add_s20 (x y : Leech) : (x + y).s20 = x.s20 + y.s20 := rfl

@[simp]
theorem add_s21 (x y : Leech) : (x + y).s21 = x.s21 + y.s21 := rfl

@[simp]
theorem add_s22 (x y : Leech) : (x + y).s22 = x.s22 + y.s22 := rfl

@[simp]
theorem add_s23 (x y : Leech) : (x + y).s23 = x.s23 + y.s23 := rfl

@[simp]
theorem add_s24 (x y : Leech) : (x + y).s24 = x.s24 + y.s24 := rfl

@[simp]
theorem neg_s1 (x : Leech) : (-x).s1 = -x.s1 := rfl

@[simp]
theorem neg_s2 (x : Leech) : (-x).s2 = -x.s2 := rfl

@[simp]
theorem neg_s3 (x : Leech) : (-x).s3 = -x.s3 := rfl

@[simp]
theorem neg_s4 (x : Leech) : (-x).s4 = -x.s4 := rfl

@[simp]
theorem neg_s5 (x : Leech) : (-x).s5 = -x.s5 := rfl

@[simp]
theorem neg_s6 (x : Leech) : (-x).s6 = -x.s6 := rfl

@[simp]
theorem neg_s7 (x : Leech) : (-x).s7 = -x.s7 := rfl

@[simp]
theorem neg_s8 (x : Leech) : (-x).s8 = -x.s8 := rfl

@[simp]
theorem neg_s9 (x : Leech) : (-x).s9 = -x.s9 := rfl

@[simp]
theorem neg_s10 (x : Leech) : (-x).s10 = -x.s10 := rfl

@[simp]
theorem neg_s11 (x : Leech) : (-x).s11 = -x.s11 := rfl

@[simp]
theorem neg_s12 (x : Leech) : (-x).s12 = -x.s12 := rfl

@[simp]
theorem neg_s13 (x : Leech) : (-x).s13 = -x.s13 := rfl

@[simp]
theorem neg_s14 (x : Leech) : (-x).s14 = -x.s14 := rfl

@[simp]
theorem neg_s15 (x : Leech) : (-x).s15 = -x.s15 := rfl

@[simp]
theorem neg_s16 (x : Leech) : (-x).s16 = -x.s16 := rfl

@[simp]
theorem neg_s17 (x : Leech) : (-x).s17 = -x.s17 := rfl

@[simp]
theorem neg_s18 (x : Leech) : (-x).s18 = -x.s18 := rfl

@[simp]
theorem neg_s19 (x : Leech) : (-x).s19 = -x.s19 := rfl

@[simp]
theorem neg_s20 (x : Leech) : (-x).s20 = -x.s20 := rfl

@[simp]
theorem neg_s21 (x : Leech) : (-x).s21 = -x.s21 := rfl

@[simp]
theorem neg_s22 (x : Leech) : (-x).s22 = -x.s22 := rfl

@[simp]
theorem neg_s23 (x : Leech) : (-x).s23 = -x.s23 := rfl

@[simp]
theorem neg_s24 (x : Leech) : (-x).s24 = -x.s24 := rfl

instance is_AddCommGroup : AddCommGroup Leech where
  zero := 0
  add := (· + ·)
  neg x := -x
  add_assoc := by
    intros
    ext <;> simp <;> ring
  zero_add := by
    intros
    ext <;> simp
  add_zero := by
    intros
    ext <;> simp
  add_left_neg := by
    intros
    ext <;> simp
  add_comm := by
    intros
    ext <;> simp <;> ring

  -- n ⬝ (∑ x.si * B i) = ∑ (n * x.si) * B i. ただし，n ∈ N.
  nsmul := fun n x => ⟨n * x.s1, n * x.s2, n * x.s3, n * x.s4, n * x.s5, n * x.s6, n * x.s7, n * x.s8,
  n * x.s9, n * x.s10, n * x.s11, n * x.s12, n * x.s13, n * x.s14, n * x.s15,
  n * x.s16, n * x.s17, n * x.s18, n * x.s19, n * x.s20, n * x.s21, n * x.s22,
  n * x.s23, n * x.s24⟩

  -- n ⬝ (∑ x.si * B i) = ∑ (n * x.si) * B i. ただし， n ∈ ℤ.
  zsmul := fun n x => ⟨n * x.s1, n * x.s2, n * x.s3, n * x.s4, n * x.s5, n * x.s6, n * x.s7, n * x.s8,
  n * x.s9, n * x.s10, n * x.s11, n * x.s12, n * x.s13, n * x.s14, n * x.s15,
  n * x.s16, n * x.s17, n * x.s18, n * x.s19, n * x.s20, n * x.s21, n * x.s22,
  n * x.s23, n * x.s24⟩

  nsmul_zero := by
    intros
    ext <;> simp
  nsmul_succ := by
    intros
    ext <;> simp <;> ring
  zsmul_zero' := by
    intros
    ext <;> simp
  zsmul_succ' := by
    intros
    ext <;> simp <;> ring
  zsmul_neg' := by
    intros
    ext <;> simp [Int.negSucc_coe] <;> ring

-- 内積は各成分同士の積たちの和 (基底の定義で √8 倍してたので / 8 している)
noncomputable def inner (x y : Leech) : ℝ :=
  (coor x 1 * coor y 1 + coor x 2 * coor y 2 + coor x 3 * coor y 3 + coor x 4 * coor y 4 + coor x 5 * coor y 5 + coor x 6 * coor y 6 + coor x 7 * coor y 7 + coor x 8 * coor y 8 + coor x 9 * coor y 9 + coor x 10 * coor y 10 + coor x 11 * coor y 11 + coor x 12 * coor y 12 + coor x 13 * coor y 13 + coor x 14 * coor y 14 + coor x 15 * coor y 15 + coor x 16 * coor y 16 + coor x 17 * coor y 17 + coor x 18 * coor y 18 + coor x 19 * coor y 19 + coor x 20 * coor y 20 + coor x 21 * coor y 21 + coor x 22 * coor y 22 + coor x 23 * coor y 23 + coor x 24 * coor y 24
  ) / 8

noncomputable def norm (x : Leech) : ℝ := inner x x

theorem inner_comm (x y : Leech) : inner x y = inner y x := by
  simp [inner]
  ring

noncomputable def Gram_matrix : Matrix (Fin 24) (Fin 24) ℝ :=
  λ i j => inner (b i) (b j)

theorem norm_min : ∀ x : Leech, norm x ≥ 4 := by
  intro x
  rw [norm, inner]
  simp
  have h1 : ∀ i : Fin 24, 0 ≤ coor x i := by
    intro i
    apply coor_nonneg
  have h2 : ∀ i : Fin 24, 0 ≤ coor x i * coor x i := by
    intro i
    apply mul_self_nonneg
  have h3 : ∀ i : Fin 24, 0 ≤ coor x i * coor x i * 8 := by
    intro i
    apply mul_nonneg h2 (by norm_num)
  have h4 : 0 ≤ ∑ i : Fin 24, coor x i * coor x i * 8 := by
    apply sum_nonneg h3
  have h5 : 0 ≤ ∑ i : Fin 24, coor x i * coor x i := by
    linarith
  have h6 : 0 ≤ ∑ i : Fin 24, coor x i * coor x i / 8 := by
    apply div_nonneg h5 (by norm_num)
  exact h6

theorem is_even : ∀ x : Leech, ∃ n : ℤ, norm x = 2 * n := by
  intro x
  rw [norm, inner]
  simp [← pow_two]
  rw [coor, B_comp, B]
  simp
  ring_nf
  use x.s1 * x.s2
  simp

theorem is_unimodular : (Gram_matrix).det = 1 ∨ (Gram_matrix).det = -1 := by
  left
  rw [Matrix.det]
  simp
  rw [Gram_matrix]
  ring


end Leech
