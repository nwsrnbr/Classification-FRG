import Mathlib.Data.Real.basic
import Mathlib.LinearAlgebra.Matrix.Determinant

-- 基底は b1 := [1, 0] と b2 := [0, 1].
-- Hyperbolic は s1 * b1 + s2 * b2 と書いたときの s1 と s2 の組たちの集合．
@[ext]
structure Hyperbolic where
  s1 : ℤ
  s2 : ℤ

namespace Hyperbolic

def b1 : Hyperbolic :=
  ⟨1, 0⟩

def b2 : Hyperbolic :=
  ⟨0, 1⟩

instance : Zero Hyperbolic :=
  ⟨0, 0⟩

instance : Add Hyperbolic :=
  ⟨fun x y ↦ ⟨x.s1 + y.s1, x.s2 + y.s2⟩⟩

instance : Neg Hyperbolic :=
  ⟨fun x ↦ ⟨-x.s1, -x.s2⟩⟩

theorem zero_def : (0 : Hyperbolic) = ⟨0, 0⟩ :=
  rfl

theorem add_def (x y : Hyperbolic) : x + y = ⟨x.s1 + y.s1, x.s2 + y.s2⟩ :=
  rfl

theorem neg_def (x : Hyperbolic) : -x = ⟨-x.s1, -x.s2⟩ :=
  rfl

@[simp]
theorem zero_s1 : (0 : Hyperbolic).s1 = 0 :=
  rfl

@[simp]
theorem zero_s2 : (0 : Hyperbolic).s2 = 0 :=
  rfl

@[simp]
theorem add_s1 (x y : Hyperbolic) : (x + y).s1 = x.s1 + y.s1 :=
  rfl

@[simp]
theorem add_s2 (x y : Hyperbolic) : (x + y).s2 = x.s2 + y.s2 :=
  rfl

@[simp]
theorem neg_s1 (x : Hyperbolic) : (-x).s1 = -x.s1 :=
  rfl

@[simp]
theorem neg_s2 (x : Hyperbolic) : (-x).s2 = -x.s2 :=
  rfl

instance is_AddCommGroup : AddCommGroup Hyperbolic where
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
  nsmul := fun n x => ⟨n * x.s1, n * x.s2⟩
  zsmul := fun n x => ⟨n * x.s1, n * x.s2⟩
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

noncomputable def inner (x y : Hyperbolic) : ℝ :=
  x.s1 * y.s2 + x.s2 * y.s1

noncomputable def norm (x : Hyperbolic) : ℝ := inner x x

theorem inner_comm (x y : Hyperbolic) : inner x y = inner y x := by
  simp [inner]
  ring

noncomputable def Gram_matrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![inner b1 b1, inner b1 b2;
     inner b2 b1, inner b2 b2]

theorem is_even : ∀ x : Hyperbolic, ∃ n : ℤ, norm x = 2 * n := by
  intro x
  rw [norm, inner]
  ring_nf
  use x.s1 * x.s2
  simp

theorem is_unimodular : (Gram_matrix).det = 1 ∨ (Gram_matrix).det = -1 := by
  right
  simp [Gram_matrix, inner, b1, b2]

end Hyperbolic
