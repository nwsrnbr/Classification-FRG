/-
Copyright (c) 2024 Erik van der Plas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik van der Plas
-/
import Mathlib.GroupTheory.IntegralLattice.Leech.Basic
import Mathlib.GroupTheory.IntegralLattice.Aut
import Mathlib.Analysis.InnerProductSpace.Basic

variable (Λ : Type*) [LeechLattice Λ]

/-- A cross `C` is a subset of the Leech lattice `Λ` consisting of vectors of norm 8
  such that for each pair `x, y ∈ C` one of the following three conditions holds:
  (1) `x` and `y` are perpendicular, i.e. `⟪x, y⟫_ℤ = 0`,
  (2) `x = y` or
  (3) `x = -y`.
-/
@[ext]
structure Cross where
  (carrier : Set Λ)
  (norm_8 : ∀ x ∈ carrier, ⟪x, x⟫_ℤ = 8)
  (perpendicular : ∀ x ∈ carrier, ∀ y ∈ carrier, x ≠ y → ⟪x, y⟫_ℤ = 0 ∨ x = -y)

namespace Cross

instance : SMul (IntegralLatticeAut Λ) (Cross Λ) where
  smul f C := {
    carrier := f '' C.carrier,
    norm_8 := by
      intro x h
      simp at h
      rcases h with ⟨y, hy, rfl⟩
      rw [f.preserves_inner]
      apply C.norm_8 y hy
    perpendicular := by
      intro x hx y hy hxy
      simp at hx hy
      rcases hx with ⟨x, hx, rfl⟩
      rcases hy with ⟨y, hy, rfl⟩
      rw [f.preserves_inner]
      have := C.perpendicular x hx y hy
      rw [← map_neg f]
      simp_all [- map_neg]
  }

@[simp]
lemma smul_carrier (f : IntegralLatticeAut Λ) (C : Cross Λ) :
  (f • C).carrier = f '' C.carrier := rfl

instance : MulAction (IntegralLatticeAut Λ) (Cross Λ) where
  one_smul := by
    intro C
    ext x
    simp
  mul_smul := by
    intro f g C
    ext x
    simp

lemma card_cross : Nat.card (Cross Λ) = 8292375 := sorry

lemma card_cross_carrier (C : Cross Λ) : Nat.card C.carrier = 48 := by
  sorry

end Cross
