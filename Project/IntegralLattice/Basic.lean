/-
Copyright (c) 2024 Erik van der Plas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik van der Plas
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

open InnerProductSpace
open Module
open FiniteDimensional

/-- An *integral lattice* is a finitely generated free abelian group
of finite rank `n` with a bilinear form that takes integer values. -/
class IntegralLattice (Λ : Type*) extends Inner ℤ Λ, AddCommGroup Λ where
  [free : Free ℤ Λ]
  [finite : Module.Finite ℤ Λ]
  (add_inner : ∀ x y z: Λ, ⟪(x + y), z⟫_ℤ = ⟪x, z⟫_ℤ + ⟪y, z⟫_ℤ)
  (inner_sym : ∀ x y: Λ, ⟪x, y⟫_ℤ = ⟪y, x⟫_ℤ)
  (inner_self : ∀ x: Λ, ⟪x, x⟫_ℤ ≥ 0)
  (inner_self_eq_zero : ∀ x: Λ, ⟪x, x⟫_ℤ = 0 → x = 0)

attribute [instance] IntegralLattice.free IntegralLattice.finite

namespace IntegralLattice

variable {Λ : Type*} [IntegralLattice Λ]

/-- Inner product is also additive in the second argument by symmetry. -/
lemma inner_add (x y z : Λ) : ⟪x, (y + z)⟫_ℤ = ⟪x, y⟫_ℤ + ⟪x, z⟫_ℤ := by
  rw [inner_sym, add_inner, inner_sym y x, inner_sym z x]

/-- Bilinear form of the inner product on an integral lattice as additive monoid homomorphism.  -/
def InnerBilin : Λ →+ Λ →+ ℤ :=
  AddMonoidHom.mk' (fun x ↦ AddMonoidHom.mk' (fun y ↦ ⟪x, y⟫_ℤ) (inner_add x)) <| by
    intro x y
    ext z
    dsimp
    apply add_inner

/-- Inner product with zero vector is always zero. -/
@[simp]
lemma inner_zero (x : Λ) : ⟪x, 0⟫_ℤ = 0 := by
  apply (InnerBilin x).map_zero

@[simp]
lemma zero_inner (y : Λ) : ⟪0, y⟫_ℤ = 0 := by
  rw [inner_sym, inner_zero]

variable (Λ)

/-- A lattice is even if all norms are even. -/
def IsEven : Prop := ∀ x: Λ, Even ⟪x, x⟫_ℤ

def gramMatrix {Λ ι : Type*} [IntegralLattice Λ] (v : ι → Λ) :=
  Matrix.of (fun i j ↦ ⟪v i, v j⟫_ℤ)

/-- The determinant of a lattice is defined as the determinant
of the Gram matrix of its basis. -/
noncomputable
def determinant : ℤ :=
  (gramMatrix (Free.chooseBasis ℤ Λ)).det

/-- A lattice is unimodular if its determinant is equal to 1. -/
def IsUnimodular : Prop := determinant Λ = 1

end IntegralLattice
