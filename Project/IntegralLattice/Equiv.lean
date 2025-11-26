/-
Copyright (c) 2024 Erik van der Plas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik van der Plas
-/
import Project.IntegralLattice.Basic

open InnerProductSpace
open IntegralLattice

/-- A lattice equivalence corresponds to structure preserving isometries fixing the origin,
  i.e. equivalence preserving vector additions and inner products. -/
structure IntegralLatticeEquiv (Λ₁ Λ₂ : Type*)
  [IntegralLattice Λ₁] [IntegralLattice Λ₂]
  extends Λ₁ ≃+ Λ₂ where
  (preserves_inner' : ∀ x y: Λ₁, ⟪toFun x, toFun y⟫_ℤ = ⟪x, y⟫_ℤ)

/-- Notation for an `IntegralLatticeEquiv`. -/
infixl:25 " ≃ₗ " => IntegralLatticeEquiv

namespace IntegralLatticeEquiv

variable {Λ₁ Λ₂ Λ₃ : Type*} [IntegralLattice Λ₁] [IntegralLattice Λ₂] [IntegralLattice Λ₃]

/-- Lattice equivalence relation is reflexive. -/
def refl (Λ : Type*) [IntegralLattice Λ] : Λ ≃ₗ Λ where
  __ := AddEquiv.refl Λ
  preserves_inner' _ _ := rfl

/-- Lattice equivalence relation is symmetric. -/
def symm (f : Λ₁ ≃ₗ Λ₂) : Λ₂ ≃ₗ Λ₁ where
  __ := f.toAddEquiv.symm
  preserves_inner' x y := by
    rw [← f.preserves_inner']
    simp

/-- Lattice equivalence relation is transitive. -/
def trans (f : Λ₁ ≃ₗ Λ₂) (g : Λ₂ ≃ₗ Λ₃) : Λ₁ ≃ₗ Λ₃ where
  __ := f.toAddEquiv.trans g.toAddEquiv
  preserves_inner' x y := by
    rw [← f.preserves_inner', ← g.preserves_inner']
    simp

instance : EquivLike (Λ₁ ≃ₗ Λ₂) Λ₁ Λ₂ where
  coe := fun x => x.toFun
  inv := fun x ↦ x.invFun
  left_inv := fun x ↦ x.left_inv
  right_inv := fun x ↦ x.right_inv
  coe_injective' := by
    intros f g h
    cases f
    simp_all

instance : AddEquivClass (Λ₁ ≃ₗ Λ₂) Λ₁ Λ₂ where
  map_add f a b := f.map_add a b

lemma preserves_inner (f : Λ₁ ≃ₗ Λ₂) (x y : Λ₁) : ⟪f x, f y⟫_ℤ = ⟪x, y⟫_ℤ :=
  f.preserves_inner' x y

@[ext]
theorem ext {f g : Λ₁ ≃ₗ Λ₂} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp]
theorem self_trans_symm (f : Λ₁ ≃ₗ Λ₂) : f.trans f.symm = refl Λ₁ :=
  ext f.left_inv

end IntegralLatticeEquiv
