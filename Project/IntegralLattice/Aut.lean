/-
Copyright (c) 2024 Erik van der Plas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik van der Plas
-/
import Mathlib.GroupTheory.IntegralLattice.Equiv
import Mathlib.LinearAlgebra.Determinant

variable (Λ : Type*) [IntegralLattice Λ]

/-- The group of integral lattice automorphisms -/
@[reducible]
def IntegralLatticeAut := IntegralLatticeEquiv Λ Λ

namespace IntegralLatticeAut

/-- Integral lattice automorphisms form a group under composition. -/
instance : Group (IntegralLatticeAut Λ) where
  mul f g := IntegralLatticeEquiv.trans g f
  one := IntegralLatticeEquiv.refl Λ
  inv := IntegralLatticeEquiv.symm
  mul_assoc := by intros; rfl
  one_mul := by intros; rfl
  mul_one := by intros; rfl
  mul_left_inv := IntegralLatticeEquiv.self_trans_symm

variable {Λ}

@[simp]
lemma one_apply (x : Λ) : (1 : IntegralLatticeAut Λ) x = x :=
  rfl

@[simp]
lemma mul_apply (f g : IntegralLatticeAut Λ) (x : Λ) : (f * g) x = f (g x) :=
  rfl

/-- The determinant of an integral lattice automorphism, as a group homomorphism. -/
noncomputable
def det : IntegralLatticeAut Λ →* ℤ where
  toFun := fun f ↦ LinearMap.det f.toAddEquiv.toAddMonoidHom.toIntLinearMap
  map_one' := LinearMap.det_id
  map_mul' := fun f g ↦ by
    dsimp
    rw [← map_mul]
    rfl

lemma _root_.SignType.cast_inj : Function.Injective SignType.cast := by
  intros a b h
  revert a b
  decide

def _root_.Int.SignHom : ℤ →* SignType := {
  toFun := fun n => SignType.sign n,
  map_one' := rfl
  map_mul' := fun n m => by
    dsimp
    have : Int.sign (n * m) = Int.sign n * Int.sign m := by
      simp
    simp [Int.sign_eq_sign] at this
    norm_cast at this
    rwa [SignType.cast_inj.eq_iff] at this
}

noncomputable
def SignHom : IntegralLatticeAut Λ →* SignType := Int.SignHom.comp det

end IntegralLatticeAut
