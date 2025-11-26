import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant

open Module
open FiniteDimensional

/-- An *integral lattice* is a finitely generated free abelian group
of finite rank `n` with a bilinear form that takes integer values. -/
class IntegralLatticeNondefinite (Λ : Type*) extends Inner ℤ Λ, AddCommGroup Λ where
  [free : Free ℤ Λ]
  [finite : Finite ℤ Λ]
  (add_inner : ∀ x y z: Λ, ⟪(x + y), z⟫_ℤ = ⟪x, z⟫_ℤ + ⟪y, z⟫_ℤ)
  (inner_sym : ∀ x y: Λ, ⟪x, y⟫_ℤ = ⟪y, x⟫_ℤ)
--  (inner_self : ∀ x: Λ, ⟪x, x⟫_ℤ ≥ 0)
--  (inner_self_eq_zero : ∀ x: Λ, ⟪x, x⟫_ℤ = 0 → x = 0)
