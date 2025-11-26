import Mathlib.Data.Fintype.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.GroupTheory.Coxeter.Basic

namespace CoxeterMatrix

#check Matrix.toSquareBlock

variable {B B' : Type*}
variable {W H : Type*} [Group W] [Group H]
variable {M : CoxeterMatrix B} (csW : CoxeterSystem M W)
variable {N : CoxeterMatrix B'} (csH : CoxeterSystem N H)

def CoxeterDiagram (M : CoxeterMatrix B) : SimpleGraph B :=
  { Adj := fun i j => M i j ≥ 3,
    symm := by
      intro i j h
      rwa [symmetric],
    loopless := by
      intro i
      simp }

def irreducible (M : CoxeterMatrix B) : Prop :=
  (CoxeterDiagram M).Connected

def Isreducible (M : CoxeterMatrix B) : Prop :=
  ∃ I : Set B, I.Nonempty ∧ ∀ i j, i ∈ I → j ∉ I → M i j = 2

def IsIrreducible (M : CoxeterMatrix B) : Prop :=
  ¬ Isreducible M

theorem classification (h_irred : M.irreducible) (h_fin : Finite B) :
  (∃ (n : ℕ) (e : B ≃ Fin n), M.reindex e = Aₙ n ∨ M.reindex e = Bₙ n ∨ M.reindex e = Dₙ n) ∨
  (∃ (e : B ≃ Fin 2), M.reindex e = G₂ ∨ ∃ m : ℕ, M.reindex e = I₂ₘ m) ∨
  (∃ (e : B ≃ Fin 3), M.reindex e = H₃) ∨
  (∃ (e : B ≃ Fin 4), M.reindex e = F₄ ∨ M.reindex e = H₄) ∨
  (∃ (e : B ≃ Fin 6), M.reindex e = E₆) ∨
  (∃ (e : B ≃ Fin 7), M.reindex e = E₇) ∨
  (∃ (e : B ≃ Fin 8), M.reindex e = E₈) := by
    apply Finite.exists_equiv_fin at h_fin
    obtain ⟨n, e⟩ := h_fin
    sorry

end CoxeterMatrix
