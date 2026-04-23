/-

--import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.LinearAlgebra.Reflection
import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.LinearAlgebra.RootSystem.IsValuedIn
import Mathlib.LinearAlgebra.RootSystem.Reduced

/-
variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

structure FiniteReflectionGroup where
  W : Subgroup (E ≃ₗᵢ[𝕜] E)
  isFinite : Finite W
  gen_ref : ∃ n : ℕ, ∃ v : Fin n → E, W = Subgroup.closure (Set.range fun i ↦ (Submodule.span 𝕜 {v i}).reflection)
-/
variable (ι R M N : Type*) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

structure FiniteReflectionGroup where
  W : Subgroup (M ≃ₗ[R] M)
  isFinite : Finite W
  α : ι ↪ M
  eq_two : ∀ i, ∃ f : Module.Dual R M, f (α i) = 2
  gen_set : Set (M ≃ₗ[R] M) := Set.range fun i ↦ Module.reflection (eq_two i).choose_spec
  gen_ref : W = Subgroup.closure gen_set

def Fix (W : FiniteReflectionGroup ι R M) :=
  {v : M // ∀ w : W.W, w.val v = v}

structure essFRG extends FiniteReflectionGroup ι R M where
  essential : ∀ v : M, ∀ w : W, w.val v = v ↔ v = 0

namespace FiniteReflectionGroup
variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-
def essFRG_to_RootSystem (W : essFRG ι R M) (W' : essFRG ι R M) : IsRootSystem ι R M M where
  toFun := by
    rcases W.eq_two with f
  root := W.v
  coroot := W'.v
  root_coroot_two := by
    intro i
    rcases W.eq_two i with ⟨f, hf⟩
    simp
-/

def RootSystem_to_essFRG (P : IsRootSystem ι R M N) : essFRG ι R M where
  W := Subgroup.closure (Set.range fun i ↦ P.reflection i)
  isFinite := by sorry
  α := P.root
  eq_two := by
    intro i
    use (P.flip.toLinearMap (P.coroot i))
    apply P.flip.root_coroot_two i
  gen_set := (Set.range fun i ↦ P.reflection i)
  gen_ref := rfl
  essential := by
    intro v w
    constructor
    <;> intro h
    · sorry
    · rw [h]
      simp

end FiniteReflectionGroup

variable {ι E F : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] [SeminormedAddCommGroup F]
  [InnerProductSpace ℝ F] (Φ : IsRootSystem ι ℝ E F) [Φ.IsReduced]

structure PositiveRootSystem (Φ : IsRootSystem ι ℝ E F) (p : E) where
  pos_index : Set ι
  p_ne_zero : p ≠ 0
  inner_ne_zero : ∀ i : pos_index, inner ℝ (Φ.root i) p ≠ 0
  pos : ∀ i : pos_index, inner ℝ (Φ.root i) p > 0

structure SimpleRootSystem (p : E) (P : PositiveRootSystem Φ p) where
  simp_index : Set ι
  simp_index_fin : Fintype (Subtype simp_index) -- Subtype simp_index = {i ∈ ι | ι ∈ simp_index}
  indep : LinearIndependent ℝ (Φ.root ∘ (Subtype.val : Subtype simp_index → ι))
  span : Submodule.span ℝ (Set.range (Φ.root ∘ (Subtype.val : Subtype simp_index → ι))) = ⊤
  linear_comb : ∀ i : P.pos_index, ∃ c : Subtype simp_index → ℝ, (∀ j, 0 ≤ c j) ∧ (Φ.root i = ∑ j, c j • Φ.root j)

namespace RootPairing

theorem exists_PositiveRootSystem (Φ : IsRootSystem ι ℝ E F) :
    ∃ p : E, ∃ P : PositiveRootSystem Φ p, True := by
  sorry

theorem exists_SimpleRootSystem (Φ : IsRootSystem ι ℝ E F) :
    ∃ Δ : SimpleRootSystem Φ (exists_PositiveRootSystem Φ).choose (exists_PositiveRootSystem Φ).choose_spec.choose, True := by
  sorry

theorem unique_SimpleRootSystem (Φ : IsRootSystem ι ℝ E F) :
    ∀ Δ₁ Δ₂ : SimpleRootSystem Φ (exists_PositiveRootSystem Φ).choose (exists_PositiveRootSystem Φ).choose_spec.choose,
      Δ₁ = Δ₂ := by
  sorry

theorem FRG_gen_by_SimpleRootSystem (Φ :IsRootSystem ι ℝ E F) :
    (FiniteReflectionGroup.RootSystem_to_essFRG Φ).gen_set =
      Set.range fun i : (exists_SimpleRootSystem Φ).choose.simp_index ↦ Module.reflection ((FiniteReflectionGroup.RootSystem_to_essFRG Φ).eq_two i).choose_spec := by
  sorry


-/
