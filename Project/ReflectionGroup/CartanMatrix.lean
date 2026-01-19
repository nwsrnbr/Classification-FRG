import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Symmetric

namespace MyCartanMatrix

variable (n : ℕ)

/-- The Cartan matrix of type Aₙ.

The corresponding Coxeter-Dynkin diagram is:
```
    o --- o --- o ⬝ ⬝ ⬝ ⬝ o --- o
```
-/
def Aₙ : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
      else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then -1 else 0)

/-- The Cartan matrix of type Bₙ.

The corresponding Coxeter-Dynkin diagram is:
```
    o =<= o --- o ⬝ ⬝ ⬝ ⬝ o --- o
```
-/
def Bₙ : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
      else (if i = n - 2 ∧ j = n - 1 then -2
        else (if j = n - 2 ∧ i = n - 1 then -1
          else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then -1 else 0)))

/-- The Cartan matrix of type Cₙ.

The corresponding Coxeter-Dynkin diagram is:
```
    o =>= o --- o ⬝ ⬝ ⬝ ⬝ o --- o
```
-/
def Cₙ : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
      else (if i = n - 2 ∧ j = n - 1 then -1
        else (if j = n - 2 ∧ i = n - 1 then -2
          else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then -1 else 0)))

/-- The Cartan matrix of type Dₙ.

The corresponding Coxeter-Dynkin diagram is:
```
    o
     \
      o --- o ⬝ ⬝ ⬝ ⬝ o --- o
     /
    o
```
-/
def Dₙ : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j : Fin n ↦
    if i = j then 2
      else (if i = (0 : ℕ) ∧ j = (2 : ℕ) ∨ j = (0 : ℕ) ∧ i = (2 : ℕ) then -1
        else(if i = (0 : ℕ) ∧ j = (1 : ℕ) ∨ j = (0 : ℕ) ∧ i = (1 : ℕ) then 0
          else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then -1 else 0)))
-- Mathlib.GroupTheory.Coxeter.Matrix の Dₙ の定義は多分間違ってる(ループができてしまう)

/-- The Cartan matrix of type E₆. See [bourbaki1968] plate V, page 277.

The corresponding Dynkin diagram is:
```
            o
            |
o --- o --- o --- o --- o
```
-/
def E₆ : Matrix (Fin 6) (Fin 6) ℤ :=
  !![2, -1, 0, 0, 0, 0;
    -1, 2, -1, 0, 0, 0;
    0, -1, 2, -1, -1, 0;
    0, 0, -1, 2, 0, 0;
    0, 0, -1, 0, 2, -1;
    0, 0, 0, 0, -1, 2]

/-- The Cartan matrix of type e₇. See [bourbaki1968] plate VI, page 281.

The corresponding Dynkin diagram is:
```
            o
            |
o --- o --- o --- o --- o --- o
```
-/
def E₇ : Matrix (Fin 7) (Fin 7) ℤ :=
  !![2, -1, 0, 0, 0, 0, 0;
    -1, 2, -1, 0, 0, 0, 0;
    0, -1, 2, -1, -1, 0, 0;
    0, 0, -1, 2, 0, 0, 0;
    0, 0, -1, 0, 2, -1, 0;
    0, 0, 0, 0, -1, 2, -1;
    0, 0, 0, 0, 0, -1, 2]

/-- The Cartan matrix of type e₈. See [bourbaki1968] plate VII, page 285.

The corresponding Dynkin diagram is:
```
            o
            |
o --- o --- o --- o --- o --- o --- o
```
-/
def E₈ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![2, -1, 0, 0, 0, 0, 0, 0;
    -1, 2, -1, 0, 0, 0, 0, 0;
    0, -1, 2, -1, -1, 0, 0, 0;
    0, 0, -1, 2, 0, 0, 0, 0;
    0, 0, -1, 0, 2, -1, 0, 0;
    0, 0, 0, 0, -1, 2, -1, 0;
    0, 0, 0, 0, 0, -1, 2, -1;
    0, 0, 0, 0, 0, 0, -1, 2]

/-- The Cartan matrix of type f₄. See [bourbaki1968] plate VIII, page 288.

The corresponding Dynkin diagram is:
```
o --- o =>= o --- o
```
-/
def F₄ : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2, -1, 0, 0; -1, 2, -2, 0; 0, -1, 2, -1; 0, 0, -1, 2]

/-- The Cartan matrix of type g₂. See [bourbaki1968] plate IX, page 290.

The corresponding Dynkin diagram is:
```
o ≡>≡ o
```
Actually we are using the transpose of Bourbaki's matrix. This is to make this matrix consistent
with `CartanMatrix.F₄`, in the sense that all non-zero values below the diagonal are -1. -/
def G₂ : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2, -3; -1, 2]

/-- The Cartan matrix of type A'ₙ.

The corresponding Coxeter-Dynkin diagram is:
```
    ┌---------- o ------------┐
    o --- o --- o ⬝ ⬝ ⬝ ⬝ o --- o
```
-/
def A'ₙ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if i = j then 2
      else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then -1
        else (if i = (0 : ℕ) ∧ j = n ∨ j = (0 : ℕ) ∧ i = n then -1 else 0))

/-- The Cartan matrix of type B'ₙ.

The corresponding Coxeter-Dynkin diagram is:
```
    o
     \
      o --- o ⬝ ⬝ ⬝ ⬝ o =>= o
     /
    o
```
-/
def B'ₙ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if i = j then 2
      else (if i = (0 : ℕ) ∧ j = (2 : ℕ) ∨ j = (0 : ℕ) ∧ i = (2 : ℕ) then -1
        else(if i = (0 : ℕ) ∧ j = (1 : ℕ) ∨ j = (0 : ℕ) ∧ i = (1 : ℕ) then 0
          else (if i = n - 1 ∧ j = n then -2
            else (if j = n - 1 ∧ i = n then -1
              else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then -1 else 0)))))

/-- The Cartan matrix of type C'ₙ.

The corresponding Coxeter-Dynkin diagram is:
```

    o =>= o --- o ⬝ ⬝ ⬝ ⬝ o =<= o
```
-/
def C'ₙ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if i = j then 2
      else (if i = n - 1 ∧ j = n then -1
        else (if j = n - 1 ∧ i = n then -2
          else (if i = (1 : ℕ) ∧ j = (0 : ℕ) then -1
            else (if j = (1 : ℕ) ∧ i = (0 : ℕ) then -2
              else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then -1 else 0)))))

/-- The Cartan matrix of type D'ₙ.

The corresponding Coxeter-Dynkin diagram is:
```
    o                       o
     \                     /
      o --- o ⬝ ⬝ ⬝ ⬝ o --- o
     /                     \
    o                       o
```
-/
def D'ₙ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun i j : Fin (n + 1) ↦
    if i = j then 2
      else (if i = (0 : ℕ) ∧ j = (2 : ℕ) ∨ j = (0 : ℕ) ∧ i = (2 : ℕ) then -1
        else(if i = (0 : ℕ) ∧ j = (1 : ℕ) ∨ j = (0 : ℕ) ∧ i = (1 : ℕ) then 0
          else (if i = n - 1 ∧ j = n - 3 ∨ j = n - 1 ∧ i = n - 3 then -1
            else(if i = n - 2 ∧ j = n - 3 ∨ j = n - 2 ∧ i = n - 3 then 0
              else (if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then -1 else 0)))))
-- Mathlib.GroupTheory.Coxeter.Matrix の Dₙ の定義は多分間違ってる(ループができてしまう)

/-- The Cartan matrix of type E'₆.

The corresponding Dynkin diagram is:
```
            o
            |
            o
            |
o --- o --- o --- o --- o
```
-/
def E'₆ : Matrix (Fin 7) (Fin 7) ℤ :=
  !![2, -1, 0, 0, 0, 0, 0;
    -1, 2, -1, 0, 0, 0, 0;
    0, -1, 2, -1, 0, -1, 0;
    0, 0, -1, 2, -1, 0, 0;
    0, 0, 0, -1, 2, 0, 0;
    0, 0, -1, 0, 0, 2, -1;
    0, 0, 0, 0, 0, -1, 2]

/-- The Cartan matrix of type E'₇.

The corresponding Dynkin diagram is:
```
                  o
                  |
o --- o --- o --- o --- o --- o --- o
```
-/
def E'₇ : Matrix (Fin 8) (Fin 8) ℤ :=
  !![2, -1, 0, 0, 0, 0, 0, 0;
    -1, 2, -1, 0, 0, 0, 0, 0;
    0, -1, 2, -1, 0, 0, 0, 0;
    0, 0, -1, 2, -1, -1, 0, 0;
    0, 0, 0, -1, 2, 0, 0, 0;
    0, 0, 0, -1, 0, 2, -1, 0;
    0, 0, 0, 0, 0, -1, 2, -1;
    0, 0, 0, 0, 0, 0, -1, 2]

/-- The Cartan matrix of type E'₈.

The corresponding Dynkin diagram is:
```
            o
            |
o --- o --- o --- o --- o --- o --- o --- o
```
-/
def E'₈ : Matrix (Fin 9) (Fin 9) ℤ :=
  !![2, -1, 0, 0, 0, 0, 0, 0, 0;
    -1, 2, -1, 0, 0, 0, 0, 0, 0;
    0, -1, 2, -1, -1, 0, 0, 0, 0;
    0, 0, -1, 2, 0, 0, 0, 0, 0;
    0, 0, -1, 0, 2, -1, 0, 0, 0;
    0, 0, 0, 0, -1, 2, -1, 0, 0;
    0, 0, 0, 0, 0, -1, 2, -1, 0;
    0, 0, 0, 0, 0, 0, -1, 2, -1;
    0, 0, 0, 0, 0, 0, 0, -1, 2]

/-- The Cartan matrix of type F'₄.

The corresponding Dynkin diagram is:
```
o --- o --- o =>= o --- o
```
-/
def F'₄ : Matrix (Fin 5) (Fin 5) ℤ :=
  !![2, -1, 0, 0, 0;
    -1, 2, -2, 0, 0;
    0, -1, 2, -1, 0;
    0, 0, -1, 2, -1;
    0, 0, 0, -1, 2]

/-- The Cartan matrix of type G'₂.

The corresponding Dynkin diagram is:
```
o --- o ≡>≡ o
```
Actually we are using the transpose of Bourbaki's matrix. This is to make this matrix consistent
with `CartanMatrix.F₄`, in the sense that all non-zero values below the diagonal are -1. -/
def G'₂ : Matrix (Fin 3) (Fin 3) ℤ :=
  !![2, -3, 0;
    -1, 2, -1;
    0, -1, 2]

#eval A'ₙ 4

/-

-/
end MyCartanMatrix
