-------------------------
-- 1.6 形式体系における証明
-------------------------
module LK where
-- P.23

open import PropositionalLogic
open import Data.List renaming (_++_ to _,_)

-- 式
infix 1 _⟶_ -- U+27F6 
data _⟶_ : List 論理式 → List 論理式 → Set where
  始式 : (A : 論理式) → [ A ] ⟶ [ A ]
  -- 構造に関する推論規則 P.24
  weakening左 : ∀ Γ Δ A → (Γ ⟶ Δ) → ([ A ] , Γ ⟶ Δ)
  weakening右 : ∀ Γ Δ A → (Γ ⟶ Δ) → (Γ ⟶ Δ , [ A ])
  contraction左 : ∀ Γ Δ A → ([ A ] , [ A ] , Γ ⟶ Δ) → ([ A ] , Γ ⟶ Δ) 
  contraction右 : ∀ Γ Δ A → (Γ ⟶ Δ , [ A ] , [ A ]) → (Γ ⟶ Δ , [ A ]) 
  exchange左 : ∀ Γ Δ Π A B  → (Γ , [ A ] , [ B ] , Π ⟶ Δ) → (Γ , [ B ] , [ A ] , Π ⟶ Δ) 
  exchange右 : ∀ Γ Δ Σ A B  → (Γ ⟶ Δ , [ A ] , [ B ] , Σ) → (Γ ⟶ Δ , [ B ] , [ A ] , Σ) 
  cut : ∀ Γ Δ Π Σ A  → (Π ⟶ Δ , [ A ]) → ([ A ] , Π ⟶ Σ) → (Γ , Π ⟶ Δ , Σ) 
  -- 論理結合子に関する推論規則 P.26
  ∧左1 : ∀ Γ Δ A B → ([ A ] , Γ ⟶ Δ) → ([ A ∧ B ] , Γ ⟶ Δ) 
  ∧左2 : ∀ Γ Δ A B → ([ B ] , Γ ⟶ Δ) → ([ A ∧ B ] , Γ ⟶ Δ) 
  ∧右  : ∀ Γ Δ A B → (Γ ⟶ Δ , [ A ]) → (Γ ⟶ Δ , [ B ]) → (Γ ⟶ Δ , [ A ∧ B ])
  ∨左  : ∀ Γ Δ A B → ([ A ] , Γ ⟶ Δ) → ([ B ] , Γ ⟶ Δ) → ([ A ∨ B ] , Γ ⟶ Δ)
  ∨右1 : ∀ Γ Δ A B → (Γ ⟶ Δ , [ A ]) → (Γ ⟶ Δ , [ A ∨ B ])
  ∨右2 : ∀ Γ Δ A B → (Γ ⟶ Δ , [ B ]) → (Γ ⟶ Δ , [ A ∨ B ])
  ⊃左 : ∀ Γ Δ Π Σ A B → (Γ ⟶ Δ , [ A ]) → ([ B ] , Π ⟶ Σ) → ([ A ⊃ B ] , Γ , Π ⟶ Δ , Σ)
  ⊃右 : ∀ Γ Δ A B → ([ A ] , Γ ⟶ Δ , [ B ]) → (Γ ⟶ Δ , [ A ⊃ B ])
  ¬左 : ∀ Γ Δ A → (Γ ⟶ Δ , [ A ]) → ([ ¬ A ] , Γ ⟶ Δ)
  ¬右 : ∀ Γ Δ A → ([ A ] , Γ ⟶ Δ) → (Γ ⟶ Δ , [ ¬ A ])

-- syntax sugar
⟶_ : List 論理式 → Set
⟶ A = [] ⟶ A

-- P.27 定義1.3
data 証明図[終式_] : Set → Set where
  c1 : (A : 論理式) → 証明図[終式 (⟶ [ A ]) ]
  c2 : {A B C D : List 論理式} 
         (P1 : 証明図[終式 A ⟶ B ]) → (A ⟶ B → C ⟶ D) → 証明図[終式 C ⟶ D ]
  c3 : {A B C D E F : List 論理式}
         (P1 : 証明図[終式 A ⟶ B ]) (P2 : 証明図[終式 C ⟶ D ]) 
                      → (A ⟶ B → C ⟶ D → E ⟶ F) → 証明図[終式 E ⟶ F ]


例1-12 : ∀ A → [] ⟶ [ A ∨ ¬ A ] -- 問1-13でもある
例1-12 A = contraction右 [] [] (A ∨ ¬ A)
          (∨右1 [] [ A ∨ ¬ A ] A (¬ A) 
          (exchange右 [] [] [] A (A ∨ ¬ A) 
          (∨右2 [] [ A ] A (¬ A) 
          (¬右 [] [ A ] A 
          (始式 A))))) 

例1-12' : (A : 論理式) → 証明図[終式 (⟶ [ A ∨ ¬ A ]) ]
例1-12' A = c2 (c2 (c2 (c2 (c2 (c2 (c1 A) 
            (λ _ → 始式 A))
            (¬右 [] [ A ] A)) 
            (∨右2 [] [ A ] A (¬ A))) 
            (exchange右 [] [] [] A (A ∨ ¬ A))) 
            (∨右1 [] [ A ∨ ¬ A ] A (¬ A))) 
            (contraction右 [] [] (A ∨ ¬ A))

証明可能 : (Γ Δ : List 論理式) → Set
証明可能 Γ Δ = 証明図[終式 Γ ⟶ Δ ]

-- P.32 トートロジーの式への拡張
_* : List 論理式 → 論理式
[] *       = ⊥
(x ∷ xs) * = x ∨ (xs *) 

_` : List 論理式 → 論理式 -- 下付き*はないので代用
[] `       = ⊤
(x ∷ xs) ` = x ∧ (xs `)

トートロジー' : (Γ Δ : List 論理式) → Γ ⟶ Δ → Set
トートロジー' Γ Δ seq = トートロジー ((Γ `) ⊃ (Δ *))
