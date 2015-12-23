-------------------------
-- 1.6 形式体系における証明
-------------------------
module LK2 where
-- P.23

open import PropositionalLogic public
open import Data.List renaming (_++_ to _,_) hiding ([_])
open import Data.Product renaming (_,_ to _+_)
open import Relation.Binary using (IsEquivalence)

infix 2 _⟶_ -- U+27F6
data 式 : Set where
  nil : 式 -- 明示されていないが、空の式というものもあると考えたほうが便利。
  _⟶_ : List 論理式 → List 論理式 → 式

-- Syntax sugars
infix 4 [_]
[_] : 論理式 → List 論理式
[ A ] = A ∷ []

postulate
  --始式 : (A : 論理式) → nil → ([ A ] ⟶ [ A ]) 

  -- 構造に関する推論規則 P.24
  weakening左   : ∀ Γ Δ A →  Γ ⟶ Δ  →  [ A ] , Γ ⟶ Δ 
  weakening右   : ∀ Γ Δ A →  Γ ⟶ Δ  →  Γ ⟶ Δ , [ A ] 

  contraction左 : ∀ Γ Δ A →  [ A ]  , [ A ] , Γ ⟶ Δ  →  [ A ] , Γ ⟶ Δ 
  contraction右 : ∀ Γ Δ A →  Γ ⟶ Δ , [ A ] , [ A ]   →  Γ ⟶ Δ , [ A ] 

  exchange左    : ∀ Γ Δ Π A B →  Γ , [ A ] , [ B ] , Π ⟶ Δ  →  Γ , [ B ] , [ A ] , Π ⟶ Δ 
  exchange右    : ∀ Γ Δ Σ A B →  Γ ⟶ Δ , [ A ] , [ B ] , Σ  →  Γ ⟶ Δ , [ B ] , [ A ] , Σ 

  cut          : ∀ Γ Δ Π Σ A → (Π ⟶ Δ , [ A ]) + ([ A ] , Π ⟶ Σ) →  Γ , Π ⟶ Δ , Σ 

  -- 論理結合子に関する推論規則 P.26
  ∧左1 : ∀ Γ Δ A B →  [ A ] , Γ ⟶ Δ  →  [ A ∧ B ] , Γ ⟶ Δ 
  ∧左2 : ∀ Γ Δ A B →  [ B ] , Γ ⟶ Δ  →  [ A ∧ B ] , Γ ⟶ Δ 
  ∧右  : ∀ Γ Δ A B → (Γ ⟶ Δ , [ A ]) + (Γ ⟶ Δ , [ B ]) →  (Γ ⟶ Δ , [ A ∧ B ]) 
  ∨左  : ∀ Γ Δ A B → ([ A ] , Γ ⟶ Δ) + ([ B ] , Γ ⟶ Δ) →  ([ A ∨ B ] , Γ ⟶ Δ) 
  ∨右1 : ∀ Γ Δ A B →  Γ ⟶ Δ , [ A ]  →  Γ ⟶ Δ , [ A ∨ B ] 
  ∨右2 : ∀ Γ Δ A B →  Γ ⟶ Δ , [ B ]  →  Γ ⟶ Δ , [ A ∨ B ] 
  ⊃左 : ∀ Γ Δ Π Σ A B → (Γ ⟶ Δ , [ A ]) + ([ B ] , Π ⟶ Σ) →  [ A ⊃ B ] , Γ , Π ⟶ Δ , Σ 
  ⊃右 : ∀ Γ Δ A B     →  [ A ] , Γ ⟶ Δ , [ B ]  →  Γ ⟶ Δ , [ A ⊃ B ] 
  ¬左 : ∀ Γ Δ A   →  Γ ⟶ Δ , [ A ]  →  [ ¬ A ] , Γ ⟶ Δ 
  ¬右 : ∀ Γ Δ A   →  [ A ] , Γ ⟶ Δ  →  Γ ⟶ Δ , [ ¬ A ] 

-- syntax sugar
⟶_ : List 論理式 → 式
⟶ A = [] ⟶ A


例1-12 : ∀ A → nil →  ⟶ [ A ∨ ¬ A ]  -- 問1-13でもある
例1-12 A = {!!}
{-
contraction右 [] [] (A ∨ ¬ A)
          (∨右1 [] [ A ∨ ¬ A ] A (¬ A)
          (exchange右 [] [] [] A (A ∨ ¬ A)
          (∨右2 [] [ A ] A (¬ A)
          (¬右 [] [ A ] A
          (始式 A)))))
-}

{-

-- P.27 定義1.3
data 証明図[終式_] : Set → Set where
  c1 : (A : 論理式) → 証明図[終式 (⟶ [ A ]) ]
  c2 : {A B C D : List 論理式}
         (P1 : 証明図[終式 A ⟶ B ]) → (A ⟶ B → C ⟶ D) → 証明図[終式 C ⟶ D ]
  c3 : {A B C D E F : List 論理式}
         (P1 : 証明図[終式 A ⟶ B ]) (P2 : 証明図[終式 C ⟶ D ])
                      → (A ⟶ B → C ⟶ D → E ⟶ F) → 証明図[終式 E ⟶ F ]



例1-12' : (A : 論理式) → 証明図[終式 (⟶ [ A ∨ ¬ A ]) ]
例1-12' A = c2 (c2 (c2 (c2 (c2 (c2 (c1 A)
            (λ _ → 始式 A))
            (¬右 [] [ A ] A))
            (∨右2 [] [ A ] A (¬ A)))
            (exchange右 [] [] [] A (A ∨ ¬ A)))
            (∨右1 [] [ A ∨ ¬ A ] A (¬ A)))
            (contraction右 [] [] (A ∨ ¬ A))

証明可能 : {Γ Δ : List 論理式} → Γ ⟶ Δ → Set
証明可能 {Γ} {Δ} seq = 証明図[終式 Γ ⟶ Δ ]

-- P.32 トートロジーの式への拡張
_* : List 論理式 → 論理式
[] *       = ⊥
(x ∷ xs) * = x ∨ (xs *)

_` : List 論理式 → 論理式 -- 下付き*はないので代用
[] `       = ⊤
(x ∷ xs) ` = x ∧ (xs `)

トートロジー' : (Γ Δ : List 論理式) → Set
トートロジー' Γ Δ = トートロジー ((Γ `) ⊃ (Δ *))

open import Relation.Binary.PropositionalEquality
-- 健全性定理
定理1-7 : ∀ {Γ Δ seq} → 証明可能 {Γ} {Δ} seq  → トートロジー' Γ Δ
定理1-7 {seq = 始式 A} proof v with v ⟦ A ⟧
定理1-7 {.(A ∷ [])} {.(A ∷ [])} {始式 A} proof v | t = refl
定理1-7 {.(A ∷ [])} {.(A ∷ [])} {始式 A} proof v | f = refl
定理1-7 {seq = weakening左 Γ ._ A seq} proof v = {!!}
定理1-7 {seq = weakening右 ._ Δ A seq} proof v = {!!}
定理1-7 {seq = contraction左 Γ ._ A seq} proof v = {!!}
定理1-7 {seq = contraction右 ._ Δ A seq} proof v = {!!}
定理1-7 {seq = exchange左 Γ ._ Π A B seq} proof v = {!!}
定理1-7 {seq = exchange右 ._ Δ Σ A B seq} proof v = {!!}
定理1-7 {seq = cut Γ Δ Π Σ A seq seq₁} proof v = {!!}
定理1-7 {seq = ∧左1 Γ ._ A B seq} proof v = {!!}
定理1-7 {seq = ∧左2 Γ ._ A B seq} proof v = {!!}
定理1-7 {seq = ∧右 ._ Δ A B seq seq₁} proof v = {!!}
定理1-7 {seq = ∨左 Γ ._ A B seq seq₁} proof v = {!!}
定理1-7 {seq = ∨右1 ._ Δ A B seq} proof v = {!!}
定理1-7 {seq = ∨右2 ._ Δ A B seq} proof v = {!!}
定理1-7 {seq = ⊃左 Γ Δ Π Σ A B Γ→ΔA BΠ→Σ} proof v = {!!}
定理1-7 {seq = ⊃右 ._ Δ A B seq} proof v = {!!}
定理1-7 {seq = ¬左 Γ ._ A seq} proof v = {!!}
定理1-7 {seq = ¬右 ._ Δ A seq} proof v = {!!}
-}
