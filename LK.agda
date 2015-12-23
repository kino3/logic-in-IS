-------------------------
-- 1.6 形式体系における証明
-------------------------
module LK where
-- P.23

open import PropositionalLogic public renaming (トートロジー to トートロジー')
open import Data.List renaming (_++_ to _,_) hiding ([_])
open import Data.Product renaming (_,_ to _+_)
open import Relation.Binary using (IsEquivalence)
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _≈_) hiding ([_])
open import Data.Unit renaming (⊤ to True)

infix 2 _⟶_ -- U+27F6
data 式 : Set where
  n : 式 -- 明示されていないが、空の式というものもあると考えたほうが便利。
  _⟶_ : List 論理式 → List 論理式 → 式

-- Syntax sugars
nil : 式 × 式
nil = n + n

infix 4 [_]
[_] : 論理式 → List 論理式
[ A ] = A ∷ []

infix 3 ⟨_⟩
⟨_⟩ : 式 → 式 × 式
⟨ S ⟩ = S + n

infix 1 _/_
{-
 証明図の横棒を'/'で表現する。
 証明図には上式2,下式1のものと上式1,下式1のものがある。両方に対応するため、
 _/_というのは式2つの上の関係であると定義する。
-}
data _/_ : 式 × 式 → 式 × 式 → Set where
  -- 構造に関する推論規則 P.24
  weakening左   : ∀ Γ Δ A → ⟨ Γ ⟶ Δ ⟩ / ⟨ [ A ] , Γ ⟶ Δ ⟩
  weakening右   : ∀ Γ Δ A → ⟨ Γ ⟶ Δ ⟩ / ⟨ Γ ⟶ Δ , [ A ] ⟩

  contraction左 : ∀ Γ Δ A → ⟨ [ A ]  , [ A ] , Γ ⟶ Δ ⟩ / ⟨ [ A ] , Γ ⟶ Δ ⟩
  contraction右 : ∀ Γ Δ A → ⟨ Γ ⟶ Δ , [ A ] , [ A ] ⟩  / ⟨ Γ ⟶ Δ , [ A ] ⟩

  exchange左    : ∀ Γ Δ Π A B → ⟨ Γ , [ A ] , [ B ] , Π ⟶ Δ ⟩ / ⟨ Γ , [ B ] , [ A ] , Π ⟶ Δ ⟩
  exchange右    : ∀ Γ Δ Σ A B → ⟨ Γ ⟶ Δ , [ A ] , [ B ] , Σ ⟩ / ⟨ Γ ⟶ Δ , [ B ] , [ A ] , Σ ⟩

  cut          : ∀ Γ Δ Π Σ A → (Π ⟶ Δ , [ A ]) + ([ A ] , Π ⟶ Σ) / ⟨ Γ , Π ⟶ Δ , Σ ⟩

  -- 論理結合子に関する推論規則 P.26
  ∧左1 : ∀ Γ Δ A B → ⟨ [ A ] , Γ ⟶ Δ ⟩ / ⟨ [ A ∧ B ] , Γ ⟶ Δ ⟩
  ∧左2 : ∀ Γ Δ A B → ⟨ [ B ] , Γ ⟶ Δ ⟩ / ⟨ [ A ∧ B ] , Γ ⟶ Δ ⟩
  ∧右  : ∀ Γ Δ A B → (Γ ⟶ Δ , [ A ]) + (Γ ⟶ Δ , [ B ]) / ⟨ (Γ ⟶ Δ , [ A ∧ B ]) ⟩
  ∨左  : ∀ Γ Δ A B → ([ A ] , Γ ⟶ Δ) + ([ B ] , Γ ⟶ Δ) / ⟨ ([ A ∨ B ] , Γ ⟶ Δ) ⟩
  ∨右1 : ∀ Γ Δ A B → ⟨ Γ ⟶ Δ , [ A ] ⟩ / ⟨ Γ ⟶ Δ , [ A ∨ B ] ⟩
  ∨右2 : ∀ Γ Δ A B → ⟨ Γ ⟶ Δ , [ B ] ⟩ / ⟨ Γ ⟶ Δ , [ A ∨ B ] ⟩
  ⊃左 : ∀ Γ Δ Π Σ A B → (Γ ⟶ Δ , [ A ]) + ([ B ] , Π ⟶ Σ) / ⟨ [ A ⊃ B ] , Γ , Π ⟶ Δ , Σ ⟩
  ⊃右 : ∀ Γ Δ A B     → ⟨ [ A ] , Γ ⟶ Δ , [ B ] ⟩ / ⟨ Γ ⟶ Δ , [ A ⊃ B ] ⟩
  ¬左 : ∀ Γ Δ A   → ⟨ Γ ⟶ Δ , [ A ] ⟩ / ⟨ [ ¬ A ] , Γ ⟶ Δ ⟩
  ¬右 : ∀ Γ Δ A   → ⟨ [ A ] , Γ ⟶ Δ ⟩ / ⟨ Γ ⟶ Δ , [ ¬ A ] ⟩

-- syntax sugar
⟶_ : List 論理式 → 式
⟶ A = [] ⟶ A

{-
必要かとおもっていたが、証明図を定義したことで不要になった。
postulate
  refl  : ∀ {x} → x / x
  sym   : ∀ {x y} → x / y → y / x
  trans : ∀ {x y z} → x / y → y / z → x / z 
-}

{- 
 始式というのは特定の式のことを指しているのだから、ある意味式の性質であり、この型が妥当かと。
 こう定義することで他の推論規則とは区別される。
-}
data 始式 : 式 → Set where
  init : (A : 論理式) → 始式 ([ A ] ⟶ [ A ])

data 証明図[終式_] : 式 → Set where
  c1 : {seq : 式} → 始式 seq → 証明図[終式 seq ]
  c2 : {A B C D : List 論理式}
         (P1 : 証明図[終式 A ⟶ B ]) → (⟨ A ⟶ B ⟩ / ⟨ C ⟶ D ⟩) → 証明図[終式 C ⟶ D ]
  c3 : {A B C D E F : List 論理式}
         (P1 : 証明図[終式 A ⟶ B ]) (P2 : 証明図[終式 C ⟶ D ])
                      → (A ⟶ B) + (C ⟶ D) / ⟨ E ⟶ F ⟩ → 証明図[終式 E ⟶ F ]

証明可能 : 式 → Set
証明可能 S = 証明図[終式 S ]

式_は_である : 式 → (式 → Set) → Set
式 S は P である = P S

例1-12 : ∀ A → 式 (⟶ [ A ∨ ¬ A ]) は 証明可能 である 
例1-12 A = c2 (c2 (c2 (c2 (c2 (c1 
          (init A)) 
          (¬右 [] [ A ] A)) 
          (∨右2 [] [ A ] A (¬ A))) 
          (exchange右 [] [] [] A (A ∨ ¬ A))) 
          (∨右1 [] ([ A ∨ ¬ A ]) A (¬ A))) 
          (contraction右 [] [] (A ∨ ¬ A)) 

-- P.32 トートロジーの式への拡張
_* : List 論理式 → 論理式
[] *       = ⊥
(x ∷ xs) * = x ∨ (xs *)

_` : List 論理式 → 論理式 -- 下付き*はないので代用
[] `       = ⊤
(x ∷ xs) ` = x ∧ (xs `)

トートロジー : 式 → Set
トートロジー n        = True
トートロジー (Γ ⟶ Δ) = トートロジー' ((Γ `) ⊃ (Δ *)) --

Lemma1-7-1 : ∀ seq → 始式 seq → 式 seq  は トートロジー である
Lemma1-7-1 .([ A ] ⟶ [ A ]) (init A) v with v ⟦ A ⟧
Lemma1-7-1 .([ A ] ⟶ [ A ]) (init A) v | t = refl
Lemma1-7-1 .([ A ] ⟶ [ A ]) (init A) v | f = refl

open import Relation.Nullary.Negation using (contradiction)
Lemma1-7-2 : ∀ S1 S2 S3 → S1 + S2 / ⟨ S3 ⟩ 
  → 式 S1 は トートロジー である → 式 S2 は トートロジー である → 式 S3 は トートロジー である
Lemma1-7-2 .(Γ ⟶ Δ) .n .(A ∷ Γ ⟶ Δ) (weakening左 Γ Δ A) prf1 tt v = {!!}

Lemma1-7-2 .(Γ ⟶ Δ) .n .(Γ ⟶ Δ , A ∷ []) (weakening右 Γ Δ A) prf1 prf2 v = {!!}
Lemma1-7-2 .(A ∷ A ∷ Γ ⟶ Δ) .n .(A ∷ Γ ⟶ Δ) (contraction左 Γ Δ A) prf1 prf2 v = {!!}
Lemma1-7-2 .(Γ ⟶ Δ , A ∷ A ∷ []) .n .(Γ ⟶ Δ , A ∷ []) (contraction右 Γ Δ A) prf1 prf2 v = {!!}
Lemma1-7-2 .(Γ , A ∷ B ∷ Π ⟶ Δ) .n .(Γ , B ∷ A ∷ Π ⟶ Δ) (exchange左 Γ Δ Π A B) prf1 prf2 v = {!!}
Lemma1-7-2 .(Γ ⟶ Δ , A ∷ B ∷ Σ) .n .(Γ ⟶ Δ , B ∷ A ∷ Σ) (exchange右 Γ Δ Σ A B) prf1 prf2 v = {!!}
Lemma1-7-2 .(Π ⟶ Δ , A ∷ []) .(A ∷ Π ⟶ Σ) .(Γ , Π ⟶ Δ , Σ) (cut Γ Δ Π Σ A) prf1 prf2 v = {!!}
Lemma1-7-2 .(A ∷ Γ ⟶ Δ) .n .(A ∧ B ∷ Γ ⟶ Δ) (∧左1 Γ Δ A B) prf1 prf2 v = {!!}
Lemma1-7-2 .(B ∷ Γ ⟶ Δ) .n .(A ∧ B ∷ Γ ⟶ Δ) (∧左2 Γ Δ A B) prf1 prf2 v = {!!}
Lemma1-7-2 .(Γ ⟶ Δ , A ∷ []) .(Γ ⟶ Δ , B ∷ []) .(Γ ⟶ Δ , A ∧ B ∷ []) (∧右 Γ Δ A B) prf1 prf2 v = {!!}
Lemma1-7-2 .(A ∷ Γ ⟶ Δ) .(B ∷ Γ ⟶ Δ) .(A ∨ B ∷ Γ ⟶ Δ) (∨左 Γ Δ A B) prf1 prf2 v = {!!}
Lemma1-7-2 .(Γ ⟶ Δ , A ∷ []) .n .(Γ ⟶ Δ , A ∨ B ∷ []) (∨右1 Γ Δ A B) prf1 prf2 v = {!!}
Lemma1-7-2 .(Γ ⟶ Δ , B ∷ []) .n .(Γ ⟶ Δ , A ∨ B ∷ []) (∨右2 Γ Δ A B) prf1 prf2 v = {!!}
Lemma1-7-2 .(Γ ⟶ Δ , A ∷ []) .(B ∷ Π ⟶ Σ) .(A ⊃ B ∷ Γ , Π ⟶ Δ , Σ) (⊃左 Γ Δ Π Σ A B) prf1 prf2 v = {!!}
Lemma1-7-2 .(A ∷ Γ ⟶ Δ , B ∷ []) .n .(Γ ⟶ Δ , A ⊃ B ∷ []) (⊃右 Γ Δ A B) prf1 prf2 v = {!!}
Lemma1-7-2 .(Γ ⟶ Δ , A ∷ []) .n .(¬ A ∷ Γ ⟶ Δ) (¬左 Γ Δ A) prf1 prf2 v = {!!}
Lemma1-7-2 .(A ∷ Γ ⟶ Δ) .n .(Γ ⟶ Δ , ¬ A ∷ []) (¬右 Γ Δ A) prf1 prf2 v = {!!}

-- 健全性定理 定理1.7
健全性定理 : ∀ S → 式 S は 証明可能 である → 式 S は トートロジー である
健全性定理 n prf = tt
健全性定理 (.([ A ]) ⟶ .([ A ])) (c1 (init A)) = Lemma1-7-1 ([ A ] ⟶ [ A ]) (init A)
健全性定理 (Γ ⟶ Δ) (c2 {A} {B} {.Γ} {.Δ} prf x) 
  = Lemma1-7-2 (A ⟶ B) n (Γ ⟶ Δ) x (健全性定理 (A ⟶ B) prf) tt
健全性定理 (Γ ⟶ Δ) (c3 {A} {B} {C} {D} {.Γ} {.Δ} prf1 prf2 x) 
  = Lemma1-7-2 (A ⟶ B) (C ⟶ D) (Γ ⟶ Δ) x (健全性定理 (A ⟶ B) prf1) (健全性定理 (C ⟶ D) prf2) 

