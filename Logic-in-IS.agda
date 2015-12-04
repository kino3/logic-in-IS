module Logic-in-IS where

-- 情報科学における論理 in Agda
-- http://www.nippyo.co.jp/book/1292.html

-- とりあえずＬＫのところまでかいてみる。

{-
 第1章 命題論理
-}

-------------------------
-- 1.1 形式化ということ
-------------------------

-------------------------
-- 1.2 命題と論理式
-------------------------
module Semantics where

open import Data.Char
命題変数 = Char

-- 定義1.1
data 論理式 : Set where
  <_> : 命題変数 → 論理式
  ⊤ : 論理式 -- P.12 命題定数
  ⊥ : 論理式 -- P.12 命題定数
  _∧_ : 論理式 → 論理式 → 論理式
  _∨_ : 論理式 → 論理式 → 論理式
  _⊃_ : 論理式 → 論理式 → 論理式
  ¬_  : 論理式 → 論理式

infix 100 ¬_

-- 例1.1
例1-1 : 論理式
例1-1 = < 'p' > ⊃ ( < 'q' > ∨ ¬ < 'r' >)

open import Data.Bool 
  renaming (true to t; false to f;_∧_ to _and_;_∨_ to _or_)


-------------------------
-- 1.3 論理式と真偽
-------------------------

-- P.9
付値 = 命題変数 → Bool

--論理式への拡張
_⟦_⟧ : 付値 → 論理式 → Bool
v ⟦ < x > ⟧   = v(x)
v ⟦ ⊤ ⟧       = t
v ⟦ ⊥ ⟧       = f
v ⟦ A ∧ B ⟧   = v ⟦ A ⟧ and v ⟦ B ⟧  
v ⟦ A ∨ B ⟧   = v ⟦ A ⟧ or  v ⟦ B ⟧ 
v ⟦ A ⊃ B ⟧   = not (v ⟦ A ⟧) or v ⟦ B ⟧
v ⟦ ¬ A ⟧     = not (v ⟦ A ⟧)

open import Relation.Binary.PropositionalEquality as PropEq 
  renaming (_≡_ to _≈_) hiding ([_])
-- ≡はあとで定義したいのでrenameする。

open import Data.Product renaming (_,_ to _&_)
-- 必要十分条件
_⇔_ : Set → Set → Set
A ⇔ B = (A → B) × (B → A)
infix 0 _⇔_

open import Relation.Nullary using (yes;no;Dec)
トートロジー : 論理式 → Set
トートロジー A = (v : 付値) → v ⟦ A ⟧ ≈ t

定理1-1 : (v : 付値) (A : 論理式) → Dec (v ⟦ A ⟧ ≈ t)
定理1-1 v < x >   with v ⟦ < x > ⟧
定理1-1 v < x > | t = yes refl
定理1-1 v < x > | f = no (λ ())
定理1-1 v ⊤       = yes refl
定理1-1 v ⊥       = no  (λ ())
定理1-1 v (A ∧ B) with v ⟦ A ⟧ | v ⟦ B ⟧
定理1-1 v (A ∧ B) | t | t = yes refl
定理1-1 v (A ∧ B) | t | f = no (λ ())
定理1-1 v (A ∧ B) | f | t = no (λ ())
定理1-1 v (A ∧ B) | f | f = no (λ ())
定理1-1 v (A ∨ B) with v ⟦ A ⟧ | v ⟦ B ⟧
定理1-1 v (A ∨ B) | t | t = yes refl
定理1-1 v (A ∨ B) | t | f = yes refl
定理1-1 v (A ∨ B) | f | t = yes refl
定理1-1 v (A ∨ B) | f | f = no (λ ())
定理1-1 v (A ⊃ B) with v ⟦ A ⟧ | v ⟦ B ⟧
定理1-1 v (A ⊃ B) | t | t = yes refl
定理1-1 v (A ⊃ B) | t | f = no (λ ())
定理1-1 v (A ⊃ B) | f | t = yes refl
定理1-1 v (A ⊃ B) | f | f = yes refl
定理1-1 v (¬ A)   with v ⟦ A ⟧
定理1-1 v (¬ A) | t = no (λ ())
定理1-1 v (¬ A) | f = yes refl

充足可能 : 論理式 → Set
充足可能 A = Σ[ v ∈ 付値 ] v ⟦ A ⟧ ≈ t

論理式_が_である : 論理式 → (論理式 → Set) → Set
論理式 a が P である = P a

恒真 = トートロジー

例1-3 : 論理式 ((< 'p' > ∧ (< 'p' > ⊃ < 'q' >)) ⊃ < 'q' > ) が トートロジー である
例1-3 v with v('p') | v('q') 
... | t | t = refl
... | t | f = refl
... | f | t = refl
... | f | f = refl

問1-2 : 論理式 (((< 'p' > ∨ < 'q' >) ⊃ < 'r' >) ∨ (< 'p' > ∧ < 'q' >)) が 充足可能 である
問1-2 = v & refl
  where
   v : 付値
   v 'p' = t
   v 'q' = f
   v 'r' = t
   v _   = f

問1-2' : ∀ p q r v → (Dec (v ⟦ (((p ∨ q) ⊃ r) ∨ (p ∧ q)) ⟧ ≈ t))
問1-2' p q r v = {!!}


-------------------------
-- 1.4 論理的に同値な論理式
-------------------------

-- equivalent
_≡_ : 論理式 → 論理式 → 論理式
A ≡ B = (A ⊃ B) ∧ (B ⊃ A)
infix 1 _≡_

問1-4 : {v : 付値} {A B : 論理式} → v ⟦ (A ≡ B) ⟧ ≈ t ⇔ v ⟦ A ⟧ ≈ v ⟦ B ⟧
問1-4 {v} {A} {B} with v ⟦ A ⟧ | v ⟦ B ⟧
問1-4 | t | t = (λ x → refl) & (λ x → refl)
問1-4 | t | f = (λ ()) & (λ ())
問1-4 | f | t = (λ ()) & (λ ())
問1-4 | f | f = (λ x → refl) & (λ x → refl)

問1-5 : {A B : 論理式} (v : 付値) → v ⟦ A ≡ B ⟧ ≈ v ⟦(A ∧ B) ∨ (¬ A ∧ ¬ B)⟧
問1-5 {A} {B} v with v ⟦ A ⟧ | v ⟦ B ⟧
問1-5 v | t | t = refl
問1-5 v | t | f = refl
問1-5 v | f | t = refl
問1-5 v | f | f = refl

定理1-3-1a : ∀ A → 論理式 (A ∧ A ≡ A) が トートロジー である
定理1-3-1a A v with v ⟦ A ⟧
定理1-3-1a A v | t = refl
定理1-3-1a A v | f = refl

定理1-3-1b : ∀ A → 論理式 (A ∨ A ≡ A) が トートロジー である
定理1-3-1b A v with v ⟦ A ⟧
定理1-3-1b A v | t = refl
定理1-3-1b A v | f = refl

_と_は_である : 論理式 → 論理式 → (論理式 → 論理式 → Set) → Set
A と B は P である = P A B

論理的に同値 : 論理式 → 論理式 → Set
論理的に同値 A B = 論理式 A ≡ B が トートロジー である

-- 問1-4より、これも同じこと。 
論理的に同値' : 論理式 → 論理式 → Set
論理的に同値' A B = ∀ v → v ⟦ A ⟧ ≈ v ⟦ B ⟧

-- Agdaの証明に便利なので、後者を採用する。
_∼_ : 論理式 → 論理式 → Set
A ∼ B = A と B は 論理的に同値' である

定理1-4-1 : (A : 論理式) → A ∼ A
定理1-4-1 A v = refl

定理1-4-2 : (A B : 論理式) → A ∼ B → B ∼ A
定理1-4-2 A B prf v = sym (prf v)

定理1-4-3 : (A B C : 論理式) → A ∼ B → B ∼ C → A ∼ C
定理1-4-3 A B C A∼B B∼C v = trans (A∼B v) (B∼C v)

-- 論理式Cの中の命題変数のいくつかの出現を論理式Aでおきかえて得られる論理式を
-- C [ p ≔ A ] と表す。
infix 30 _[_≔_]
_[_≔_] : 論理式 → 命題変数 → 論理式 → 論理式
< x > [ p ≔ A ] with p == x
... | t = A
... | f = < x >
⊤ [ p ≔ A ]         = ⊤
⊥ [ p ≔ A ]         = ⊥
(C1 ∧ C2) [ p ≔ A ] = C1 [ p ≔ A ] ∧ C2 [ p ≔ A ]
(C1 ∨ C2) [ p ≔ A ] = C1 [ p ≔ A ] ∨ C2 [ p ≔ A ]
(C1 ⊃ C2) [ p ≔ A ] = C1 [ p ≔ A ] ⊃ C2 [ p ≔ A ]
(¬ C) [ p ≔ A ]     = ¬ (C [ p ≔ A ])

定理1-4-4 : (A B C : 論理式) (p : 命題変数) → A ∼ B → C [ p ≔ A ] ∼ C [ p ≔ B ]
-- 証明が例1.7
定理1-4-4 A B < q >   p A∼B v with p == q -- (1)
... | t = A∼B v  -- Cがある命題変数qに等しいとき、がこれ。
... | f = 定理1-4-1 < q > v -- qがpと異なるとき、がこれ。
定理1-4-4 A B ⊤       p A∼B v = refl
定理1-4-4 A B ⊥       p A∼B v = refl
-- 帰納法の仮定でrewriteすると、あとはAgdaでといてくれる。
定理1-4-4 A B (D ∧ E) p A∼B v rewrite 定理1-4-4 A B D p A∼B v | 定理1-4-4 A B E p A∼B v = refl
定理1-4-4 A B (D ∨ E) p A∼B v rewrite 定理1-4-4 A B D p A∼B v | 定理1-4-4 A B E p A∼B v = refl
定理1-4-4 A B (D ⊃ E) p A∼B v rewrite 定理1-4-4 A B D p A∼B v | 定理1-4-4 A B E p A∼B v = refl
定理1-4-4 A B (¬ D)   p A∼B v rewrite 定理1-4-4 A B D p A∼B v = refl

-------------------------
-- 1.5 標準形
-------------------------


-------------------------
-- 1.6 形式体系における証明
-------------------------
module LK where
-- P.23

open Semantics
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

{-
例1-12' : (A : 論理式) → 証明図[終式 (⟶ [ A ∨ ¬ A ]) ]
例1-12' A = {!!}
-}
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

