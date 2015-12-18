module PredicateLogicSkelton where
{-
 2015-12-19 書いてみての感想。
 この形式化は理解するためにはよいのだが、
 これを使ってAgda上で証明するにはよくないと思われるので、
 Agda上で証明するための、もうすこし簡便な形式化は別途行う。
-}

-- 第2章 述語論理
-- P.59 2. 述語論理の論理式

open import Data.List
open import Data.Nat

対象定数-自然数 = ℕ

-- 何変数なのかをあらかじめ指定しておくので、ℕ → Set
data 関数記号-自然数 : ℕ → Set where
  + : 関数記号-自然数 2
  × : 関数記号-自然数 2

data 述語記号-自然数 : ℕ → Set where
  ≡ : 述語記号-自然数 2
  < : 述語記号-自然数 2

record 言語 : Set1 where
  field
    対象定数 : Set
    関数記号 : ℕ → Set
    述語記号 : ℕ → Set
    -- 補助記号 : Set これはAgdaのシステムが補助してくれるもののこととする。

  data 論理結合子 : Set where
    ∧ ∨ ⊃ ¬ : 論理結合子

  data 量化記号 : Set where
    ALL EX : 量化記号 -- ∀がつかえないので辛抱。

  data 対象変数 : Set where
    p q r s t u v w x y z : 対象変数 --TODO 無限個 Char?


述語論理の言語 : 言語
述語論理の言語 = record
                   { 
                     対象定数 = 対象定数-自然数
                   ; 関数記号 = 関数記号-自然数
                   ; 述語記号 = 述語記号-自然数
                   }

-- P.60 ●項と論理式

-- 1つの言語Lが与えられているとする。
module Formula (L : 言語) where

 -- 定義2.1
 data 項 : Set where
   t1a : 言語.対象変数 L → 項
   t1b : 言語.対象定数 L → 項
   t2  : {m : ℕ} → (f : 言語.関数記号 L m) → (ts : List 項) → 項

 -- 定義2.2
 data 論理式 : Set where
   t1 : {n : ℕ} → (P : 言語.述語記号 L n) → (ts : List 項) → 論理式 -- 原子論理式
   t2 : (A B : 論理式) → 言語.論理結合子 L → 論理式 --これだと¬が変。
   t3 : (A : 論理式) → (x' : 言語.対象変数 L) → 論理式
  -- これだと論理式の概念は定義できているが構文を定義できていない、そんな感じ。

