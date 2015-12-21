module PredicateLogic where
-- 第2章 述語論理
-- P.59 2. 述語論理の論理式

open import Data.List
open import Data.Nat using (ℕ)

対象定数 = ℕ

data 対象変数 : Set where
  p q r s t u v w x y z : 対象変数 --TODO 無限個 Char?

-- P.60 ●項と論理式

-- 言語Lをパラメータ化するのは煩雑すぎるのでやめて、ひとまずべた書きする。

-- 定義2.1
-- 自然数の加算と乗算だけ考える。
data 項 : Set where
  v : 対象変数 → 項 -- variable
  c : 対象定数 → 項 -- constant
  _+_  : 項 → 項 → 項
  _×_  : 項 → 項 → 項

-- 定義2.2
data 原子論理式 : Set where
  _≡_ : 項 → 項 → 原子論理式
  _<_ : 項 → 項 → 原子論理式

data 論理式 : Set where
  atom : 原子論理式 → 論理式 
  _∧_ : 論理式 → 論理式 → 論理式
  _∨_ : 論理式 → 論理式 → 論理式
  _⊃_ : 論理式 → 論理式 → 論理式
  ¬_  : 論理式 → 論理式
  A : 対象変数 → 論理式 → 論理式
  E : 対象変数 → 論理式 → 論理式

sample : 論理式 -- ∀x.(x < 5 ⊃ x < 2×3)
sample = A x (atom (v x < c 5) ⊃ atom (v x < (c 2 × c 3)))

