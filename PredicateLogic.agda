module PredicateLogic where
-- 第2章 述語論理
-- P.59 2. 述語論理の論理式

open import Data.List
open import Data.Nat using (ℕ)
open import Data.Char using (Char)

対象定数 = ℕ

対象変数 = Char

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
sample = A 'x' (atom (v 'x' < c 5) ⊃ atom (v 'x' < (c 2 × c 3)))

-- 定義2.3 束縛された出現と自由な出現

-- 定義2.4 項の代入
_[_/_] : 項 → 項 → 対象変数 → 項
s [ t / x ] = {!!}

-- 定義2.5 言語ℒに対する構造S = <U,I>
--   フラクトゥールのAはやめて単にS(Structure)とした。

{-
record 解釈 : Set1 where
  field
    

record 構造 : Set1 where
  field
    U : Set
    I : 解釈
-}
