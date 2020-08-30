{-# OPTIONS --prop #-}

module sign-analysis where


open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
open import Data.Nat using (zero; suc)
open import Data.Bool using (false; true; if_then_else_) 
  renaming (_≤_ to _≤𝔹_; Bool to 𝔹; _∧_ to _∧𝔹_; _∨_ to _∨𝔹_)
open import Signs
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)


α : ℤ -> Sgns
α (+_ zero) = sg z
α (+_ (suc n)) = sg +
α (-[1+_] n) = sg -


-- +-sgns : Sgns -> Sgns -> 

data Expr : Set where
  I   : ℤ -> Expr
  _+_ : Expr -> Expr -> Expr
  _*_ : Expr -> Expr -> Expr


eval : Expr -> ℤ
eval (I x) = x
eval (c1 + c2) = eval c1 +ℤ eval c2
eval (c1 * c2) = eval c1 *ℤ eval c2

eval^ : Expr -> Sgns
eval^ (I x) = α x
eval^ (e1 + e2) = (eval^ e1) +^ (eval^ e2)
eval^ (e1 * e2) = (eval^ e1) *^ (eval^ e2)

pos : ℤ -> Set
pos v = α v ≡ sg +

pos+pos : (v1 v2 : ℤ) -> (pos v1) -> (pos v2) -> pos (v1 +ℤ v2)
pos+pos (+_ n) (+_ m) p1 p2 = {!!}


α-homo : ∀ (v1 v2 : ℤ) -> ((α (v1 +ℤ v2)) ≤ (α v1 +^ α v2)) ≡ true
α-homo (+_ n) (+_ zero) = {!!}
α-homo (+_ n) (+_ (suc m)) = {!!}
α-homo (+_ n) (-[1+_] n₁) = {!!}
α-homo (-[1+_] n) v2 = {!!}

refl-≤ : ∀ {s} ->  s ≤ s ≡ true
refl-≤ {Sgns.⊥} = refl
refl-≤ {sg x} = refl-=sgn x
refl-≤ {+- } = refl
refl-≤ {z- } = refl
refl-≤ {z+} = refl
refl-≤ {Sgns.⊤} = refl

soundness : (e : Expr) -> (α (eval e) ≤ eval^ e) ≡ true
soundness (I x) = refl-≤
soundness (e1 + e2) with soundness e1 | soundness e2
... |  pf1 | pf2 = {!!}
soundness (e1 * e2) = {!!}







