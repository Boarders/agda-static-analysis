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
open import Data.Product using (∃-syntax; ∃; _,_)


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

pos-lem1 : (n : ℤ) -> pos n -> ∃[ m ] (+_ (suc m) ≡ n)
pos-lem1 (+_ (suc n)) p = n , refl


pos+pos : (v1 v2 : ℤ) -> (pos v1) -> (pos v2) -> pos (v1 +ℤ v2)
pos+pos n m p1 p2 with pos-lem1 n p1 | pos-lem1 m p2 
... | n+ , refl | m+ , refl = refl

pos+z : (v1 v2 : ℤ) -> (pos v1) -> (pos v2) -> pos (v1 +ℤ v2)
pos+z n m p1 p2 with pos-lem1 n p1 | pos-lem1 m p2 
... | n+ , refl | m+ , refl = refl


α+-homo : ∀ (v1 v2 : ℤ) -> ((α (v1 +ℤ v2)) ≤ (α v1 +^ α v2))
α+-homo (+_ zero) (+_ zero) = tt
α+-homo (+_ (suc n)) (+_ zero) = tt
α+-homo (+_ zero) (+_ (suc m)) = tt
α+-homo (+_ (suc n)) (+_ (suc m)) = tt
α+-homo (+_ zero) (-[1+_] n₁) = tt
α+-homo (+_ (suc n)) (-[1+_] n₁) = ge-⊤
α+-homo (-[1+_] n) (+_ zero) = tt
α+-homo (-[1+_] n) (+_ (suc n₁)) = ge-⊤
α+-homo (-[1+_] n) (-[1+_] n₁) = tt



soundness : (e : Expr) -> (α (eval e) ≤ eval^ e)
soundness (I x) = refl-≤
soundness (e1 + e2) with soundness e1 | soundness e2
... |  pf1 | pf2 = trans (α+-homo (eval e1) (eval e2)) {!!}
soundness (e1 * e2) = {!!}







