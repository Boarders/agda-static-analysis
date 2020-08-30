module Signs where


open import Data.Bool using (false; true; if_then_else_) 
  renaming (_≤_ to _≤𝔹_; Bool to 𝔹; _∧_ to _∧𝔹_; _∨_ to _∨𝔹_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

data Sgn : Set where
  + : Sgn
  - : Sgn
  z : Sgn


data Sgns : Set where
  ⊥   : Sgns
  sg : Sgn ->  Sgns
  +- : Sgns
  z- : Sgns
  z+ : Sgns
  ⊤  : Sgns

_=sgn_ : Sgn -> Sgn -> 𝔹
+ =sgn + = true
+ =sgn - = false
+ =sgn z = false
- =sgn + = false
- =sgn - = true
- =sgn z = false
z =sgn + = false
z =sgn - = false
z =sgn z = true

refl-=sgn : ∀ (s : Sgn) -> (s =sgn s) ≡ true
refl-=sgn + = refl
refl-=sgn - = refl
refl-=sgn z = refl


_+sgn_ :  Sgn -> Sgn -> Sgns
+ +sgn + = sg +
+ +sgn - = +-
+ +sgn z = z+
- +sgn + = +-
- +sgn - = sg -
- +sgn z = z-
z +sgn + = z+
z +sgn - = z-
z +sgn z = sg z


_*sgn_ : Sgn -> Sgn -> Sgns
+ *sgn +  = sg +
+ *sgn -  = sg -
+ *sgn z  = sg z
- *sgn +  = sg -
- *sgn -  = sg +
- *sgn z  = sg z
z *sgn s2 = sg z

add : Sgns -> Sgn -> Sgns
add ⊥ s2 = sg s2
add (sg sgn1) sgn2 = sgn1 +sgn sgn2
add +- + = +-
add +- - = +-
add +- z = ⊤
add z- + = ⊤
add z- - = z-
add z- z = z-
add z+ + = z+
add z+ - = ⊤
add z+ z = z+
add ⊤ s2 = ⊤

infixl 5 _∨_
_∨_ : Sgns -> Sgns -> Sgns
⊥ ∨ s2 = s2
sg s ∨ s2 = add s2 s
+- ∨ ⊥ = +-
+- ∨ sg x = add +- x
+- ∨ +- = +-
+- ∨ z- = ⊤
+- ∨ z+ = ⊤
+- ∨ ⊤ = ⊤
z- ∨ ⊥ = z-
z- ∨ sg x = add z- x
z- ∨ +- = ⊤
z- ∨ z- = z-
z- ∨ z+ = ⊤
z- ∨ ⊤ = ⊤
z+ ∨ ⊥ = z+
z+ ∨ sg x = add z+ x
z+ ∨ +- = ⊤
z+ ∨ z- = ⊤
z+ ∨ z+ = z+
z+ ∨ ⊤ = ⊤
⊤ ∨ s2 = ⊤

_∈_ : Sgn -> Sgns -> 𝔹
s ∈ ⊥ = false
s ∈ sg x = s =sgn x
+ ∈ +- = true
- ∈ +- = true
z ∈ +- = false
+ ∈ z- = false
- ∈ z- = true
z ∈ z- = true
+ ∈ z+ = true
- ∈ z+ = false
z ∈ z+ = true
s ∈ ⊤ = true

_≤_ : Sgns -> Sgns -> 𝔹
⊥ ≤ s2 = true
sg s ≤ s2 = s ∈ s2
+- ≤ s2 = (+ ∈ s2) ∧𝔹 (- ∈ s2)
z- ≤ s2 = (z ∈ s2) ∧𝔹 (- ∈ s2)
z+ ≤ s2 = (z ∈ s2) ∧𝔹 (+ ∈ s2)
⊤ ≤ ⊥ = false
⊤ ≤ sg x = false
⊤ ≤ +- = false
⊤ ≤ z- = false
⊤ ≤ z+ = false
⊤ ≤ ⊤ = true

ext : (Sgn -> Sgns) -> Sgns -> Sgns
ext f ⊥ = ⊥
ext f (sg x) = f x
ext f +- = f + ∨ f -
ext f z- = f z ∨ f -
ext f z+ = f z ∨ f +
ext f ⊤ = f z ∨ f + ∨ f -

ext2 : (Sgn -> Sgn -> Sgns) -> Sgns -> Sgns -> Sgns
ext2 op ⊥ s2 = ⊥
ext2 op (sg x) s2 = ext (op x) s2
ext2 op +- s2 = ext (op +) s2 ∨ ext (op -) s2
ext2 op z- s2 = ext (op z) s2 ∨ ext (op -) s2
ext2 op z+ s2 = ext (op z) s2 ∨ ext (op +) s2
ext2 op ⊤ s2 = ext (op z) s2 ∨ ext (op +) s2 ∨ ext (op -) s2

_+^_ : Sgns -> Sgns -> Sgns
_+^_ = ext2 _+sgn_

_*^_ : Sgns -> Sgns -> Sgns
_*^_ = ext2 _*sgn_


 
