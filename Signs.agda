module Signs where


open import Data.Bool using (false; true; if_then_else_) 
  renaming (_≤_ to _≤𝔹_; Bool to 𝔹; _∧_ to _∧𝔹_; _∨_ to _∨𝔹_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; _≢_)
open import Data.Unit using (tt) renaming (⊤ to one)
open import Data.Empty renaming (⊥ to zero)

data Sgn : Set where
  + : Sgn
  - : Sgn
  z : Sgn


data Sgns : Set where
  ⊥   : Sgns
  sg : Sgn ->  Sgns
  ⊤  : Sgns

_=sgn_ : Sgn -> Sgn -> Set
+ =sgn + = one
+ =sgn - = zero
+ =sgn z = zero
- =sgn + = zero
- =sgn - = one
- =sgn z = zero
z =sgn + = zero
z =sgn - = zero
z =sgn z = one

=sgn-≡ : ∀ {s1 s2 : Sgn} -> s1 =sgn s2 -> s1 ≡ s2
=sgn-≡ { + } { + } p = refl
=sgn-≡ { - } { - } p = refl
=sgn-≡ { z } { z } p = refl

=sgn=-⊥ : ∀ {s1 s2} -> s1 ≢ s2 ->  (s1 =sgn s2) -> zero
=sgn=-⊥ {s1} {s2} neq p = neq (=sgn-≡ p)
 
refl-=sgn : ∀ (s : Sgn) -> (s =sgn s)
refl-=sgn + = tt
refl-=sgn - = tt
refl-=sgn z = tt



_+sgn_ :  Sgn -> Sgn -> Sgns
+ +sgn + = sg +
+ +sgn - = ⊤
+ +sgn z = sg +
- +sgn + = ⊤
- +sgn - = sg -
- +sgn z = sg -
z +sgn + = sg +
z +sgn - = sg -
z +sgn z = sg z

comm-+sgn+ : (s1 s2 : Sgn) -> s1 +sgn s2 ≡ s2 +sgn s1
comm-+sgn+ + + = refl
comm-+sgn+ + - = refl
comm-+sgn+ + z = refl
comm-+sgn+ - + = refl
comm-+sgn+ - - = refl
comm-+sgn+ - z = refl
comm-+sgn+ z + = refl
comm-+sgn+ z - = refl
comm-+sgn+ z z = refl


_*sgn_ : Sgn -> Sgn -> Sgns
+ *sgn +  = sg +
+ *sgn -  = sg -
+ *sgn z  = sg z
- *sgn +  = sg -
- *sgn -  = sg +
- *sgn z  = sg z
z *sgn s2 = sg z

add : Sgns -> Sgn -> Sgns
add ⊥ s2 = ⊥
add (sg sgn1) sgn2 = sgn1 +sgn sgn2
add ⊤ s2 = ⊤



infixl 7 _∨_
_∨_ : Sgns -> Sgns -> Sgns
⊥ ∨ s2 = s2
sg s ∨ s2 = add s2 s
⊤ ∨ s2 = ⊤

_∈_ : Sgn -> Sgns -> Set
s ∈ ⊥ = zero
s ∈ sg x = s =sgn x
s ∈ ⊤ = one



infixl 3 _≤_
_≤_ : Sgns -> Sgns -> Set
⊥ ≤ s2 = one
sg s ≤ s2 = s ∈ s2
⊤ ≤ ⊥ = zero
⊤ ≤ sg x = zero
⊤ ≤ ⊤ = one

ge-⊤ : ∀ {s : Sgns} -> (s ≤ ⊤)
ge-⊤ {⊥} = tt
ge-⊤ {sg x} = tt
ge-⊤ {⊤} = tt

uniq-⊤ : ∀ {s : Sgns} -> (⊤ ≤ s) -> s ≡ ⊤
uniq-⊤ {⊤} p = refl

refl-≤ : ∀ {s} ->  s ≤ s 
refl-≤ {⊥} = tt
refl-≤ {sg x} = refl-=sgn x
refl-≤ {⊤} = tt



trans : {s1 s2 s3 : Sgns} -> s1 ≤ s2 -> s2 ≤ s3 -> s1 ≤ s3
trans {⊥} {s2} {s3} p1 p2 = tt
trans {sg x} {sg y} {s3} p1 p2 with =sgn-≡ p1
... | refl = p2
trans {sg x} {⊤} {s3} p1 p2 with uniq-⊤ {s3} p2
... | refl = tt
trans {⊤} {s2} {s3} p1 p2 with uniq-⊤ {s2} p1
... | refl = p2

ext : (Sgn -> Sgns) -> Sgns -> Sgns
ext f ⊥ = ⊥
ext f (sg x) = f x
ext f ⊤ = f z ∨ f + ∨ f -

ext2 : (Sgn -> Sgn -> Sgns) -> Sgns -> Sgns -> Sgns
ext2 op ⊥ s2 = ⊥
ext2 op (sg x) s2 = ext (op x) s2
ext2 op ⊤ s2 = ext (op z) s2 ∨ ext (op +) s2 ∨ ext (op -) s2

_+^_ : Sgns -> Sgns -> Sgns
_+^_ = ext2 _+sgn_

add-mono : {s1 s2 : Sgns} -> (sgn  : Sgn) -> s1 ≤ s2 -> add s1 sgn ≤ add s2 sgn
add-mono {⊥} {⊥} sgn p = tt
add-mono {⊥} {sg +} + p = tt
add-mono {⊥} {sg - } + p = tt
add-mono {⊥} {sg z} + p = tt
add-mono {⊥} {sg +} - p = tt
add-mono {⊥} {sg - } - p = tt
add-mono {⊥} {sg z} - p = tt
add-mono {⊥} {sg +} z p = tt
add-mono {⊥} {sg - } z p = tt
add-mono {⊥} {sg z} z p = tt
add-mono {⊥} {⊤} sgn p = tt
add-mono {sg +} {sg +} sgn p = refl-≤
add-mono {sg +} {⊤} sgn p = ge-⊤
add-mono {sg - } {sg - } sgn p = refl-≤
add-mono {sg - } {⊤} sgn p = ge-⊤
add-mono {sg z} {sg z} sgn p = refl-≤
add-mono {sg z} {⊤} sgn p = ge-⊤
add-mono {⊤} {s2} sgn p with uniq-⊤ {s2} p
... | refl = tt

s : _
s = add (sg +) z

ext-+mono : (sgn : Sgn) -> (s1 s2 : Sgns) -> s1 ≤ s2 -> ext (_+sgn_ sgn) s1 ≤ ext (_+sgn_ sgn) s2
ext-+mono s ⊥ s2 p = tt
ext-+mono + (sg +) (sg +) p = tt
ext-+mono + (sg +) ⊤ p = tt
ext-+mono + (sg -) (sg -) tt = tt
ext-+mono + (sg -) ⊤ p = tt
ext-+mono + (sg z) (sg z) p = tt
ext-+mono + (sg z) ⊤ p = tt
ext-+mono - (sg +) (sg +) p = tt
ext-+mono - (sg -) (sg -) p = tt
ext-+mono - (sg z) (sg z) p = tt
ext-+mono - (sg +) ⊤ p = tt
ext-+mono - (sg -) ⊤ p = tt
ext-+mono - (sg z) ⊤ p = tt
ext-+mono z (sg +) (sg +) p = tt
ext-+mono z (sg +) ⊤ p = tt
ext-+mono z (sg -) (sg -) p = tt
ext-+mono z (sg -) ⊤ p = tt
ext-+mono z (sg z) (sg z) p = tt
ext-+mono z (sg z) ⊤ p = tt
ext-+mono s ⊤ s2 p with uniq-⊤ {s2} p 
... | refl = refl-≤



mono-∨ : ∀ {s1 s2 s : Sgns} -> s1 ≤ s2 -> s1 ∨ s ≤ s2 ∨ s
mono-∨ {⊥} {⊥} {s} le = refl-≤
mono-∨ {⊥} {sg x} {s} le = {!!}
mono-∨ {⊥} {⊤} {s} le = {!!}
mono-∨ {sg x} {s2} {s} le = {!!}
mono-∨ {⊤} {s2} {s} le = {!!}

mono-+^ : (s1 s2 s3 s4 : Sgns) ->  s1 ≤ s2 -> s3 ≤ s4 -> (s1 +^ s3) ≤ (s2 +^ s4)
mono-+^ ⊥ s2 ⊥ s4 p1 p2 = tt
mono-+^ ⊥ s2 (sg x) s4 p1 p2 = tt
mono-+^ ⊥ s2 ⊤ s4 p1 p2 = tt
mono-+^ (sg x) (sg y) s3 s4 p1 p2 with =sgn-≡ p1
... | refl = ext-+mono x s3 s4 p2
mono-+^ (sg x) ⊤ s3 s4 p1 p2 = {!!}
--with uniq-⊤ p1 
--... | eq = {!!}
mono-+^ ⊤ s2 s3 s4 p1 p2 with uniq-⊤ {s2} p1
... | refl = {!!}

_*^_ : Sgns -> Sgns -> Sgns
_*^_ = ext2 _*sgn_





 
