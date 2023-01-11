```agda
{-# OPTIONS --type-in-type --exact-split #-}
open import Level
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum renaming (inj₁ to left; inj₂ to right)
-- open import Data.Bool hiding (_∨_ ; _∧_)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_ ; _≗_)
open import Relation.Binary renaming (_⇔_ to _⇔₂_)
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary.Lattice
open import Function renaming (_⇔_ to _⇔fun_; _↔_ to _↔fun_)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Fin using (Fin; suc; zero)
open import Data.Bool using (Bool; true ; false)

private variable
  ℓ : Level
  X : Set

level-of : {ℓ : Level} (X : Set ℓ) → Level
level-of {ℓ} _ = ℓ

prop = Set

pred : Set → prop
pred X = Pred X (level-of X)

subset : Set → prop
subset = pred

⊆-refl : ∀ {X} (S : subset X) → S ⊆ S
⊆-refl S x∈S = x∈S

comprehension-syntax : ∀ {X} → pred X → subset X
comprehension-syntax = \ { x → x }

sigma-syntax :  (X : Set) → (X → Set) → Set
sigma-syntax  = Σ

syntax comprehension-syntax (\ x → P) = ｛ x ∣ P ｝
```

```agda
{-# DISPLAY comprehension-syntax P = P #-}
{-# DISPLAY Σ-syntax D E = Σ D E #-}

｛_,_｝₂ : ∀ {X} → X → X → pred X
｛ x , x' ｝₂ = ｛ x ｝ ∪ ｛ x' ｝

rel : Set → Set → prop
rel X Y = REL X Y (level-of X ⊔ level-of Y)

pointwise : ∀ {C X Y} → rel X Y → rel (C → X) (C → Y)
pointwise _~_ f g = ∀ c → f c ~ g c

map-rel : ∀ {C D X Y} → (C → X) → (D → Y) → rel X Y → rel C D
map-rel f g r c d = r (f c) (g d)

_⋈_ : ∀{X Y Z} → subset (X × Y) → subset (Y × Z) → subset (X × Z)
(r ⋈ r') (x , z) = Σ _ \ y → (x , y) ∈ r × (y , z) ∈ r'

_⊆₂_ : ∀ {X Y} → rel (rel X Y) (rel X Y)
R ⊆₂ R' = ∀ {x y} → R x y → R' x y

binop : Set → Set
binop X = X → X → X

subsetop : Set → Set
subsetop X = subset X → X

κ-subset : Set → Set → prop
κ-subset κ X = κ → X

finite-subset = κ-subset (ℕ)
decidable-subset = Set → Bool

_∈κ_ : ∀ {κ} → rel X (κ-subset κ X)
x ∈κ S = Σ _ \ i → S i ≡ x

_⊆κ_ : ∀ {κ} → rel (κ-subset κ X) (κ-subset κ X)
S ⊆κ S' = ∀ x → x ∈κ S → x ∈κ S'

rel2subset : ∀ {X Y} → rel X Y → subset (X × Y)
rel2subset R (x , y) = R x y
subset2rel : ∀ {X Y} → subset (X × Y) → rel X Y
subset2rel S x y = (x , y) ∈ S

rimage : ∀ {X Y} → rel X Y → subset X → subset Y
rimage _R_ SX = ｛ y ∣ Σ[ x ∈ _ ] (x ∈ SX × x R y) ｝

rpreimage : ∀ {X Y} → rel X Y → subset Y → subset X
rpreimage _R_ SY = ｛ x ∣ Σ[ y ∈ _ ] (y ∈ SY × x R y) ｝

fimage : ∀ {X Y} → (X → Y) → subset X → subset Y
fimage f SX = ｛ y ∣ Σ[ x ∈ _ ] (x ∈ SX × f x ≡ y)  ｝

record iso-pair (_~_ : rel X X) (x y : X) : prop where
  field
    forward : x ~ y
    backward : y ~ x

  ! : iso-pair _~_ y x
  forward ! = backward
  backward ! = forward

open iso-pair public

infix 0 _↔_
_↔_ : rel prop prop
_↔_ = iso-pair (\X Y → X → Y)

infix 1 _≅_
_≅_ : ∀ {X} → rel (subset X) (subset X)
_≅_ = iso-pair _⊆_

hidden↔explicit : ∀ {X : Set} (P : pred X) → (∀ {x} → P x) ↔ (∀ x → P x)
forward (hidden↔explicit P) ∀P x = ∀P
backward (hidden↔explicit P) ∀P = ∀P _

module _×rel_ {D E : Set} (_≤D_ : rel D D) (_≤E_ : rel E E) where
  _≤₁_ = _≤D_
  _≤₂_ = _≤E_

  _≤_ : rel (D × E) (D × E)
  (d , e) ≤ (d' , e') = d ≤₁ d' × e ≤₂ e'

  _≈₁_ = iso-pair _≤₁_
  _≈₂_ = iso-pair _≤₂_
  _≈_ = iso-pair _≤_

  fst-≤ : {p p' : D × E} → p ≤ p' → fst p ≤₁ fst p'
  fst-≤ x = fst x

  snd-≤ : {p p' : D × E} → p ≤ p' → snd p ≤₂ snd p'
  snd-≤ x = snd x

  fst-≈ : {p p' : D × E} → p ≈ p' → fst p ≈₁ fst p'
  forward (fst-≈ x) = fst (forward x)
  backward (fst-≈ x) = fst (backward x)
  snd-≈ : {p p' : D × E} → p ≈ p' → snd p ≈₂ snd p'
  forward (snd-≈ x) = snd (forward x)
  backward (snd-≈ x) = snd (backward x)

fst-subset : ∀ {D E} → subset (D × E) → subset D
fst-subset S d = Σ _ \ e → (d , e) ∈ S

snd-subset : ∀ {D E} → subset (D × E) → subset E
snd-subset S e = Σ _ \ d → (d , e) ∈ S

fst-rel : ∀ {D E} → rel D E → subset D
fst-rel R d = Σ _ \ e → R d e

snd-rel : ∀ {D E} → rel D E → subset E
snd-rel R e = Σ _ \ d → R d e

pair-fst : ∀ {D E} → (S : subset (D × E)) (d : D) {e : E} → (d , e) ∈ S → d ∈ fst-subset S
pair-fst S d {e} de∈S = e , de∈S

≅×≅→≅ : ∀ {X Y} {S S' : subset X} {T T' : subset Y} → S ≅ S' → T ≅ T' → ((S ∘ fst) ∩ (T ∘ snd)) ≅ ((S' ∘ fst) ∩ (T' ∘ snd))
forward (≅×≅→≅ S=S' T=T') (d , e) = (forward S=S' d) , (forward T=T' e)
backward (≅×≅→≅ S=S' T=T') (d , e) = (backward S=S' d) , (backward T=T' e)

```
