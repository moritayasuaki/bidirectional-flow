
Lattices, preorder, relation, subset, and monotone functions
------------------------------------------------------------

We use type-in-type to avoid about universe level arithmetic

```agda
{-# OPTIONS --type-in-type --exact-split #-}
```

<!--
```agda
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
import Data.Nat as Nat
```


```agda
module bidirectional where
private variable
  ℓ : Level
  X : Set

level-of : {ℓ : Level} (X : Set ℓ) → Level
level-of {ℓ} _ = ℓ

prop = Set

data false : prop where

record true : prop where
  constructor ⋆

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

open iso-pair

infix 0 _↔_
_↔_ : rel prop prop
_↔_ = iso-pair (\X Y → X → Y)

infix 1 _≅_
_≅_ : ∀ {X} → rel (subset X) (subset X)
_≅_ = iso-pair _⊆_

hidden↔explicit : ∀ {X : Set} (P : pred X) → (∀ {x} → P x) ↔ (∀ x → P x)
forward (hidden↔explicit P) ∀P x = ∀P
backward (hidden↔explicit P) ∀P = ∀P _


module _ {X : Set} where

  is-reflexive : pred (rel X X)
  is-reflexive _~_ = ∀ x → x ~ x

  is-transitive : pred (rel X X)
  is-transitive _~_ = ∀ {x y z} → x ~ y → y ~ z → x ~ z

  is-symmetric : pred (rel X X)
  is-symmetric _~_ = ∀ {x y} → x ~ y → y ~ x

  is-antisymmetric : rel (rel X X) (rel X X)
  is-antisymmetric _≈_ _≤_ = ∀ {x y} → x ≤ y → y ≤ x → x ≈ y

  iso-refl : {_~_ : rel X X} → is-reflexive _~_ → is-reflexive (iso-pair _~_)
  forward (iso-refl r-refl x) = r-refl x
  backward (iso-refl r-refl x) = r-refl x

  -- I use preorder instead of partial order and use equivalence a ≈ b := a ≤ b and b
  record is-preorder (_≤_ : rel X X) : Set where
    field
      rel-is-reflexive : is-reflexive _≤_
      rel-is-transitive : is-transitive _≤_

    identity-to-rel : ∀ {x y} → x ≡ y → x ≤ y
    identity-to-rel ≡.refl = rel-is-reflexive _

    iso-reflexive : ∀ x → iso-pair _≤_ x x
    forward (iso-reflexive x) = rel-is-reflexive x
    backward (iso-reflexive x) = rel-is-reflexive x

    iso-transitive : ∀ {x y z} → iso-pair _≤_ x y → iso-pair _≤_ y z → iso-pair _≤_ x z
    forward (iso-transitive x~y y~z) = rel-is-transitive (forward x~y) (forward y~z)
    backward (iso-transitive x~y y~z) =  rel-is-transitive (backward y~z) (backward x~y)

    ↑ : X → subset X
    ↑ x = x ≤_

    ↓ : X → subset X
    ↓ x = _≤ x

    opposite : is-preorder (flip _≤_)
    rel-is-reflexive opposite = rel-is-reflexive
    rel-is-transitive opposite = flip rel-is-transitive


  record is-equivalence (_~_ : rel X X) : Set where
    field
      rel-is-reflexive : is-reflexive _~_
      rel-is-transitive : is-transitive _~_
      rel-is-symmetric : is-symmetric _~_

    identity-to-rel : ∀ {x y} → x ≡ y → x ~ y
    identity-to-rel ≡.refl = rel-is-reflexive _

  module _ (_≤_ : rel X X) where
    module _ where
      open is-preorder
      open is-equivalence

      private
        _≈_ : rel X X
        _≈_ = iso-pair _≤_

      loop-antisymmetric : is-preorder _≤_ → is-antisymmetric _≈_ _≤_
      forward (loop-antisymmetric ≤-pre x≤y y≤x) = x≤y
      backward (loop-antisymmetric ≤-pre x≤y y≤x) = y≤x

      loop-equivalence : is-preorder _≤_ → is-equivalence _≈_
      forward (rel-is-reflexive (loop-equivalence ≤-pre) x) = rel-is-reflexive ≤-pre x
      backward (rel-is-reflexive (loop-equivalence ≤-pre) x) = rel-is-reflexive ≤-pre x
      forward (rel-is-transitive (loop-equivalence ≤-pre) x≈y y≈z) = rel-is-transitive ≤-pre (forward x≈y) (forward y≈z)
      backward (rel-is-transitive (loop-equivalence ≤-pre) x≈y y≈z) = rel-is-transitive ≤-pre (backward y≈z) (backward x≈y)
      forward (rel-is-symmetric (loop-equivalence ≤-pre) x≈y) = backward x≈y
      backward (rel-is-symmetric (loop-equivalence ≤-pre) x≈y) = forward x≈y



      module reasoning (≤-pre : is-preorder _≤_) where
        private
          ≈-equiv = loop-equivalence ≤-pre

        data _R_ (x y : X) : prop where
          R≤ : (x≤y : x ≤ y) → x R y
          R≈ : (x≈y : x ≈ y) → x R y
          R≡ : (x≡y : x ≡ y) → x R y

        R-is-equiv : ∀ {x y} → x R y → prop
        R-is-equiv (R≤ x≤y) = false
        R-is-equiv (R≈ x≈y) = true
        R-is-equiv (R≡ x≡y) = true

        R-is-identity : ∀ {x y} → x R y → prop
        R-is-identity (R≤ x≤y) = false
        R-is-identity (R≈ x≈y) = false
        R-is-identity (R≡ x≡y) = true

        infix 1 begin-≤_ begin-≈_ begin-≡_
        infixr 2 step-≤ step-≈ step-≡ _≡⟨⟩_
        infix 3 _∎

        R-into-≤ : ∀ {x y} → x R y → x ≤ y
        R-into-≤ (R≤ x≤y) = x≤y
        R-into-≤ (R≈ x≈y) = forward x≈y
        R-into-≤ (R≡ ≡.refl) = is-preorder.rel-is-reflexive ≤-pre _

        R-into-≈ : ∀ {x y} → (r : x R y) → {R-is-equiv r} → x ≈ y
        R-into-≈ (R≈ x≈y) {s} = x≈y
        R-into-≈ (R≡ x≡y) {s} = is-equivalence.identity-to-rel ≈-equiv x≡y

        R-into-≡ : ∀ {x y} → (r : x R y) → {R-is-identity r} → x ≡ y
        R-into-≡ (R≡ x≡y) = x≡y


        step-≤ : ∀ (x : X) {y z} → y R z → x ≤ y → x R z
        step-≤ x (R≤ y≤z) x≤y = R≤ (rel-is-transitive ≤-pre x≤y y≤z)
        step-≤ x (R≈ y≈z) x≤y = R≤ (rel-is-transitive ≤-pre x≤y (R-into-≤ (R≈ y≈z)))
        step-≤ x (R≡ y≡z) x≤y = R≤ (rel-is-transitive ≤-pre x≤y (R-into-≤ (R≡ y≡z)))

        step-≈ : ∀ (x : X) {y z} → y R z → x ≈ y → x R z
        step-≈ x (R≤ y≤z) x≈y = R≤ (rel-is-transitive ≤-pre (R-into-≤ (R≈ x≈y)) y≤z)
        step-≈ x (R≈ y≈z) x≈y = R≈ (rel-is-transitive ≈-equiv x≈y y≈z)
        step-≈ x (R≡ y≡z) x≈y = R≈ (rel-is-transitive ≈-equiv x≈y (is-equivalence.identity-to-rel ≈-equiv y≡z))

        step-≡ : ∀ (x : X) {y z} → y R z → x ≡ y → x R z
        step-≡ x (R≤ y≤z) ≡.refl = R≤ y≤z
        step-≡ x (R≈ y≈z) ≡.refl = R≈ y≈z
        step-≡ x (R≡ y≡z) ≡.refl = R≡ y≡z

        begin-≤_ = R-into-≤
        begin-≈_ = R-into-≈
        begin-≡_ = R-into-≡

        _≡⟨⟩_ : ∀ (x : X) {y} → x R y → x R y
        x ≡⟨⟩ x≤y = x≤y


        _∎ : ∀ x → x R x
        x ∎ = R≡ ≡.refl

        syntax step-≤  x y∼z x≤y = x ≤⟨ x≤y ⟩ y∼z
        syntax step-≈  x y∼z x≈y = x ≈⟨ x≈y ⟩ y∼z
        syntax step-≡  x y∼z x≡y = x ≡⟨ x≡y ⟩ y∼z

    is-minimum : pred X
    is-minimum ⊥ = ∀ x → ⊥ ≤ x

    is-maximum : pred X
    is-maximum ⊤ = ∀ x → x ≤ ⊤

    module _ (S : subset X) where
      is-lowerbound : pred X
      is-lowerbound l = ∀ x → x ∈ S → l ≤ x

      is-upperbound : pred X
      is-upperbound u = ∀ x → x ∈ S → x ≤ u


      record is-greatest (g : X) : prop where
        constructor mk-greatest
        field
          element : g ∈ S
          property : is-upperbound g

      record is-least (l : X) : prop where
        constructor mk-least
        field
          element : l ∈ S
          property : is-lowerbound l

    module _ {x y u : X} where
      bin-upperbound→subset-upperbound : (x ≤ u × y ≤ u) → u ∈ is-upperbound (｛ x , y ｝₂)
      bin-upperbound→subset-upperbound (x≤u , y≤u) .x (left ≡.refl) = x≤u
      bin-upperbound→subset-upperbound (x≤u , y≤u) .y (right ≡.refl) = y≤u

      bin-upperbound←subset-upperbound : u ∈ is-upperbound (｛ x , y ｝₂) → (x ≤ u × y ≤ u)
      bin-upperbound←subset-upperbound u∈↑xy = u∈↑xy x (left ≡.refl) , u∈↑xy y (right ≡.refl)


    is-infimum : subset X → pred X
    is-infimum S gl = is-greatest (is-lowerbound S) gl

    is-supremum : subset X → pred X
    is-supremum S lb = is-least (is-upperbound S) lb

  record is-join-semilattice (_≤_ : rel X X) (_∨_ : binop X) : prop where
    field
      rel-is-preorder : is-preorder _≤_
      op-is-join : ∀ x x' → is-supremum _≤_ ｛ x , x' ｝₂ (x ∨ x')

  record is-meet-semilattice (_≤_ : rel X X) (_∧_ : binop X) : prop where
    field
      rel-is-preorder : is-preorder _≤_
      op-is-meet : ∀ x x' → is-infimum _≤_ ｛ x , x' ｝₂ (x ∧ x')

  record is-complete-join-semilattice (_≤_ : rel X X) (⋁ : subsetop X) : prop where
    field
      rel-is-preorder : is-preorder _≤_
      op-is-bigjoin : ∀ S → is-supremum _≤_ S (⋁ S)
    private
      _≈_ = iso-pair _≤_

    open is-preorder rel-is-preorder public
    module _ (S : subset X) where
      open is-least (op-is-bigjoin S) renaming (element to bigjoin-upperbound; property to bigjoin-least) public

  record is-complete-meet-semilattice (_≤_ : rel X X) (⋀ : subsetop X) : prop where
    field
      rel-is-preorder : is-preorder _≤_
      op-is-bigmeet : ∀ S → is-infimum _≤_ S (⋀ S)

    private
      _≈_ = iso-pair _≤_

    open is-preorder rel-is-preorder public
    module _ (S : subset X) where
      open is-greatest (op-is-bigmeet S) renaming (element to bigmeet-lowerbound; property to bigmeet-greatest) public

    bigmeet-up-iso : ∀ x → x ≈ ⋀ (↑ x)
    forward (bigmeet-up-iso x) = bigmeet-greatest (↑ x) x \_ → id
    backward (bigmeet-up-iso x) = bigmeet-lowerbound (↑ x) x (rel-is-reflexive x)

    bigmeet-up-intersection-iso : ∀ x S → S x → x ≈ ⋀ (↑ x ∩ S)
    forward (bigmeet-up-intersection-iso x S x∈S) = bigmeet-greatest (↑ x ∩ S) x \ _ → fst
    backward (bigmeet-up-intersection-iso x S x∈S) = bigmeet-lowerbound (↑ x ∩ S) x (rel-is-reflexive x , x∈S)

    bigmeet-up-intersection-iso-r : ∀ x S → S x → x ≈ ⋀ (S ∩ ↑ x)
    forward (bigmeet-up-intersection-iso-r x S x∈S) = bigmeet-greatest (S ∩ ↑ x) x \ _ → snd
    backward (bigmeet-up-intersection-iso-r x S x∈S) = bigmeet-lowerbound (S ∩ ↑ x) x (x∈S , rel-is-reflexive x)

    bigmeet-monotone : ∀ {S S'} → S ⊆ S' → ⋀ S' ≤ ⋀ S
    bigmeet-monotone {S} {S'} S⊆S' =
      let ⋀S-glb = bigmeet-greatest S
          ⋀S'-lb = bigmeet-lowerbound S'
      in
      begin-≤
      ⋀ S' ≤⟨ ⋀S-glb (⋀ S') (\ x x∈S → ⋀S'-lb x (S⊆S' x∈S)) ⟩
      ⋀ S ∎
      where open reasoning _ rel-is-preorder

    bigmeet-welldefined : ∀{S S'} → S ≅ S' → ⋀ S' ≈ ⋀ S
    forward (bigmeet-welldefined S=S') = bigmeet-monotone (forward S=S')
    backward (bigmeet-welldefined S=S') = bigmeet-monotone (backward S=S')

    bigmeet-equivalence :  ∀ S x → (∀ S' → S' ⊆ S → ⋀ S' ∈ S) → (⋀ S ≤ x) ↔ Σ _ \ x' → x' ≤ x × x' ∈ S
    forward (bigmeet-equivalence S x ⋀wd) ⋀S≤x = ⋀ S , ⋀S≤x , ⋀wd S id  
    backward (bigmeet-equivalence S x ⋀wd) (x' , x'≤x , x'∈X) =
      begin-≤
      ⋀ S ≤⟨  bigmeet-lowerbound _ _ x'∈X ⟩
      x' ≤⟨ x'≤x ⟩
      x ∎
      where open reasoning _ rel-is-preorder

    bigmeet-≡-≤ : ∀ {Y} → ∀ (f : Y → X) (p : Y → prop)  → ⋀ (\ x →  Σ Y \ y → (p y × (f y ≡ x))) ≈ ⋀ (\ x → Σ Y \ y → (p y × (f y ≤ x)))
    forward (bigmeet-≡-≤ f p) = bigmeet-greatest _ _ \ { x (y , py , fy≤x) → bigmeet-lowerbound _ _ (y , (py , (≡.refl))) ⟨ rel-is-transitive ⟩ fy≤x }
    backward (bigmeet-≡-≤ f p) = bigmeet-monotone \{ {x'} (y , py , fy≡x') → y , (py , identity-to-rel fy≡x') }

    bigmeet-mono-equivalence : ∀ S {f : X → X} (f-is-mono : ∀ {x x'} → x ≤ x' → f x ≤ f x') → (∀ x₀ → x₀ ∈ S → f x₀ ≤ x₀) ↔ (∀ x₀ → f x₀ ≤ ⋀ (\ x → x₀ ≤ x × x ∈ S))
    forward (bigmeet-mono-equivalence S f-is-mono) ∀x,x∈S→fx≤x x₀ = bigmeet-greatest _ _ \{ x (x₀≤x , x∈S) → rel-is-transitive (f-is-mono x₀≤x) (∀x,x∈S→fx≤x x x∈S)}
      where open reasoning _ rel-is-preorder
    backward (bigmeet-mono-equivalence S f-is-mono) ∀x₀,fx₀≤⋀[x:x₀≤x×x∈S] x x∈S =  rel-is-transitive (∀x₀,fx₀≤⋀[x:x₀≤x×x∈S] x) (bigmeet-lowerbound _ _ ((rel-is-reflexive _) , x∈S))

  is-binop-closed-subset : (_≤_ : rel X X) (_∧_ : binop X) (S : subset X) → prop
  is-binop-closed-subset _≤_ _∧_ S = ∀ x x' → x ∧ x' ∈ S

  is-subsetop-closed-subset : (_≤_ : rel X X) (⋀ : subsetop X) (S : subset X) → prop
  is-subsetop-closed-subset _≤_ ⋀ S = ∀ S' → S' ⊆ S → ⋀ S' ∈ S

  is-meet-closed-subset :  {_≤_ : rel X X} {⋀ : subsetop X} → is-complete-meet-semilattice _≤_ ⋀ → pred (subset X)
  is-meet-closed-subset {_≤_} {⋀} cmlat = is-subsetop-closed-subset _≤_ ⋀

  module _ {_≤_ : rel X X} {⋀ : subsetop X}
    {superset-is-cmlat : is-complete-meet-semilattice _≤_ ⋀}
    {S : subset X} (S-meet-closed : is-meet-closed-subset superset-is-cmlat S)
    where
    open is-complete-meet-semilattice superset-is-cmlat
    ↑∩-is-meet-closed : ∀ x → is-subsetop-closed-subset _≤_ ⋀ (↑ x ∩ S)
    fst (↑∩-is-meet-closed x S' S'⊆↑x∩S) = bigmeet-greatest _ _ \ _ → fst ∘ S'⊆↑x∩S
    snd (↑∩-is-meet-closed x S' S'⊆↑x∩S) = S-meet-closed S' (snd ∘ S'⊆↑x∩S)


module product-order {D E : Set} (_≤D_ : rel D D) (_≤E_ : rel E E) where
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

record preordered-set : Set where
  constructor pre
  field
    carrier : Set
    relation : rel carrier carrier
    property : is-preorder relation

  lowerbounds : (S : subset carrier) → subset carrier
  lowerbounds S = is-lowerbound relation S

  upperbounds : (S : subset carrier) → subset carrier
  upperbounds S = is-upperbound relation S

  opposite : preordered-set
  carrier opposite = carrier
  relation opposite = flip relation
  property opposite = is-preorder.opposite property
  equiv = iso-pair relation


module _ where
  open is-preorder
  →-is-preorder : is-preorder (\ X Y → (X → Y))
  rel-is-reflexive →-is-preorder X x = x
  rel-is-transitive →-is-preorder f g x = g (f x)

  ⊆-is-preorder : ∀ {X : Set} → is-preorder {X = subset X} _⊆_
  rel-is-reflexive ⊆-is-preorder S x∈S = x∈S
  rel-is-transitive ⊆-is-preorder S⊆S' S'⊆S'' x∈S = S'⊆S'' (S⊆S' x∈S)

  ⊆₂-is-preorder : ∀ {X Y : Set} → is-preorder {X = rel X Y} _⊆₂_
  rel-is-reflexive ⊆₂-is-preorder S x∈S = x∈S
  rel-is-transitive ⊆₂-is-preorder S⊆S' S'⊆S'' x∈S = S'⊆S'' (S⊆S' x∈S)

module _ {X : Set} {Y : Set} {_≤X_ : rel X X} {_≤Y_ : rel Y Y}
  (≤X-pre : is-preorder _≤X_) (≤Y-pre : is-preorder _≤Y_) where
  private
    _≈X_ = iso-pair _≤X_
    _≈Y_ = iso-pair _≤Y_

  is-welldefined : pred (X → Y)
  is-welldefined f = ∀ {d d'} → d ≈X d' → f d ≈Y f d'

  is-monotone : pred (X → Y)
  is-monotone f = ∀ {d d'} → d ≤X d' → f d ≤Y f d'


  monotone2welldefined : {f : X → Y} → is-monotone f → is-welldefined  f
  forward (monotone2welldefined {f} f-is-monotone d≈d') = f-is-monotone (forward d≈d')
  backward (monotone2welldefined {f} f-is-monotone d≈d') = f-is-monotone (backward d≈d')

  transport : {f : X → Y} → (func-is-welldefined : is-welldefined f) → {d d' : X} → (iso-pair : d ≈X d') → f d ≤Y f d'
  transport func-is-welldefined iso-pair = forward (func-is-welldefined iso-pair)

is-antitone : {X : Set} {Y : Set} {_≤X_ : rel X X} {_≤Y_ : rel Y Y} (≤X-pre : is-preorder _≤X_) (≤Y-pre : is-preorder _≤Y_) → pred (X → Y)
is-antitone ≤X-pre ≤Y-pre f = is-monotone ≤X-pre (is-preorder.opposite ≤Y-pre) f


≅→∀↔∀ : {X : Set} → (P Q : pred X) → P ≅ Q → (∀ x → P x) ↔ (∀ x → Q x)
forward (≅→∀↔∀ P Q P≅Q) ∀P x = forward P≅Q (∀P x)
backward (≅→∀↔∀ P Q P≅Q) ∀Q x = backward P≅Q (∀Q x)

module _ {X : Set} {_≤_ : rel X X} (≤-pre : is-preorder _≤_)
  where
  private
    _≈_ = iso-pair _≤_

  is-welldefined-subset : pred (subset X)
  is-welldefined-subset S = is-welldefined ≤-pre →-is-preorder S

record monotone-func (D E : preordered-set) : Set where
  constructor mono
  open preordered-set D renaming (carrier to |D| ; property to ≤D-pre)
  open preordered-set E renaming (carrier to |E| ; property to ≤E-pre)
  field
    func : |D| → |E|
    property : is-monotone ≤D-pre ≤E-pre func

  dual : monotone-func (preordered-set.opposite D) (preordered-set.opposite E)
  func dual = func
  property dual = property

antitone-func : (D E : preordered-set) → Set
antitone-func D E = monotone-func D (preordered-set.opposite E)

pre-comp : ∀ {X Y Z : preordered-set} → monotone-func Y Z →  monotone-func X Y → monotone-func X Z
pre-comp (mono f f-mono) (mono g g-mono) = mono (f ∘ g) (f-mono ∘ g-mono)

pre-comp-anti : ∀ {X Y Z : preordered-set} → antitone-func Y Z →  antitone-func X Y → monotone-func X Z
pre-comp-anti (mono f f-mono) (mono g g-mono) = mono (f ∘ g) (f-mono ∘ g-mono)


record complete-join-semilattice : Set where
  constructor cjlat
  field
    carrier : Set
    relation : rel carrier carrier
    operation : subsetop carrier
    property : is-complete-join-semilattice relation operation

record complete-meet-semilattice : Set where
  constructor cmlat
  field
    carrier : Set
    relation : rel carrier carrier
    operation : subsetop carrier
    property : is-complete-meet-semilattice relation operation

record join-semilattice : Set where
  constructor jlat
  field
    carrier : Set
    relation : rel carrier carrier
    operation : binop carrier
    property : is-join-semilattice relation operation

record meet-semilattice : Set where
  constructor m-slat
  field
    carrier : Set
    relation : rel carrier carrier
    operation : binop carrier
    property : is-meet-semilattice relation operation

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

cmlat→pre : complete-meet-semilattice → preordered-set
cmlat→pre (cmlat _ _ _ X-cmlat) = pre _ _ X.rel-is-preorder
  where
    module X = is-complete-meet-semilattice X-cmlat


cm2j : ∀ {X} → rel X X → subsetop X → binop X
cm2j _≤_ ⋀ x x' = ⋀ ((\ u → x ≤ u) ∩ (\ u → x' ≤ u))

cm2cj : ∀ {X} → rel X X → subsetop X → subsetop X
cm2cj _≤_ ⋀ S = ⋀ (is-upperbound _≤_ S)

{-
is-complete-meet-semilattice X _≤_ ⋀ props → is-join-semilattice X _≤_ (\ x
-}


-- complete meet semilattice is complete join semilattice
cmlat→cjlat : complete-meet-semilattice → complete-join-semilattice
cmlat→cjlat (cmlat X _≤_ ⋀  X-prop) =
  cjlat X _≤_ _ X-cjlat
  where
    open is-complete-meet-semilattice X-prop
      renaming (rel-is-preorder to ≤-is-preorder ; op-is-bigmeet to ⋀-is-bigmeet)
    open is-complete-join-semilattice
    -- open is-preorder ≤-is-preorder
    open reasoning _ ≤-is-preorder
    X-cjlat : is-complete-join-semilattice _≤_ _
    rel-is-preorder X-cjlat = ≤-is-preorder
    is-least.element (op-is-bigjoin X-cjlat S) x x∈S =
      begin-≤
      x ≤⟨ bigmeet-greatest (is-upperbound _≤_ S) x (\ x' p → p x x∈S) ⟩
      cm2cj _≤_ ⋀ S ∎
    is-least.property (op-is-bigjoin X-cjlat S) x x∈ubS =
      begin-≤
      cm2cj _≤_ ⋀ S ≤⟨ bigmeet-lowerbound (is-upperbound _≤_ S) x x∈ubS ⟩
      x ∎

-- binary preordered-set product
_×-pre_ : preordered-set → preordered-set → preordered-set
(pre D _≤D_ ≤D-pre) ×-pre (pre E _≤E_ ≤E-pre) =
  pre (D × E) _≤_ ≤D×E-po
  where
    module ≤D = is-preorder ≤D-pre
    module ≤E = is-preorder ≤E-pre
    open is-preorder
    _≤_ : rel (D × E) (D × E)
    _≤_ = \ (d  , e) (d' , e') → d ≤D d' × e ≤E e'
    ≤D×E-po : is-preorder _≤_
    rel-is-reflexive ≤D×E-po (d , e) = ≤D.rel-is-reflexive d , ≤E.rel-is-reflexive e
    rel-is-transitive ≤D×E-po (d≤d' , e≤e') (d'≤d'' , e'≤e'') = ≤D.rel-is-transitive d≤d' d'≤d'' , ≤E.rel-is-transitive e≤e' e'≤e''

-- binary complete meet semilattice product
_×-cmlat_ : complete-meet-semilattice → complete-meet-semilattice → complete-meet-semilattice
D-cmlat@(cmlat D _≤D_ ⋀D D-prop) ×-cmlat E-cmlat@(cmlat E _≤E_ ⋀E E-prop) =
  cmlat
  (D × E)
  (preordered-set.relation D×E-pre)
  (\ S → ⋀D (fst-subset S) , ⋀E (snd-subset S))
  property
    where
    open is-complete-meet-semilattice D-prop renaming (rel-is-preorder to ≤D-is-preorder ; op-is-bigmeet to ⋀D-is-bigmeet ; ↑ to ↑D)
    open is-complete-meet-semilattice E-prop renaming (rel-is-preorder to ≤E-is-preorder ; op-is-bigmeet to ⋀E-is-bigmeet ; ↑ to ↑E)
    D-pre = cmlat→pre D-cmlat
    E-pre = cmlat→pre E-cmlat
    D×E-pre = D-pre ×-pre E-pre
    open is-complete-meet-semilattice
    module D-prop = is-complete-meet-semilattice D-prop
    module E-prop = is-complete-meet-semilattice E-prop
    property : is-complete-meet-semilattice _ _
    rel-is-preorder property = preordered-set.property D×E-pre
    is-greatest.element (op-is-bigmeet property S) (d' , e') de'∈S = ⋀S₁≤d' , ⋀S₂≤e'
      where
        ⋀S₁≤d' : ⋀D (fst-subset S) ≤D d'
        ⋀S₁≤d' =
          begin-≤
          ⋀D (fst-subset S)     ≤⟨ D-prop.bigmeet-lowerbound (fst-subset S) d' (e' , de'∈S) ⟩
          d' ∎
          where open reasoning _ ≤D-is-preorder
        ⋀S₂≤e' : (⋀E (snd-subset S)) ≤E e'
        ⋀S₂≤e' =
          begin-≤
          ⋀E (snd-subset S)     ≤⟨ E-prop.bigmeet-lowerbound (snd-subset S) e' (d' , de'∈S) ⟩
          e' ∎
          where open reasoning _≤E_ (preordered-set.property E-pre)

    is-greatest.property (op-is-bigmeet property S) (d , e) de-lbS = d≤⋀S₁ ,  e≤⋀S₂
      where
        d≤⋀S₁ : d ≤D ⋀D (fst-subset S)
        d≤⋀S₁ =
          begin-≤
          d ≤⟨ D-prop.bigmeet-greatest (fst-subset S) d (\ u u∈S₁ → fst (de-lbS (u , fst u∈S₁) (snd u∈S₁))) ⟩
          ⋀D (fst-subset S) ∎
          where open reasoning _ ≤D-is-preorder
        e≤⋀S₂ : e ≤E ⋀E (snd-subset S)
        e≤⋀S₂ =
          begin-≤
          e ≤⟨ E-prop.bigmeet-greatest (snd-subset S) e (\ u u∈S₀ → snd (de-lbS (fst u∈S₀ , u) (snd u∈S₀))) ⟩
          ⋀E (snd-subset S) ∎
          where open reasoning _ ≤E-is-preorder

module _ (D E : Set) where
  func-pair : Set
  func-pair = (D → E) × (E → D)

  pair-app : func-pair → D × E → E × D
  pair-app fb de = fst fb (fst de) , snd fb (snd de)

module _ {D E : Set} {_≤D_ : rel D D} {_≤E_ : rel E E} where
  module _ (≤D-pre : is-preorder _≤D_) (≤E-pre : is-preorder _≤E_) where
    is-monotone-pair : pred (func-pair D E)
    is-monotone-pair fb = is-monotone ≤D-pre ≤E-pre (fst fb) × is-monotone ≤E-pre ≤D-pre (snd fb)

    record monotone-func-pair : Set where
      constructor mfp
      field
        funcp : func-pair D E
        funcp-is-monotone : is-monotone-pair funcp

    mfp2fp : monotone-func-pair → func-pair D E
    mfp2fp (mfp funcp _) = funcp

is-galois-connection : {C D : preordered-set} (L : monotone-func D C) (R : monotone-func C D) → Set
is-galois-connection {C} {D} L R = ∀ (c : C.carrier) (d : D.carrier) → C.relation (L.func d) c ↔ D.relation d (R.func c)
  where
    module C = preordered-set C
    module D = preordered-set D
    module L = monotone-func L
    module R = monotone-func R

is-antitone-galois-connection : {C D : preordered-set} (L : antitone-func D C) (R : antitone-func C D) → Set
is-antitone-galois-connection {C} L R = is-galois-connection {preordered-set.opposite C} L (monotone-func.dual R)

is-antitone-galois-connection' : {C D : preordered-set} (L : antitone-func D C) (R : antitone-func C D) → Set
is-antitone-galois-connection' {C} {D} L R = is-galois-connection {C} {preordered-set.opposite D} (monotone-func.dual L) R

record galois-connection (C D : preordered-set) : Set where
  constructor gal-conn
  field
    left-adjoint : monotone-func D C
    right-adjoint : monotone-func C D

  private
    module C = preordered-set C renaming (relation to _≤_ ; equiv to _≅_)
    module D = preordered-set D renaming (relation to _≤_ ; equiv to _≅_)
    module C-pre = is-preorder C.property
    module D-pre = is-preorder D.property
    module L = monotone-func left-adjoint renaming (property to mono)
    module R = monotone-func right-adjoint renaming (property to mono)
  field
    left-right-is-galois-connection : is-galois-connection left-adjoint right-adjoint

  rl = R.func ∘ L.func
  lr = L.func ∘ R.func

  rl-mono : is-monotone D.property D.property rl
  rl-mono = R.mono ∘ L.mono

  lr-mono : is-monotone C.property C.property lr
  lr-mono = L.mono ∘ R.mono

  rl-increasing : id ⟨ pointwise D._≤_ ⟩ rl
  rl-increasing d = forward (left-right-is-galois-connection (L.func d) d) (C-pre.rel-is-reflexive _)

  lr-decreasing : lr ⟨ pointwise C._≤_ ⟩ id
  lr-decreasing c = backward (left-right-is-galois-connection c (R.func c)) (D-pre.rel-is-reflexive _)

  rl-idempotent : rl ∘ R.func ⟨ pointwise D._≅_ ⟩ R.func
  forward (rl-idempotent c) = R.mono (lr-decreasing c)
  backward (rl-idempotent c) = rl-increasing (R.func c)

  lr-idempotent : lr ∘ L.func ⟨ pointwise C._≅_ ⟩ L.func
  forward (lr-idempotent d) = lr-decreasing (L.func d)
  backward (lr-idempotent d) = L.mono (rl-increasing d)

antitone-galois-connection : preordered-set → preordered-set → Set
antitone-galois-connection C D = galois-connection (preordered-set.opposite C) D

comp-galois-connection : {C D E : preordered-set} → galois-connection C D → galois-connection D E → galois-connection C E
comp-galois-connection {C} {D} {E}
  (gal-conn L R gl-LR) (gal-conn L' R' gl-LR')
  = gal-conn (pre-comp L L') (pre-comp R' R) gl
  where
    gl : is-galois-connection (pre-comp L L') (pre-comp R' R)
    forward (gl c e) LL'e≤c = forward (gl-LR' _ _) (forward (gl-LR _ _) LL'e≤c)
    backward (gl c e) e≤R'Rc = backward (gl-LR _ _) (backward (gl-LR' _ _) e≤R'Rc)


is-order-isomorphism : {C D : preordered-set} (L : monotone-func D C) (R : monotone-func C D) → Set
is-order-isomorphism {C} {D} L R = (func L ∘ func R ⟨ pointwise (equiv C) ⟩ id) × (func R ∘ func L ⟨ pointwise (equiv D) ⟩ id)
  where open monotone-func
        open preordered-set

record order-isomorphic (C D : preordered-set) : Set where
  constructor ord-iso
  field
    from : monotone-func D C
    to : monotone-func C D
    to-is-order-isomorphism : is-order-isomorphism from to

module _
  {D : _} {_≤D_ : _} {⋀D : _} (D-is-cmlat : _)
  {E : _} {_≤E_ : _} {⋀E : _} (E-is-cmlat : _) where


  private
    D-cmlat = cmlat D _≤D_ ⋀D D-is-cmlat
    E-cmlat = cmlat E _≤E_ ⋀E E-is-cmlat
    D-pre = cmlat→pre D-cmlat
    E-pre = cmlat→pre E-cmlat
    module D = is-complete-meet-semilattice D-is-cmlat renaming (rel-is-preorder to ≤-pre ; rel-is-reflexive to ≤-refl ; rel-is-transitive to ≤-trans)
    module E = is-complete-meet-semilattice E-is-cmlat renaming (rel-is-preorder to ≤-pre ; rel-is-reflexive to ≤-refl ; rel-is-transitive to ≤-trans)
    D×E-cmlat = D-cmlat ×-cmlat E-cmlat
    D×E-is-cmlat = complete-meet-semilattice.property D×E-cmlat


  open complete-meet-semilattice D×E-cmlat renaming (operation to ⋀ ; relation to _≤_)
  open is-complete-meet-semilattice D×E-is-cmlat renaming (rel-is-preorder to ≤-pre ; rel-is-reflexive to ≤-refl ; rel-is-transitive to ≤-trans)

  open product-order _≤D_ _≤E_ renaming (_≈₁_ to _≈D_ ; _≈₂_ to _≈E_)

  -- d₀≤d → fd≤e → fd₀≤e
  mono-≤ : {f : D → E} (f-mono : is-monotone D.≤-pre E.≤-pre f) → ∀ {d e d₀} → d₀ ≤D d → f d ≤E e → f d₀ ≤E e
  mono-≤ {f} f-mono {d} {e} {d₀} d≤d₀ fd≤e =
    begin-≤
    f d₀ ≤⟨ f-mono d≤d₀ ⟩
    f d ≤⟨ fd≤e ⟩
    e ∎
    where
      open reasoning _  E.≤-pre

  -- f (⋀S) ≤ ⋀ (f S)
  mono-meet≤meet-mono : {f : D → E} (f-mono : is-monotone D.≤-pre E.≤-pre f) → (S : subset D) → f (⋀D S) ≤E ⋀E (fimage f S)
  mono-meet≤meet-mono {f} f-mono S =
    begin-≤
    f (⋀D S) ≤⟨ E.bigmeet-greatest _ _ (\ {e (d , d∈S , fd≡e) →  ≡.subst (f (⋀D S) ≤E_) fd≡e (f-mono (D.bigmeet-lowerbound S d d∈S)) }) ⟩
    ⋀E (fimage f S) ∎
    where
      open reasoning _  E.≤-pre

  module _ (f : D → E) (b : E → D) where

    -- f d ≤ e × b e ≤ d ↔ b (f d) ≤ d
    mono-pair-backforward : (b-mono : is-monotone E.≤-pre D.≤-pre b) → ∀ d → (Σ[ e ∈ E ] (f d ≤E e) × (b e ≤D d)) ↔ (b (f d) ≤D d)
    forward (mono-pair-backforward b-mono d) (e , fd≤e , be≤d) =
      begin-≤
      b (f d) ≤⟨ b-mono fd≤e ⟩
      b e ≤⟨ be≤d ⟩
      d ∎
      where
        open reasoning _ D.≤-pre
    backward (mono-pair-backforward _ d) bfd≤d = f d , E.≤-refl (f d) , bfd≤d


    -- f d ≤ e × b e ≤ d ↔ f (b e) ≤ e
    mono-pair-forwardback : (f-mono : is-monotone D.≤-pre E.≤-pre f) → ∀ e → (Σ[ d ∈ D ] (f d ≤E e) × (b e ≤D d)) ↔ (f (b e) ≤E e)
    forward (mono-pair-forwardback f-mono e) (d , fd≤e , be≤d) =
      begin-≤
      f (b e) ≤⟨ f-mono be≤d ⟩
      f d ≤⟨ fd≤e ⟩
      e ∎
      where
        open reasoning _ E.≤-pre
    backward (mono-pair-forwardback _ e) fbe≤e = b e , fbe≤e , D.≤-refl (b e)




```

-->

2-poset
-------

https://ncatlab.org/nlab/show/2-poset

- Category of relations:
  - objects: complete lattices, D , E , F , ...
  - morphisms: relations between objects, r , r' , r'' , ...
  - compositions: relation composition, r;r'
  - 2-morphisms: inclusion r ⊆ r'

- Category of bidirectional monotone functions
  - objects: complete lattices, D , E , F , ...
  - morphisms: pairs of forward and backward monotone functions, (f , b) , (f' , b') , ...
  - compositions: composition of forward and backward monotone functions, (f , b) ∘ (f' , b') = (f ∘ f' , b' ∘ b)
  - 2-morphisms: pointwise ordering, (f , b) ≤ (f' , b') := (∀ d, f d ≤ f' d) ∧ (∀ e , b e ≤ b' e)

here is an adjunction

```txt
            R ⊆ f2r fb
r2f ⊣ f2r   ==========
            r2f R ≥ fb
```


In homogeneous setting, composition of 2-morphisms is a tensor product in monoidal category
- (D , D) ⊗ (D , D) → (D , D)

```txt
                       r2f
                      ---->
            (𝒫(D×E),⊆) ⊥   (D⇒E × E⇒D , ≤) + monotone
                 |    <----    |
                 |     f2r     |
                 |             |
            (𝒫(D×E),⊆) ==== (D⇒E × E⇒D , ≤)
            + something       monotone + something
```

The bottom two categories in the diagram are fixed point of adjunction.
Their tensor product does different thing (e.g. adding pair of retation) from the top two.

- r2f ∘ f2r adds pairs on the relation for butterfly shape relation

```txt
    d     e
    |\   /|
    | \ / |
    d₀ x  e₀  ===> d₀---e₀
    | / \ |
    |/   \|
    d'    e'
```



```agda

module transfer-function-pair
  (D : _) (_≤D_ : _) (⋀D : _) (D-is-cmlat : _)
  (E : _) (_≤E_ : _) (⋀E : _) (E-is-cmlat : _)
  where
  private
    D-cmlat = cmlat D _≤D_ ⋀D D-is-cmlat
    E-cmlat = cmlat E _≤E_ ⋀E E-is-cmlat

  private
    module D = is-complete-meet-semilattice D-is-cmlat
      renaming (rel-is-preorder to ≤-pre ; op-is-bigmeet to ⋀-bigmeet ; rel-is-reflexive to ≤-refl ; rel-is-transitive to ≤-trans)
    module E = is-complete-meet-semilattice E-is-cmlat
      renaming (rel-is-preorder to ≤-pre ; op-is-bigmeet to ⋀-bigmeet ; rel-is-reflexive to ≤-refl ; rel-is-transitive to ≤-trans)
    module ≤D-reasoning = reasoning _ D.≤-pre
    module ≤E-reasoning = reasoning _ E.≤-pre

    D×E-cmlat = D-cmlat ×-cmlat E-cmlat

  open complete-meet-semilattice D×E-cmlat
    renaming (relation to _≤_ ; operation to ⋀ ; property to D×E-is-cmlat )

  D-cjlat = cmlat→cjlat D-cmlat
  open complete-join-semilattice D-cjlat
    renaming (operation to ⋁D ; property to D-is-cjlat)
  E-cjlat = cmlat→cjlat E-cmlat
  open complete-join-semilattice E-cjlat
    renaming (operation to ⋁E ; property to E-is-cjlat)

  D×E-cjlat = cmlat→cjlat D×E-cmlat
  open complete-join-semilattice D-cjlat
    renaming (operation to ⋁ ; property to D×E-is-cjlat)

  ⊤D = ⋀D ∅
  ⊤E = ⋀E ∅
  ⊤ = ⋀ ∅

  ⊥D = ⋁D ∅
  ⊥E = ⋁E ∅
  ⊥ = ⋁ ∅

  _∨D_ = \ x y → ⋁D ｛ x , y ｝₂
  _∨E_ = \ x y → ⋁E ｛ x , y ｝₂
  _∨_ = \ x y → ⋁ ｛ x , y ｝₂


  open is-complete-meet-semilattice D×E-is-cmlat
    renaming (rel-is-preorder to ≤-pre ; op-is-bigmeet to ⋀-bigmeet ; rel-is-reflexive to ≤-refl ; rel-is-transitive to ≤-trans)

  private
    module ≤-reasoning = reasoning _ ≤-pre

  open product-order _≤D_ _≤E_ renaming (_≈₁_ to _≈D_ ; _≈₂_ to _≈E_)

  private
    _→mono_ = is-monotone

  _≤fp_ : rel (func-pair D E) (func-pair D E)
  (f , b) ≤fp (f' , b') = (∀ d → f d ≤E f' d) × (∀ e → b e ≤D b' e)

  _≤mfp_ : rel (monotone-func-pair D.≤-pre E.≤-pre) (monotone-func-pair D.≤-pre E.≤-pre)
  mfb ≤mfp mfb' = mfb.funcp ≤fp mfb'.funcp
    where module mfb = monotone-func-pair mfb
          module mfb' = monotone-func-pair mfb'

  ≈×≈→≈ : ∀ {d d' e e'} → d ≈D d' → e ≈E e' → (d , e) ≈ (d' , e')
  forward (≈×≈→≈ ≈D ≈E) = forward ≈D , forward ≈E
  backward (≈×≈→≈ ≈D ≈E) = backward ≈D , backward ≈E


  ≅×≅→≅ : ∀ {X Y} {S S' : subset X} {T T' : subset Y} → S ≅ S' → T ≅ T' → ((S ∘ fst) ∩ (T ∘ snd)) ≅ ((S' ∘ fst) ∩ (T' ∘ snd))
  forward (≅×≅→≅ S=S' T=T') (d , e) = (forward S=S' d) , (forward T=T' e)
  backward (≅×≅→≅ S=S' T=T') (d , e) = (backward S=S' d) , (backward T=T' e)

  _≈fp_ = iso-pair _≤fp_
  _≈mfp_ = iso-pair _≤mfp_

  module _ where
    open is-preorder
    ≤fp-is-preorder : is-preorder _≤fp_
    fst (rel-is-reflexive ≤fp-is-preorder (f , b)) d = E.≤-refl (f d)
    snd (rel-is-reflexive ≤fp-is-preorder (f , b)) e = D.≤-refl (b e)
    fst (rel-is-transitive ≤fp-is-preorder fb≤fb' fb'≤fb'') d = E.≤-trans (fst fb≤fb' d) (fst fb'≤fb'' d)
    snd (rel-is-transitive ≤fp-is-preorder fb≤fb' fb'≤fb'') e = D.≤-trans (snd fb≤fb' e) (snd fb'≤fb'' e)

    ≤mfp-is-preorder : is-preorder _≤mfp_
    fst (rel-is-reflexive ≤mfp-is-preorder (mfp (f , b) _)) d = E.≤-refl (f d)
    snd (rel-is-reflexive ≤mfp-is-preorder (mfp (f , b) _)) e = D.≤-refl (b e)
    fst (rel-is-transitive ≤mfp-is-preorder fb≤fb' fb'≤fb'') d = E.≤-trans (fst fb≤fb' d) (fst fb'≤fb'' d)
    snd (rel-is-transitive ≤mfp-is-preorder fb≤fb' fb'≤fb'') e = D.≤-trans (snd fb≤fb' e) (snd fb'≤fb'' e)

  module _ {R : subset (D × E)}
    (R-welldefined : is-welldefined-subset ≤-pre R)
    (R-meet-closed : is-meet-closed-subset D×E-is-cmlat R) where
    R-subst : ∀{p q} → (iso : p ≈ q) → R p → R q
    R-subst iso = transport ≤-pre →-is-preorder R-welldefined iso

    fst-meet-closed : is-meet-closed-subset D-is-cmlat (fst-subset R)
    fst-meet-closed S₁ S₁⊆R₁ = ⋀E S₂ , ⋀S₁⋀S₂∈R
      where

      counterpart : ∀ {d} → d ∈ S₁ → E
      counterpart d∈S₁ = fst (S₁⊆R₁ d∈S₁)

      pairing-in-R : ∀ {d} → (d∈S₁ : d ∈ S₁) → (d , counterpart (d∈S₁)) ∈ R
      pairing-in-R d∈S₁ = snd (S₁⊆R₁ d∈S₁)

      S : subset (D × E)
      S (d , e) = Σ (d ∈ S₁) \ d∈S₁ → counterpart d∈S₁ ≈E e

      S₂ : subset E
      S₂ = snd-subset S

      fstS=S₁ : fst-subset S ≅ S₁
      backward fstS=S₁ d∈S₁                      = (counterpart d∈S₁ , d∈S₁ , iso-refl E.≤-refl _)
      forward  fstS=S₁ (d∈fstS @ (_ , d∈S₁ , _)) = d∈S₁

      S=S₁×S₂ : ((fst-subset S ∘ fst) ∩ (snd-subset S ∘ snd)) ≅ ((S₁ ∘ fst) ∩ (S₂ ∘ snd))
      S=S₁×S₂ =  ≅×≅→≅ fstS=S₁ (is-preorder.iso-reflexive ⊆-is-preorder S₂)

      ⋀fstS≈D⋀S₁ : ⋀D (fst-subset S) ≈D ⋀D S₁
      ⋀fstS≈D⋀S₁ = D.bigmeet-welldefined (! fstS=S₁)

      S⊆R : S ⊆ R
      S⊆R (d∈S' , counterpart-d=e) = R-subst (≈×≈→≈ (D.iso-reflexive _) counterpart-d=e) (pairing-in-R d∈S')

      ⋀S∈R : ⋀ S ∈ R
      ⋀S∈R = R-meet-closed S S⊆R

      ⋀S₁⋀S₂∈R : (⋀D S₁ , ⋀E S₂) ∈ R
      ⋀S₁⋀S₂∈R = R-subst (≈×≈→≈ ⋀fstS≈D⋀S₁ (E.iso-reflexive _)) ⋀S∈R

    snd-meet-closed : is-meet-closed-subset E-is-cmlat (snd-subset R)
    snd-meet-closed S₂ S₂⊆R₂ = ⋀D S₁ , ⋀S₁⋀S₂∈R
      where

      counterpart : ∀ {e} → e ∈ S₂ → D
      counterpart e∈S₂ = fst (S₂⊆R₂ e∈S₂)

      pairing-in-R : ∀ {e} → (e∈S₂ : e ∈ S₂) → (counterpart (e∈S₂), e) ∈ R
      pairing-in-R e∈S₂ = snd (S₂⊆R₂ e∈S₂)

      S : subset (D × E)
      S (d , e) = Σ (e ∈ S₂) \ e∈S₂ → counterpart e∈S₂ ≈D d

      S₁ : subset D
      S₁ = fst-subset S

      sndS=S₂ : snd-subset S ≅ S₂
      backward sndS=S₂ e∈S₂                      = (counterpart e∈S₂ , e∈S₂ , iso-refl D.≤-refl _)
      forward  sndS=S₂ (e∈sndS @ (_ , e∈S₂ , _)) = e∈S₂

      S=S₁×S₂ : ((fst-subset S ∘ fst) ∩ (snd-subset S ∘ snd)) ≅ ((S₁ ∘ fst) ∩ (S₂ ∘ snd))
      S=S₁×S₂ =  ≅×≅→≅ (is-preorder.iso-reflexive ⊆-is-preorder S₁) sndS=S₂

      ⋀sndS≈E⋀S₂ : ⋀E (snd-subset S) ≈E ⋀E S₂
      ⋀sndS≈E⋀S₂ = E.bigmeet-welldefined (! sndS=S₂)

      S⊆R : S ⊆ R
      S⊆R (e∈S' , counterpart-e=d) = R-subst (≈×≈→≈ counterpart-e=d (E.iso-reflexive _)) (pairing-in-R e∈S')

      ⋀S∈R : ⋀ S ∈ R
      ⋀S∈R = R-meet-closed S S⊆R

      ⋀S₁⋀S₂∈R : (⋀D S₁ , ⋀E S₂) ∈ R
      ⋀S₁⋀S₂∈R = R-subst (≈×≈→≈ (D.iso-reflexive _) ⋀sndS≈E⋀S₂) ⋀S∈R


  -- Left adjoin
  r2f : subset (D × E) → func-pair D E
  fst (r2f R) d₀ = ⋀E ｛ e ∣ Σ[ d ∈ D ] (d₀ ≤D d × (d , e) ∈ R) ｝
  snd (r2f R) e₀ = ⋀D ｛ d ∣ Σ[ e ∈ E ] (e₀ ≤E e × (d , e) ∈ R) ｝

  -- Right adjoint
  f2r : func-pair D E → subset (D × E)
  f2r (f , b) (d , e) = f d ≤E e × b e ≤D d


  module _ {f : D → E} {b : E → D}
    (f-is-mono : is-monotone D.≤-pre E.≤-pre f) (b-is-mono : is-monotone E.≤-pre D.≤-pre b) where
    f2r-mono-join-closed : is-meet-closed-subset D×E-is-cmlat (f2r (f , b))
    fst (f2r-mono-join-closed S' S'⊆) =
      begin-≤
      f (fst (⋀ S')) ≡⟨⟩
      f (⋀D ｛ d ∣ Σ[ e ∈ E ] ((d , e) ∈ S')｝) ≤⟨ mono-meet≤meet-mono D-is-cmlat E-is-cmlat f-is-mono ｛ d ∣ Σ[ e ∈ E ] ((d , e) ∈ S')｝ ⟩
      ⋀E (fimage f ｛ d ∣ Σ[ e ∈ E ] ((d , e) ∈ S')｝) ≡⟨⟩
      ⋀E ｛ e ∣ Σ[ d ∈ D ] ((Σ[ e' ∈ E ](S' (d , e'))) × f d ≡ e)｝ ≈⟨ E.bigmeet-≡-≤ f _ ⟩
      ⋀E ｛ e ∣ Σ[ d ∈ D ] ((Σ[ e' ∈ E ](S' (d , e'))) × f d ≤E e)｝ ≤⟨ E.bigmeet-monotone (\ { {e} (d , de∈S') → d , ((e , de∈S') , fst (S'⊆ de∈S')) }) ⟩
      ⋀E ｛ e ∣ Σ[ d ∈ D ] ((d , e) ∈ S')｝ ≡⟨⟩
      snd (⋀ S') ∎
      where open ≤E-reasoning
    snd (f2r-mono-join-closed S' S'⊆) =
      begin-≤
      b (snd (⋀ S')) ≡⟨⟩
      b (⋀E ｛ e ∣ Σ[ d ∈ D ] ((d , e) ∈ S')｝) ≤⟨ mono-meet≤meet-mono E-is-cmlat D-is-cmlat b-is-mono ｛ e ∣ Σ[ d ∈ D ] ((d , e) ∈ S')｝ ⟩
      ⋀D (fimage b ｛ e ∣ Σ[ d ∈ D ] ((d , e) ∈ S')｝) ≡⟨⟩
      ⋀D ｛ d ∣ Σ[ e ∈ E ] ((Σ[ d' ∈ D ](S' (d' , e))) × b e ≡ d)｝ ≈⟨ D.bigmeet-≡-≤ b _ ⟩
      ⋀D ｛ d ∣ Σ[ e ∈ E ] ((Σ[ d' ∈ D ](S' (d' , e))) × b e ≤D d)｝ ≤⟨ D.bigmeet-monotone (\ { {d} (e , de∈S') → e , ((d , de∈S') , snd (S'⊆ de∈S')) }) ⟩
      ⋀D ｛ d ∣ Σ[ e ∈ E ] ((d , e) ∈ S')｝ ≡⟨⟩
      fst (⋀ S') ∎
      where open ≤D-reasoning


  module _ (R : subset (D × E)) where
    r2f-R-is-monotone-pair : is-monotone-pair D.≤-pre E.≤-pre (r2f R)
    fst r2f-R-is-monotone-pair {d} {d'} d≤d' =
      begin-≤
      fst (r2f R) d ≤⟨ E.bigmeet-monotone (\ { {e} (d'' , d'≤d'' , Rd''e) → d'' , (d≤d' ⟨ D.≤-trans ⟩ d'≤d'') , Rd''e }) ⟩
      fst (r2f R) d' ∎
      where open ≤E-reasoning
    snd r2f-R-is-monotone-pair {e} {e'} e≤e' =
      begin-≤
      snd (r2f R) e ≤⟨ D.bigmeet-monotone (\ { {d} (e'' , e'≤e'' , Rde'') → e'' , (e≤e' ⟨ E.≤-trans ⟩ e'≤e'') , Rde'' }) ⟩
      snd (r2f R) e' ∎
      where open ≤D-reasoning

  r2f-is-antitone : is-antitone ⊆-is-preorder ≤fp-is-preorder r2f
  fst (r2f-is-antitone {r} {r'} r⊆r') de = E.bigmeet-monotone \{ (d , d≤d , dre) → d , d≤d , r⊆r' dre}
  snd (r2f-is-antitone {r} {r'} r⊆r') de = D.bigmeet-monotone \{ (e , e≤e , dre) → e , e≤e , r⊆r' dre}

  f2r-is-antitone : is-antitone ≤fp-is-preorder ⊆-is-preorder f2r
  f2r-is-antitone (f'≤f , b'≤b) {d , e} (fd≤e , be≤d) = (f'≤f d ⟨ E.≤-trans ⟩ fd≤e) , (b'≤b e ⟨ D.≤-trans ⟩ be≤d)

  pre-fp = pre (func-pair D E) _≤fp_ ≤fp-is-preorder
  pre-mfp : preordered-set
  pre-mfp = pre (monotone-func-pair D.≤-pre E.≤-pre) _≤mfp_ ≤mfp-is-preorder
  pre-r : preordered-set
  pre-r = pre (subset (D × E)) _⊆_ ⊆-is-preorder

  f2r-anti : antitone-func pre-mfp pre-r
  monotone-func.func f2r-anti (mfp funcp funcp-is-monotone) = f2r funcp
  monotone-func.property f2r-anti = f2r-is-antitone

  r2f-anti : antitone-func pre-r pre-mfp
  monotone-func.func r2f-anti r = mfp (r2f r) (r2f-R-is-monotone-pair r)
  monotone-func.property r2f-anti = r2f-is-antitone

  f2r-r2f-mono = pre-comp-anti f2r-anti r2f-anti
  open monotone-func f2r-r2f-mono renaming (property to f2r-r2f-is-monotone)
  r2f-f2r-mono = pre-comp-anti r2f-anti f2r-anti
  open monotone-func r2f-f2r-mono renaming (property to r2f-f2r-is-monotone)

  module _
    {R : subset (D × E)}
    (R-meet-closed : is-meet-closed-subset D×E-is-cmlat R)
    (R-welldefined : is-welldefined-subset ≤-pre R)
    where
    fst-boundedmeet→butterfly : ∀ d₀ e₀ → (⋀D \ d → ∃ \ e → e₀ ≤E e × R (d , e)) ≤D d₀ → (∃ \ d' → ∃ \ e → d' ≤D d₀ × e₀ ≤E e × R (d' , e))
    fst-boundedmeet→butterfly d₀ e₀ ≤d₀ =
      (⋀D (\ d → ∃ \ e → e₀ ≤E e × R (d , e))) , (( ⋀E (λ e → ∃ (\ d → (e₀ ≤E e) × R (d , e)))  ) , (≤d₀ , ((E.bigmeet-greatest _ _ (λ{ e'' (d'' , e₀≤ , r)  → e₀≤})) , R-meet-closed ( (\{(d , e) → (e₀ ≤E e) × R (d , e)}))  \{ (_ , dRe) → dRe})))

    snd-boundedmeet→butterfly : ∀ d₀ e₀ → (⋀E \ e → ∃ \ d → d₀ ≤D d × R (d , e)) ≤E e₀ → (∃ \ e' → ∃ \ d → e' ≤E e₀ × d₀ ≤D d × R (d , e'))
    snd-boundedmeet→butterfly d₀ e₀ ≤e₀ =
      ((⋀E \ e → ∃ \ d → d₀ ≤D d × R (d , e))) , (( ⋀D (λ d → ∃ (λ e → (d₀ ≤D d) × R (d , e)))  ) , (≤e₀ , ((D.bigmeet-greatest _ _ (λ{ d'' (e'' , d₀≤ , r)  → d₀≤})) , R-meet-closed ( (\{(d , e) → (d₀ ≤D d) × R (d , e)}))  \{ (_ , dRe) → dRe})))

  module _
    (R : subset (D × E))
    (f : D → E) (b : E → D) where

    right-transpose : (f , b) ≤fp r2f R → R ⊆ f2r (f , b)
    fst (right-transpose (f≤ , b≤) {d , e} dRe) =
      begin-≤
      f d ≤⟨ f≤ d ⟩
      fst (r2f R) d ≤⟨ E.bigmeet-lowerbound _ _ (d , D.≤-refl d , dRe) ⟩
      e ∎
        where open ≤E-reasoning
    snd (right-transpose (f≤ , b≤) {d , e} dRe) =
      begin-≤
      b e ≤⟨ b≤ e ⟩
      snd (r2f R) e ≤⟨ D.bigmeet-lowerbound _ _ (e , E.≤-refl e , dRe) ⟩
      d ∎
        where open ≤D-reasoning
    module _
      (f-is-mono : is-monotone D.≤-pre E.≤-pre f) (b-is-mono : is-monotone E.≤-pre D.≤-pre b) where

      f-is-wd : f ∈ is-welldefined D.≤-pre E.≤-pre
      f-is-wd = monotone2welldefined D.≤-pre E.≤-pre f-is-mono
      b-is-wd : b ∈ is-welldefined E.≤-pre D.≤-pre
      b-is-wd = monotone2welldefined E.≤-pre D.≤-pre b-is-mono

      left-transpose : R ⊆ f2r (f , b) → (f , b) ≤fp r2f R
      fst (left-transpose R⊆f2r[fb]) d₀ =
        begin-≤
        f d₀                                         ≈⟨ f-is-wd (D.bigmeet-up-iso d₀) ⟩
        f (⋀D (D.↑ d₀))                              ≤⟨ mono-meet≤meet-mono D-is-cmlat E-is-cmlat f-is-mono (D.↑ d₀) ⟩
        ⋀E (fimage f (D.↑ d₀))                       ≈⟨ E.bigmeet-≡-≤ f _ ⟩
        ⋀E ｛ e ∣ Σ[ d ∈ D ] (d₀ ≤D d × f d ≤E e) ｝  ≤⟨ E.bigmeet-monotone (\ { (e' , e₀≤e' , d'Re') → e' , e₀≤e' , fst (R⊆f2r[fb] d'Re')}) ⟩
        ⋀E ｛ e ∣ Σ[ d ∈ D ] (d₀ ≤D d × (d , e) ∈ R) ｝  ≡⟨⟩
        fst (r2f R) d₀ ∎
          where open ≤E-reasoning
      snd (left-transpose R⊆f2r[fb]) e₀ =
        begin-≤
        b e₀                                         ≈⟨ b-is-wd (E.bigmeet-up-iso e₀) ⟩
        b (⋀E (E.↑ e₀))                              ≤⟨ mono-meet≤meet-mono E-is-cmlat D-is-cmlat b-is-mono (E.↑ e₀) ⟩
        ⋀D (fimage b (E.↑ e₀))                       ≈⟨ D.bigmeet-≡-≤ b _ ⟩
        ⋀D ｛ d ∣ Σ[ e ∈ E ] (e₀ ≤E e × b e ≤D d) ｝  ≤⟨ D.bigmeet-monotone (\ { (e' , e₀≤e' , d'Re') → e' , e₀≤e' , snd (R⊆f2r[fb] d'Re')}) ⟩
        ⋀D ｛ d ∣ Σ[ e ∈ E ] (e₀ ≤E e × (d , e) ∈ R) ｝ ≡⟨⟩
        snd (r2f R) e₀ ∎
          where open ≤D-reasoning



      -- R ⊆ f2r (f , b) ↔ (f , b) ≤fp r2f R
      -- forward galois-connection = left-transpose
      -- backward galois-connection = right-transpose

      unit : ((f , b) ≤fp r2f R) → (f , b) ≤fp r2f R
      unit = left-transpose ∘ right-transpose

      counit : R ⊆ f2r (f , b) → R ⊆ f2r (f , b)
      counit = right-transpose ∘ left-transpose

  module unit (R : subset (D × E)) where


    f2r-r2f-increasing : R ⊆ f2r (r2f R)
    fst (f2r-r2f-increasing {d₀ , e₀} d₀Re₀) =
      begin-≤
      fst (r2f R) d₀                                     ≡⟨⟩
      ⋀E ｛ e ∣ Σ[ d ∈ D ] (d₀ ≤D d × (d , e) ∈ R) ｝     ≤⟨ E.bigmeet-monotone (\ { (d , (d₀≤d , e₀≤e) , dRe) → d , d₀≤d , dRe }) ⟩
      snd (⋀ (↑ (d₀ , e₀) ∩ ｛ de ∣ de ∈ R ｝)) ≤⟨ snd (backward (bigmeet-up-intersection-iso (d₀ , e₀) (\de → de ∈ R) d₀Re₀)) ⟩
      e₀ ∎
      where open ≤E-reasoning
    snd (f2r-r2f-increasing {d₀ , e₀} d₀Re₀) =
      begin-≤
      snd (r2f R) e₀                                    ≡⟨⟩
      ⋀D ｛ d ∣ Σ[ e ∈ E ] (e₀ ≤E e × (d , e) ∈ R) ｝     ≤⟨ D.bigmeet-monotone (\ { (e , (d₀≤d , e₀≤e) , dRe) → e , e₀≤e , dRe }) ⟩
      fst (⋀ (↑ (d₀ , e₀) ∩ ｛ de ∣ de ∈ R ｝)) ≤⟨ fst (backward (bigmeet-up-intersection-iso (d₀ , e₀) (\de → de ∈ R) d₀Re₀)) ⟩
      d₀ ∎
      where open ≤D-reasoning

    is-butterfly : pred (subset (D × E))
    is-butterfly R = ∀ d₀ e₀ {d e d' e'}
      → d' ≤D d₀ → d₀ ≤D d
      → e' ≤E e₀ → e₀ ≤E e
      → (d' , e) ∈ R → (d , e') ∈ R → (d₀ , e₀) ∈ R

    f2r-r2f-butterfly : f2r (r2f R) ⊆ R → is-butterfly R
    f2r-r2f-butterfly r2rR⊆R d₀ e₀ {d} {e} {d'} {e'} d'≤d₀ d₀≤d e'≤e₀ e₀≤e d'Re dRe' =  r2rR⊆R (⋀E≤e₀ , ⋀D≤d₀)
      where
      ⋀E≤e₀ : fst (r2f R) d₀ ≤E e₀
      ⋀E≤e₀ =
        begin-≤
        fst (r2f R) d₀ ≡⟨⟩
        ⋀E ｛ e ∣ Σ[ d ∈ D ] (d₀ ≤D d × (d , e) ∈ R) ｝ ≤⟨ E.bigmeet-lowerbound _ _ (d , d₀≤d , dRe') ⟩
        e' ≤⟨ e'≤e₀ ⟩
        e₀ ∎
        where open ≤E-reasoning
      ⋀D≤d₀ : snd (r2f R) e₀ ≤D d₀
      ⋀D≤d₀ =
        begin-≤
        snd (r2f R) e₀ ≡⟨⟩
        ⋀D ｛ d ∣ Σ[ e ∈ E ] (e₀ ≤E e × (d , e) ∈ R) ｝ ≤⟨  D.bigmeet-lowerbound _ _ (e , e₀≤e , d'Re) ⟩
        d' ≤⟨ d'≤d₀ ⟩
        d₀ ∎
        where open ≤D-reasoning

    module _ where
      R' = f2r (r2f R)
      R'-meet-closed : is-meet-closed-subset D×E-is-cmlat (f2r (r2f R))
      R'-meet-closed = f2r-mono-join-closed (fst (r2f-R-is-monotone-pair R)) (snd (r2f-R-is-monotone-pair R))

    module _ (R-meet-closed : is-meet-closed-subset D×E-is-cmlat R) where

      butterfly-f2r-r2f : is-butterfly R → f2r (r2f R) ⊆ R
      butterfly-f2r-r2f R-butterfly {(d₀ , e₀)} d₀R'e₀ =
        R-butterfly d₀ e₀
          {d =  ⋀D (λ d → ∃ (λ e → (d₀ ≤D d) × (d , e) ∈ R))}
          {e =  ⋀E (λ e → ∃ (λ d → (e₀ ≤E e) × (d , e) ∈ R))}
          {d' = ⋀D ｛ d ∣ ∃ (\ e → e₀ ≤E e × (d , e) ∈ R) ｝ }
          {e' = ⋀E ｛ e ∣ ∃ (\ d → d₀ ≤D d × (d , e) ∈ R) ｝ }
          (snd d₀R'e₀) (D.bigmeet-greatest _ _ \ _ → fst ∘ snd)
          (fst d₀R'e₀) (E.bigmeet-greatest _ _ \ _ → fst ∘ snd)
          (R-meet-closed _ snd)
          (R-meet-closed _ snd)

  module counit (f : D → E) (b : E → D)
    (f-mono : is-monotone D.≤-pre E.≤-pre f)
    (b-mono : is-monotone E.≤-pre D.≤-pre b) where

    r2f-f2r-increasing : (f , b) ≤fp r2f (f2r (f , b))
    r2f-f2r-increasing = left-transpose (f2r (f , b)) f b f-mono b-mono id

    private
      fb = f , b
      fb' = r2f (f2r fb)

      a : D → D
      a d₀ = ⋀D ｛ d ∣ Σ _ (\ e → d₀ ≤D d × f d ≤E e × b e ≤D d) ｝

      p : E → E
      p e₀ = ⋀E ｛ e ∣ Σ _ (\ d → e₀ ≤E e × f d ≤E e × b e ≤D d) ｝

      id≤a : ∀ d₀ → d₀ ≤D a d₀
      id≤a d₀ = D.bigmeet-greatest _ _ (\ { d (e , d₀≤d , fd≤e , be≤d) → d₀≤d})

      id≤p : ∀ e₀ → e₀ ≤E p e₀
      id≤p e₀ = E.bigmeet-greatest _ _ (\ { e (d , e₀≤e , fd≤e , be≤d) → e₀≤e})

      bf≤a : ∀ d₀ →  b (f d₀) ≤D a d₀
      bf≤a d₀ =
        begin-≤
        b (f d₀) ≤⟨ D.bigmeet-greatest _ _ (\{ d (e , d₀≤d , fd≤e , be≤d) → b-mono (f-mono d₀≤d) ⟨ D.≤-trans ⟩ b-mono fd≤e ⟨ D.≤-trans ⟩ be≤d }) ⟩
        ⋀D (\ d → ∃ \ e → d₀ ≤D d × f d ≤E e × b e ≤D d) ≡⟨⟩
        a d₀ ∎
        where open ≤D-reasoning

      fb≤p : ∀ e₀ →  f (b e₀) ≤E p e₀
      fb≤p e₀ =
        begin-≤
        f (b e₀) ≤⟨ E.bigmeet-greatest _ _ (\{ e (d , e₀≤e , fd≤e , be≤d) → f-mono (b-mono e₀≤e) ⟨ E.≤-trans ⟩ f-mono be≤d ⟨ E.≤-trans ⟩ fd≤e }) ⟩
        ⋀E (\ e → ∃ \ d → e₀ ≤E e × f d ≤E e × b e ≤D d) ≡⟨⟩
        p e₀ ∎
        where open ≤E-reasoning



    private
      f* : D → E
      f* d = f (b (f d) ∨D d)
      b* : E → D
      b* e = b (f (b e) ∨E e)

      fb* : (D → E) × (E → D)
      fb* = f* , b*

    r2f-f2r→fix : fb' ≤fp fb → fb* ≤fp fb
    r2f-f2r→fix ≤fb = fb*≤ ⟨ ≤fp-trans ⟩ ≤fb
      where
        open is-preorder ≤fp-is-preorder renaming (rel-is-transitive to ≤fp-trans)
        fb*≤ : fb* ≤fp fb'
        fst fb*≤ d =
          begin-≤
          fst fb* d ≤⟨ mono-meet≤meet-mono D-is-cmlat E-is-cmlat f-mono _ ⟩
          ⋀E ((fimage f) (is-upperbound _≤D_ ｛ b (f d) , d ｝₂ )) ≡⟨⟩
          ⋀E  (\ e → Σ D (\ d' → (d' ∈ is-upperbound _≤D_ ｛ b (f d) , d ｝₂) × (f d' ≡ e))) ≈⟨ E.bigmeet-≡-≤ f _ ⟩
          ⋀E  (\ e → Σ D (\ d' → (d' ∈ is-upperbound _≤D_ ｛ b (f d) , d ｝₂) × (f d' ≤E e))) ≤⟨ E.bigmeet-monotone (\ {(d' , d≤d' , fd'≤e , be≤d' ) → d' , bin-upperbound→subset-upperbound _≤D_ ((b-mono (f-mono d≤d') ⟨ D.≤-trans ⟩ b-mono fd'≤e ⟨ D.≤-trans ⟩ be≤d') , d≤d') , fd'≤e }) ⟩
          ⋀E (\ e → Σ D (\ d' → d ≤D d' × f d' ≤E e × b e ≤D d')) ≡⟨⟩
          fst fb' d ∎
          where
            open ≤E-reasoning
        snd fb*≤ e =
          begin-≤
          snd fb* e ≤⟨ mono-meet≤meet-mono E-is-cmlat D-is-cmlat b-mono _ ⟩
          ⋀D ((fimage b) (is-upperbound _≤E_ ｛ f (b e) , e ｝₂ )) ≡⟨⟩
          ⋀D  (\ d → Σ E (\ e' → (e' ∈ is-upperbound _≤E_ ｛ f (b e) , e ｝₂) × (b e' ≡ d))) ≈⟨ D.bigmeet-≡-≤ b _ ⟩
          ⋀D  (\ d → Σ E (\ e' → (e' ∈ is-upperbound _≤E_ ｛ f (b e) , e ｝₂) × (b e' ≤D d))) ≤⟨ D.bigmeet-monotone (\ {(e' , e≤e' , fd≤e' , be'≤d) → e' , bin-upperbound→subset-upperbound _≤E_ ((f-mono (b-mono e≤e') ⟨ E.≤-trans ⟩ f-mono be'≤d ⟨ E.≤-trans ⟩ fd≤e') , e≤e') , be'≤d }) ⟩
          ⋀D (\ d → Σ E (\ e' → e ≤E e' × f d ≤E e' × b e' ≤D d)) ≡⟨⟩
          snd fb' e ∎
          where
            open ≤D-reasoning

    fix→r2f-f2r : fb* ≤fp fb → fb' ≤fp fb
    fst (fix→r2f-f2r fb*≤fb) d =
      begin-≤
      fst fb' d ≡⟨⟩
      ⋀E ｛ e ∣ Σ[ d' ∈ D ] (d ≤D d' × f d' ≤E e × b e ≤D d') ｝  ≤⟨ E.bigmeet-lowerbound _ _ ((b (f d) ∨D d) , (D⋁.bigjoin-upperbound _ _ (right ≡.refl) , fst fb*≤fb d , D⋁.bigjoin-upperbound _ _ (left ≡.refl))) ⟩
      f d ≡⟨⟩
      fst fb d ∎
      where open ≤E-reasoning
            module D⋁ = is-complete-join-semilattice D-is-cjlat

    snd (fix→r2f-f2r fb*≤fb) e =
      begin-≤
      snd fb' e ≡⟨⟩
      ⋀D ｛ d ∣ Σ[ e' ∈ E ] (e ≤E e' × f d ≤E e' × b e' ≤D d) ｝  ≤⟨ D.bigmeet-lowerbound _ _ ((f (b e) ∨E e) , (E⋁.bigjoin-upperbound _ _ (right ≡.refl) , E⋁.bigjoin-upperbound _ _ (left ≡.refl) , snd fb*≤fb e)) ⟩
      b e ≡⟨⟩
      snd fb e ∎
      where open ≤D-reasoning
            module E⋁ = is-complete-join-semilattice E-is-cjlat

```

- Category of subsets on complete lattice X:
  - objects: subsets of X, s∈𝓟X, s'∈𝓟X, ...
  - morphisms: inclusion s ⊆ s' fp

- Category of endo functions on complete lattice X
  - objects: endo monotone fucntions e, e', e'' : X → X
  - morphisms: pointwise order relation e ≤ e'



```txt
            s ⊆ f2s f
            =========
            s2f s ≥ f
```

```agda
module _ (X : Set) where
  endo = X → X

module _ (X : preordered-set) where
  monotone-endo = monotone-func X X

module endo-function (X : _) (_≤X_ : _) (⋀X : _) (X-is-cmlat : _) where
  private
    X-cmlat = cmlat X _≤X_ ⋀X X-is-cmlat
    X-pre = cmlat→pre X-cmlat

    module X = is-complete-meet-semilattice X-is-cmlat
      renaming (rel-is-preorder to ≤-pre ; op-is-bigmeet to ⋀-bigmeet ; rel-is-reflexive to ≤-refl ; rel-is-transitive to ≤-trans)

  X-cjlat = cmlat→cjlat X-cmlat
  open complete-join-semilattice X-cjlat
    renaming (operation to ⋁X ; property to X-is-cjlat)

  ⊤X = ⋀X ∅

  ⊥X = ⋁X ∅

  _∨X_ = \ x y → ⋁X ｛ x , y ｝₂

  s2f : subset X → (X → X)
  s2f s x₀ = ⋀X ｛ x ∣ x₀ ≤X x × x ∈ s ｝

  s2f-s-is-monotone : ∀ s → is-monotone X.≤-pre X.≤-pre (s2f s)
  s2f-s-is-monotone s x≤x' = X.bigmeet-monotone \ { (x'≤x'' , x''∈s) → X.≤-trans x≤x' x'≤x'' , x''∈s }

  f2s : endo X → subset X
  f2s f x = f x ≤X x

  _≤f_ : rel (endo X) (endo X)
  f ≤f f' = ∀ x → f x ≤X f' x

  module _ where
    open monotone-func
    open preordered-set
    _≤mf_ : rel (monotone-endo X-pre) (monotone-endo X-pre)
    f ≤mf f' = func f ≤f func f'

    open is-preorder
    ≤f-is-preorder : is-preorder _≤f_
    (rel-is-reflexive ≤f-is-preorder f) d = X.≤-refl (f d)
    (rel-is-transitive ≤f-is-preorder f≤f' f'≤f'') d = X.≤-trans (f≤f' d) (f'≤f'' d)

    ≤mf-is-preorder : is-preorder _≤mf_
    rel-is-reflexive ≤mf-is-preorder d = (rel-is-reflexive ≤f-is-preorder (func d))
    rel-is-transitive ≤mf-is-preorder f≤f' f'≤f'' = rel-is-transitive ≤f-is-preorder f≤f' f'≤f''

    _≈f_ : rel (X → X) (X → X)
    _≈f_ = iso-pair _≤f_

    _≈mf_ : rel (monotone-endo X-pre) (monotone-endo X-pre)
    _≈mf_ = iso-pair _≤mf_

    pre-s = pre (subset X) _⊆_ ⊆-is-preorder
    pre-mf = pre (monotone-endo X-pre) _≤mf_ ≤mf-is-preorder

    s2f-antitone : antitone-func pre-s pre-mf
    func s2f-antitone s = mono (s2f s) (s2f-s-is-monotone s)
    property s2f-antitone {s} {s'} s⊆s' x₀ = X.bigmeet-monotone \{ (x₀≤x , x∈s) → x₀≤x , s⊆s' x∈s}

    f2s-antitone : antitone-func pre-mf pre-s
    func f2s-antitone f = f2s (func f)
    property f2s-antitone {f} {f'} f≤f' {x} x∈f2sf' = X.≤-trans (f≤f' x) x∈f2sf'


  module _ where
    f2s-s2f-antitone-galois-connection : is-antitone-galois-connection f2s-antitone s2f-antitone
    f2s-s2f-antitone-galois-connection s f-mono =
      begin-≈
      flip _⊆_ (f2sm f-mono) s ≡⟨⟩
      (∀ {x : X} → s x → f x ≤X x) ≈⟨ hidden↔explicit _ ⟩
      (∀ x₀ → x₀ ∈ s → f x₀ ≤X x₀) ≈⟨ X.bigmeet-mono-equivalence s (f-is-mono)  ⟩
      (∀ x₀ → f x₀ ≤X ⋀X (\ x → x₀ ≤X x × x ∈ s)) ≡⟨⟩
      f ≤f s2f s ∎
      where open reasoning _ (→-is-preorder)
            open monotone-func f2s-antitone renaming (func to f2sm ; property to f2sm-is-antitone)
            open monotone-func f-mono renaming (func to f ; property to f-is-mono)

```

```
module _ (D-cmlat E-cmlat : complete-meet-semilattice) where
  module D-cmlat = complete-meet-semilattice D-cmlat
  module E-cmlat = complete-meet-semilattice E-cmlat
  D-is-pre = is-complete-meet-semilattice.rel-is-preorder D-cmlat.property
  E-is-pre = is-complete-meet-semilattice.rel-is-preorder E-cmlat.property

  open transfer-function-pair D-cmlat.carrier D-cmlat.relation D-cmlat.operation D-cmlat.property E-cmlat.carrier E-cmlat.relation E-cmlat.operation E-cmlat.property

  f2r-r2f-antitone-galois-connection : is-antitone-galois-connection f2r-anti r2f-anti
  forward (f2r-r2f-antitone-galois-connection r (mfp (f , b) (f-mono , b-mono))) = left-transpose r f b f-mono b-mono
  backward (f2r-r2f-antitone-galois-connection r (mfp (f , b) _)) = right-transpose r f b

  rel-mfp-connected : galois-connection (preordered-set.opposite pre-r) pre-mfp
  galois-connection.left-adjoint rel-mfp-connected = f2r-anti
  galois-connection.right-adjoint rel-mfp-connected = monotone-func.dual r2f-anti
  galois-connection.left-right-is-galois-connection rel-mfp-connected = f2r-r2f-antitone-galois-connection

  module D×E-cmlat = complete-meet-semilattice (D-cmlat ×-cmlat E-cmlat)
  D×E-is-pre = is-complete-meet-semilattice.rel-is-preorder D×E-cmlat.property
  open endo-function D×E-cmlat.carrier D×E-cmlat.relation D×E-cmlat.operation D×E-cmlat.property

  rel-mf-connected : galois-connection (preordered-set.opposite pre-r) pre-mf
  galois-connection.left-adjoint rel-mf-connected = f2s-antitone
  galois-connection.right-adjoint rel-mf-connected = monotone-func.dual s2f-antitone
  galois-connection.left-right-is-galois-connection rel-mf-connected = f2s-s2f-antitone-galois-connection

  f2fp : endo (D-cmlat.carrier × E-cmlat.carrier) → func-pair (D-cmlat.carrier) (E-cmlat.carrier)
  fst (f2fp f) d = snd (f (d , E-cmlat.operation U))
  snd (f2fp f) e = fst (f (D-cmlat.operation U , e))

  mf2mfp : monotone-endo (cmlat→pre (D-cmlat ×-cmlat E-cmlat)) → monotone-func-pair D-is-pre E-is-pre
  fst (monotone-func-pair.funcp (mf2mfp (mono h h-is-mono))) = fst (f2fp h)
  snd (monotone-func-pair.funcp (mf2mfp (mono h h-is-mono))) = snd (f2fp h)
  fst (monotone-func-pair.funcp-is-monotone (mf2mfp (mono h h-is-mono))) d≤d' = snd (h-is-mono (d≤d' , is-preorder.rel-is-reflexive E-is-pre _))
  snd (monotone-func-pair.funcp-is-monotone (mf2mfp (mono h h-is-mono))) e≤e' = fst (h-is-mono (is-preorder.rel-is-reflexive D-is-pre _ , e≤e'))

  fp2f : func-pair (D-cmlat.carrier) (E-cmlat.carrier) → endo (D-cmlat.carrier × E-cmlat.carrier)
  fp2f (f , b) (d , e) = (b e , f d)

  mfp2mf : monotone-func-pair D-is-pre E-is-pre → monotone-endo (cmlat→pre (D-cmlat ×-cmlat E-cmlat))
  monotone-func.func (mfp2mf (mfp (f , b) (f-mono , b-mono))) (d , e) = fp2f (f , b) (d , e)
  monotone-func.property (mfp2mf (mfp (f , b) (f-mono , b-mono))) (d≤d' , e≤e') = b-mono e≤e' , f-mono d≤d'

  mf-mfp-connected : galois-connection pre-mf pre-mfp
  galois-connection.left-adjoint mf-mfp-connected = mono mfp2mf (\{ (f-mono , b-mono) (d , e) → b-mono e , f-mono d})
  galois-connection.right-adjoint mf-mfp-connected = mono mf2mfp (\ f≤f' → (\ d → snd (f≤f' (d , E-cmlat.operation U))) , (\ e → fst (f≤f' (D-cmlat.operation U , e))))
  forward (galois-connection.left-right-is-galois-connection mf-mfp-connected (mono h h-mono) (mfp (f , b) (f-mono , b-mono))) mfp2mf[fb]≤h
    = f≤snd[h[id,⊥]] , b≤fst[h[⊥,id]]
    where
    f≤snd[h[id,⊥]] : ∀ d → E-cmlat.relation (f d) (snd (h (d , _)))
    f≤snd[h[id,⊥]] d = snd (mfp2mf[fb]≤h (d , E-cmlat.operation U))
    b≤fst[h[⊥,id]] : ∀ e → D-cmlat.relation (b e) (fst (h (_ , e)))
    b≤fst[h[⊥,id]] e = fst (mfp2mf[fb]≤h (D-cmlat.operation U , e))

  backward (galois-connection.left-right-is-galois-connection mf-mfp-connected (mono h h-mono) (mfp (f , b) (f-mono , b-mono))) (f≤snd[mf2mfp[h]] , b≤fst[mf2mfp[h]])
    = fp2f[f,b]≤h
    where
    fp2f[f,b]≤h : ∀ p → D×E-cmlat.relation (fp2f (f , b) p) (h p)
    fst (fp2f[f,b]≤h p) = begin-≤ fst (fp2f (f , b) p) ≤⟨  b≤fst[mf2mfp[h]] (snd p) ⟩ fst (h (D-cmlat.operation U , snd p)) ≤⟨ fst (h-mono ((is-complete-meet-semilattice.bigmeet-lowerbound D-cmlat.property _ _ _ ) , (is-preorder.rel-is-reflexive E-is-pre _))) ⟩ fst (h p) ∎
      where
      open reasoning _ D-is-pre
    snd (fp2f[f,b]≤h p) = begin-≤ snd (fp2f (f , b) p) ≤⟨  f≤snd[mf2mfp[h]] (fst p) ⟩ snd (h (fst p , E-cmlat.operation U)) ≤⟨ snd (h-mono ((is-preorder.rel-is-reflexive D-is-pre _) , (is-complete-meet-semilattice.bigmeet-lowerbound E-cmlat.property _ _ _ ))) ⟩ snd (h p) ∎
      where
      open reasoning _ E-is-pre

  rel-mf-mfp-connected = comp-galois-connection rel-mf-connected mf-mfp-connected

```
* fixed-points of galois-connection

Let X is a poset,

```txt

                         L
                      ------->
            (𝒫(C),⊆)    ⊥       X
                      <-------
               | ↑       R      | ↑
               | |              | |
               |⊣|              |⊢|
               ↓ J        α     ↓ J
                      ------->
        (𝒫(C),⊆)_fix     ≅     X_fix
                      <-------


                         L
                      ------->            ---------->
            (𝒫(A × B),⊆)    ⊥   A×B→A×B                 A→B × B→ A
                      <-------            <-----------
               | ↑       R      | ↑                      | |
               | |              | |                      | |
               |⊣|              |⊢|                      | |
               ↓ J        α     ↓ J                      | |
                      ------->                           | |
        (𝒫(A×B),⊆)_fix   ≅    A×B→A×B_fix               | |
              | |     <-------                           | |
              | |                                        | |
              | |                                        | |
              | |                                        | |
              | |                                        | |
              | |       ------------------------------   | |
        (𝒫(A×B),⊆)_fix₂               ≅                  A→B × B→A (f (id ∧ b ⊥) ≥ f
                        ------------------------------

```

If we have a pair of adjuncts L, R on the top then we have
a full sub category (𝒫(C),⊆)_fix of (𝒫(C),⊆) whose objects are c with an isomorphism c ≃ηc RL(c)
and a full sub category X_fix of X whose objects are x with an isomorphism LR(x) ≃εx x
https://ncatlab.org/nlab/show/fixed+point+of+an+adjunction

X → Y → Z

p2f (f2p f ⋈ f2p g) = f ⊗ g = p2f (f2p (f * g))
p2f (f2p (f * (g * h))) = f ⊗ g ⊗ h

```agda
module fixed-points-of-galois-connection {C D : preordered-set} (C-D-connected : galois-connection C D) where
  open galois-connection C-D-connected
  open is-preorder
  open monotone-func renaming (property to monotonicity)
  private
    module C = preordered-set C renaming (relation to _≤_ ; property to is-pre ; equiv to _≅_)
    module D = preordered-set D renaming (relation to _≤_ ; property to is-pre ; equiv to _≅_)

  C*-carrier = Σ _ \ c → c C.≤ lr c
  C*-is-pre : is-preorder {C*-carrier} (map-rel fst fst C._≤_)
  rel-is-reflexive C*-is-pre _ = rel-is-reflexive C.is-pre _
  rel-is-transitive C*-is-pre =  rel-is-transitive C.is-pre

  C* : preordered-set
  C* = pre C*-carrier (map-rel fst fst C._≤_) C*-is-pre

  D*-carrier = Σ _ \ d → rl d D.≤ d
  D*-is-pre : is-preorder {D*-carrier} (map-rel fst fst D._≤_)
  rel-is-reflexive D*-is-pre _ = rel-is-reflexive D.is-pre _
  rel-is-transitive D*-is-pre =  rel-is-transitive D.is-pre

  D* : preordered-set
  D* = pre D*-carrier (map-rel fst fst D._≤_) D*-is-pre

  {-

    D ←L C
    ↓L   ↑L
    D* ≅ C*
  -}

  -- inclusion C* → C
  C*2C : monotone-func C* C
  func C*2C = fst
  monotonicity C*2C = id

  C2C* : monotone-func C C*
  func C2C* c = lr c , backward (lr-idempotent (func right-adjoint c))
  monotonicity C2C* c≤c' = lr-mono c≤c'

  D*2D : monotone-func D* D
  func D*2D = fst
  monotonicity D*2D = id

  D2D* : monotone-func D D*
  func D2D* d = rl d , forward (rl-idempotent (func left-adjoint d))
  monotonicity D2D* d≤d' = rl-mono d≤d'

  C*2C-C2C*-is-galois-connection : is-galois-connection C*2C C2C*
  forward (C*2C-C2C*-is-galois-connection c (c* , c*≤lrc*)) c*≤c =
    begin-≤
    c* ≤⟨ c*≤lrc* ⟩
    lr c* ≤⟨ lr-mono c*≤c ⟩
    lr c ∎
    where
      open reasoning _ C.is-pre
  backward (C*2C-C2C*-is-galois-connection c (c* , c*≤lrc*)) c*≤lrc =
    begin-≤
    c* ≤⟨ c*≤lrc ⟩
    lr c ≤⟨ lr-decreasing c ⟩
    c ∎
    where
      open reasoning _ C.is-pre

  C-C*-connected : galois-connection C C*
  C-C*-connected = gal-conn C*2C C2C* C*2C-C2C*-is-galois-connection

  D2D*-D*2D-is-galois-connection : is-galois-connection D2D* D*2D
  forward (D2D*-D*2D-is-galois-connection (d* , rld*≤d*) d) rld≤d* =
    begin-≤
    d ≤⟨ rl-increasing d ⟩
    rl d ≤⟨ rld≤d* ⟩
    d* ∎
    where
      open reasoning _ D.is-pre

  backward (D2D*-D*2D-is-galois-connection (d* , rld*≤d*) d) d≤d* =
    begin-≤
    rl d ≤⟨ rl-mono d≤d* ⟩
    rl d* ≤⟨ rld*≤d* ⟩
    d* ∎
    where
      open reasoning _ D.is-pre

  C*2D* : monotone-func C* D*
  func C*2D* c* = (func D2D* ∘ func right-adjoint ∘ func C*2C) c*
  monotonicity C*2D* c*≤c*' = (monotonicity D2D* ∘ monotonicity right-adjoint) c*≤c*' -- c*≤c*' is defined by relation on projecion (snd c* is irrelevant) applying monotonicity C*2C is valid but make it ambiguous

  D*2C* : monotone-func D* C*
  func D*2C* d* = (func C2C* ∘ func left-adjoint ∘ func D*2D) d*
  monotonicity D*2C* d*≤d*' = (monotonicity C2C* ∘ monotonicity left-adjoint) d*≤d*'

  private
    rl-welldefined : is-welldefined D.is-pre D.is-pre rl
    rl-welldefined = monotone2welldefined D.is-pre D.is-pre rl-mono
    rld≤d→rld≅d : ∀ {d} → rl d D.≤ d → rl d D.≅ d
    forward (rld≤d→rld≅d ≤) = ≤
    backward (rld≤d→rld≅d ≤) = rl-increasing _
    rld≤d→rlrlrld≅d : ∀ {d} → rl d D.≤ d → rl (rl (rl d)) D.≅ d
    rld≤d→rlrlrld≅d {d} rld≤d = begin-≈
      rl (rl (rl d)) ≈⟨ rl-welldefined (rl-welldefined rld≅d) ⟩
      rl (rl d) ≈⟨ rl-welldefined rld≅d ⟩
      rl d ≈⟨ rld≅d ⟩
      d ∎
      where
      open reasoning _ D.is-pre
      rld≅d : rl d D.≅ d
      rld≅d = rld≤d→rld≅d rld≤d

    lr-welldefined : is-welldefined C.is-pre C.is-pre lr
    lr-welldefined = monotone2welldefined C.is-pre C.is-pre lr-mono
    c≤lrc→c≅lrc : ∀ {c} → c C.≤ lr c → c C.≅ lr c
    forward (c≤lrc→c≅lrc ≤) = ≤
    backward (c≤lrc→c≅lrc ≤) = lr-decreasing _
    c≤lrc→c≅lrlrlrc : ∀ {c} → c C.≤ lr c → c C.≅ lr (lr (lr c))
    c≤lrc→c≅lrlrlrc {c} c≤lrc = begin-≈
      c ≈⟨ c≅lrc ⟩
      lr c ≈⟨ lr-welldefined c≅lrc ⟩
      lr (lr c) ≈⟨  lr-welldefined (lr-welldefined c≅lrc) ⟩
      lr (lr (lr c)) ∎
      where
      open reasoning _ C.is-pre
      c≅lrc : c C.≅ lr c
      c≅lrc = c≤lrc→c≅lrc c≤lrc

  C*2D*-D*2C*-is-order-isomorphism : is-order-isomorphism C*2D* D*2C*
  forward (fst C*2D*-D*2C*-is-order-isomorphism (d , rld≤d)) = forward (rld≤d→rlrlrld≅d rld≤d)
  backward (fst C*2D*-D*2C*-is-order-isomorphism (d , rld≤d)) = backward (rld≤d→rlrlrld≅d rld≤d)
  forward (snd C*2D*-D*2C*-is-order-isomorphism (c , c≤lrc)) =  backward (c≤lrc→c≅lrlrlrc c≤lrc)
  backward (snd C*2D*-D*2C*-is-order-isomorphism (c , c≤lrc)) = forward (c≤lrc→c≅lrlrlrc c≤lrc)

```


we have relation composition

⋈ : (𝓟(C × D),⊆) × (𝓟(D × E),⊆) → (𝓟(C × E),⊆)
which preserves meet-closed property but not butterfly condition.

We first think of n-ary relation composition operation indexed by lists of lattices Aᵢ.
big-⋈_{A₁A₂A₃...Aₙ} : 𝓟(A₁×A₂) → 𝓟(A₂×A₃) ... → 𝓟(Aₙ₋₁×Aₙ) → 𝒫(A×Z)
big-⋈_{A₁A₂A₃...Aₙ} r₁₂ r₂₃ ... rₙ₋₁ₙ = r₁₂ ⋈ r₂₃ ⋈ ... ⋈ rₙ₋₁ₙ


We derive corresponding n-ary composition operations on the following posets, from big-⋈ and adjunctions between the target poset and 𝒫(D × E):
- endofunctions ((D × E) → (D × E))
- bidirectional pairs of functions ((D → E) × (E → D))
- bidirectional pairs of functions with fb* ≤fp fb
- butterfly relations
- unidirectional functions (D → E)

big-⊗_{A₁A₂A₃...Aₙ} x₁₂ x₂₃ ... xₙ₋₁ₙ = G₁ₙ ((F₁₂ x₁₂) ⋈ (F₂₃ x₂₃) ⋈ ... ⋈ (Fₙ₋₁ₙ xₙ₋₁ₙ))
  where each pair (Gₙₘ , Fₙₘ) is the galois connection between 𝓟(Aₙ×Aₘ) and the target poset

```agda
module nary-composition-homogeneous
  (let lat = complete-meet-semilattice)
  where

  -- homogeneous case -> bi-operads
  nary-prod : Set → Nat.ℕ → Set
  nary-prod hom Nat.zero = Data.Unit.⊤
    where import Data.Unit
  nary-prod hom (Nat.suc n) = hom × nary-prod hom n

  nary-op : Set → Set
  nary-op hom = ∀ n → nary-prod hom n → hom

  is-unbiased : (X-pre : preordered-set) (let (pre X _≤_ X-is-pre) = X-pre) (op : nary-op X) → Set
  is-unbiased X-pre op =
    let (pre X _≤_ X-is-pre) = X-pre
        _≈_ = iso-pair _≤_
    in ∀ n x xs → op (Nat.suc n) (x , xs) ≈ op 2 (op 1 (x , _) , op n xs , _)

  module _
    (X : lat)
    (let X×X = X ×-cmlat X)
    (let (cmlat X-carrier _≤_ ⋀ X-is-cmlat) = X)
    (let (cmlat X×X-carrier _≤×_ ⋀× X×X-is-cmlat) = X×X)
    where

    open endo-function X×X-carrier _≤×_ ⋀× X×X-is-cmlat
    open transfer-function-pair X-carrier _≤_ ⋀ X-is-cmlat X-carrier _≤_ ⋀ X-is-cmlat

    ⨝ : nary-op (preordered-set.carrier pre-r)
    ⨝ Nat.zero _ (x , x')  = iso-pair _≤_ x x'
      where open complete-meet-semilattice
    ⨝ (Nat.suc n) (r , rs) = r ⋈ (⨝ n rs)

    gal-⨝ : (hom-pre : preordered-set) → galois-connection (preordered-set.opposite pre-r) hom-pre → nary-op (preordered-set.carrier hom-pre)
    gal-⨝  hom-pre (gal-conn l r g) n ps = monotone-func.func r (⨝ _ (nmap _ ps))
      where
      nmap : ∀ n → nary-prod (preordered-set.carrier hom-pre) n → nary-prod (preordered-set.carrier (preordered-set.opposite pre-r)) n
      nmap Nat.zero _ = _
      nmap (Nat.suc n) (p , ps) = monotone-func.func l p , nmap n ps

    ⨝-mf : nary-op (preordered-set.carrier pre-mf)
    ⨝-mf = gal-⨝ pre-mf (rel-mf-connected X X)

    ⨝-mfp : nary-op (preordered-set.carrier pre-mfp)
    ⨝-mfp = gal-⨝ pre-mfp (rel-mfp-connected X X)

```

```agda
module nary-composition-heterogeneous where
  private
    lat = complete-meet-semilattice

  -- type of index for nary-operation hom(X₁, X₂) → hom(X₂, X₃) → hom(X₃ , X₄) → ... hom(Xₙ₋₁ , Xₙ) → hom(X₁, Xₙ)
  -- whose each element is just a non-empty list  X₁ & X₂ & ... & rightmost Xₙ
  -- where `hom' is a type constructor that takes a pair of lattices, e.g.,
  -- * type of binary relation (subsets of product)
  -- * type of monotone endofunctions (function space between products)
  -- * type of bidirectional monotone function pair
  -- * type of unidirection monotone function

  open import Data.List


  module _ {X : Set} where
    data comptree : X → X → Set where
      leaf : (x y : X) → comptree x y
      _⊛_ : {x y z : X} → comptree x y → comptree y z → comptree x z

    rot-right : ∀ {l r} → comptree l r → comptree l r
    rot-right (leaf l r) = leaf l r
    rot-right (leaf l m ⊛ tr) = leaf l m ⊛ tr
    rot-right ((tl ⊛ tm) ⊛ tr) = tl ⊛ (tm ⊛ tr)

    module _ (hom : X → X → Set) where
      nary-prod : ∀ {l r} → comptree l r → Set
      nary-prod (leaf l r) = hom l r
      nary-prod (tl ⊛ tr) = nary-prod tl × nary-prod tr

  module _ where
    open complete-meet-semilattice
    sub-lat : lat → lat → Set
    sub-lat D E = subset (carrier D × carrier E)

    -- nullary case
    ⋈₀ : ∀ {D} → sub-lat D D
    ⋈₀ {D} (x , x') = iso-pair (relation D) x x'

    ⋈+ : ∀ {L R} (t : comptree L R) → nary-prod sub-lat t → sub-lat L R
    ⋈+ (leaf _ _) s = s -- unary case
    ⋈+ (lt ⊛ rt) (ls , rs) = (⋈+ lt ls) ⋈ (⋈+ rt rs) -- nary (n >= 2) case

{-
  -- type of nary composition operation hom(X₁, X₂) → hom(X₂, X₃) → hom(X₃ , X₄) → ... hom(Xₙ₋₁ , Xₙ) → hom(X₁, Xₙ)
  nary-comp : (lat → lat → Set) → latlist → Set
  nary-comp-helper : (lat → lat → Set) → lat → lat → latlist → Set

  nary-comp hom [ R ] = hom R R -- nullary case
  nary-comp hom (L ∷ [ R ]) = hom L R → hom L R -- unary case
  nary-comp hom (L ∷ M ∷ [ R ]) = hom L M → hom M R → hom L R -- binary case
  nary-comp hom (L ∷ M ∷ R ∷ Rs) = hom L M → hom M R → nary-comp-helper hom L R Rs -- nary case
  nary-comp-helper hom L M [ R ] = hom M R → hom L R
  nary-comp-helper hom L M (R ∷ Rs) = hom M R → nary-comp-helper hom L R Rs

  module _ where
    open complete-meet-semilattice
    rel-lat : lat → lat → Set
    rel-lat D E = subset (carrier D × carrier E)
    big-⋈ : {Ls : latlist} → nary-comp rel-lat Ls
    big-⋈-helper : (L M : lat) → (Rs : latlist) → (subset (carrier L × carrier M)) → nary-comp-helper rel-lat L M Rs

    big-⋈ {[ R ]} (x , x') = iso-pair (relation R) x x'  -- id relation
    big-⋈ {L ∷ [ R ]} r = r -- no composition
    big-⋈ {L ∷ M ∷ [ R ]} r r' = r ⋈ r'
    big-⋈ {L ∷ M ∷ R ∷ Rs} r r' =  big-⋈-helper L R Rs (r ⋈ r')
    big-⋈-helper L M [ R ] r r' = r ⋈ r'
    big-⋈-helper L M (R ∷ Rs) r r' = big-⋈-helper L R Rs (r ⋈ r')
-}
```

Some refs:
- https://arxiv.org/abs/math/0305049
- https://math.stackexchange.com/questions/1688187/strongly-unbiased-symmetric-monoidal-category
- https://mathoverflow.net/questions/193422/reference-for-multi-monoidal-categories
- https://arxiv.org/pdf/0906.2866.pdf
- https://en.wikipedia.org/wiki/Predicate_transformer_semantics
- https://proofassistants.stackexchange.com/questions/1239/replacing-strict-positivity-with-monotonicity-on-propositions
