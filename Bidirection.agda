{-# OPTIONS --type-in-type --postfix-projections #-}

module _ where

open import Agda.Primitive hiding (Prop) renaming (lzero to lzero ; _⊔_ to lmax ; Set to Set ; Setω to Setω) public
open import Algebra as Algebra
open import Data.Unit as Unit hiding (⊤)
open import Data.Empty as Empty hiding (⊥)
open import Data.Sum as Sum
open import Data.Sum.Properties as SumProps
import Data.Product as Product
open Product renaming (Σ to Σ')
open import Data.Product.Properties as ProductProps
import Data.Product.Relation.Binary.Pointwise.NonDependent as ProductBinR
open import Relation.Nullary as NumR
import Relation.Unary as UniR
open import Relation.Binary as BinR renaming (Rel to RelPoly ; Setoid to SetoidPoly ; Poset to PosetPoly)
import Relation.Binary.Morphism.Construct.Composition as BinRMorphComp
import Relation.Binary.Morphism.Construct.Constant as BinRMorphConst
import Relation.Binary.Morphism.Construct.Identity as BinRMorphId
open import Relation.Binary.Lattice as BinRLat
open import Function hiding (_↔_)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_ ; _≢_ ; _≗_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
import Relation.Binary.Reasoning.PartialOrder as PosetReasoning
open import Algebra
open import Data.Wrap

infixr -100 -Σ -Π

Σ : {X : Set} (Y : X → Set) → _
Σ Y = Σ' _ Y

-Σ : (X : Set) (Y : X → Set) → _
-Σ X Y = Σ Y
syntax -Σ X (\x → e) = Σ x ∶ X , e

Π : {X : Set} (Y : X → Set) → _
Π Y = ∀ x → Y x

-Π : (X : Set) (Y : X → Set) → _
-Π X Y = (x : X) → Y x
syntax -Π X (\x → e) = Π x ∶ X , e

record HasCarrier (Structure : Set) : Set where
  field
    Carrier : Structure → Set
  ∣_∣ = Carrier

open HasCarrier {{...}} hiding (Carrier) public

Setoid : Set
Setoid = SetoidPoly lzero lzero

Poset : Set
Poset = PosetPoly lzero lzero lzero

instance
  setoid-carrier : HasCarrier Setoid
  setoid-carrier .HasCarrier.Carrier = SetoidPoly.Carrier

  poset-carrier : HasCarrier Poset
  poset-carrier .HasCarrier.Carrier = PosetPoly.Carrier


module _ where
  import Relation.Binary.Morphism as BinRMorph
  open BinRMorph using () renaming (IsOrderHomomorphism to IsMono ; IsRelHomomorphism to IsCong) public
  module Cong = BinRMorph.SetoidHomomorphism renaming (isRelHomomorphism to isCongruent)
  module Mono = BinRMorph.PosetHomomorphism renaming (isOrderHomomorphism to isMonotone)

  _→cong_ = BinRMorph.SetoidHomomorphism
  _→mono_ = BinRMorph.PosetHomomorphism

record Has⟦⟧ (A : Set) (B : Set) : Set where
  field
    ⟦_⟧ : A → B

open Has⟦⟧ {{...}} public

instance
  cong-map : {x y : Setoid} → Has⟦⟧ (x →cong y) (∣ x ∣ → ∣ y ∣)
  Has⟦⟧.⟦ cong-map ⟧ = Cong.⟦_⟧

  mono-map : {x y : Poset} → Has⟦⟧ (x →mono y) (∣ x ∣ → ∣ y ∣)
  Has⟦⟧.⟦ mono-map ⟧ = Mono.⟦_⟧

infixr 10 _∘-cong_
_∘-cong_ : {A B C : Setoid} (f : B →cong C) (g : A →cong B) → A →cong C
f ∘-cong g = BinRMorphComp.setoidHomomorphism g f

infixr 10 _∘-mono_
_∘-mono_ : {A B C : Poset} (f : B →mono C) (g : A →mono B) → A →mono C
f ∘-mono g = BinRMorphComp.posetHomomorphism g f

⟦_⟧cong : {x y : Poset} → x →mono y → PosetPoly.Eq.setoid x →cong PosetPoly.Eq.setoid y
Cong.⟦ ⟦ f ⟧cong ⟧ = ⟦ f ⟧
⟦ f ⟧cong .Cong.isCongruent .IsCong.cong = f .Mono.isMonotone .IsMono.cong

infix 0 _↔_
_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

Prop→-poset : Poset
Prop→-poset .PosetPoly.Carrier = Set
Prop→-poset .PosetPoly._≈_ A B = A ↔ B
Prop→-poset .PosetPoly._≤_ A B = A → B
Prop→-poset .PosetPoly.isPartialOrder .IsPartialOrder.isPreorder .IsPreorder.isEquivalence .IsEquivalence.refl = id , id
Prop→-poset .PosetPoly.isPartialOrder .IsPartialOrder.isPreorder .IsPreorder.isEquivalence .IsEquivalence.sym = Product.swap
Prop→-poset .PosetPoly.isPartialOrder .IsPartialOrder.isPreorder .IsPreorder.isEquivalence .IsEquivalence.trans ij jk = jk .proj₁ ∘ ij .proj₁ , ij .proj₂ ∘ jk .proj₂
Prop→-poset .PosetPoly.isPartialOrder .IsPartialOrder.isPreorder .IsPreorder.reflexive = proj₁
Prop→-poset .PosetPoly.isPartialOrder .IsPartialOrder.isPreorder .IsPreorder.trans ij jk = jk ∘ ij
Prop→-poset .PosetPoly.isPartialOrder .IsPartialOrder.antisym = _,_

implicit↔explicit : {A : Set} {B : A → Set} → ({x : A} → B x) ↔ ((x : A) → B x)
implicit↔explicit .proj₁ = λ-
implicit↔explicit .proj₂ = _$-

curry↔uncurry : {A : Set} {B : Set} {C : A × B → Set} → ((ab : A × B) → C ab) ↔ ((a : A) (b : B) → C (a , b))
curry↔uncurry .proj₁ = curry
curry↔uncurry .proj₂ = uncurry

implication-↔× : {A : Set} {B : Set} → (A → B) → A ↔ B × A
implication-↔× φ .proj₁ a = (φ a , a)
implication-↔× φ .proj₂ (b , a) = a

Prop↔-setoid : Setoid
Prop↔-setoid = PosetPoly.Eq.setoid Prop→-poset

curry-↔ : ∀ a b c → (a × b → c) ↔ (a → b → c)
curry-↔ a b c .proj₁ f = curry f 
curry-↔ a b c .proj₂ g = uncurry g

_×-↔_ : {A B C D : Set} → (A ↔ B) → (C ↔ D) → (A × C) ↔ (B × D)
(a→b , b→a) ×-↔ (c→d , d→c) = Product.map a→b c→d , Product.map b→a d→c

{-
module _ (D≤ : Poset) where
  open PosetPoly D

  yoneda : ∀ a b → (a ≤ b) → (∀ c → b ≤ c → a ≤ c)
  yoneda a b a≤b c b≤c = trans a≤b b≤c

  yoneda-↔ : ∀ a b → (a ≤ b) ↔ (∀ c → b ≤ c → a ≤ c)
  yoneda-↔ a b .proj₁ = yoneda a b
  yoneda-↔ a b .proj₂ ∀c→b≤c→a≤c = ∀c→b≤c→a≤c b refl

  coyoneda : ∀ a b → (a ≤ b) → (∀ c → c ≤ a → c ≤ b)
  coyoneda a b a≤b c c≤a = trans c≤a a≤b

  coyoneda-↔ : ∀ a b → (a ≤ b) ↔ (∀ c → c ≤ a → c ≤ b)
  coyoneda-↔ a b .proj₁ = coyoneda a b
  coyoneda-↔ a b .proj₂ ∀c→c≤a→c≤b = ∀c→c≤a→c≤b a refl
-}
module _ where
  open ProductBinR
  module _ where
    open SetoidPoly

    _×-setoid_ : (D : Setoid) (E : Setoid) → Setoid
    (D ×-setoid E) .Carrier = ∣ D ∣ × ∣ E ∣
    (D ×-setoid E) ._≈_ = Pointwise (D ._≈_) (E ._≈_)
    (D ×-setoid E) .isEquivalence = ×-isEquivalence (D .isEquivalence) (E .isEquivalence)

  module _ where
    open PosetPoly

    _×-poset_ : (D : Poset) (E : Poset) → Poset
    (D ×-poset E) .Carrier = ∣ D ∣ × ∣ E ∣
    (D ×-poset E) ._≈_ = Pointwise (D ._≈_) (E ._≈_)
    (D ×-poset E) ._≤_ = Pointwise (D ._≤_) (E ._≤_)
    (D ×-poset E) .isPartialOrder = ×-isPartialOrder (D .isPartialOrder) (E .isPartialOrder)

module _ (D : Setoid) (E : Setoid) where
  private
    module D = SetoidPoly D
    module E = SetoidPoly E
    module D×E = SetoidPoly (D ×-setoid E)

  proj₁-cong : IsCong D×E._≈_ D._≈_ proj₁
  proj₁-cong .IsCong.cong = proj₁

  proj₁≈ : (D ×-setoid E) →cong D
  Cong.⟦ proj₁≈ ⟧ = proj₁
  proj₁≈ .Cong.isCongruent = proj₁-cong

  proj₂-cong : IsCong D×E._≈_ E._≈_ proj₂
  proj₂-cong .IsCong.cong = proj₂

  proj₂≈ : (D ×-setoid E) →cong E
  Cong.⟦ proj₂≈ ⟧ = proj₂
  proj₂≈ .Cong.isCongruent = proj₂-cong

module _ (D : Poset) (E : Poset) where
  private
    module D = PosetPoly D
    module E = PosetPoly E
    module D×E = PosetPoly (D ×-poset E)

  proj₁-mono : IsMono D×E._≈_ D._≈_ D×E._≤_ D._≤_ proj₁
  proj₁-mono .IsMono.cong = proj₁
  proj₁-mono .IsMono.mono = proj₁

  proj₁≤ : (D ×-poset E) →mono D
  Mono.⟦ proj₁≤ ⟧ = proj₁
  Mono.isMonotone proj₁≤ = proj₁-mono

  proj₂-mono : IsMono D×E._≈_ E._≈_ D×E._≤_ E._≤_ proj₂
  proj₂-mono .IsMono.cong = proj₂
  proj₂-mono .IsMono.mono = proj₂

  proj₂≤ : (D ×-poset E) →mono E
  Mono.⟦ proj₂≤ ⟧ = proj₂
  Mono.isMonotone proj₂≤ = proj₂-mono

record Pred (X : Setoid) : Set where
  constructor mkPred
  open SetoidPoly X
  field
    ⟦_⟧ : ∣ X ∣ → Set
    isWellDefined : {x y : _} → x ≈ y → ⟦ x ⟧ → ⟦ y ⟧

instance
  pred-map : {X : Setoid} → Has⟦⟧ (Pred X) (∣ X ∣ → Set)
  Has⟦⟧.⟦ pred-map ⟧ = Pred.⟦_⟧


≈→↔ : {X : Setoid} (P : Pred X) → {x y : ∣ X ∣} → SetoidPoly._≈_ X x y → (⟦ P ⟧ x) ↔ (⟦ P ⟧ y)
≈→↔ {X = X} P x≈y = (Pred.isWellDefined P x≈y) , (Pred.isWellDefined P (SetoidPoly.sym X x≈y))


Rel : Set → Set
Rel X = RelPoly X lzero

_∈_ : {X : Setoid} → ∣ X ∣ → Pred X → Set
x ∈ P = x UniR.∈ ⟦ P ⟧

∅ : {X : Setoid} → Pred X
Pred.⟦ ∅ ⟧ = UniR.∅
Pred.isWellDefined ∅ _ ()

｛_｝ : {X : Setoid} → ∣ X ∣ → Pred X
Pred.⟦  ｛_｝ {X} x ⟧ = X .SetoidPoly._≈_ x
｛_｝ {X} x .Pred.isWellDefined {y} {z} y≈z x≈y = X .SetoidPoly.trans x≈y y≈z

U : {X : Setoid} → Pred X
Pred.⟦ U ⟧ = UniR.U
U .Pred.isWellDefined _ _ = _


_⊆_ : {X : Setoid} → Pred X → Pred X → Set
P ⊆ Q = ⟦ P ⟧ UniR.⊆ ⟦ Q ⟧


U-max : {X : Setoid} (P : Pred X) → P ⊆ U
U-max _ _ = _

_≐_ : {X : Setoid} → Pred X → Pred X → Set
P ≐ Q = ⟦ P ⟧ UniR.≐ ⟦ Q ⟧

_∩_ : {X : Setoid} → Pred X → Pred X → Pred X
(P ∩ Q) .Pred.⟦_⟧ = (⟦ P ⟧ UniR.∩ ⟦ Q ⟧)
(P ∩ Q) .Pred.isWellDefined = λ{ x≈y (x∈P , x∈Q) → P.isWellDefined x≈y x∈P , Q.isWellDefined x≈y x∈Q }
  where private
    module P = Pred P
    module Q = Pred Q

∩-⊆-l : {X : Setoid} (S T : Pred X) → (S ∩ T) ⊆ S
∩-⊆-l S T (d∈S , d∈T) = d∈S

∩-⊆-r : {X : Setoid} (S T : Pred X) → (S ∩ T) ⊆ T
∩-⊆-r S T (d∈S , d∈T) = d∈T


∩-mono-l : {X : Setoid} (P Q S : Pred X) → P ⊆ Q → (P ∩ S) ⊆ (Q ∩ S)
∩-mono-l P Q S P⊆Q = (λ (x∈P , x∈S) → (P⊆Q x∈P , x∈S))

∩-mono-r : {X : Setoid} (P Q S : Pred X) → P ⊆ Q → (S ∩ P) ⊆ (S ∩ Q)
∩-mono-r P Q S P⊆Q = (λ (x∈S , x∈P) → (x∈S , P⊆Q x∈P))

∩-mono : {X : Setoid} (P Q S R : Pred X) → P ⊆ Q → S ⊆ R → (P ∩ S) ⊆ (Q ∩ R)
∩-mono P Q S R P⊆Q S⊆R = (λ (x∈P , x∈S) → (P⊆Q x∈P , S⊆R x∈S))

∩-cong-l : {X : Setoid} (P Q S : Pred X) → P ≐ Q → (P ∩ S) ≐ (Q ∩ S)
∩-cong-l P Q S P≐Q = ∩-mono-l P Q S (P≐Q .proj₁) , ∩-mono-l Q P S (P≐Q .proj₂)

∩-cong-r : {X : Setoid} (P Q S : Pred X) → P ≐ Q → (S ∩ P) ≐ (S ∩ Q)
∩-cong-r P Q S P≐Q = ∩-mono-r P Q S (P≐Q .proj₁) , ∩-mono-r Q P S (P≐Q .proj₂)

module _ {X : Setoid} where
  open SetoidPoly X
  _∪_ : Pred X → Pred X → Pred X
  Pred.⟦ P ∪ Q ⟧ = ⟦ P ⟧ UniR.∪ ⟦ Q ⟧
  (P ∪ Q) .Pred.isWellDefined {x} {y} x≈y (inj₁ x∈P) = inj₁ (P .Pred.isWellDefined x≈y x∈P)
  (P ∪ Q) .Pred.isWellDefined {x} {y} x≈y (inj₂ x∈Q) = inj₂ (Q .Pred.isWellDefined x≈y x∈Q)

_⋈_ : {X Y Z : Setoid} → Pred (X ×-setoid Y) → Pred (Y ×-setoid Z) → Pred (X ×-setoid Z)
(R ⋈ S) .Pred.⟦_⟧ = λ(x , z) → Σ y ∶ _ , (x , y) ∈ R × (y , z) ∈ S
_⋈_ {Y = Y} R S .Pred.isWellDefined {x , z} {x' , z'} (x≈x' , z≈z') (y , xy∈R , yz∈S)
  = y
  , R .Pred.isWellDefined (x≈x' , BinR.Setoid.refl Y) xy∈R
  , S .Pred.isWellDefined (BinR.Setoid.refl Y , z≈z') yz∈S

⋈-mono-l : {X Y Z : Setoid} (P Q : Pred (X ×-setoid Y)) (S : Pred (Y ×-setoid Z)) → P ⊆ Q → (P ⋈ S) ⊆ (Q ⋈ S)
⋈-mono-l P Q S P⊆Q = (λ (y , xy∈P , yz∈S) → (y , P⊆Q xy∈P , yz∈S))

⋈-mono-r : {X Y Z : Setoid} (P Q : Pred (Y ×-setoid Z)) (S : Pred (X ×-setoid Y)) → P ⊆ Q → (S ⋈ P) ⊆ (S ⋈ Q)
⋈-mono-r P Q S P⊆Q = (λ (y , xy∈S , yz∈P) → (y , xy∈S , P⊆Q yz∈P))

⋈-mono : {X Y Z : Setoid} (P Q : Pred (X ×-setoid Y)) (S R : Pred (Y ×-setoid Z)) → P ⊆ Q → S ⊆ R → (P ⋈ S) ⊆ (Q ⋈ R)
⋈-mono P Q S R P⊆Q S⊆R = (λ (y , xy∈P , yz∈S) → (y , P⊆Q xy∈P , S⊆R yz∈S)) 

⋈-cong-l : {X Y Z : Setoid} (P Q : Pred (X ×-setoid Y)) (S : Pred (Y ×-setoid Z)) → P ≐ Q → (P ⋈ S) ≐ (Q ⋈ S)
⋈-cong-l P Q S P≐Q = ⋈-mono-l P Q S (P≐Q .proj₁) , ⋈-mono-l Q P S (P≐Q .proj₂)


⋈-cong-r : {X Y Z : Setoid} (P Q : Pred (Y ×-setoid Z)) (S : Pred (X ×-setoid Y)) → P ≐ Q → (S ⋈ P) ≐ (S ⋈ Q)
⋈-cong-r P Q S P≐Q = ⋈-mono-r P Q S (P≐Q .proj₁) , ⋈-mono-r Q P S (P≐Q .proj₂)


module _ {X≈ Y≈ : Setoid} where
  private
    module Y = SetoidPoly Y≈
    module X = SetoidPoly X≈
    X = ∣ X≈ ∣
    Y = ∣ Y≈ ∣

  imageF-raw : (X → Y) → UniR.Pred Y lzero
  imageF-raw f y = Σ x ∶ X , f x Y.≈ y

  imageF : (X≈ →cong Y≈) → Pred Y≈
  Pred.⟦ imageF f ⟧ = imageF-raw ⟦ f ⟧
  imageF f .Pred.isWellDefined {y} {y'} y≈y' (x , fx≈y) = (x , Y.trans fx≈y y≈y')

  preimageF-raw : (X → Y) → UniR.Pred X lzero
  preimageF-raw f x = Σ y ∶ Y , f x Y.≈ y

  preimageF : (X≈ →cong Y≈) → Pred X≈
  Pred.⟦ preimageF f ⟧ = preimageF-raw ⟦ f ⟧
  preimageF f .Pred.isWellDefined {x} {x'} x≈x' (y , fx≈y) = (y , Y.trans (f .Cong.cong (X.sym x≈x')) fx≈y)

  imageR-raw : UniR.Pred (X × Y) lzero → UniR.Pred X lzero → UniR.Pred Y lzero
  imageR-raw R P y = Σ x ∶ X , R (x , y) × P x

  imageR : Pred (X≈ ×-setoid Y≈) → Pred X≈ → Pred Y≈
  Pred.⟦ imageR R P ⟧ = imageR-raw ⟦ R ⟧ ⟦ P ⟧
  imageR R P .Pred.isWellDefined {y} {y'} y≈y' (x , xy∈R , x∈P) = (x , R .Pred.isWellDefined (X.refl , y≈y') xy∈R , x∈P)

  preimageR-raw : UniR.Pred (X × Y) lzero → UniR.Pred Y lzero → UniR.Pred X lzero
  preimageR-raw R Q x = Σ y ∶ Y , R (x , y) × Q y

  preimageR : Pred (X≈ ×-setoid Y≈) → Pred Y≈ → Pred X≈
  Pred.⟦ preimageR R Q ⟧ = preimageR-raw ⟦ R ⟧ ⟦ Q ⟧
  preimageR R Q .Pred.isWellDefined {x} {x'} x≈x' (y , xy∈R , y∈Q) = (y , R .Pred.isWellDefined (x≈x' , Y.refl) xy∈R , y∈Q)

{-
image : {X : Setoid} {Y : Setoid} → (X →cong Y) → Pred X → Pred Y
image {X = X} {Y = Y} f P .Pred.⟦_⟧ y = Σ x ∶ ∣ X ∣ , x ∈ P × ⟦ f ⟧ x ≈ y
  where
  open SetoidPoly Y
image {X = X} {Y = Y} f P .Pred.isWellDefined y≈y' (x , x∈S , fx≈y) = x , x∈S , trans fx≈y y≈y'
  where
  open SetoidPoly Y

image↓ : {X≈ : Setoid} (Y≤ : Poset) → (X≈ →cong PosetPoly.Eq.setoid Y≤) → Pred X≈ → Pred (PosetPoly.Eq.setoid Y≤)
Pred.⟦ image↓ Y≤ f P ⟧ y = Σ x ∶ _ , x ∈ P × y ≤ ⟦ f ⟧ x
  where
  open PosetPoly Y≤
image↓ Y≤ f P .Pred.isWellDefined y≈y' (x , x∈S , y≤fx) = x , x∈S , trans (reflexive (Eq.sym y≈y')) y≤fx
  where
  open PosetPoly Y≤

preimage : {X : Setoid} {Y : Setoid} → (X →cong Y) → Pred Y → Pred X
Pred.⟦ preimage {X = X} {Y = Y} f P ⟧ x = ⟦ f ⟧ x UniR.∈ ⟦ P ⟧
preimage {X = X} {Y = Y} f P .Pred.isWellDefined {x} {x'} x≈x' fx∈P = P .Pred.isWellDefined (f .Cong.cong x≈x') fx∈P

image-mono : {X Y : Setoid} (f : X →cong Y) (S S' : Pred X) → S ⊆ S' → image f S ⊆ image f S'
image-mono f S S' S⊆S' {y} (x , x∈S , fx≈y) = x , S⊆S' x∈S , fx≈y

preimage-mono : {X Y : Setoid} (f : X →cong Y) (S S' : Pred Y) → S ⊆ S' → preimage f S ⊆ preimage f S'
preimage-mono f S S' S⊆S' {x} fx∈S = S⊆S' fx∈S

id⊆preimage∘image : {X Y : Setoid} (f : X →cong Y) (S : Pred X) → S ⊆ preimage f (image f S)
id⊆preimage∘image {Y = Y} f S x∈S = _ , x∈S , Y .SetoidPoly.refl

image-preimage⊆id : {X Y : Setoid} (f : X →cong Y) (S : Pred Y) → image f (preimage f S) ⊆ S
image-preimage⊆id f S {y} (x , fx∈S , fx≈y) = S .Pred.isWellDefined fx≈y fx∈S
-}
module _ (C≈ : Setoid) where
  open SetoidPoly C≈
  private
    C = ∣ C≈ ∣

  fix-raw : (C → C) → UniR.Pred C lzero
  fix-raw f d = d ≈ f d

  fix : C≈ →cong C≈ → Pred C≈
  Pred.⟦ fix f ⟧ = fix-raw ⟦ f ⟧
  fix f .Pred.isWellDefined {x} {y} x≈y x≈fx =
    begin
    y ≈˘⟨ x≈y ⟩
    x ≈⟨ x≈fx ⟩
    ⟦ f ⟧ x ≈⟨ f .Cong.cong x≈y ⟩
    ⟦ f ⟧ y ∎
    where
    open SetoidReasoning C≈

module _ (C≤ : Poset) where
  open PosetPoly C≤
  private
    C = ∣ C≤ ∣
    C≈ = PosetPoly.Eq.setoid C≤

  ub-raw : UniR.Pred C lzero → UniR.Pred C lzero
  ub-raw S x = ∀ x' → x' UniR.∈ S → x' ≤ x

  lb-raw : UniR.Pred C lzero → UniR.Pred C lzero
  lb-raw S x = ∀ x' → x' UniR.∈ S → x ≤ x'

  pre-raw : (C → C) → UniR.Pred C lzero
  pre-raw f x = f x ≤ x

  pre : (C≈ →cong C≈) → Pred C≈
  Pred.⟦ pre f ⟧ = pre-raw ⟦ f ⟧
  pre f .Pred.isWellDefined {x} {y} x≈y fx≤x =
    begin
    ⟦ f ⟧ y ≈˘⟨ f .Cong.cong x≈y ⟩
    ⟦ f ⟧ x ≤⟨ fx≤x ⟩
    x ≈⟨ x≈y ⟩
    y ∎
    where
    open PosetReasoning C≤

  post-raw : (C → C) → UniR.Pred C lzero
  post-raw f x = x ≤ f x

  post : (C≈ →cong C≈) → Pred C≈
  Pred.⟦ post f ⟧ d = d ≤ ⟦ f ⟧ d
  post f .Pred.isWellDefined {x} {y} x≈y x≤fx =
    begin
    y ≈˘⟨ x≈y ⟩
    x ≤⟨ x≤fx ⟩
    ⟦ f ⟧ x ≈⟨ f .Cong.cong x≈y ⟩
    ⟦ f ⟧ y ∎
    where
    open PosetReasoning C≤

  post∩pre⊆fix : (f : C≈ →cong C≈) → (post f ∩ pre f) ⊆ fix C≈ f
  post∩pre⊆fix f (x≤fx , fx≤x) = antisym x≤fx fx≤x

  fix⊆post∩pre : (f : C≈ →cong C≈) → fix C≈ f ⊆ (post f ∩ pre f)
  fix⊆post∩pre f x≈fx = reflexive x≈fx , reflexive (Eq.sym x≈fx)

  lfp-raw : (C → C) → UniR.Pred C lzero
  lfp-raw f = fix-raw C≈ f UniR.∩ lb-raw (fix-raw C≈ f)

  lfp : (C≈ →cong C≈) → Pred C≈
  Pred.⟦ lfp f ⟧ = lfp-raw ⟦ f ⟧
  lfp f .Pred.isWellDefined {x} {y} x≈y (x∈fixf , x'∈fixf→x≤x') = (fix C≈ f .Pred.isWellDefined x≈y x∈fixf) , (trans (reflexive (Eq.sym x≈y)) ∘₂ x'∈fixf→x≤x')

  gfp-raw : (C → C) → UniR.Pred C lzero
  gfp-raw f = fix-raw C≈ f UniR.∩ ub-raw (fix-raw C≈ f)

  gfp : (C≈ →cong C≈) → Pred C≈
  Pred.⟦ gfp f ⟧ = gfp-raw ⟦ f ⟧
  gfp f .Pred.isWellDefined {x} {y} x≈y (x∈fixf , x'∈fixf→x'≤x) = (fix C≈ f .Pred.isWellDefined x≈y x∈fixf) , (flip trans (reflexive x≈y) ∘₂ x'∈fixf→x'≤x)

module _ {P : Poset} where
  open PosetPoly P
  _ᵘ : Pred (Eq.setoid) → Pred (Eq.setoid)
  Pred.⟦ A ᵘ ⟧ x = ∀ a → ⟦ A ⟧ a → a ≤ x
  Pred.isWellDefined (A ᵘ) {x} {y} x≈y up z z∈A = trans (up z z∈A) (reflexive x≈y)

  _ˡ : Pred (Eq.setoid) → Pred (Eq.setoid)
  Pred.⟦ A ˡ ⟧ x = ∀ a → ⟦ A ⟧ a → x ≤ a
  Pred.isWellDefined (A ˡ) {x} {y} x≈y low z z∈A = trans (reflexive (Eq.sym x≈y)) (low z z∈A)

module _ {X≈ Y≈ : Setoid} where

  private

    module X = SetoidPoly X≈
    module Y = SetoidPoly Y≈

    X = ∣ X≈ ∣
    Y = ∣ Y≈ ∣

  Pred-swap : Pred (X≈ ×-setoid Y≈) → Pred (Y≈ ×-setoid X≈)
  Pred.⟦ Pred-swap R ⟧ (y , x) = Pred.⟦ R ⟧ (x , y)
  Pred-swap R .Pred.isWellDefined {y , x} {y' , x'} (y≈y' , x≈x') Rxy = R .Pred.isWellDefined (x≈x' , y≈y') Rxy

  Pred-proj₁ : Pred (X≈ ×-setoid Y≈) → Pred X≈
  Pred.⟦ Pred-proj₁ R ⟧ = λ x → Σ y ∶ Y , ((x , y) ∈ R)
  Pred-proj₁ R .Pred.isWellDefined x≈x' (y , xy∈R) = y , R .Pred.isWellDefined (x≈x' , Y.refl) xy∈R

  _∣₁ : Pred (X≈ ×-setoid Y≈) → Pred X≈
  _∣₁ = Pred-proj₁

  Pred-proj₂ : Pred (X≈ ×-setoid Y≈) → Pred Y≈
  Pred.⟦ Pred-proj₂ R ⟧ = λ y → Σ x ∶ X , ((x , y) ∈ R)
  Pred-proj₂ R .Pred.isWellDefined y≈y' (x , xy∈R) = x , R .Pred.isWellDefined (X.refl , y≈y') xy∈R

  _∣₂ : Pred (X≈ ×-setoid Y≈) → Pred Y≈
  _∣₂ = Pred-proj₂

  Pred-proj₁-∈ : {x : _} {y : _} (R : Pred (X≈ ×-setoid Y≈)) → (x , y) ∈ R → x ∈ Pred-proj₁ R
  Pred-proj₁-∈ R xy∈R = -, xy∈R

  Pred-proj₂-∈ : {x : _} {y : _} (R : Pred (X≈ ×-setoid Y≈)) → (x , y) ∈ R → y ∈ Pred-proj₂ R
  Pred-proj₂-∈ R xy∈R = -, xy∈R

  Pred-proj₁-mono : (R Q : Pred (X≈ ×-setoid Y≈)) → R ⊆ Q → Pred-proj₁ R ⊆ Pred-proj₁ Q
  Pred-proj₁-mono R Q R⊆Q {x} (y , xy∈R) = (y , R⊆Q xy∈R)

  Pred-proj₂-mono : (R Q : Pred (X≈ ×-setoid Y≈)) → R ⊆ Q → Pred-proj₂ R ⊆ Pred-proj₂ Q
  Pred-proj₂-mono R Q R⊆Q {y} (x , xy∈R) = (x , R⊆Q xy∈R)

module _ {X≈ Y≈ Z≈ : Setoid} where

  private

    module X = SetoidPoly X≈
    module Y = SetoidPoly Y≈
    module Z = SetoidPoly Z≈

    X = ∣ X≈ ∣
    Y = ∣ Y≈ ∣
    Z = ∣ Z≈ ∣

  Pred-assoc-rl : Pred (X≈ ×-setoid (Y≈ ×-setoid Z≈)) → Pred ((X≈ ×-setoid Y≈) ×-setoid Z≈)
  Pred.⟦ Pred-assoc-rl R ⟧ ((x , y) , z) = Pred.⟦ R ⟧ (x , (y , z))
  Pred-assoc-rl R .Pred.isWellDefined {(x , y) , z} {(x' , y') , z'} ((x≈x' , y≈y') , z≈z') Rxyz = R .Pred.isWellDefined (x≈x' , (y≈y' , z≈z')) Rxyz

  Pred-assoc-lr : Pred ((X≈ ×-setoid Y≈) ×-setoid Z≈) → Pred (X≈ ×-setoid (Y≈ ×-setoid Z≈))
  Pred.⟦ Pred-assoc-lr R ⟧ (x , (y , z)) = Pred.⟦ R ⟧ ((x , y) , z)
  Pred-assoc-lr R .Pred.isWellDefined {x , (y , z)} {x' , (y' , z')} (x≈x' , (y≈y' , z≈z')) Rxyz = R .Pred.isWellDefined ((x≈x' , y≈y') , z≈z') Rxyz



{-
DM : Poset' → Poset'
Poset.Carrier (DM P) = Σ A ∶ Pred (Eq.setoid) , (((A ᵘ) ˡ) ≐ A )
  where open Poset P
Poset._≈_ (DM P) = {!!}
Poset._≤_ (DM P) = {!!}
Poset.isPartialOrder (DM P) = {!!}
-}

module _ (D≤ : Poset) where
  open PosetPoly D≤
  private
    D≈ = PosetPoly.Eq.setoid D≤
  ↓ : ∣ D≤ ∣ → Pred D≈
  Pred.⟦ ↓ d ⟧ d' = d' ≤ d
  Pred.isWellDefined (↓ d) d'≈d'' d'≤d = trans (reflexive (Eq.sym d'≈d'')) d'≤d

  ↓-mono : (d d' : ∣ D≤ ∣) → D≤ .PosetPoly._≤_ d d' → ↓ d ⊆ ↓ d'
  ↓-mono d d' d≤d' = (λ d''≤d → trans d''≤d d≤d')

  ↓-cong : (d d' : ∣ D≤ ∣) → D≤ .PosetPoly._≈_ d d' → ↓ d ≐ ↓ d'
  ↓-cong d d' d≈d' = ↓-mono d d' (reflexive d≈d') , ↓-mono d' d (reflexive (Eq.sym d≈d'))

  principal-downset = ↓
  principal-downset-mono = ↓-mono
  principal-downset-cong = ↓-cong

  principal-upset : ∣ D≤ ∣ → Pred (PosetPoly.Eq.setoid D≤)
  Pred.⟦ principal-upset d ⟧ d' = d ≤ d'
  Pred.isWellDefined (principal-upset d) d'≈d'' d≤d' = trans d≤d' (reflexive d'≈d'')

  principal-upset-mono : (d d' : ∣ D≤ ∣) → D≤ .PosetPoly._≤_ d d' → principal-upset d' ⊆ principal-upset d
  principal-upset-mono d d' d≤d' = \d'≤d'' → trans d≤d' d'≤d''

  principal-upset-cong : (d d' : ∣ D≤ ∣) → D≤ .PosetPoly._≈_ d d' → principal-upset d ≐ principal-upset d'
  principal-upset-cong d d' d≈d' = principal-upset-mono d' d (reflexive (Eq.sym d≈d')) , principal-upset-mono d d' (reflexive d≈d')

  ↑ = principal-upset
  ↑-mono = principal-upset-mono
  ↑-cong = principal-upset-cong

record SLat : Set where
  field
    Carrier : Set
    _≈_ : Rel Carrier
    _≤_ : Rel Carrier
    ≤-po : IsPartialOrder _≈_ _≤_

  poset : Poset
  poset = record {isPartialOrder = ≤-po}

  module Po = PosetPoly poset
  module Eq = Po.Eq

  field
    ⨆ :  Pred Eq.setoid → Carrier
    _⊓_ : Op₂ Carrier
    ⊤ : Carrier
    ⊓-inf : Infimum _≤_ _⊓_
    ⊤-max : Maximum _≤_ ⊤
    ⨆-sup : ∀ S → (∀ x → x ∈ S → x ≤ ⨆ S) × (∀ y → (∀ x → x ∈ S → x ≤ y) → ⨆ S ≤ y)

  ↓≤ : Carrier → Pred Eq.setoid
  ↓≤ = ↓ poset

  ⊥ : Carrier
  ⊥ = ⨆ ∅

  _⊔_ : Op₂ Carrier
  x ⊔ y = ⨆ (｛ x ｝ ∪ ｛ y ｝)

  ⨆-upper : ∀ S x → x ∈ S → x ≤ ⨆ S
  ⨆-upper S = ⨆-sup S .proj₁

  ⨆-least : ∀ S y → (∀ x → x ∈ S → x ≤ y) → ⨆ S ≤ y
  ⨆-least S = ⨆-sup S .proj₂

  ⨆-mono : ∀ S S' → S ⊆ S' → ⨆ S ≤ ⨆ S'
  ⨆-mono S S' S⊆S' = ⨆-least S (⨆ S') (\ x x∈S → ⨆-upper S' x (S⊆S' x∈S))

  ⨆-cong : ∀ S S' → S ≐ S' → ⨆ S ≈ ⨆ S'
  ⨆-cong S S' (S⊆S' , S⊇S')  = Po.antisym (⨆-mono S S' S⊆S') (⨆-mono S' S S⊇S')

  ⨆-↓≥ : ∀ x → x ≤ ⨆ (↓ poset x)
  ⨆-↓≥ x = ⨆-upper (↓ poset x) x (Po.reflexive Eq.refl)

  ⨆-↓≤ : ∀ x → ⨆ (↓ poset x) ≤ x
  ⨆-↓≤ x = ⨆-least (↓ poset x) x \x' x'∈↓x → x'∈↓x

  ⨆-↓ : ∀ x → ⨆ (↓ poset x) ≈ x
  ⨆-↓ x = Po.antisym (⨆-↓≤ x) (⨆-↓≥ x)

  ⊓-lower-l : ∀ x y → (x ⊓ y) ≤ x
  ⊓-lower-l x y = proj₁ (⊓-inf x y)

  ⊓-lower-r : ∀ x y → (x ⊓ y) ≤ y
  ⊓-lower-r x y = proj₁ (proj₂ (⊓-inf x y))

  ⊓-greatest : ∀ x y → (∀ z → z ≤ x → z ≤ y → z ≤ (x ⊓ y))
  ⊓-greatest x y = proj₂ (proj₂ (⊓-inf x y))

  ⊤≈⨆U : ⊤ ≈ ⨆ U
  ⊤≈⨆U = Po.antisym (⨆-upper U _ tt ) (⊤-max (⨆ U))

{-
  ≤⊓→≤-l : ∀ x y z → z ≤ (x ⊓ y) → z ≤ x
  ≤⊓→≤-l x y = coyoneda poset _ _ (⊓-lower-l x y)

  ≤⊓→≤-r : ∀ x y z → z ≤ (x ⊓ y) → z ≤ y
  ≤⊓→≤-r x y = coyoneda poset _ _ (⊓-lower-r x y)

  ≤⊓→≤ : ∀ x y z → z ≤ (x ⊓ y) → z ≤ x × z ≤ y
  ≤⊓→≤ x y z z≤x⊓y = ≤⊓→≤-l x y z z≤x⊓y , ≤⊓→≤-r x y z z≤x⊓y

  ≤⊓←≤ : ∀ x y z → z ≤ x × z ≤ y → z ≤ (x ⊓ y)
  ≤⊓←≤ x y z (z≤x , z≤y) = ⊓-greatest x y z z≤x z≤y

  ≤⊓↔≤ : ∀ x y z → (z ≤ (x ⊓ y)) ↔ (z ≤ x × z ≤ y)
  ≤⊓↔≤ x y z .proj₁ = ≤⊓→≤ x y z
  ≤⊓↔≤ x y z .proj₂ = ≤⊓←≤ x y z
-}
  ⨆≤→∀≤ : ∀ S x → ⨆ S ≤ x → ∀ x' → x' ∈ S → x' ≤ x
  ⨆≤→∀≤ S x ⨆S≤x x' x'∈S = Po.trans (⨆-upper _ _ x'∈S) ⨆S≤x

  ⨆≤←∀≤ : ∀ S x → (∀ x' → x' ∈ S → x' ≤ x) → ⨆ S ≤ x
  ⨆≤←∀≤ = ⨆-least

  ⨆≤↔∀≤ : ∀ S x → ⨆ S ≤ x ↔ (∀ x' → x' ∈ S → x' ≤ x)
  ⨆≤↔∀≤ S x .proj₁ = ⨆≤→∀≤ S x
  ⨆≤↔∀≤ S x .proj₂ = ⨆≤←∀≤ S x


  ⊓≈⨆∩↓ : ∀ x y → (x ⊓ y) ≈ ⨆ (↓ poset x ∩ ↓ poset y)
  ⊓≈⨆∩↓ x y = Po.antisym
    (⨆-upper (↓≤ x ∩ ↓≤ y) (x ⊓ y) (⊓-inf x y .proj₁ , ⊓-inf x y .proj₂ .proj₁))
    (⊓-inf x y .proj₂ .proj₂ (⨆ (↓≤ x ∩ ↓≤ y)) (⨆-least (↓≤ x ∩ ↓≤ y) x (\_ p → p .proj₁)) ( (⨆-least (↓≤ x ∩ ↓≤ y) y (\_ p → p .proj₂))))

  ⨆↓≈⨆↓∩ : ∀ x S → x ∈ S → ⨆ (↓≤ x) ≈ ⨆ (↓≤ x ∩ S)
  ⨆↓≈⨆↓∩ x S x∈S = Po.antisym
    (⨆-upper (↓≤ x ∩ S) (⨆ (↓≤ x)) (⨆-↓≤ x , Pred.isWellDefined S (Eq.sym (⨆-↓ x)) x∈S))
    (⨆-mono (↓≤ x ∩ S) (↓≤ x) proj₁)

  post≤ = post poset

  ν : (Eq.setoid →cong Eq.setoid) → Carrier
  ν f = ⨆ (post poset f)

  ν-gfp : (f≤ : poset →mono poset) → ν (⟦ f≤ ⟧cong) ∈ gfp poset (⟦ f≤ ⟧cong)
  ν-gfp f≤ .proj₁ = -- proof that ν f is a fixed point of f
    Po.antisym R L
    where
    f≈ = ⟦ f≤ ⟧cong
    f = ⟦ f≤ ⟧
    open PosetReasoning poset
    ι : ∀ x → x ∈ post poset f≈ → x ≤ f (ν f≈)
    ι x x≤fx =
      begin
      x        ≤⟨ x≤fx ⟩
      f x      ≤⟨ f≤ .Mono.mono (⨆-upper (post≤ f≈) x x≤fx) ⟩
      f (ν f≈) ∎

    R : ν f≈ ≤ f (ν f≈)
    R =
      begin
      ν f≈     ≤⟨ ⨆-least (post≤ f≈) (f (ν f≈)) ι ⟩
      f (ν f≈) ∎

    L : f (ν f≈) ≤ ν f≈
    L =
      begin
      f (ν f≈) ≤⟨ ⨆-upper (post≤ f≈) (f (ν f≈)) (f≤ .Mono.mono (⨆-least (post≤ f≈) (f (ν f≈)) ι)) ⟩
      ν f≈     ∎
  ν-gfp f≤ .proj₂ x' x'∈fixf = u -- proof that ν f is the greatest fixed point
    where
    f≈ = ⟦ f≤ ⟧cong
    f = ⟦ f≤ ⟧
    open PosetReasoning poset
    u =
      begin
      x'   ≤⟨ ⨆-upper (post≤ f≈) x' (Po.reflexive x'∈fixf) ⟩
      ν f≈ ∎

  ν-mono : (f≈ g≈ : Eq.setoid →cong Eq.setoid) → ((x : Carrier) → ⟦ f≈ ⟧ x ≤ ⟦ g≈ ⟧ x) → ν f≈ ≤ ν g≈
  ν-mono f≈ g≈ f≤g = ⨆-mono (post≤ f≈) (post≤ g≈) \ {d} d≤fd → Po.trans d≤fd (f≤g d)

instance
  slat-has-carrier : HasCarrier (SLat)
  slat-has-carrier .HasCarrier.Carrier = SLat.Carrier

module _ (D⨆ : SLat) where
  open SLat D⨆
  private
    D≤ = poset
    D≈ = Eq.setoid
    D = ∣ D⨆ ∣

  ⨆S↓≤⨆S : (S↓ S : Pred D≈) → (∀ d → d ∈ S↓ → Σ d' ∶ D , d' ∈ S × d ≤ d') → ⨆ S↓ ≤ ⨆ S
  ⨆S↓≤⨆S S↓ S d∈S↓→d≤d'∈S = ⨆-least S↓ (⨆ S) P₁
    where
    open PosetReasoning D≤
    P₁ : (d : D) → d ∈ S↓ → d ≤ ⨆ S
    P₁ d d∈S↓ =
      let
      (d' , d'∈S , d≤d') = d∈S↓→d≤d'∈S d d∈S↓
      in
      begin
      d ≤⟨ d≤d' ⟩
      d' ≤⟨ ⨆-upper S d' d'∈S ⟩
      ⨆ S ∎

  ⨆-endomono : (f : D≤ →mono D≤) (S : Pred D≈) → ((d : D) → d ∈ S → d ≤ ⟦ f ⟧ d) → ((d : D) → ( ⨆ (↓ D≤ d ∩ S) ≤ ⟦ f ⟧ d))
  ⨆-endomono f S ∈S→postfix-of-f d = ⨆-least (↓ D≤ d ∩ S) (⟦ f ⟧ d) ↓d∩S⇒≤fd
    where
    ↓d∩S⇒≤fd : ∀ d' → d' ∈ (↓ D≤ d ∩ S) → d' ≤ ⟦ f ⟧ d
    ↓d∩S⇒≤fd d' (d'≤d , d'∈S) = Po.trans (∈S→postfix-of-f d' d'∈S) (Mono.mono f d'≤d)

  ⨆-endomono' : (f : D≤ →mono D≤) (S : Pred D≈) → ((d : D) → ( ⨆ (↓ D≤ d ∩ S) ≤ ⟦ f ⟧ d)) → ((d : D) → d ∈ S → d ≤ ⟦ f ⟧ d)
  ⨆-endomono' f S ⨆↓-∩S≤f- d d∈S = Po.trans (⨆-upper (↓ D≤ d ∩ S) d (Po.refl , d∈S)) (⨆↓-∩S≤f- d)

module _ where
  open ProductBinR
  open PosetPoly
  open SLat
  _×-slat_ : (D : SLat) (E : SLat) → SLat
  (D ×-slat E) .Carrier = ∣ D ∣ × ∣ E ∣
  (D ×-slat E) ._≈_ = Pointwise (D ._≈_) (E ._≈_)
  (D ×-slat E) ._≤_ = Pointwise (D ._≤_) (E ._≤_)
  (D ×-slat E) .≤-po = ×-isPartialOrder (D .≤-po) (E .≤-po)
  (D ×-slat E) .⨆ R =  D .⨆ (R ∣₁) , E .⨆ (R ∣₂)
  (D ×-slat E) ._⊓_ (d , e) (d' , e') = (D ._⊓_ d d' , E ._⊓_ e e')
  (D ×-slat E) .⊤ = D .⊤ , E .⊤
  (D ×-slat E) .⊓-inf (d , e) (d' , e') = D×E-lower₁ , D×E-lower₂ , D×E-greatest
    where
    D-inf = D .⊓-inf d d'
    E-inf = E .⊓-inf e e'
    D-lower₁ = D-inf .proj₁
    D-lower₂ = D-inf .proj₂ .proj₁
    E-lower₁ = E-inf .proj₁
    E-lower₂ = E-inf .proj₂ .proj₁
    D-greatest = D-inf .proj₂ .proj₂
    E-greatest = E-inf .proj₂ .proj₂
    D×E-lower₁ = D-lower₁ , E-lower₁
    D×E-lower₂ = D-lower₂ , E-lower₂
    D×E-greatest : (de'' : _) →
                     (D ×-slat E) ._≤_ de'' (d , e) →
                     (D ×-slat E) ._≤_ de'' (d' , e') →
                     (D ×-slat E) ._≤_ de'' ((D ×-slat E) ._⊓_ (d , e) (d' , e'))
    D×E-greatest (d'' , e'') (d''≤d , e''≤e) (d''≤d' , e''≤e') = D-greatest d'' d''≤d d''≤d' , E-greatest e'' e''≤e e''≤e'
  (D ×-slat E) .⊤-max (d , e) = D .⊤-max d , E .⊤-max e
  (D ×-slat E) .⨆-sup R = upper , least
    where
    upper : (x : ∣ D ∣ × ∣ E ∣) → x ∈ R → (D ×-slat E) ._≤_ x ((D ×-slat E) .⨆ R)
    upper (d , e) de∈R
      = (⨆-sup D (R ∣₁) .proj₁ d (Pred-proj₁-∈ R de∈R))
      , (⨆-sup E (R ∣₂) .proj₁ e (Pred-proj₂-∈ R de∈R))
    least : (y : (D ×-slat E) .Carrier) →
              ((x : (D ×-slat E) .Carrier) → x ∈ R → (D ×-slat E) ._≤_ x y) →
              (D ×-slat E) ._≤_ ((D ×-slat E) .⨆ R) y
    least (d , e) p-upper
      = ⨆-least D (Pred-proj₁ R) d d-upper
      , ⨆-least E (Pred-proj₂ R) e e-upper
      where
      d-upper : (d' : D .Carrier) → d' ∈ (R ∣₁) → D ._≤_ d' d
      d-upper d' (e' , de'∈R) = p-upper (d' , e') de'∈R .proj₁
      e-upper : (e' : E .Carrier) → e' ∈ (R ∣₂) → E ._≤_ e' e
      e-upper e' (d' , de'∈R) = p-upper (d' , e') de'∈R .proj₂

module _ where
  open PosetPoly
  open Mono
  record GaloisConnection {C : Poset} {D : Poset} (L : C →mono D) (R : D →mono C) : Set where
    private module C = PosetPoly C
    private module D = PosetPoly D
    field
      ψ : ∀ c d → (⟦ L ⟧ c D.≤ d) ↔ (c C.≤ ⟦ R ⟧ d)

    η : ∀ c → id c C.≤ (⟦ R ⟧ ∘ ⟦ L ⟧) c
    η c = ψ c (⟦ L ⟧ c) .proj₁ D.refl
    ε : ∀ d → (⟦ L ⟧ ∘ ⟦ R ⟧) d D.≤ id d
    ε d = ψ (⟦ R ⟧ d) d .proj₂ C.refl

    preRL : Pred C.Eq.setoid
    preRL = pre C ⟦ R ∘-mono L ⟧cong

    postLR : Pred D.Eq.setoid
    postLR = post D ⟦ L ∘-mono R ⟧cong

    preRL⊆imageR : preRL ⊆ imageF ⟦ R ⟧cong
    preRL⊆imageR {c} c∈preRL = (⟦ L ⟧ c , C.antisym c∈preRL (η c))

    preRL⊇imageR : imageF ⟦ R ⟧cong ⊆ preRL
    preRL⊇imageR {c} (d , Rd≈c) =
      let open PosetReasoning C in
      begin
      ⟦ R ∘-mono L ⟧ c ≈˘⟨ (R ∘-mono L) .Mono.cong Rd≈c ⟩
      ⟦ (R ∘-mono L) ∘-mono R ⟧ d ≤⟨ R .Mono.mono (ε d) ⟩
      ⟦ R ⟧ d ≈⟨ Rd≈c ⟩
      c ∎

    preRL≐imageR : preRL ≐ imageF ⟦ R ⟧cong
    preRL≐imageR = preRL⊆imageR , preRL⊇imageR
    
    R∈preRL : ∀ d → ⟦ R ⟧ d ∈ preRL
    R∈preRL = R .mono ∘ ε

    L∈postLR : ∀ c → ⟦ L ⟧ c ∈ postLR
    L∈postLR = L .mono ∘ η


    LRL≈L : ∀ c → ⟦ L ∘-mono (R ∘-mono L) ⟧ c D.≈ ⟦ L ⟧ c
    LRL≈L c = D.antisym LRL≤L LRL≥L
      where
      LRL≥L : ⟦ L ⟧ c D.≤ (⟦ L ⟧ ∘ ⟦ R ⟧ ∘ ⟦ L ⟧) c
      LRL≥L = L∈postLR c
      LRL≤L : (⟦ L ⟧ ∘ ⟦ R ⟧ ∘ ⟦ L ⟧) c D.≤ ⟦ L ⟧ c
      LRL≤L = ε (⟦ L ⟧ c)

    RLR≈R : ∀ d → ⟦ R ∘-mono (L ∘-mono R) ⟧ d C.≈ ⟦ R ⟧ d
    RLR≈R d = C.antisym RLR≤R RLR≥R
      where
      RLR≤R : (⟦ R ⟧ ∘ ⟦ L ⟧ ∘ ⟦ R ⟧) d C.≤ ⟦ R ⟧ d
      RLR≤R = R∈preRL d
      RLR≥R : ⟦ R ⟧ d C.≤ (⟦ R ⟧ ∘ ⟦ L ⟧ ∘ ⟦ R ⟧) d
      RLR≥R = η (⟦ R ⟧ d)



  _⊣_ : {C : Poset} {D : Poset} (L : C →mono D ) (R : D →mono C) → Set _
  L ⊣ R = GaloisConnection L R

lift→ : {D : Set} → (P Q : UniR.Pred D lzero) → ((d : D) → P d → Q d) → (∀ d → P d) → (∀ d → Q d)
lift→ P Q P⇒Q ∀P d = P⇒Q d (∀P d)

lift↔ : {D : Set} → (P Q : UniR.Pred D lzero) → ((d : D) → P d ↔ Q d) → (∀ d → P d) ↔ (∀ d → Q d)
lift↔ P Q P⇔Q .proj₁ ∀P d = P⇔Q d .proj₁ (∀P d)
lift↔ P Q P⇔Q .proj₂ ∀Q d = P⇔Q d .proj₂ (∀Q d)

lift→-implicit : {D : Set} → (P Q : UniR.Pred D lzero) → (∀ {d} → P d → Q d) → (∀ {d} → P d) → (∀ {d} → Q d)
lift→-implicit P Q P⇒Q ∀P = P⇒Q ∀P

lift↔-implicit : {D : Set} → (P Q : UniR.Pred D lzero) → (∀ {d} → P d ↔ Q d) → (∀ {d} → P d) ↔ (∀ {d} → Q d)
lift↔-implicit P Q P⇔Q .proj₁ ∀P = P⇔Q .proj₁ ∀P
lift↔-implicit P Q P⇔Q .proj₂ ∀Q = P⇔Q .proj₂ ∀Q

module _ {C : Poset} {D : Poset} {E : Poset} {L : C →mono D} {R : D →mono C} {L' : D →mono E} {R' : E →mono D} where
  open GaloisConnection
  private
    module C = PosetPoly C
    module D = PosetPoly D
    module E = PosetPoly E

  infixr 20 _∘-galois_
  _∘-galois_ : L ⊣ R → L' ⊣ R' → (L' ∘-mono L) ⊣ (R ∘-mono R')
  (L⊣R ∘-galois L'⊣R') .ψ c e =
    let open SetoidReasoning Prop↔-setoid in
    begin
    ⟦ L' ∘-mono L ⟧ c E.≤ e     ≈⟨ L'⊣R' .ψ (⟦ L ⟧ c) e ⟩
    ⟦ L ⟧ c D.≤ ⟦ R' ⟧ e       ≈⟨ L⊣R .ψ c (⟦ R' ⟧ e) ⟩
    c C.≤ ⟦ R ∘-mono R' ⟧ e     ∎

  preRL-∘-⊆ : (α : L ⊣ R) (β : L' ⊣ R') → preRL (α ∘-galois β) ⊆ preRL α
  preRL-∘-⊆ α β {c} RR'L'Lc≤c =
    let open PosetReasoning C in
    begin
    ⟦ R ∘-mono L ⟧ c ≤⟨ R .Mono.mono (η β (⟦ L ⟧ c)) ⟩
    ⟦ (R ∘-mono R') ∘-mono L' ∘-mono L ⟧ c ≤⟨ RR'L'Lc≤c ⟩
    c ∎


module FunBinR where
  open IsPartialOrder using (isPreorder)
  open IsPreorder using (isEquivalence)

  Pointwise : {D : Set} (C : Set) → Rel D → Rel (C → D)
  Pointwise C _R_ f g = (c : C) → (f c) R (g c)

  →isEquivalence : {D : Set} (C : Set) {_≈_ : Rel D} → IsEquivalence _≈_ → IsEquivalence (Pointwise C _≈_)
  →isEquivalence C ≈-eqv .IsEquivalence.refl c = ≈-eqv .IsEquivalence.refl
  →isEquivalence C ≈-eqv .IsEquivalence.sym f≈g c = ≈-eqv .IsEquivalence.sym (f≈g c)
  →isEquivalence C ≈-eqv .IsEquivalence.trans f≈g g≈h c = ≈-eqv .IsEquivalence.trans (f≈g c) (g≈h c)

  →isPartialOrder : {D : Set} (C : Set) {_≈_ _≤_ : Rel D} → IsPartialOrder _≈_ _≤_ → IsPartialOrder (Pointwise C _≈_) (Pointwise C _≤_)
  →isPartialOrder C ≤-po .isPreorder .isEquivalence = →isEquivalence C (≤-po .isPreorder .isEquivalence )
  →isPartialOrder C ≤-po .isPreorder .IsPreorder.reflexive f≈g c = ≤-po .isPreorder .IsPreorder.reflexive (f≈g c)
  →isPartialOrder C ≤-po .isPreorder .IsPreorder.trans f≤g g≤h c = ≤-po .isPreorder .IsPreorder.trans (f≤g c) (g≤h c)
  →isPartialOrder C ≤-po .IsPartialOrder.antisym f≤g g≤f c = ≤-po .IsPartialOrder.antisym (f≤g c) (g≤f c)

  module _ (C D : Poset) where
    open PosetPoly D
    MonoPointwise : Rel ∣ D ∣ → Rel (C →mono D)
    MonoPointwise _R_ f g = (c : ∣ C ∣) → (⟦ f ⟧ c) R (⟦ g ⟧ c)

    →mono-isEquivalence : IsEquivalence (MonoPointwise (_≈_))
    →mono-isEquivalence .IsEquivalence.refl c = Eq.refl
    →mono-isEquivalence .IsEquivalence.sym f≈g c = Eq.sym (f≈g c)
    →mono-isEquivalence .IsEquivalence.trans f≈g g≈h c = Eq.trans (f≈g c) (g≈h c)

    →mono-isPartialOrder : IsPartialOrder (MonoPointwise _≈_) (MonoPointwise _≤_)
    →mono-isPartialOrder .isPreorder .isEquivalence = →mono-isEquivalence
    →mono-isPartialOrder .isPreorder .IsPreorder.reflexive f≈g c = reflexive (f≈g c)
    →mono-isPartialOrder .isPreorder .IsPreorder.trans f≤g g≤h c = trans (f≤g c) (g≤h c)
    →mono-isPartialOrder .IsPartialOrder.antisym f≤g g≤f c = antisym (f≤g c) (g≤f c)


module _ where
  open PosetPoly

  _→≤-poset_ : (C : Set) (D : Poset) → Poset
  _→≤-poset_ C D .Carrier = C → ∣ D ∣
  _→≤-poset_ C D ._≈_ = FunBinR.Pointwise C (D ._≈_)
  _→≤-poset_ C D ._≤_ = FunBinR.Pointwise C (D ._≤_)
  _→≤-poset_ C D .isPartialOrder = FunBinR.→isPartialOrder C (D .isPartialOrder)

  _→mono≤-poset_ : (C : Poset) (D : Poset) → Poset
  _→mono≤-poset_ C D .Carrier = C →mono D
  _→mono≤-poset_ C D ._≈_ f g = FunBinR.Pointwise ∣ C ∣ (D ._≈_) ⟦ f ⟧ ⟦ g ⟧
  _→mono≤-poset_ C D ._≤_ f g = FunBinR.Pointwise ∣ C ∣ (D ._≤_) ⟦ f ⟧ ⟦ g ⟧
  _→mono≤-poset_ C D .isPartialOrder = FunBinR.→mono-isPartialOrder C D

  open IsPartialOrder using (isPreorder)
  open IsPreorder using (isEquivalence)
  Pred⊆-poset : (D : Setoid) → Poset
  Pred⊆-poset D .Carrier = Pred D
  Pred⊆-poset D ._≈_ P Q = P ≐ Q
  Pred⊆-poset D ._≤_ = _⊆_
  Pred⊆-poset D .isPartialOrder .isPreorder .isEquivalence .IsEquivalence.refl = id , id
  Pred⊆-poset D .isPartialOrder .isPreorder .isEquivalence .IsEquivalence.sym (⊆ , ⊇) = (⊇ , ⊆)
  Pred⊆-poset D .isPartialOrder .isPreorder .isEquivalence .IsEquivalence.trans (⊆₁ , ⊇₁) (⊆₂ , ⊇₂) = (⊆₂ ∘ ⊆₁) , (⊇₁ ∘ ⊇₂)
  Pred⊆-poset D .isPartialOrder .isPreorder .IsPreorder.reflexive = proj₁
  Pred⊆-poset D .isPartialOrder .isPreorder .IsPreorder.trans ⊆₁ ⊆₂ = ⊆₂ ∘ ⊆₁
  Pred⊆-poset D .isPartialOrder .IsPartialOrder.antisym ⊆ ⊇ = ⊆ , ⊇

  Pred≐-setoid : (D : Setoid) → Setoid
  Pred≐-setoid D = PosetPoly.Eq.setoid (Pred⊆-poset D)

  Pred⊆-→mono-Prop→ : (D : Setoid) → Pred⊆-poset D →mono Prop→-poset
  Mono.⟦ Pred⊆-→mono-Prop→ D ⟧ P = ∀ d → d ∈ P
  Pred⊆-→mono-Prop→ D .Mono.isMonotone .IsMono.mono {P} {Q} P⊆Q ∀d→d∈P d = P⊆Q (∀d→d∈P d)
  Pred⊆-→mono-Prop→ D .Mono.isMonotone .IsMono.cong {P} {Q} (P⊆Q , P⊇Q) .proj₁ ∀d→d∈P d = P⊆Q (∀d→d∈P d)
  Pred⊆-→mono-Prop→ D .Mono.isMonotone .IsMono.cong {P} {Q} (P⊆Q , P⊇Q) .proj₂ ∀d→d∈Q d = P⊇Q (∀d→d∈Q d)

module _ (D⨆ E⨆ : SLat) where
  private
    module D = SLat D⨆
    module E = SLat E⨆
    D≤ = D.poset
    E≤ = E.poset
    D≈ = D.Eq.setoid
    E≈ = E.Eq.setoid
    D = ∣ D⨆ ∣
    E = ∣ E⨆ ∣
    𝒫⊆ = Pred⊆-poset (D≈ ×-setoid E≈)

  module _ (X : Poset) (F : 𝒫⊆ →mono X) (G : X →mono 𝒫⊆) (F⊣G : F ⊣ G) where

IsCoclosure : (D : Poset) (f : ∣ D ∣ → ∣ D ∣) → Set
IsCoclosure D f = ∀ d → f d ≤ d × f d ≤ f (f d)
  where open PosetPoly D

Is⨆Closed : (D : SLat) → Pred (SLat.Eq.setoid D) → Set
Is⨆Closed D S = (∀ S' → S' ⊆ S → (D .SLat.⨆ S') ∈ S)

module _ (D⨆ E⨆ : SLat) where

  private
    D≤ = SLat.poset D⨆
    D≈ = SLat.Eq.setoid D⨆
    D = ∣ D⨆ ∣
    module D = SLat D⨆

    E≤ = SLat.poset E⨆
    E≈ = SLat.Eq.setoid E⨆
    E = ∣ E⨆ ∣
    module E = SLat E⨆

    open SLat (D⨆ ×-slat E⨆)

  proj₁-⨆closed : ∀ R → Is⨆Closed (D⨆ ×-slat E⨆) R → Is⨆Closed D⨆ (R ∣₁)
  proj₁-⨆closed R R-⨆closed S S⊆R₁ = ⨆ T .proj₂ , R .Pred.isWellDefined (D.⨆-cong (T ∣₁) S T₁≐S , E.Eq.refl) ⨆T∈R
    where
    T : Pred (D≈ ×-setoid E≈)
    Pred.⟦ T ⟧ (d , e) = d ∈ S × (d , e) ∈ R
    T .Pred.isWellDefined {d , e} {d' , e'} (d≈d' , e≈e') (d∈S , de∈R) = S .Pred.isWellDefined d≈d' d∈S , R .Pred.isWellDefined (d≈d' , e≈e') de∈R
    T₁≐S : (T ∣₁) ≐ S
    T₁≐S .proj₂ d∈S = let (e , de∈R) = S⊆R₁ d∈S  in e , d∈S , de∈R
    T₁≐S .proj₁ (e , d∈S , de∈R) = d∈S
    T⊆R : T ⊆ R
    T⊆R {d , e} (d∈S , de∈R) = de∈R
    ⨆T∈R : ⨆ T ∈ R
    ⨆T∈R = R-⨆closed T T⊆R

  proj₂-⨆closed : ∀ R → Is⨆Closed (D⨆ ×-slat E⨆) R → Is⨆Closed E⨆ (R ∣₂)
  proj₂-⨆closed R R-⨆closed S S⊆R₂ = ⨆ T .proj₁ , R .Pred.isWellDefined (D.Eq.refl , E.⨆-cong (T ∣₂) S T₂≐S) ⨆T∈R
    where
    T : Pred (D≈ ×-setoid E≈)
    Pred.⟦ T ⟧ (d , e) = e ∈ S × (d , e) ∈ R
    T .Pred.isWellDefined {d , e} {d' , e'} (d≈d' , e≈e') (d∈S , de∈R) = S .Pred.isWellDefined e≈e' d∈S , R .Pred.isWellDefined (d≈d' , e≈e') de∈R
    T₂≐S : (T ∣₂) ≐ S
    T₂≐S .proj₂ e∈S = let (d , de∈R) = S⊆R₂ e∈S  in d , e∈S , de∈R
    T₂≐S .proj₁ (d , e∈S , de∈R) = e∈S
    T⊆R : T ⊆ R
    T⊆R {d , e} (d∈S , de∈R) = de∈R
    ⨆T∈R : ⨆ T ∈ R
    ⨆T∈R = R-⨆closed T T⊆R

-- First abstraction
module 𝒫⊆-and-Endo (C⨆ : SLat) where

  private
    C≤ = SLat.poset C⨆
    C≈ = SLat.Eq.setoid C⨆
    C = ∣ C⨆ ∣

  𝒫⊆ = Pred⊆-poset C≈
  Endo = C≤ →mono≤-poset C≤
  open SLat C⨆


  -- This module gives an adjoint poset map between binary relations and endo monotone functions on product
  --     (𝒫 (D × E) , ⊆)
  --        F ↓ ⊣ ↑ G
  --  ((D × E →m D × E) , ≤)
  --
  -- This is followed by adjoint poset map between subsets and endo monotone functions (general setting)
  --    (𝒫 (C) , ⊆)
  --     F ↓ ⊣ ↑ G
  --   ((C →m C) , ≤)

  -- F : (Pred⊆-poset D≈) →mono (D≤ →mono≤-poset D≤)
  -- G : (D≤ →mono≤-poset D≤) →mono (Pred⊆-poset D≈)
  -- F⊣G : F ⊣ G

  F-raw : Pred C≈ → C → C
  F-raw S d = ⨆ ((↓ C≤ d) ∩ S)

  F-mono : Pred C≈ → (C≤ →mono C≤)
  Mono.⟦ F-mono S ⟧ = F-raw S
  F-mono S .Mono.isMonotone .IsMono.mono {d} {d'}
    = ⨆-mono ((↓ C≤ d) ∩ S) ((↓ C≤ d') ∩ S)
    ∘ ∩-mono-l (↓ C≤ d) (↓ C≤ d') S
    ∘ ↓-mono C≤ d d'
  F-mono S .Mono.isMonotone .IsMono.cong d≈d' = Po.antisym
    (F-mono S .Mono.mono (Po.reflexive d≈d'))
    (F-mono S .Mono.mono (Po.reflexive (Eq.sym d≈d')))

  G-raw : (C → C) → UniR.Pred C lzero
  G-raw f = post-raw C≤ f

  G-pred : (C≤ →mono C≤) → Pred C≈
  G-pred f = post C≤ ⟦ f ⟧cong

  F : 𝒫⊆ →mono Endo
  Mono.⟦ F ⟧ = F-mono
  F .Mono.isMonotone .IsMono.mono {P} {Q} P⊆Q d
    = ⨆-mono (↓ C≤ d ∩ P) (↓ C≤ d ∩ Q)
             (∩-mono-r P Q (↓ C≤ d) P⊆Q)
  F .Mono.isMonotone .IsMono.cong {P} {Q} P≐Q d = Po.antisym
    (F .Mono.isMonotone .IsMono.mono {P} {Q} (P≐Q .proj₁) d)
    (F .Mono.isMonotone .IsMono.mono {Q} {P} (P≐Q .proj₂) d)

  G : Endo →mono 𝒫⊆
  Pred.⟦ Mono.⟦ G ⟧ f ⟧ = ⟦ G-pred f ⟧
  Mono.⟦ G ⟧ f .Pred.isWellDefined {d} {d'} d≈d' d≤fd
    = begin
    d'                 ≈˘⟨ d≈d' ⟩
    d                  ≤⟨ d≤fd ⟩
    ⟦ f ⟧ d            ≈⟨ f .Mono.cong d≈d' ⟩
    ⟦ f ⟧ d'           ∎
    where
    open PosetReasoning C≤
  G .Mono.isMonotone .IsMono.mono {f} {g} f≤g {d} d≤fd
    = begin
    d                  ≤⟨ d≤fd ⟩
    ⟦ f ⟧ d            ≤⟨ f≤g d ⟩
    ⟦ g ⟧ d            ∎
    where
    open PosetReasoning C≤
  G .Mono.isMonotone .IsMono.cong {f} {g} f≈g .proj₁ {d} d≤fd = G .Mono.isMonotone. IsMono.mono {f} {g} (M.reflexive {f} {g} f≈g) d≤fd
    where
    private module M = PosetPoly (C≤ →mono≤-poset C≤)
  G .Mono.isMonotone .IsMono.cong {f} {g} f≈g .proj₂ {d} d≤gd = G .Mono.isMonotone. IsMono.mono {g} {f} (M.reflexive {g} {f} (M.Eq.sym {f} {g} f≈g)) d≤gd
    where
    private module M = PosetPoly (C≤ →mono≤-poset C≤)


  F⊣G : F ⊣ G
  F⊣G .GaloisConnection.ψ P f .proj₁ FP≤f {d} d∈P = Po.trans (⨆-upper (↓ C≤ d ∩ P) d (Po.refl , d∈P)) (FP≤f d)
  F⊣G .GaloisConnection.ψ P f .proj₂ P⊆Gf d = ⨆-least (↓ C≤ d ∩ P) (⟦ f ⟧ d) \d' (d'≤d , d'∈P) → Po.trans (P⊆Gf d'∈P) (Mono.mono f d'≤d)
    where
    private module M = PosetPoly (C≤ →mono≤-poset C≤)

  preFG : (f≤ : C≤ →mono C≤)
    → (f≤ ∈ pre (C≤ →mono≤-poset C≤) ⟦ F ∘-mono G ⟧cong)
  preFG = GaloisConnection.ε F⊣G

  postFG-characterization : (f≤ : C≤ →mono C≤)
    → f≤ ∈ GaloisConnection.postLR F⊣G ↔ IsCoclosure C≤ ⟦ f≤ ⟧
  postFG-characterization f≤ =
    let open SetoidReasoning (Prop↔-setoid) in
    begin
    (f≤ ∈ post (C≤ →mono≤-poset C≤) ⟦ F ∘-mono G ⟧cong) ≡⟨⟩
    (∀ d → f d ≤ ⨆ (↓ poset d ∩ post C≤ f≈ )) ≈⟨ lift↔ _ _ ψ ⟩
    (∀ d → f d ≤ d × (f d ≤ f (f d))) ≡⟨⟩
    IsCoclosure C≤ f ∎
    where
    f≈ = ⟦ f≤ ⟧cong
    f = ⟦ f≤ ⟧
    ψ : ∀ d  → (f d ≤ ⨆ (↓ poset d ∩ post C≤ f≈)) ↔ ((f d ≤ d) × (f d ≤ f (f d)))
    ψ d = Product.< ε , δ > , uncurry φ
      where
      ε : f d ≤ ⨆ (↓ poset d ∩ post C≤ f≈) → f d ≤ d
      ε φ =
        let open PosetReasoning C≤ in
        begin
        f d  ≤⟨ φ ⟩
        ⨆ (↓ poset d ∩ post C≤ f≈)  ≤⟨ ⨆-mono (↓ poset d ∩ post C≤ f≈) (↓ poset d) (∩-⊆-l (↓ poset d) (post C≤ f≈)) ⟩
        ⨆ (↓ poset d) ≈⟨ ⨆-↓ d ⟩
        d  ∎
      δ : f d ≤ ⨆ (↓ poset d ∩ post C≤ f≈) → f d ≤ f (f d)
      δ φ =
        let open PosetReasoning C≤ in
        begin
        f d  ≤⟨ φ ⟩
        ⨆ (↓ poset d ∩ post C≤ f≈)  ≤⟨ ⨆-least (↓ poset d ∩ post C≤ f≈) (f (f d)) P2' ⟩
        f (f d)  ∎
        where
        P2' : ∀ d' → d' ∈ (↓ poset d ∩ post C≤ f≈) → d' ≤ f (f d)
        P2' d' (d'≤d , d'≤fd') =
          let
          ffd'≤ffd = f≤ .Mono.mono (f≤ .Mono.mono d'≤d)
          fd'≤ffd' = f≤ .Mono.mono d'≤fd'
          open PosetReasoning C≤
          in
          begin
          d' ≤⟨ d'≤fd' ⟩
          f d' ≤⟨ fd'≤ffd' ⟩
          f (f d') ≤⟨ ffd'≤ffd ⟩
          f (f d) ∎

      φ : f d ≤ d → f d ≤ f (f d) → f d ≤ ⨆ (↓ poset d ∩ post C≤ f≈)
      φ fd≤d fd≤ffd =
        let open PosetReasoning C≤ in
        begin
        f d ≤⟨ ⨆-upper (↓ poset d ∩ post C≤ f≈) (f d) (fd≤d , fd≤ffd) ⟩
        ⨆ (↓ poset d ∩ post C≤ f≈) ∎

  postGF : (R : Pred C≈) → (R ∈ post (Pred⊆-poset C≈) ⟦ G ∘-mono F ⟧cong)
  postGF R = GaloisConnection.η F⊣G R

  module _ where
    open GaloisConnection
    preGF-characterization : (R : Pred C≈) → R ∈ preRL F⊣G ↔ Is⨆Closed C⨆ R
    preGF-characterization R =
      let open SetoidReasoning (Prop↔-setoid) in
      begin
      R ∈ preRL F⊣G ≡⟨⟩
      (G-pred ∘ F-mono) R ⊆ R ≈⟨ λ- , _$- ⟩
      (∀ d → d ≤ ⨆ (↓≤ d ∩ R) → d ∈ R) ≈⟨ γ , γ⁻¹ ⟩
      (∀ S → S ⊆ R → ⨆ S ∈ R) ≡⟨⟩
      Is⨆Closed C⨆ R ∎
      where
      γ : (∀ d → d ≤ ⨆ (↓ poset d ∩ R) → d ∈ R) → ∀ S → S ⊆ R → ⨆ S ∈ R
      γ φ S S⊆R = φ (⨆ S) (⨆-mono S (↓≤ (⨆ S) ∩ R) \ {d} d∈S → ⨆-upper S d d∈S  , S⊆R d∈S)

      γ⁻¹ : (∀ S → S ⊆ R → ⨆ S ∈ R) → ∀ d → d ≤ ⨆ (↓≤ d ∩ R) → d ∈ R
      γ⁻¹ ψ d d≤⨆↓d∩R = R .Pred.isWellDefined (Po.antisym χ χ⁻¹)  (ψ (↓≤ d ∩ R) (∩-⊆-r (↓≤ d) R))
        where
        χ : ⨆ (↓≤ d ∩ R) ≤ d
        χ = Po.trans (⨆-mono _ _ (∩-⊆-l (↓≤ d) R)) (⨆-↓≤ d)

        χ⁻¹ : d ≤ ⨆ (↓≤ d ∩ R)
        χ⁻¹ = d≤⨆↓d∩R

module _ (D⨆ E⨆ : SLat) where

  private
    D×E⨆ = D⨆ ×-slat E⨆

    D×E≤ = SLat.poset D×E⨆
    D×E≈ = SLat.Eq.setoid D×E⨆

    D≤ = SLat.poset D⨆
    D≈ = SLat.Eq.setoid D⨆
    D = ∣ D⨆ ∣

    E≤ = SLat.poset E⨆
    E≈ = SLat.Eq.setoid E⨆
    E = ∣ E⨆ ∣

    module D = SLat D⨆
    module E = SLat E⨆
  open SLat (D⨆ ×-slat E⨆)
  open 𝒫⊆-and-Endo (D⨆ ×-slat E⨆)

  module _ where
    open GaloisConnection
    preGF-explicit : (R : Pred (D≈ ×-setoid E≈)) → R ∈ preRL F⊣G ↔ (((d , e) : D × E) → (d D.≤ D.⨆ ((↓≤ (d , e) ∩ R) ∣₁)) × (e E.≤ E.⨆ ((↓≤ (d , e) ∩ R) ∣₂)) → (d , e) ∈ R)
    preGF-explicit R =
      let open SetoidReasoning (Prop↔-setoid) in
      begin
      R ∈ preRL F⊣G                                                                                             ≡⟨⟩
      (G-raw ∘ F-raw) R UniR.⊆ Pred.⟦ R ⟧                                                                        ≈⟨ λ- , _$- ⟩
      (((d , e) : D × E) → d D.≤ D.⨆ ((↓≤ (d , e) ∩ R) ∣₁) × (e E.≤ E.⨆ ((↓≤ (d , e) ∩ R) ∣₂)) → (d , e) ∈ R) ∎

    preGF→⊔closed : (R : Pred (D≈ ×-setoid E≈))
                  → (((d , e) : D × E) → (d D.≤ D.⨆ ((↓≤ (d , e) ∩ R) ∣₁)) × (e E.≤ E.⨆ ((↓≤ (d , e) ∩ R) ∣₂)) → (d , e) ∈ R)
                  → (((d , e) : D × E) ((d₀ , e₀) : D × E) → (d₀ , e₀) ≤ (d , e) → (d₀ , e) ∈ R × (d , e₀) ∈ R → (d , e) ∈ R)
    preGF→⊔closed R ≤⨆↓∩→∈ (d , e) (d₀ , e₀) (d₀≤d , e₀≤e) (d₀e∈R , de₀∈R) = ≤⨆↓∩→∈ (d , e)
      ( D.⨆-upper ((↓≤ (d , e) ∩ R) ∣₁) d (e₀ , (D.Po.refl , e₀≤e) , de₀∈R)
      , E.⨆-upper ((↓≤ (d , e) ∩ R) ∣₂) e (d₀ , (d₀≤d , E.Po.refl) , d₀e∈R))

  -- We define the following galois connection
  --
  --     (D × E →m D × E , ≤)
  --        H₀ ↓ ⊣ ↑ I₀
  -- ((D × E →m D) × (D →m E) , ≤)

  -- H₀ : ((D≤ ×-poset E≤) →mono≤-poset (D≤ ×-poset E≤)) →mono (((D≤ ×-poset E≤) →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤))
  -- I₀ : (((D≤ ×-poset E≤) →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤)) →mono ((D≤ ×-poset E≤) →mono≤-poset (D≤ ×-poset E≤))
  -- H₀⊣I₀ : H₀ ⊣ I₀

  module _ where
    -- aux definitions
    H₀-raw : (D × E → D × E) → (D × E → D) × (D → E)
    H₀-raw f =
      ( (λ p → f p .proj₁)
      , (λ d → f (d , E.⊤) .proj₂))

    H₀-mono : (D×E≤ →mono D×E≤) → ((D×E≤ →mono D≤) × (D≤ →mono E≤))
    Mono.⟦ H₀-mono f .proj₁ ⟧ = H₀-raw ⟦ f ⟧ .proj₁
    H₀-mono f .proj₁ .Mono.isMonotone .IsMono.cong x≈y = f .Mono.cong x≈y .proj₁
    H₀-mono f .proj₁ .Mono.isMonotone .IsMono.mono x≤y = f .Mono.mono x≤y .proj₁
    Mono.⟦ H₀-mono f .proj₂ ⟧ = H₀-raw ⟦ f ⟧ .proj₂
    H₀-mono f .proj₂ .Mono.isMonotone .IsMono.cong x≈y = f .Mono.cong (x≈y , E.Eq.refl) .proj₂
    H₀-mono f .proj₂ .Mono.isMonotone .IsMono.mono x≤y = f .Mono.mono (x≤y , E.Po.refl) .proj₂

    I₀-raw : (D × E → D) × (D → E) → (D × E → D × E)
    I₀-raw (f⃖ , f⃗) (d , e) = (f⃖ (d , e) , f⃗ d)

    I₀-mono : ((D≤ ×-poset E≤) →mono D≤) × (D≤ →mono E≤) → ((D≤ ×-poset E≤) →mono (D≤ ×-poset E≤))
    Mono.⟦ I₀-mono (f⃖ , f⃗) ⟧ = I₀-raw (⟦ f⃖ ⟧ , ⟦ f⃗ ⟧)
    I₀-mono (f⃖  , f⃗) .Mono.isMonotone .IsMono.cong (d≈d' , e≈e') = ((f⃖ .Mono.isMonotone .IsMono.cong (d≈d' , e≈e')) , (f⃗ .Mono.isMonotone .IsMono.cong d≈d'))
    I₀-mono (f⃖  , f⃗) .Mono.isMonotone .IsMono.mono (d≤d' , e≤e') = ((f⃖ .Mono.isMonotone .IsMono.mono (d≤d' , e≤e')) , (f⃗ .Mono.isMonotone .IsMono.mono d≤d'))

  H₀ : ((D≤ ×-poset E≤) →mono≤-poset (D≤ ×-poset E≤)) →mono (((D≤ ×-poset E≤) →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤))
  Mono.⟦ H₀ ⟧ f = H₀-mono f
  H₀ .Mono.isMonotone .IsMono.cong f≈g = ((λ p → f≈g p .proj₁) , (λ d → f≈g (d , E.⊤) .proj₂))
  H₀ .Mono.isMonotone .IsMono.mono f≤g = ((λ p → f≤g p .proj₁) , (λ d → f≤g (d , E.⊤) .proj₂))

  I₀ : (((D≤ ×-poset E≤) →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤)) →mono ((D≤ ×-poset E≤) →mono≤-poset (D≤ ×-poset E≤))
  Mono.⟦ I₀ ⟧ = I₀-mono
  I₀ .Mono.isMonotone .IsMono.cong (f⃖≈g⃖ , f⃗≈g⃗) (d , e) = (f⃖≈g⃖ (d , e) , f⃗≈g⃗ d)
  I₀ .Mono.isMonotone .IsMono.mono (f⃖≤g⃖ , f⃗≤g⃗) (d , e) = (f⃖≤g⃖ (d , e) , f⃗≤g⃗ d)

  H₀⊣I₀ : H₀ ⊣ I₀
  H₀⊣I₀ .GaloisConnection.ψ f f⃡ .proj₁ H₀f≤f⃡ (d , e) = H₀f≤f⃡ .proj₁ (d , e) , E.Po.trans (IsMono.mono (proj₂-mono D≤ E≤) (f .Mono.mono (D.Po.refl , (E.⊤-max _))) ) (H₀f≤f⃡ .proj₂ d)
  H₀⊣I₀ .GaloisConnection.ψ f f⃡ .proj₂ f≤I₀f⃡ = ((λ p → f≤I₀f⃡ p .proj₁) , (λ d → f≤I₀f⃡ (d , E.⊤) .proj₂))

  F₀ : 𝒫⊆ →mono (((D≤ ×-poset E≤) →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤))
  F₀ = H₀ ∘-mono F

  G₀ : (((D≤ ×-poset E≤) →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤)) →mono 𝒫⊆
  G₀ = G ∘-mono I₀

  F₀⊣G₀ : F₀ ⊣ G₀
  F₀⊣G₀ = F⊣G ∘-galois H₀⊣I₀

  IsTiltBowTie : (R : Pred (D≈ ×-setoid E≈)) → (d : D) (e : E) (d₀ : D) (e₀ : E) (e₁ : E) → Set
  IsTiltBowTie R d e d₀ e₀ e₁ = (d₀ D.≤ d) × (e₀ E.≤ e) × (e E.≤ e₁) × (d₀ , e₁) ∈ R × (d , e₀) ∈ R

  tiltbowtie→≤⨆ : (R : Pred (D≈ ×-setoid E≈)) → ∀ d e → Σ d₀ ∶ D , Σ e₀ ∶ E , Σ e₁ ∶ E , IsTiltBowTie R d e d₀ e₀ e₁ → d D.≤ (D.⨆ ((↓≤ (d , e) ∩ R) ∣₁)) × e E.≤ (E.⨆ ((↓≤ (d , E.⊤) ∩ R) ∣₂))
  tiltbowtie→≤⨆ R d e (d₀ , e₀ , e₁ , d₀≤d , e₀≤e , e≤e₁ , d₀e₁∈R , de₀∈R) =
    ( D.⨆-upper ((↓≤ (d , e) ∩ R) ∣₁) d (e₀ , (D.Po.refl , e₀≤e) , de₀∈R)
    , E.Po.trans e≤e₁ (E.⨆-upper ((↓≤ (d , E.⊤) ∩ R) ∣₂) e₁ (d₀ , (d₀≤d , E.⊤-max _) , d₀e₁∈R)))

  IsTiltBowTieClosed : (R : Pred (D≈ ×-setoid E≈)) → Set
  IsTiltBowTieClosed R = (∀ d e d₀ e₀ e₁ → IsTiltBowTie R d e d₀ e₀ e₁ → (d , e) ∈ R)

  module _ where
    open GaloisConnection
    preG₀F₀-explicit : (R : Pred (D≈ ×-setoid E≈)) → (R ∈ preRL F₀⊣G₀) ↔ (((d , e) : D × E) → (d D.≤ D.⨆ ((↓≤ (d , e) ∩ R) ∣₁)) × (e E.≤ E.⨆ ((↓≤ (d , E.⊤) ∩ R) ∣₂)) → (d , e) ∈ R)
    preG₀F₀-explicit R = (λ- , _$-)

    preG₀F₀-characterization : (R : Pred (D≈ ×-setoid E≈)) → (R ∈ preRL F₀⊣G₀) ↔ (∀ d e d₀ e₀ e₁ → IsTiltBowTie R d e d₀ e₀ e₁ → (d , e) ∈ R) × Is⨆Closed (D⨆ ×-slat E⨆) R
    preG₀F₀-characterization R = (α , α⁻¹)
     where
     α₁ : (R ∈ preRL F₀⊣G₀) → (∀ d e d₀ e₀ e₁ → IsTiltBowTie R d e d₀ e₀ e₁ → (d , e) ∈ R)
     α₁ R∈preG₀F₀ d e d₀ e₀ e₁ tiltbowtie = R∈preG₀F₀ (tiltbowtie→≤⨆ R d e (d₀ , e₀ , e₁ , tiltbowtie))

     α₂ : (R ∈ preRL F₀⊣G₀) → Is⨆Closed (D⨆ ×-slat E⨆) R
     α₂ = preGF-characterization R .proj₁ ∘ preRL-∘-⊆ F⊣G H₀⊣I₀ {R}

     α : (R ∈ preRL F₀⊣G₀) → (∀ d e d₀ e₀ e₁ → IsTiltBowTie R d e d₀ e₀ e₁ → (d , e) ∈ R) × Is⨆Closed (D⨆ ×-slat E⨆) R
     α = Product.< α₁ , α₂ >

     α⁻¹ : (∀ d e d₀ e₀ e₁ → IsTiltBowTie R d e d₀ e₀ e₁ → (d , e) ∈ R) × Is⨆Closed (D⨆ ×-slat E⨆) R → (R ∈ preRL F₀⊣G₀)
     α⁻¹ (tiltbowtie→R , ⨆closed) {(d , e)} (d≤⨆↓de∩R∣₁ , e≤⨆↓d⊤∩R∣₂) =
        tiltbowtie→R d e (D.⨆ ((↓≤ (d , E.⊤) ∩ R) ∣₁)) (E.⨆ ((↓≤ (d , e) ∩ R) ∣₂)) (E.⨆ ((↓≤ (d , E.⊤) ∩ R) ∣₂))
          ( d≥⨆↓d⊤∩R∣₁
          , e≥⨆↓de∩R∣₂
          , e≤⨆↓d⊤∩R∣₂
          , ⨆closed (↓≤ (d , E.⊤) ∩ R) (∩-⊆-r (↓≤ (d , E.⊤)) R)
          , R .Pred.isWellDefined (D.Eq.sym d≈⨆↓de∩R∣₁ , E.Eq.refl) (⨆closed (↓≤ (d , e) ∩ R) (∩-⊆-r (↓≤ (d , e)) R)))
        where
        d≥⨆↓d⊤∩R∣₁ : D.⨆ ((↓≤ (d , E.⊤) ∩ R) ∣₁) D.≤ d
        d≥⨆↓d⊤∩R∣₁ = D.⨆-least ((↓≤ (d , E.⊤) ∩ R) ∣₁) d (λ d₀ (e₀ , (d₀≤d , e₀≤e) , d₀e₀∈R) → d₀≤d)

        e≥⨆↓de∩R∣₂ : E.⨆ ((↓≤ (d , e) ∩ R) ∣₂) E.≤ e
        e≥⨆↓de∩R∣₂ = E.⨆-least ((↓≤ (d , e) ∩ R) ∣₂) e (λ d₀ (e₀ , (d₀≤d , e₀≤e) , d₀e₀∈R) → e₀≤e)

        d≥⨆↓de∩R∣₁ : D.⨆ ((↓≤ (d , e) ∩ R) ∣₁) D.≤ d
        d≥⨆↓de∩R∣₁ = D.⨆-least ((↓≤ (d , e) ∩ R) ∣₁) d (λ d₀ (e₀ , (d₀≤d , e₀≤e) , d₀e₀∈R) → d₀≤d)

        d≈⨆↓de∩R∣₁ : d D.≈ D.⨆ ((↓≤ (d , e) ∩ R) ∣₁)
        d≈⨆↓de∩R∣₁ = D.Po.antisym d≤⨆↓de∩R∣₁ d≥⨆↓de∩R∣₁


  -- We define the following galois connection
  --
  -- ((D × E →m D) × (D →m E) , ≤)
  --        H₁ ↓ ⊣ ↑ I₁
  -- ((E →m D) × (D →m E) , ≤)

  -- H₁ : (((D≤ ×-poset E≤) →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤)) →mono ((E≤ →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤))
  -- I₁ : ((E≤ →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤)) →mono (((D≤ ×-poset E≤) →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤))
  -- H₁⊣I₁ : H₁ ⊣ I₁

  module _ where
    -- aux definitions

    H₁-raw : (D × E → D) × (D → E) → (E → D) × (D → E)
    H₁-raw (f⃖ , f⃗) =
      ( (λ e → f⃖ (D.⊤ , e))
      , (λ d → f⃗ d))

    H₁-mono : ((D≤ ×-poset E≤) →mono D≤) × (D≤ →mono E≤) → (E≤ →mono D≤) × (D≤ →mono E≤)
    Mono.⟦ H₁-mono (f⃖ , f⃗) .proj₁ ⟧ = H₁-raw (⟦ f⃖ ⟧ , ⟦ f⃗ ⟧) .proj₁
    H₁-mono (f⃖ , f⃗) .proj₁ .Mono.isMonotone .IsMono.cong e≈e' = f⃖ .Mono.isMonotone .IsMono.cong (D.Eq.refl , e≈e')
    H₁-mono (f⃖ , f⃗) .proj₁ .Mono.isMonotone .IsMono.mono e≤e' = f⃖ .Mono.isMonotone .IsMono.mono (D.Po.refl , e≤e')
    Mono.⟦ H₁-mono (f⃖ , f⃗) .proj₂ ⟧ = H₁-raw (⟦ f⃖ ⟧ , ⟦ f⃗ ⟧) .proj₂
    H₁-mono (f⃖ , f⃗) .proj₂ .Mono.isMonotone .IsMono.cong d≈d' = f⃗ .Mono.isMonotone .IsMono.cong d≈d'
    H₁-mono (f⃖ , f⃗) .proj₂ .Mono.isMonotone .IsMono.mono d≤d' = f⃗ .Mono.isMonotone .IsMono.mono d≤d'

    I₁-raw : (E → D) × (D → E) → (D × E → D) × (D → E)
    I₁-raw (f⃖ , f⃗) = (λ p → f⃖ (p .proj₂)) , f⃗

    I₁-mono : (E≤ →mono D≤) × (D≤ →mono E≤) → ((D≤ ×-poset E≤) →mono D≤) × (D≤ →mono E≤)
    Mono.⟦ I₁-mono (f⃖ , f⃗) .proj₁ ⟧ = I₁-raw (⟦ f⃖ ⟧ , ⟦ f⃗ ⟧) .proj₁
    I₁-mono (f⃖ , f⃗) .proj₁ .Mono.isMonotone .IsMono.cong (d≈d' , e≈e') = f⃖ .Mono.isMonotone .IsMono.cong e≈e'
    I₁-mono (f⃖ , f⃗) .proj₁ .Mono.isMonotone .IsMono.mono (d≈d' , e≤e') = f⃖ .Mono.isMonotone .IsMono.mono e≤e'
    Mono.⟦ I₁-mono (f⃖ , f⃗) .proj₂ ⟧ = I₁-raw (⟦ f⃖ ⟧ , ⟦ f⃗ ⟧) .proj₂
    I₁-mono (f⃖ , f⃗) .proj₂ .Mono.isMonotone .IsMono.cong d≈d' = f⃗ .Mono.isMonotone .IsMono.cong d≈d'
    I₁-mono (f⃖ , f⃗) .proj₂ .Mono.isMonotone .IsMono.mono d≤d' = f⃗ .Mono.isMonotone .IsMono.mono d≤d'

  H₁ : (((D≤ ×-poset E≤) →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤)) →mono ((E≤ →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤))
  Mono.⟦ H₁ ⟧ = H₁-mono
  H₁ .Mono.isMonotone .IsMono.cong (f⃖≈g⃖ , f⃗≈g⃗) = ((λ e → f⃖≈g⃖ (D.⊤ , e)) , (λ d → f⃗≈g⃗ d))
  H₁ .Mono.isMonotone .IsMono.mono (f⃖≤g⃖ , f⃗≤g⃗) = ((λ e → f⃖≤g⃖ (D.⊤ , e)) , (λ d → f⃗≤g⃗ d))

  I₁ : ((E≤ →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤)) →mono (((D≤ ×-poset E≤) →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤))
  Mono.⟦ I₁ ⟧ = I₁-mono
  I₁ .Mono.isMonotone .IsMono.cong (f⃖≈g⃖ , f⃗≈g⃗) = ((λ p → f⃖≈g⃖ (p .proj₂)) , (λ d → f⃗≈g⃗ d))
  I₁ .Mono.isMonotone .IsMono.mono (f⃖≤g⃖ , f⃗≤g⃗) = ((λ p → f⃖≤g⃖ (p .proj₂)) , (λ d → f⃗≤g⃗ d))

  H₁⊣I₁ : H₁ ⊣ I₁
  H₁⊣I₁ .GaloisConnection.ψ f⃡ g⃡ .proj₁ H₁f⃡≤g⃡ = ((λ p → D.Po.trans (f⃡ .proj₁ .Mono.mono ((D.⊤-max _) , E.Po.refl)) (H₁f⃡≤g⃡ .proj₁ (p .proj₂))) , (λ d → H₁f⃡≤g⃡ .proj₂ d))
  H₁⊣I₁ .GaloisConnection.ψ f⃡ g⃡ .proj₂ f⃡≤I₁g⃡ = ((λ e → f⃡≤I₁g⃡ .proj₁ (D.⊤ , e)) , (λ d → f⃡≤I₁g⃡ .proj₂ d))

  F₁ : 𝒫⊆ →mono ((E≤ →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤))
  F₁ = H₁ ∘-mono F₀

  G₁ : ((E≤ →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤)) →mono 𝒫⊆
  G₁ = G₀ ∘-mono I₁

  F₁⊣G₁ : F₁ ⊣ G₁
  F₁⊣G₁ = F₀⊣G₀ ∘-galois H₁⊣I₁

  IsBowTie : (R : Pred (D≈ ×-setoid E≈)) → (d : D) (e : E) (d₀ : D) (e₀ : E) (d₁ : D) (e₁ : E) → Set
  IsBowTie R d e d₀ e₀ d₁ e₁ = d₀ D.≤ d × e₀ E.≤ e × d D.≤ d₁ × e E.≤ e₁ × (d₀ , e₁) ∈ R × (d₁ , e₀) ∈ R

  IsBowTieClosed : (R : Pred (D≈ ×-setoid E≈)) → Set
  IsBowTieClosed R = ∀ d e d₀ e₀ d₁ e₁ → IsBowTie R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R


  bowtie→≤⨆ : (R : Pred (D≈ ×-setoid E≈)) → ∀ d e → Σ d₀ ∶ D , Σ e₀ ∶ E , Σ d₁ ∶ D , Σ e₁ ∶ E , IsBowTie R d e d₀ e₀ d₁ e₁ → d D.≤ (D.⨆ ((↓≤ (D.⊤ , e) ∩ R) ∣₁)) × e E.≤ (E.⨆ ((↓≤ (d , E.⊤) ∩ R) ∣₂))
  bowtie→≤⨆ R d e (d₀ , e₀ , d₁ , e₁ , d₀≤d , e₀≤e , d≤d₁ , e≤e₁ , d₀e₁∈R , d₁e₀∈R) =
    ( D.Po.trans d≤d₁ (D.⨆-upper ((↓≤ (D.⊤ , e) ∩ R) ∣₁) d₁ (e₀ , (D.⊤-max _ , e₀≤e) , d₁e₀∈R))
    , E.Po.trans e≤e₁ (E.⨆-upper ((↓≤ (d , E.⊤) ∩ R) ∣₂) e₁ (d₀ , (d₀≤d , E.⊤-max _) , d₀e₁∈R)))

  module _ where
    open GaloisConnection
    preG₁F₁-explicit : (R : Pred (D≈ ×-setoid E≈))
      → (R ∈ preRL F₁⊣G₁)
      ↔ (((d , e) : D × E) → (d D.≤ D.⨆ ((↓≤ (D.⊤ , e) ∩ R) ∣₁)) × (e E.≤ E.⨆ ((↓≤ (d , E.⊤) ∩ R) ∣₂)) → (d , e) ∈ R)
    preG₁F₁-explicit R = (λ- , _$-)

    preG₁F₁-characterization : (R : Pred (D≈ ×-setoid E≈)) → (R ∈ preRL F₁⊣G₁) ↔ (∀ d e d₀ e₀ d₁ e₁ → IsBowTie R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R) × (Is⨆Closed (D⨆ ×-slat E⨆) R)
    preG₁F₁-characterization R = (α , α⁻¹)
      where
      α₁ : (R ∈ preRL F₁⊣G₁) → (∀ d e d₀ e₀ d₁ e₁ → IsBowTie R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R)
      α₁ R∈preG₀F₀ d e d₀ e₀ d₁ e₁ bowtie = R∈preG₀F₀ (bowtie→≤⨆ R d e (d₀ , e₀ , d₁ , e₁ , bowtie))

      α₂ : (R ∈ preRL F₁⊣G₁) → (Is⨆Closed (D⨆ ×-slat E⨆) R)
      α₂ = preGF-characterization R .proj₁ ∘ preRL-∘-⊆ F⊣G (H₀⊣I₀ ∘-galois H₁⊣I₁) {R}

      α : (R ∈ preRL F₁⊣G₁) → (∀ d e d₀ e₀ d₁ e₁ → IsBowTie R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R) × Is⨆Closed (D⨆ ×-slat E⨆) R
      α = Product.< α₁ , α₂ >

      α⁻¹ : (∀ d e d₀ e₀ d₁ e₁ → IsBowTie R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R) × Is⨆Closed (D⨆ ×-slat E⨆) R → (R ∈ preRL F₁⊣G₁)
      α⁻¹ (bowtie→R , ⨆closed) {(d , e)} (d≤⨆↓⊤e∩R∣₁ , e≤⨆↓d⊤∩R∣₂) =
         bowtie→R d e
           (D.⨆ ((↓≤ (d , E.⊤) ∩ R) ∣₁)) (E.⨆ ((↓≤ (D.⊤ , e) ∩ R) ∣₂))
           (D.⨆ ((↓≤ (D.⊤ , e) ∩ R) ∣₁)) (E.⨆ ((↓≤ (d , E.⊤) ∩ R) ∣₂))
           ( d≥⨆↓d⊤∩R∣₁ , e≥⨆↓⊤e∩R∣₂
           , d≤⨆↓⊤e∩R∣₁ , e≤⨆↓d⊤∩R∣₂
           , ⨆closed (↓≤ (d , E.⊤) ∩ R) (∩-⊆-r (↓≤ (d , E.⊤)) R)
           , ⨆closed (↓≤ (D.⊤ , e) ∩ R) (∩-⊆-r (↓≤ (D.⊤ , e)) R))
         where
         d≥⨆↓d⊤∩R∣₁ : D.⨆ ((↓≤ (d , E.⊤) ∩ R) ∣₁) D.≤ d
         d≥⨆↓d⊤∩R∣₁ = D.⨆-least ((↓≤ (d , E.⊤) ∩ R) ∣₁) d (λ d₀ (e₀ , (d₀≤d , e₀≤e) , d₀e₀∈R) → d₀≤d)

         e≥⨆↓⊤e∩R∣₂ : E.⨆ ((↓≤ (D.⊤ , e) ∩ R) ∣₂) E.≤ e
         e≥⨆↓⊤e∩R∣₂ = E.⨆-least ((↓≤ (D.⊤ , e) ∩ R) ∣₂) e (λ d₀ (e₀ , (d₀≤d , e₀≤e) , d₀e₀∈R) → e₀≤e)

  -- We define the following galois connection
  --
  -- ((E →m D) × (D →m E) , ≤)
  --        H₂ ↓ ⊣ ↑ I₂
  --   ((E →m D) × E , ≤⨆↓∩→∈)

  -- H₂ : ((E≤ →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤)) →mono ((E≤ →mono≤-poset D≤) ×-poset E≤)
  -- I₂ : ((E≤ →mono≤-poset D≤) ×-poset E≤) →mono ((E≤ →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤))
  -- H₂⊣I₂ : H₂ ⊣ I₂

  module _ where
    H₂-raw : (E → D) × (D → E) → (E → D) × E
    H₂-raw (f⃖ , f⃗) = (f⃖ , f⃗ D.⊤)

    H₂-mono : (E≤ →mono D≤) × (D≤ →mono E≤) → (E≤ →mono D≤) × E
    Mono.⟦ H₂-mono (f⃖ , f⃗) .proj₁ ⟧ = H₂-raw (⟦ f⃖ ⟧ , ⟦ f⃗ ⟧) .proj₁ 
    H₂-mono (f⃖ , f⃗) .proj₁ .Mono.isMonotone .IsMono.cong e≈e' = f⃖ .Mono.isMonotone .IsMono.cong e≈e'
    H₂-mono (f⃖ , f⃗) .proj₁ .Mono.isMonotone .IsMono.mono e≤e' = f⃖ .Mono.isMonotone .IsMono.mono e≤e'
    H₂-mono (f⃖ , f⃗) .proj₂ = H₂-raw (⟦ f⃖ ⟧ , ⟦ f⃗ ⟧) .proj₂

    I₂-raw : (E → D) × E → (E → D) × (D → E)
    I₂-raw (f⃖ , e₀) = (f⃖ , const e₀)

    I₂-mono : (E≤ →mono D≤) × E → (E≤ →mono D≤) × (D≤ →mono E≤)
    Mono.⟦ I₂-mono (f⃖ , e₀) .proj₁ ⟧ = I₂-raw (⟦ f⃖ ⟧ , e₀) .proj₁
    I₂-mono (f⃖ , e₀) .proj₁ .Mono.isMonotone .IsMono.cong e≈e' = f⃖ .Mono.isMonotone .IsMono.cong e≈e'
    I₂-mono (f⃖ , e₀) .proj₁ .Mono.isMonotone .IsMono.mono e≤e' = f⃖ .Mono.isMonotone .IsMono.mono e≤e'
    Mono.⟦ I₂-mono (f⃖ , e₀) .proj₂ ⟧ = I₂-raw (⟦ f⃖ ⟧ , e₀) .proj₂
    I₂-mono (f⃖ , e₀) .proj₂ .Mono.isMonotone .IsMono.cong d≈d' = E.Eq.refl
    I₂-mono (f⃖ , e₀) .proj₂ .Mono.isMonotone .IsMono.mono d≤d' = E.Po.refl

  H₂ : ((E≤ →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤)) →mono ((E≤ →mono≤-poset D≤) ×-poset E≤)
  Mono.⟦ H₂ ⟧ = H₂-mono
  H₂ .Mono.isMonotone .IsMono.cong f⃡≈g⃡ = ((λ e → f⃡≈g⃡ .proj₁ e) , f⃡≈g⃡ .proj₂ D.⊤)
  H₂ .Mono.isMonotone .IsMono.mono f⃡≤g⃡ = ((λ e → f⃡≤g⃡ .proj₁ e) , f⃡≤g⃡ .proj₂ D.⊤)

  I₂ : ((E≤ →mono≤-poset D≤) ×-poset E≤) →mono ((E≤ →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤))
  Mono.⟦ I₂ ⟧ = I₂-mono
  I₂ .Mono.isMonotone .IsMono.cong (f≈g , e₀≈e₀') = (f≈g , const e₀≈e₀')
  I₂ .Mono.isMonotone .IsMono.mono (f≤g , e₀≤e₀') = (f≤g , const e₀≤e₀')

  H₂⊣I₂ : H₂ ⊣ I₂
  H₂⊣I₂ .GaloisConnection.ψ f⃡ g⃖e₀ .proj₁ H₂f⃡≤g⃖e₀ = ((λ e → H₂f⃡≤g⃖e₀ .proj₁ e) , (λ d → E.Po.trans (f⃡ .proj₂ .Mono.mono (D.⊤-max d)) (H₂f⃡≤g⃖e₀ .proj₂)))
  H₂⊣I₂ .GaloisConnection.ψ f⃡ g⃖e₀ .proj₂ f⃡≤I₂g⃖e₀ = ((λ e → f⃡≤I₂g⃖e₀ .proj₁ e) , f⃡≤I₂g⃖e₀ .proj₂ D.⊤)

  F₂ : 𝒫⊆ →mono ((E≤ →mono≤-poset D≤) ×-poset E≤)
  F₂ = H₂ ∘-mono F₁

  G₂ : ((E≤ →mono≤-poset D≤) ×-poset E≤) →mono 𝒫⊆
  G₂ = G₁ ∘-mono I₂

  F₂⊣G₂ : F₂ ⊣ G₂
  F₂⊣G₂ = F₁⊣G₁ ∘-galois H₂⊣I₂

  IsFan : (R : Pred (D≈ ×-setoid E≈)) → (d : D) (e : E) (d₀ : D) (e₀ : E) (d₁ : D) (e₁ : E) → Set
  IsFan R d e d₀ e₀ d₁ e₁ = e₀ E.≤ e × d D.≤ d₁ × e E.≤ e₁ × (d₀ , e₁) ∈ R × (d₁ , e₀) ∈ R

  IsFanClosed : (R : Pred (D≈ ×-setoid E≈)) → Set
  IsFanClosed R = ∀ d e d₀ e₀ d₁ e₁ → IsFan R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R

  fan→≤⨆ : (R : Pred (D≈ ×-setoid E≈))
    → ∀ d e
    → Σ d₀ ∶ D , Σ e₀ ∶ E , Σ d₁ ∶ D , Σ e₁ ∶ E , IsFan R d e d₀ e₀ d₁ e₁
    → d D.≤ D.⨆ ((↓≤ (D.⊤ , e) ∩ R) ∣₁) × e E.≤ E.⨆ ((↓≤ ⊤ ∩ R) ∣₂)
  fan→≤⨆ R d e (d₀ , e₀ , d₁ , e₁ , e₀≤e , d≤d₁ , e≤e₁ , d₀e₁∈R , d₁e₀∈R) =
    ( D.Po.trans d≤d₁ (D.⨆-upper ((↓≤ (D.⊤ , e) ∩ R) ∣₁) d₁ (e₀ , (D.⊤-max _ , e₀≤e) , d₁e₀∈R))
    , E.Po.trans e≤e₁ (E.⨆-upper ((↓≤ ⊤ ∩ R) ∣₂) e₁ (d₀ , ⊤-max _ , d₀e₁∈R)))

  module _ where
    open GaloisConnection
    preG₂F₂-explicit : (R : Pred (D≈ ×-setoid E≈))
      → (R ∈ preRL F₂⊣G₂)
      ↔ (((d , e) : D × E) → d D.≤ D.⨆ ((↓≤ (D.⊤ , e) ∩ R) ∣₁) × e E.≤ E.⨆ ((↓≤ ⊤ ∩ R) ∣₂) → (d , e) ∈ R)
    preG₂F₂-explicit R = (λ- , _$-)

    preG₂F₂-characterization : (R : Pred (D≈ ×-setoid E≈))
      → (R ∈ preRL F₂⊣G₂)
      ↔ ((∀ d e d₀ e₀ d₁ e₁ → IsFan R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R) × (Is⨆Closed (D⨆ ×-slat E⨆) R))
    preG₂F₂-characterization R = (α , α⁻¹)
     where
     α₁ : (R ∈ preRL F₂⊣G₂) → (∀ d e d₀ e₀ d₁ e₁ → IsFan R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R)
     α₁ R∈preG₂F₂ d e d₀ e₀ d₁ e₁ fan = R∈preG₂F₂ (fan→≤⨆ R d e (d₀ , e₀ , d₁ , e₁ , fan))

     α₂ : (R ∈ preRL F₂⊣G₂) → Is⨆Closed (D⨆ ×-slat E⨆) R
     α₂ = preGF-characterization R .proj₁ ∘ preRL-∘-⊆ F⊣G (H₀⊣I₀ ∘-galois H₁⊣I₁ ∘-galois H₂⊣I₂) {R}

     α : (R ∈ preRL F₂⊣G₂) → (∀ d e d₀ e₀ d₁ e₁ → IsFan R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R) × Is⨆Closed (D⨆ ×-slat E⨆) R
     α = Product.< α₁ , α₂ >

     α⁻¹ : ((∀ d e d₀ e₀ d₁ e₁ → IsFan R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R) × Is⨆Closed (D⨆ ×-slat E⨆) R) → (R ∈ preRL F₂⊣G₂)
     α⁻¹ (fan→R , ⨆closed) {(d , e)} (d≤⨆↓⊤e∩R∣₁ , e≤⨆↓⊤⊤∩R∣₂) =
       fan→R d e
         (D.⨆ ((↓≤ ⊤ ∩ R) ∣₁)) (E.⨆ ((↓≤ (D.⊤ , e) ∩ R) ∣₂))
         (D.⨆ ((↓≤ (D.⊤ , e) ∩ R) ∣₁)) (E.⨆ ((↓≤ ⊤ ∩ R) ∣₂))
         ( E.⨆-least _ _ (λ e₀ (d₀ , (d₀≤⊤ , e₀≤e) , d₀e₀∈R) → e₀≤e)
         , d≤⨆↓⊤e∩R∣₁
         , e≤⨆↓⊤⊤∩R∣₂
         , ⨆closed (↓≤ ⊤ ∩ R) (∩-⊆-r (↓≤ ⊤) R)
         , ⨆closed (↓≤ (D.⊤ , e) ∩ R) (∩-⊆-r (↓≤ (D.⊤ , e)) R))

  -- We define the following galois connection
  --
  -- ((E →m D) × E , ≤)
  --   H₃ ↓ ⊣ ↑ I₃
  -- ((E →m D) , ≤)

  module _ where
    H₃-raw : (E → D) × E → (E → D)
    H₃-raw (f⃖ , e₀) = f⃖

    H₃-mono : (E≤ →mono D≤) × E → (E≤ →mono D≤)
    H₃-mono (f⃖ , e₀) = f⃖

    I₃-raw : (E → D) → (E → D) × E
    I₃-raw f⃖ = (f⃖ , E.⊤)

    I₃-mono : (E≤ →mono D≤) → (E≤ →mono D≤) × E
    I₃-mono f⃖ = (f⃖ , E.⊤)

  H₃ : ((E≤ →mono≤-poset D≤) ×-poset E≤) →mono (E≤ →mono≤-poset D≤)
  Mono.⟦ H₃ ⟧ = H₃-mono
  H₃ .Mono.isMonotone .IsMono.cong f⃖ᶜ≈g⃖ᶜ e = f⃖ᶜ≈g⃖ᶜ .proj₁ e
  H₃ .Mono.isMonotone .IsMono.mono f⃖ᶜ≤g⃖ᶜ e = f⃖ᶜ≤g⃖ᶜ .proj₁ e

  I₃ : (E≤ →mono≤-poset D≤) →mono ((E≤ →mono≤-poset D≤) ×-poset E≤)
  Mono.⟦ I₃ ⟧ = I₃-mono
  I₃ .Mono.isMonotone .IsMono.cong f⃖≈g⃖ = f⃖≈g⃖ , E.Eq.refl
  I₃ .Mono.isMonotone .IsMono.mono f⃖≤g⃖ = f⃖≤g⃖ , E.Po.refl

  H₃⊣I₃ : H₃ ⊣ I₃
  H₃⊣I₃ .GaloisConnection.ψ f⃖ᶜ f⃖ .proj₁ H₃f⃖ᶜ≤f⃖ = (λ e → H₃f⃖ᶜ≤f⃖ e) , E.⊤-max _
  H₃⊣I₃ .GaloisConnection.ψ f⃖ᶜ f⃖ .proj₂ f⃖ᶜ≤I₃f⃖ e = f⃖ᶜ≤I₃f⃖ .proj₁ e

  F₃ : 𝒫⊆ →mono (E≤ →mono≤-poset D≤)
  F₃ = H₃ ∘-mono F₂

  G₃ : (E≤ →mono≤-poset D≤) →mono 𝒫⊆
  G₃ = G₂ ∘-mono I₃

  F₃⊣G₃ : F₃ ⊣ G₃
  F₃⊣G₃ = F₂⊣G₂ ∘-galois H₃⊣I₃

  IsTilt : (R : Pred (D≈ ×-setoid E≈)) → (d : D) (e : E) (e₀ : E) (d₁ : D) → Set
  IsTilt R d e e₀ d₁ = e₀ E.≤ e × d D.≤ d₁ × (d₁ , e₀) ∈ R

  IsTiltClosed : (R : Pred (D≈ ×-setoid E≈)) → Set
  IsTiltClosed R = ∀ d e e₀ d₁ → IsTilt R d e e₀ d₁ → (d , e) ∈ R

  tilt→≤⨆ : (R : Pred (D≈ ×-setoid E≈)) → ∀ d e → (Σ e₀ ∶ E , Σ d₁ ∶ D , IsTilt R d e e₀ d₁) → d D.≤ D.⨆ ((↓≤ (D.⊤ , e) ∩ R) ∣₁) × e E.≤ E.⊤
  tilt→≤⨆ R d e (e₀ , d₁ , e₀≤e , d≤d₁ , d₁e₀∈R) =
    ( D.Po.trans d≤d₁ (D.⨆-upper ((↓≤ (D.⊤ , e) ∩ R) ∣₁) d₁ (e₀ , ((D.⊤-max d₁ , e₀≤e) , d₁e₀∈R)))
    , E.⊤-max e)

  module _ where
    open GaloisConnection
    preG₃F₃-explicit : (R : Pred (D≈ ×-setoid E≈))
      → (R ∈ preRL F₃⊣G₃)
      ↔ (((d , e) : D × E) → d D.≤ D.⨆ ((↓≤ (D.⊤ , e) ∩ R) ∣₁) × e E.≤ E.⊤ → (d , e) ∈ R)
    preG₃F₃-explicit R = (λ- , _$-)

    preG₃F₃-characterization : (R : Pred (D≈ ×-setoid E≈))
      → (R ∈ preRL F₃⊣G₃)
      ↔ (∀ d e e₀ d₁ → IsTilt R d e e₀ d₁ → (d , e) ∈ R) × (Is⨆Closed (D⨆ ×-slat E⨆) R)
    preG₃F₃-characterization R = (α , α⁻¹)
      where
      α₁ : (R ∈ preRL F₃⊣G₃) → (∀ d e e₀ d₁ → IsTilt R d e e₀ d₁ → (d , e) ∈ R)
      α₁ R∈preG₃F₃ d e e₀ d₁ tilt = R∈preG₃F₃ (tilt→≤⨆ R d e (e₀ , d₁ , tilt))

      α₂ : (R ∈ preRL F₃⊣G₃) → (Is⨆Closed (D⨆ ×-slat E⨆) R)
      α₂ = preGF-characterization R .proj₁ ∘ preRL-∘-⊆ F⊣G (H₀⊣I₀ ∘-galois H₁⊣I₁ ∘-galois H₂⊣I₂ ∘-galois H₃⊣I₃) {R}

      α : R ∈ preRL F₃⊣G₃ → (∀ d e e₀ d₁ → IsTilt R d e e₀ d₁ → (d , e) ∈ R) × (Is⨆Closed (D⨆ ×-slat E⨆) R)
      α = Product.< α₁ , α₂ >

      α⁻¹ : (∀ d e e₀ d₁ → IsTilt R d e e₀ d₁ → (d , e) ∈ R) × (Is⨆Closed (D⨆ ×-slat E⨆) R) → R ∈ preRL F₃⊣G₃
      α⁻¹ (tilt→R , ⨆closed) {(d , e)} (d≤⨆↓⊤e∩R∣₁ , e≤⊤) =
        tilt→R d e
          (proj₂ (⨆ (↓≤ (D.⊤ , e) ∩ R))) (proj₁ (⨆ (↓≤ (D.⊤ , e) ∩ R)))
          (e≥⨆↓⊤e∩R∣₂ , d≤⨆↓⊤e∩R∣₁ , ⨆closed (↓≤ (D.⊤ , e) ∩ R) (∩-⊆-r (↓≤ (D.⊤ , e)) R))
        where
        e≥⨆↓⊤e∩R∣₂ : E.⨆ ((↓≤ (D⨆ .SLat.⊤ , e) ∩ R) ∣₂) E.≤ e
        e≥⨆↓⊤e∩R∣₂ = E.⨆-least ((↓≤ (D⨆ .SLat.⊤ , e) ∩ R) ∣₂) e (λ e₀ (d₁ , ((d₁≤⊤ , e₀≤e) , d₁e₀∈R)) → e₀≤e)


module _ {C D : Poset} (F : C →mono D) where
  -- Definition of monoidal properties for non-indexed binary operation on poset maps
  open PosetPoly D
  -- probably monoidal is not a right word for this property (it only refers to multiplication and not to unit)

  IsLaxMonoidal : (_⊗C_ : Op₂ ∣ C ∣) (_⊗D_ : Op₂ ∣ D ∣) → Set
  IsLaxMonoidal _⊗C_ _⊗D_ = (a b : ∣ C ∣ ) → ⟦ F ⟧ a ⊗D ⟦ F ⟧ b ≤ ⟦ F ⟧ (a ⊗C b)

  IsOplaxMonoidal : (_⊗C_ : Op₂ ∣ C ∣) (_⊗D_ : Op₂ ∣ D ∣) → Set
  IsOplaxMonoidal _⊗C_ _⊗D_ = (a b : ∣ C ∣ ) → ⟦ F ⟧ (a ⊗C b) ≤ ⟦ F ⟧ a ⊗D ⟦ F ⟧ b

  IsMonoidal : (_⊗C_ : Op₂ ∣ C ∣) (_⊗D_ : Op₂ ∣ D ∣) → Set
  IsMonoidal _⊗C_ _⊗D_ = (a b : ∣ C ∣ ) → ⟦ F ⟧ (a ⊗C b) ≈ ⟦ F ⟧ a ⊗D ⟦ F ⟧ b

module _ {C D : Poset}  {L : C →mono D} {R : D →mono C} where
  -- Definition of lifting of (non-indexed) binary operation on a poset along with an adjunction
  liftOpAlong⊣ : (L⊣R : L ⊣ R) (_⊗C_ : Op₂ ∣ C ∣) → Op₂ ∣ D ∣
  liftOpAlong⊣ L⊣R _⊗C_ a b = ⟦ L ⟧ (⟦ R ⟧ a ⊗C ⟦ R ⟧ b)


module _
  (C≈ : Setoid) where
  -- General results about ∩ and its lift along with any ⊣

  private
    𝒫⊆ = Pred⊆-poset C≈

  module _ {D≤ : Poset} {L : 𝒫⊆ →mono D≤} {R : D≤ →mono 𝒫⊆} (L⊣R : L ⊣ R) where
    private
      open PosetPoly D≤
      D≈ = PosetPoly.Eq.setoid D≤
      D = ∣ D≤ ∣
      _[∩]_ : Op₂ ∣ D≤ ∣
      _[∩]_ = liftOpAlong⊣ L⊣R _∩_
      open GaloisConnection L⊣R

    -- Any right adjoint functor to 𝒫⊆ is lax monoidal wrt [∩]
    [∩]-∩-right-adjoint-lax-monoidal : IsLaxMonoidal R _[∩]_ _∩_
    [∩]-∩-right-adjoint-lax-monoidal a b = η (⟦ R ⟧ a ∩ ⟦ R ⟧ b)

    -- Any left adjoint functor from 𝒫⊆ is oplax monoidal wrt ∩
    ∩-[∩]-left-adjoint-oplax-monoidal : IsOplaxMonoidal L _∩_ _[∩]_
    ∩-[∩]-left-adjoint-oplax-monoidal S S' = L .Mono.mono ((∩-mono S (⟦ R ⟧ (⟦ L ⟧ S)) S' (⟦ R ⟧ (⟦ L ⟧ S')) (η S) (η S')))

    -- If a set of fixed points of an adjunction is closed under ∩ then so is the image of the right adjoint
    preRL-∩closed→∩∈imageR : ((S S' : Pred C≈) → S ∈ preRL → S' ∈ preRL → (S ∩ S') ∈ preRL) → ((a b : D) → Σ c ∶ D , (⟦ R ⟧ c ≐ (⟦ R ⟧ a ∩ ⟦ R ⟧ b)))
    preRL-∩closed→∩∈imageR preRL-∩closed a b =
      let
      Ra∩Rb∈preRL : (⟦ R ⟧ a ∩ ⟦ R ⟧ b) ∈ preRL
      Ra∩Rb∈preRL = preRL-∩closed (⟦ R ⟧ a) (⟦ R ⟧ b) (R∈preRL a) (R∈preRL b)
      in
      preRL⊆imageR Ra∩Rb∈preRL 
    
    -- If an image of a right adjoint is closed under ∩ then the right adjoint is oplax monoidal wrt [∩] and ∩
    ∩∈imageR→[∩]-∩-right-adjoint-oplax-monoidal :
      ((a b : D) → Σ c ∶ D , (⟦ R ⟧ c ≐ (⟦ R ⟧ a ∩ ⟦ R ⟧ b))) → IsOplaxMonoidal R _[∩]_ _∩_
    ∩∈imageR→[∩]-∩-right-adjoint-oplax-monoidal ∩∈imageR a b =
      let
      (c , Rc≐Ra∩Rb) = ∩∈imageR a b -- we have c such that ⟦ R ⟧ c ≐ ⟦ R ⟧ a ∩ ⟦ R ⟧ b
      open PosetReasoning (Pred⊆-poset C≈)
      in
      begin
      ⟦ R ⟧ (a [∩] b)                      ≡⟨⟩
      ⟦ R ∘-mono L ⟧ (⟦ R ⟧ a ∩ ⟦ R ⟧ b)   ≈˘⟨ (R ∘-mono L) .Mono.cong Rc≐Ra∩Rb ⟩
      ⟦ R ∘-mono L ⟧ (⟦ R ⟧ c)             ≈⟨ RLR≈R c  ⟩
      ⟦ R ⟧ c                              ≈⟨ Rc≐Ra∩Rb ⟩
      ⟦ R ⟧ a ∩ ⟦ R ⟧ b                    ∎ 

    preRL-∩closed→[∩]-∩-right-adjoint-oplax-monoidal : ((S S' : Pred C≈) → S ∈ preRL → S' ∈ preRL → (S ∩ S') ∈ preRL) → IsOplaxMonoidal R _[∩]_ _∩_
    preRL-∩closed→[∩]-∩-right-adjoint-oplax-monoidal
      = ∩∈imageR→[∩]-∩-right-adjoint-oplax-monoidal
      ∘ preRL-∩closed→∩∈imageR

module _
  (Index : Set) where
  -- Definitions for indexed binary operations

  module _
    (P Q : Index → Index → Poset)
    (F : (C D : Index) → P C D →mono Q C D)
    where
    -- Monoidal properties between indexed posets

    module _
      (C D E : Index)
      (_⊗P_ : ∣ P C D ∣ → ∣ P D E ∣ → ∣ P C E ∣)
      (_⊗Q_ : ∣ Q C D ∣ → ∣ Q D E ∣ → ∣ Q C E ∣)
      where

      open PosetPoly (Q C E)
      IsIndexedLaxMonoidal : Set
      IsIndexedLaxMonoidal = (a : ∣ P C D ∣) → (b : ∣ P D E ∣) → ⟦ F C D ⟧ a ⊗Q ⟦ F D E ⟧ b ≤ ⟦ F C E ⟧ (a ⊗P b)

      IsIndexedOplaxMonoidal : Set
      IsIndexedOplaxMonoidal = (a : ∣ P C D ∣) → (b : ∣ P D E ∣) → ⟦ F C E ⟧ (a ⊗P b) ≤ ⟦ F C D ⟧ a ⊗Q ⟦ F D E ⟧ b

      IsIndexedMonoidal : Set
      IsIndexedMonoidal = (a : ∣ P C D ∣) → (b : ∣ P D E ∣) → ⟦ F C E ⟧ (a ⊗P b) ≈ ⟦ F C D ⟧ a ⊗Q ⟦ F D E ⟧ b

  module _ (P Q : Index → Index → Poset) where
    -- Definition of lifting of an indexed binary operation on a poset along with an adjunction
    module _ {L : (C D : Index) → P C D →mono Q C D} {R : (C D : Index) → Q C D →mono P C D} (L⊣R : (C D : Index) → L C D ⊣ R C D) where
      indexedLiftOpAlong⊣ : (C D E : Index) → (∣ P C D ∣ → ∣ P D E ∣ → ∣ P C E ∣) → (∣ Q C D ∣ → ∣ Q D E ∣ → ∣ Q C E ∣)
      indexedLiftOpAlong⊣ C D E _⊗P_ a b = ⟦ L C E ⟧ (⟦ R C D ⟧ a ⊗P ⟦ R D E ⟧ b)

  module _ (∣_∣Ix : Index → Setoid) where
    -- general results about ⋈ and ⊣
    private
      𝒫⊆ : Index → Index → Poset
      𝒫⊆ C D = Pred⊆-poset (∣ C ∣Ix ×-setoid ∣ D ∣Ix)

 
    module _ (P≤ : Index → Index → Poset)
      {L : (C D : Index) → 𝒫⊆ C D →mono P≤ C D}
      {R : (C D : Index) → P≤ C D →mono 𝒫⊆ C D}
      (L⊣R : (C D : Index) → L C D ⊣ R C D) where

      private module _ (C D : Index) where
        open GaloisConnection (L⊣R C D) public

      private module _ {C D E : Index} where
          _[⋈]_ : ∣ P≤ C D ∣ → ∣ P≤ D E ∣ → ∣ P≤ C E ∣
          _[⋈]_ = indexedLiftOpAlong⊣ 𝒫⊆ P≤ L⊣R C D E _⋈_

      module _ (C D E : Index) where
        private
          C≈ = ∣ C ∣Ix
          D≈ = ∣ D ∣Ix
          E≈ = ∣ E ∣Ix

        [⋈]-⋈-right-adjoint-lax-monoidal : IsIndexedLaxMonoidal P≤ 𝒫⊆ R C D E _[⋈]_ _⋈_
        [⋈]-⋈-right-adjoint-lax-monoidal a b = η C E (⟦ R C D ⟧ a ⋈ ⟦ R D E ⟧ b)

        ⋈-[⋈]-left-adjoint-oplax-monoidal : IsIndexedOplaxMonoidal 𝒫⊆ P≤  L C D E _⋈_ _[⋈]_
        ⋈-[⋈]-left-adjoint-oplax-monoidal S S' = L C E .Mono.mono (⋈-mono S (⟦ R C D ∘-mono L C D ⟧ S) S' (⟦ (R D E ∘-mono L D E) ⟧ S') (η C D S) (η D E S'))

        PreRL⋈Closed = ((S : Pred (C≈ ×-setoid D≈)) (S' : Pred (D≈ ×-setoid E≈)) → S ∈ preRL C D → S' ∈ preRL D E → (S ⋈ S') ∈ preRL C E)
        ⋈∈ImageR = ((a : ∣ P≤ C D ∣) (b : ∣ P≤ D E ∣) → Σ c ∶ ∣ P≤ C E ∣ , (⟦ R C E ⟧ c ≐ (⟦ R C D ⟧ a ⋈ ⟦ R D E ⟧ b)))

        preRL-⋈closed→⋈∈imageR : PreRL⋈Closed → ⋈∈ImageR
        preRL-⋈closed→⋈∈imageR preRL-⋈closed a b =
          let
          Ra⋈Rb∈preRL : (⟦ R C D ⟧ a ⋈ ⟦ R D E ⟧ b) ∈ preRL C E
          Ra⋈Rb∈preRL = preRL-⋈closed (⟦ R C D ⟧ a) (⟦ R D E ⟧ b) (R∈preRL _ _ a) (R∈preRL _ _ b)
          in
          preRL⊆imageR _ _ Ra⋈Rb∈preRL

        ⋈∈imageR→[⋈]-⋈-right-adjoint-oplax-monoidal : ⋈∈ImageR → IsIndexedOplaxMonoidal P≤ 𝒫⊆  R C D E _[⋈]_ _⋈_
        ⋈∈imageR→[⋈]-⋈-right-adjoint-oplax-monoidal ⋈∈imageR a b =
            let
            (c , Rc≐Ra⋈Rb) = ⋈∈imageR a b
            _ : typeOf Rc≐Ra⋈Rb ≡ (⟦ R C E ⟧ c ≐ (⟦ R C D ⟧ a ⋈ ⟦ R D E ⟧ b)) -- debug
            _ = ≡.refl
            open PosetReasoning (Pred⊆-poset (∣ C ∣Ix ×-setoid ∣ E ∣Ix))
            in
            begin
            ⟦ R C E ⟧ (a [⋈] b)                                  ≡⟨⟩
            ⟦ R C E ∘-mono L C E ⟧ (⟦ R C D ⟧ a ⋈ ⟦ R D E ⟧ b)   ≈˘⟨ (R _ _ ∘-mono L _ _) .Mono.cong Rc≐Ra⋈Rb ⟩
            ⟦ R C E ∘-mono L C E ⟧ (⟦ R C E ⟧ c)                  ≈⟨ RLR≈R _ _ c  ⟩
            ⟦ R C E ⟧ c                                           ≈⟨ Rc≐Ra⋈Rb ⟩
            ⟦ R C D ⟧ a ⋈ ⟦ R D E ⟧ b                            ∎

        preRL-⋈closed→[⋈]-⋈-right-adjoint-oplax-monoidal : PreRL⋈Closed → IsIndexedOplaxMonoidal P≤ 𝒫⊆  R C D E _[⋈]_ _⋈_
        preRL-⋈closed→[⋈]-⋈-right-adjoint-oplax-monoidal
          = ⋈∈imageR→[⋈]-⋈-right-adjoint-oplax-monoidal
          ∘ preRL-⋈closed→⋈∈imageR

module CheckOplaxMonoidalityForIntersection where
  -- Here we check the oplax-monoidality of G G₀ G₁ G₂ G₃, wrt ∩ and [∩], ⋈ and [⋈]

  module F⊣G (C⨆ : SLat) where
    private
      C≤ = SLat.poset C⨆
      C≈ = SLat.Eq.setoid C⨆
      C = ∣ C⨆ ∣
      open SLat C⨆
      open 𝒫⊆-and-Endo C⨆
      open GaloisConnection F⊣G
      -- naive operation for nondeterministic choice
      _[∩]_ = liftOpAlong⊣ F⊣G _∩_

    ∩-⨆closed : (R R' : Pred C≈) → Is⨆Closed C⨆ R → Is⨆Closed C⨆ R' → Is⨆Closed C⨆ (R ∩ R')
    ∩-⨆closed R R' R-⨆closed R'-⨆closed S S⊆R∩R' = (R-⨆closed S (proj₁ ∘ S⊆R∩R') , R'-⨆closed S (proj₂ ∘ S⊆R∩R'))

    ∩-preRL-closed : (R R' : Pred C≈) → R ∈ preRL → R' ∈ preRL → (R ∩ R') ∈ preRL
    ∩-preRL-closed R R' R∈preRL R'∈preRL =
      preGF-characterization (R ∩ R') .proj₂
        (∩-⨆closed R R'
          (preGF-characterization R .proj₁ R∈preRL)
          (preGF-characterization R' .proj₁ R'∈preRL))

    [∩]-∩-oplax-monoidal : IsOplaxMonoidal G _[∩]_ _∩_
    [∩]-∩-oplax-monoidal = preRL-∩closed→[∩]-∩-right-adjoint-oplax-monoidal C≈ F⊣G ∩-preRL-closed

    -- show exsistance of cheaper (efficient) version of operation that is also oplax-monoidal

  module _ (D⨆ E⨆ : SLat) where
    private
      D≤ = SLat.poset D⨆
      D≈ = SLat.Eq.setoid D⨆
      D = ∣ D⨆ ∣
      module D = SLat D⨆

      E≤ = SLat.poset E⨆
      E≈ = SLat.Eq.setoid E⨆
      E = ∣ E⨆ ∣
      module E = SLat E⨆

      open 𝒫⊆-and-Endo (D⨆ ×-slat E⨆)

    module F₀⊣G₀ where
      private
        _[∩]_ = liftOpAlong⊣ (F₀⊣G₀ D⨆ E⨆) _∩_
        open GaloisConnection (F₀⊣G₀ D⨆ E⨆)
      ∩-tiltbowtieclosed : (R R' : Pred (D≈ ×-setoid E≈))
        → IsTiltBowTieClosed D⨆ E⨆ R → IsTiltBowTieClosed D⨆ E⨆ R' → IsTiltBowTieClosed D⨆ E⨆ (R ∩ R')
      ∩-tiltbowtieclosed R R' R-closed R'-closed d e d₀ e₀ e₁ (d₀≤d , e₀≤e , e≤e₁ , (d₀e₁∈R , d₀e₁∈R') , (de₀∈R , de₀∈R'))
        = (R-closed d e d₀ e₀ e₁ (d₀≤d , e₀≤e , e≤e₁ , d₀e₁∈R , de₀∈R)) , R'-closed d e d₀ e₀ e₁ (d₀≤d , e₀≤e , e≤e₁ , d₀e₁∈R' , de₀∈R')

      ∩-preRL-closed : (R R' : Pred (D≈ ×-setoid E≈)) → R ∈ preRL → R' ∈ preRL → (R ∩ R') ∈ preRL
      ∩-preRL-closed R R' R∈preRL R'∈preRL =
        preG₀F₀-characterization D⨆ E⨆ (R ∩ R') .proj₂
          ( ∩-tiltbowtieclosed R R'
            (preG₀F₀-characterization D⨆ E⨆ R .proj₁ R∈preRL .proj₁)
            (preG₀F₀-characterization D⨆ E⨆ R' .proj₁ R'∈preRL .proj₁)
          , F⊣G.∩-⨆closed (D⨆ ×-slat E⨆) R R'
            (preG₀F₀-characterization D⨆ E⨆ R .proj₁ R∈preRL .proj₂)
            (preG₀F₀-characterization D⨆ E⨆ R' .proj₁ R'∈preRL .proj₂))

      [∩]-∩-oplax-monoidal : IsOplaxMonoidal (G₀ D⨆ E⨆) _[∩]_ _∩_
      [∩]-∩-oplax-monoidal = preRL-∩closed→[∩]-∩-right-adjoint-oplax-monoidal (D≈ ×-setoid E≈) (F₀⊣G₀ D⨆ E⨆) ∩-preRL-closed


    module F₁⊣G₁ where
      private
        _[∩]_ = liftOpAlong⊣ (F₁⊣G₁ D⨆ E⨆) _∩_
        open GaloisConnection (F₁⊣G₁ D⨆ E⨆)
      ∩-bowtieclosed : (R R' : Pred (D≈ ×-setoid E≈))
        → IsBowTieClosed D⨆ E⨆ R → IsBowTieClosed D⨆ E⨆ R' → IsBowTieClosed D⨆ E⨆ (R ∩ R')
      ∩-bowtieclosed R R' R-closed R'-closed d e d₀ e₀ d₁ e₁ (d₀≤d , e₀≤e , d≤d₁ , e≤e₁ , (d₀e₁∈R , d₀e₁∈R') , (d₁e₀∈R , d₁e₀∈R'))
        = (R-closed d e d₀ e₀ d₁ e₁ (d₀≤d , e₀≤e , d≤d₁ , e≤e₁ , d₀e₁∈R , d₁e₀∈R)) , R'-closed d e d₀ e₀ d₁ e₁ (d₀≤d , e₀≤e , d≤d₁ , e≤e₁ , d₀e₁∈R' , d₁e₀∈R')

      ∩-preRL-closed : (R R' : Pred (D≈ ×-setoid E≈)) → R ∈ preRL → R' ∈ preRL → (R ∩ R') ∈ preRL
      ∩-preRL-closed R R' R∈preRL R'∈preRL =
        preG₁F₁-characterization D⨆ E⨆ (R ∩ R') .proj₂
          ( ∩-bowtieclosed R R'
            (preG₁F₁-characterization D⨆ E⨆ R .proj₁ R∈preRL .proj₁)
            (preG₁F₁-characterization D⨆ E⨆ R' .proj₁ R'∈preRL .proj₁)
          , F⊣G.∩-⨆closed (D⨆ ×-slat E⨆) R R'
            (preG₁F₁-characterization D⨆ E⨆ R .proj₁ R∈preRL .proj₂)
            (preG₁F₁-characterization D⨆ E⨆ R' .proj₁ R'∈preRL .proj₂))

      [∩]-∩-oplax-monoidal : IsOplaxMonoidal (G₁ D⨆ E⨆) _[∩]_ _∩_
      [∩]-∩-oplax-monoidal = preRL-∩closed→[∩]-∩-right-adjoint-oplax-monoidal (D≈ ×-setoid E≈) (F₁⊣G₁ D⨆ E⨆) ∩-preRL-closed

    -- TODO: show [∩]-∩-oplax-monoidal for F₂⊣G₂ and F₃⊣G₃ (this must be as easy as F₀⊣G₀ and F₁⊣F₂)
    --
module CheckOplaxMonoidalityForComposition where
  private
    module _ (C⨆ D⨆ : SLat) where
      open 𝒫⊆-and-Endo (C⨆ ×-slat D⨆) public

  module F⊣G where
    private
      module _ (C⨆ D⨆ : SLat) where
        open GaloisConnection (F⊣G C⨆ D⨆) public

    module _ (C⨆ D⨆ E⨆ : SLat) where
      private
        _[⋈]_ = indexedLiftOpAlong⊣ SLat 𝒫⊆ Endo F⊣G C⨆ D⨆ E⨆ _⋈_
        C≤ = SLat.poset C⨆
        C≈ = SLat.Eq.setoid C⨆
        C = ∣ C⨆ ∣
        module C = SLat C⨆
        D≤ = SLat.poset D⨆
        D≈ = SLat.Eq.setoid D⨆
        D = ∣ D⨆ ∣
        module D = SLat D⨆
        E≤ = SLat.poset E⨆
        E≈ = SLat.Eq.setoid E⨆
        E = ∣ E⨆ ∣
        module E = SLat E⨆

      ⋈-⨆closed : (R : Pred (C≈ ×-setoid D≈)) (R' : Pred (D≈ ×-setoid E≈)) → Is⨆Closed (C⨆ ×-slat D⨆) R → Is⨆Closed (D⨆ ×-slat E⨆) R' → Is⨆Closed (C⨆ ×-slat E⨆) (R ⋈ R')
      ⋈-⨆closed R R' R-⨆closed R'-⨆closed S S⊆R⋈R' = (⨆T₂ , [⨆S₁,⨆T₂]∈R , [⨆T₂,⨆S₂]∈R')
        where

        -- we take a subset T ⊆ C × D × E such that eath tuple (c , d , e) ∈ T satisfies (c,e)∈S and (c,d)∈R (d,e)∈R'
        T : Pred (C≈ ×-setoid (D≈ ×-setoid E≈))
        Pred.⟦ T ⟧ (c , d , e) = (c , e) ∈ S × (c , d) ∈ R × (d , e) ∈ R'
        T .Pred.isWellDefined (c≈c' , d≈d' , e≈e') (ce∈S , cd∈R , de∈R') = (S .Pred.isWellDefined (c≈c' , e≈e') ce∈S , R .Pred.isWellDefined (c≈c' , d≈d') cd∈R , R' .Pred.isWellDefined (d≈d' , e≈e') de∈R')

        -- A bunch of equalities between projections of T and S
        T₁ = T ∣₁
        T₂ = (T ∣₂) ∣₁
        T₃ = (T ∣₂) ∣₂

        S₁ = S ∣₁
        S₂ = S ∣₂

        S₁≐T₁ : S₁ ≐ T₁
        S₁≐T₁ .proj₁ (e , ce∈S) =
          let
          (d , cde∈T) = S⊆R⋈R' ce∈S
          in
          ((d , e) , (ce∈S , cde∈T))
        S₁≐T₁ .proj₂ ((d , e) , (ce∈S , cde∈T)) = (e , ce∈S)

        S₂≐T₃ : S₂ ≐ T₃
        S₂≐T₃ .proj₁ (c , ce∈S) =
          let
          (d , cde∈T) = S⊆R⋈R' ce∈S
          in
          (d , c , ce∈S , cde∈T)
        S₂≐T₃ .proj₂ (d , c , ce∈S , cde∈T) = (c , ce∈S)

        T₁₂ : Pred (C≈ ×-setoid D≈)
        T₁₂ = (Pred-assoc-rl T) ∣₁

        T₂₃ : Pred (D≈ ×-setoid E≈)
        T₂₃ = T ∣₂

        [T₁₂]₁≐T₁ : (T₁₂ ∣₁) ≐ T₁
        [T₁₂]₁≐T₁ .proj₁ (d , e , cde∈T) = ((d , e) , cde∈T)
        [T₁₂]₁≐T₁ .proj₂ ((d , e) , cde∈T) = (d , e , cde∈T)

        [T₁₂]₂≐T₂ : (T₁₂ ∣₂) ≐ T₂
        [T₁₂]₂≐T₂ .proj₁ (c , e , cde∈T) = (e , c , cde∈T)
        [T₁₂]₂≐T₂ .proj₂ (e , c , cde∈T) = (c , e , cde∈T)

        -- One can easily check T₁₂ ⊆ R and T₂₃ ⊆ R'.
        -- Then, we get
        -- (1) ⨆ S₁ , ⨆ T₂ ≈ ⨆ T₁₂ ∈ R by S₁ ≐ T₁ and join closeness of R
        -- (2) ⨆ T₂ , ⨆ S₂ ≈ ⨆ T₂₃ ∈ R' by S₂ ≐ T₃ and join closeness of R'
        -- ⨆ S ∈ R ⋈ R' is witnessed by the intermediate element ⨆ T₂
        T₁₂⊆R : T₁₂ ⊆ R
        T₁₂⊆R (e , ce∈S , cd∈R , de∈R') = cd∈R

        T₂₃⊆R' : T₂₃ ⊆ R'
        T₂₃⊆R' (c , ce∈S , cd∈R , de∈R') = de∈R'

        module _ where
          open SLat (C⨆ ×-slat (D⨆ ×-slat E⨆))
          ⨆T : C × D × E
          ⨆T = ⨆ T

          ⨆T₁ = let (c , _ , _) = ⨆T in c
          ⨆T₂ = let (_ , d , _) = ⨆T in d
          ⨆T₃ = let (_ , _ , e) = ⨆T in e

        module _ where
          open SLat (C⨆ ×-slat E⨆)
          ⨆S = ⨆ S
          ⨆S₁ = let (c , _) = ⨆S in c
          ⨆S₂ = let (_ , e) = ⨆S in e

        ⨆S₁≈⨆T₁ : ⨆S₁ C.≈ ⨆T₁
        ⨆S₁≈⨆T₁ = C.⨆-cong S₁ T₁ S₁≐T₁

        ⨆S₂≈⨆T₃ : ⨆S₂ E.≈ ⨆T₃
        ⨆S₂≈⨆T₃ = E.⨆-cong S₂ T₃ S₂≐T₃

        module _ where
          open SLat (C⨆ ×-slat D⨆)
          ⨆T₁₂∈R : ⨆ T₁₂ ∈ R
          ⨆T₁₂∈R = R-⨆closed T₁₂ T₁₂⊆R

          ⨆T₁₂≈[⨆T₁,⨆T₂] : ⨆ T₁₂ ≈ (⨆T₁ , ⨆T₂)
          ⨆T₁₂≈[⨆T₁,⨆T₂] =
            ( C.⨆-cong (T₁₂ ∣₁) T₁ [T₁₂]₁≐T₁
            , D.⨆-cong (T₁₂ ∣₂) T₂ [T₁₂]₂≐T₂)

          [⨆T₁,⨆T₂]∈R : (⨆T₁ , ⨆T₂) ∈ R
          [⨆T₁,⨆T₂]∈R = R .Pred.isWellDefined ⨆T₁₂≈[⨆T₁,⨆T₂] ⨆T₁₂∈R

          [⨆S₁,⨆T₂]∈R : (⨆S₁ , ⨆T₂) ∈ R
          [⨆S₁,⨆T₂]∈R = R .Pred.isWellDefined (C.Eq.sym ⨆S₁≈⨆T₁ , D.Eq.refl) [⨆T₁,⨆T₂]∈R

        module _ where
          open SLat (D⨆ ×-slat E⨆)
          [⨆T₂,⨆T₃]∈R' : (⨆T₂ , ⨆T₃) ∈ R'
          [⨆T₂,⨆T₃]∈R' = R'-⨆closed T₂₃ T₂₃⊆R'

          [⨆T₂,⨆S₂]∈R' : (⨆T₂ , ⨆S₂) ∈ R'
          [⨆T₂,⨆S₂]∈R' = R' .Pred.isWellDefined (D.Eq.refl , E.Eq.sym ⨆S₂≈⨆T₃) [⨆T₂,⨆T₃]∈R'

      ⋈-preRL-closed : (R : Pred (C≈ ×-setoid D≈)) (R' : Pred (D≈ ×-setoid E≈)) → R ∈ preRL C⨆ D⨆ → R' ∈ preRL D⨆ E⨆ → (R ⋈ R') ∈ preRL C⨆ E⨆
      ⋈-preRL-closed R R' R∈preGF R'∈preGF =
        preGF-characterization C⨆ E⨆ (R ⋈ R') .proj₂
          (⋈-⨆closed R R'
            (preGF-characterization C⨆ D⨆ R .proj₁ R∈preGF)
            (preGF-characterization D⨆ E⨆ R' .proj₁ R'∈preGF))

      [⋈]-⋈-oplax-monoidal :  IsIndexedOplaxMonoidal SLat Endo 𝒫⊆ G C⨆ D⨆ E⨆ _[⋈]_ _⋈_
      [⋈]-⋈-oplax-monoidal =  preRL-⋈closed→[⋈]-⋈-right-adjoint-oplax-monoidal SLat SLat.Eq.setoid Endo F⊣G C⨆ D⨆ E⨆ ⋈-preRL-closed

      -- show cheaper (efficient) version of oplax-monoidal operation

  module F₂⊣G₂ where
    private
      module _ (C⨆ D⨆ : SLat) where
        open GaloisConnection (F₂⊣G₂ C⨆ D⨆) public
    module _ (C⨆ D⨆ E⨆ : SLat) where
      private
        _[⋈]_ = indexedLiftOpAlong⊣ SLat 𝒫⊆ _ F₂⊣G₂ C⨆ D⨆ E⨆ _⋈_
        C≤ = SLat.poset C⨆
        C≈ = SLat.Eq.setoid C⨆
        C = ∣ C⨆ ∣
        module C = SLat C⨆
        D≤ = SLat.poset D⨆
        D≈ = SLat.Eq.setoid D⨆
        D = ∣ D⨆ ∣
        module D = SLat D⨆
        E≤ = SLat.poset E⨆
        E≈ = SLat.Eq.setoid E⨆
        E = ∣ E⨆ ∣
        module E = SLat E⨆

      ⋈-fanclosed : (R : Pred (C≈ ×-setoid D≈)) (R' : Pred (D≈ ×-setoid E≈)) → IsFanClosed C⨆ D⨆ R → IsFanClosed D⨆ E⨆ R' → IsFanClosed C⨆ E⨆ (R ⋈ R')
      ⋈-fanclosed R R' R-fanclosed  R'-fanclosed = ?

      ⋈-preRL-closed : (R : Pred (C≈ ×-setoid D≈)) (R' : Pred (D≈ ×-setoid E≈)) → R ∈ preRL C⨆ D⨆ → R' ∈ preRL D⨆ E⨆ → (R ⋈ R') ∈ preRL C⨆ E⨆
      ⋈-preRL-closed R R' R∈preRL R'∈preRL =
        preG₂F₂-characterization C⨆ E⨆ (R ⋈ R') .proj₂
          ( ⋈-fanclosed R R'
            (preG₂F₂-characterization C⨆ D⨆ R .proj₁ R∈preRL .proj₁)
            (preG₂F₂-characterization D⨆ E⨆ R' .proj₁ R'∈preRL .proj₁)
          , F⊣G.⋈-⨆closed C⨆ D⨆ E⨆ R R'
            (preG₂F₂-characterization C⨆ D⨆ R .proj₁ R∈preRL .proj₂)
            (preG₂F₂-characterization D⨆ E⨆ R' .proj₁ R'∈preRL .proj₂))

  module F₃⊣G₃ where
    private
      module _ (C⨆ D⨆ : SLat) where
        open GaloisConnection (F₃⊣G₃ C⨆ D⨆) public
    module _ (C⨆ D⨆ E⨆ : SLat) where
      private
        _[⋈]_ = indexedLiftOpAlong⊣ SLat 𝒫⊆ _ F₃⊣G₃ C⨆ D⨆ E⨆ _⋈_
        C≤ = SLat.poset C⨆
        C≈ = SLat.Eq.setoid C⨆
        C = ∣ C⨆ ∣
        module C = SLat C⨆
        D≤ = SLat.poset D⨆
        D≈ = SLat.Eq.setoid D⨆
        D = ∣ D⨆ ∣
        module D = SLat D⨆
        E≤ = SLat.poset E⨆
        E≈ = SLat.Eq.setoid E⨆
        E = ∣ E⨆ ∣
        module E = SLat E⨆

      ⋈-tiltclosed : (R : Pred (C≈ ×-setoid D≈)) (R' : Pred (D≈ ×-setoid E≈)) → IsTiltClosed C⨆ D⨆ R → IsTiltClosed D⨆ E⨆ R' → IsTiltClosed C⨆ E⨆ (R ⋈ R')
      ⋈-tiltclosed R R' R-tiltclosed  R'-tiltclosed c e e₀ c₁ (e₀≤e , c≤c₁ , (d , c₁d∈R , de₀∈R)) =
        (d , R-tiltclosed c d d c₁ (D.Po.refl , c≤c₁ , c₁d∈R) , R'-tiltclosed d e e₀ d (e₀≤e , D.Po.refl , de₀∈R))

      ⋈-preRL-closed : (R : Pred (C≈ ×-setoid D≈)) (R' : Pred (D≈ ×-setoid E≈)) → R ∈ preRL C⨆ D⨆ → R' ∈ preRL D⨆ E⨆ → (R ⋈ R') ∈ preRL C⨆ E⨆
      ⋈-preRL-closed R R' R∈preRL R'∈preRL =
        preG₃F₃-characterization C⨆ E⨆ (R ⋈ R') .proj₂
          ( ⋈-tiltclosed R R'
            (preG₃F₃-characterization C⨆ D⨆ R .proj₁ R∈preRL .proj₁)
            (preG₃F₃-characterization D⨆ E⨆ R' .proj₁ R'∈preRL .proj₁)
          , F⊣G.⋈-⨆closed C⨆ D⨆ E⨆ R R'
            (preG₃F₃-characterization C⨆ D⨆ R .proj₁ R∈preRL .proj₂)
            (preG₃F₃-characterization D⨆ E⨆ R' .proj₁ R'∈preRL .proj₂))
