
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

private variable
  ℓ ℓ' ℓ'' o o' p p' : Level

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

_∘-cong_ : {A B C : Setoid} (f : B →cong C) (g : A →cong B) → A →cong C
f ∘-cong g = BinRMorphComp.setoidHomomorphism g f

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

Prop↔-setoid : Setoid
Prop↔-setoid = PosetPoly.Eq.setoid Prop→-poset

curry-↔ : ∀ a b c → (a × b → c) ↔ (a → b → c)
curry-↔ a b c .proj₁ f = curry f 
curry-↔ a b c .proj₂ g = uncurry g

module _ (D≤ : Poset) where
  open PosetPoly D≤

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

∩-lower-l : {X : Setoid} (S T : Pred X) → (S ∩ T) ⊆ S
∩-lower-l S T (d∈S , d∈T) = d∈S

∩-lower-r : {X : Setoid} (S T : Pred X) → (S ∩ T) ⊆ T
∩-lower-r S T (d∈S , d∈T) = d∈T


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

  Pred-proj₁ : Pred (X≈ ×-setoid Y≈) → Pred X≈
  Pred.⟦ Pred-proj₁ R ⟧ = λ x → Σ y ∶ Y , ((x , y) ∈ R)
  Pred-proj₁ R .Pred.isWellDefined x≈x' (y , xy∈R) = y , R .Pred.isWellDefined (x≈x' , Y.refl) xy∈R

  Pred-proj₂ : Pred (X≈ ×-setoid Y≈) → Pred Y≈
  Pred.⟦ Pred-proj₂ R ⟧ = λ y → Σ x ∶ X , ((x , y) ∈ R)
  Pred-proj₂ R .Pred.isWellDefined y≈y' (x , xy∈R) = x , R .Pred.isWellDefined (X.refl , y≈y') xy∈R

  Pred-proj₁-∈ : {x : _} {y : _} (R : Pred (X≈ ×-setoid Y≈)) → (x , y) ∈ R → x ∈ Pred-proj₁ R
  Pred-proj₁-∈ R xy∈R = -, xy∈R

  Pred-proj₂-∈ : {x : _} {y : _} (R : Pred (X≈ ×-setoid Y≈)) → (x , y) ∈ R → y ∈ Pred-proj₂ R
  Pred-proj₂-∈ R xy∈R = -, xy∈R

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

  ⊥ : Carrier
  ⊥ = ⨆ ∅

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

  ⨆≤→∀≤ : ∀ S x → ⨆ S ≤ x → ∀ x' → x' ∈ S → x' ≤ x
  ⨆≤→∀≤ S x ⨆S≤x x' x'∈S = Po.trans (⨆-upper _ _ x'∈S) ⨆S≤x

  ⨆≤←∀≤ : ∀ S x → (∀ x' → x' ∈ S → x' ≤ x) → ⨆ S ≤ x
  ⨆≤←∀≤ = ⨆-least

  ⨆≤↔∀≤ : ∀ S x → ⨆ S ≤ x ↔ (∀ x' → x' ∈ S → x' ≤ x)
  ⨆≤↔∀≤ S x .proj₁ = ⨆≤→∀≤ S x
  ⨆≤↔∀≤ S x .proj₂ = ⨆≤←∀≤ S x


  ⊓≈⨆∩↓ : ∀ x y → (x ⊓ y) ≈ ⨆ (↓ poset x ∩ ↓ poset y)
  ⊓≈⨆∩↓ x y = Po.antisym
    (⨆-upper (↓ poset x ∩ ↓ poset y) (x ⊓ y) (⊓-inf x y .proj₁ , ⊓-inf x y .proj₂ .proj₁))
    (⊓-inf x y .proj₂ .proj₂ (⨆ (↓ poset x ∩ ↓ poset y)) (⨆-least (↓ poset x ∩ ↓ poset y) x (\_ p → p .proj₁)) ( (⨆-least (↓ poset x ∩ ↓ poset y) y (\_ p → p .proj₂))))

  ⨆↓≈⨆↓∩ : ∀ x S → x ∈ S → ⨆ (↓ poset x) ≈ ⨆ (↓ poset x ∩ S)
  ⨆↓≈⨆↓∩ x S x∈S = Po.antisym
    (⨆-upper (↓ poset x ∩ S) (⨆ (↓ poset x)) (⨆-↓≤ x , Pred.isWellDefined S (Eq.sym (⨆-↓ x)) x∈S))
    (⨆-mono (↓ poset x ∩ S) (↓ poset x) proj₁)

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
      f x      ≤⟨ f≤ .Mono.mono (⨆-upper (post poset f≈) x x≤fx) ⟩
      f (ν f≈) ∎

    R : ν f≈ ≤ f (ν f≈)
    R =
      begin
      ν f≈     ≤⟨ ⨆-least (post poset f≈) (f (ν f≈)) ι ⟩
      f (ν f≈) ∎

    L : f (ν f≈) ≤ ν f≈
    L =
      begin
      f (ν f≈) ≤⟨ ⨆-upper (post poset f≈) (f (ν f≈)) (f≤ .Mono.mono (⨆-least (post poset f≈) (f (ν f≈)) ι)) ⟩
      ν f≈     ∎
  ν-gfp f≤ .proj₂ x' x'∈fixf = u -- proof that ν f is the greatest fixed point
    where
    f≈ = ⟦ f≤ ⟧cong
    f = ⟦ f≤ ⟧
    open PosetReasoning poset
    u =
      begin
      x'   ≤⟨ ⨆-upper (post poset f≈) x' (Po.reflexive x'∈fixf) ⟩
      ν f≈ ∎

  ν-mono : (f≈ g≈ : Eq.setoid →cong Eq.setoid) → ((x : Carrier) → ⟦ f≈ ⟧ x ≤ ⟦ g≈ ⟧ x) → ν f≈ ≤ ν g≈
  ν-mono f≈ g≈ f≤g = ⨆-mono (post poset f≈) (post poset g≈) \ {d} d≤fd → Po.trans d≤fd (f≤g d)

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
  (D ×-slat E) .⨆ R =  D .⨆ (Pred-proj₁ R) , E .⨆ (Pred-proj₂ R)
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
      = (⨆-sup D (Pred-proj₁ R) .proj₁ d (Pred-proj₁-∈ R de∈R))
      , (⨆-sup E (Pred-proj₂ R) .proj₁ e (Pred-proj₂-∈ R de∈R))
    least : (y : (D ×-slat E) .Carrier) →
              ((x : (D ×-slat E) .Carrier) → x ∈ R → (D ×-slat E) ._≤_ x y) →
              (D ×-slat E) ._≤_ ((D ×-slat E) .⨆ R) y
    least (d , e) p-upper
      = ⨆-least D (Pred-proj₁ R) d d-upper
      , ⨆-least E (Pred-proj₂ R) e e-upper
      where
      d-upper : (d' : D .Carrier) → d' ∈ Pred-proj₁ R → D ._≤_ d' d
      d-upper d' (e' , de'∈R) = p-upper (d' , e') de'∈R .proj₁
      e-upper : (e' : E .Carrier) → e' ∈ Pred-proj₂ R → E ._≤_ e' e
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
  private
    module C = PosetPoly C
    module D = PosetPoly D
    module E = PosetPoly E

  _∘-galois_ : L ⊣ R → L' ⊣ R' → (L' ∘-mono L) ⊣ (R ∘-mono R')
  (L⊣R ∘-galois L'⊣R') .GaloisConnection.ψ c e =
    let open SetoidReasoning Prop↔-setoid in
    begin
    ⟦ L' ∘-mono L ⟧ c E.≤ e     ≈⟨ L'⊣R' .GaloisConnection.ψ (⟦ L ⟧ c) e ⟩
    ⟦ L ⟧ c D.≤ ⟦ R' ⟧ e       ≈⟨ L⊣R .GaloisConnection.ψ c (⟦ R' ⟧ e) ⟩
    c C.≤ ⟦ R ∘-mono R' ⟧ e     ∎


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



module _ (C⨆ : SLat) where

  private
    C≤ = SLat.poset C⨆
    C≈ = SLat.Eq.setoid C⨆
    C = ∣ C⨆ ∣

  open SLat C⨆

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

  F-mono-valued : Pred C≈ → (C≤ →mono C≤)
  Mono.⟦ F-mono-valued S ⟧ = F-raw S
  F-mono-valued S .Mono.isMonotone .IsMono.mono {d} {d'}
    = ⨆-mono ((↓ C≤ d) ∩ S) ((↓ C≤ d') ∩ S)
    ∘ ∩-mono-l (↓ C≤ d) (↓ C≤ d') S
    ∘ ↓-mono C≤ d d'
  F-mono-valued S .Mono.isMonotone .IsMono.cong d≈d' = Po.antisym
    (F-mono-valued S .Mono.mono (Po.reflexive d≈d'))
    (F-mono-valued S .Mono.mono (Po.reflexive (Eq.sym d≈d')))

  G-raw : (C → C) → UniR.Pred C lzero
  G-raw f = post-raw C≤ f

  G-pred : (C≤ →mono C≤) → Pred C≈
  G-pred f = post C≤ ⟦ f ⟧cong

  F : 𝒫⊆ →mono (C≤ →mono≤-poset C≤)
  Mono.⟦ F ⟧ = F-mono-valued
  F .Mono.isMonotone .IsMono.mono {P} {Q} P⊆Q d
    = ⨆-mono (↓ C≤ d ∩ P) (↓ C≤ d ∩ Q)
             (∩-mono-r P Q (↓ C≤ d) P⊆Q)
  F .Mono.isMonotone .IsMono.cong {P} {Q} P≐Q d = Po.antisym
    (F .Mono.isMonotone .IsMono.mono {P} {Q} (P≐Q .proj₁) d)
    (F .Mono.isMonotone .IsMono.mono {Q} {P} (P≐Q .proj₂) d)

  G : (C≤ →mono≤-poset C≤) →mono (Pred⊆-poset C≈)
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
    → f≤ ∈ post (C≤ →mono≤-poset C≤) ⟦ F ∘-mono G ⟧cong ↔ IsCoclosure C≤ ⟦ f≤ ⟧
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
        ⨆ (↓ poset d ∩ post C≤ f≈)  ≤⟨ ⨆-mono (↓ poset d ∩ post C≤ f≈) (↓ poset d) (∩-lower-l (↓ poset d) (post C≤ f≈)) ⟩
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

  preGF-characterization : (R : Pred C≈) → (R ∈ pre (Pred⊆-poset C≈) ⟦ G ∘-mono F ⟧cong) ↔ Is⨆Closed C⨆ R
  preGF-characterization R =
    let open SetoidReasoning (Prop↔-setoid) in
    begin
    (R ∈ pre (Pred⊆-poset C≈) ⟦ G ∘-mono F ⟧cong) ≡⟨⟩
    (∀ {d} → d ≤ ⨆ (↓ poset d ∩ R) → d ∈ R) ≈⟨ γ , γ⁻¹ ⟩
    (∀ S → S ⊆ R → ⨆ S ∈ R) ≡⟨⟩
    Is⨆Closed C⨆ R ∎
    where
    γ : (∀ {d} → d ≤ ⨆ (↓ poset d ∩ R) → d ∈ R) → ∀ S → S ⊆ R → ⨆ S ∈ R
    γ φ S S⊆R = φ {d = ⨆ S} (⨆-mono S (↓ poset (⨆ S) ∩ R) \ {d} d∈S → ⨆-upper S d d∈S  , S⊆R d∈S)

    γ⁻¹ : (∀ S → S ⊆ R → ⨆ S ∈ R) → ∀ {d} → d ≤ ⨆ (↓ poset d ∩ R) → d ∈ R
    γ⁻¹ ψ {d} d≤⨆↓d∩R = R .Pred.isWellDefined (Po.antisym χ χ⁻¹)  (ψ (↓ poset d ∩ R) (∩-lower-r (↓ poset d) R))
      where
      χ : ⨆ (↓ poset d ∩ R) ≤ d
      χ = Po.trans (⨆-mono _ _ (∩-lower-l (↓ poset d) R)) (⨆-↓≤ d)

      χ⁻¹ : d ≤ ⨆ (↓ poset d ∩ R)
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

  open 𝒫⊆-and-Endo (D⨆ ×-slat E⨆)

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

  IsButterfly : Pred (D≈ ×-setoid E≈) → Set
  IsButterfly R = ∀ d₀ d d₁ e₀ e e₁
    → d₀ D.≤ d → d D.≤ d₁ → e₀ E.≤ e → e E.≤ e₁
    → (d₀ , e₁) ∈ R → (d₁ , e₀) ∈ R → (d , e) ∈ R

  -- We define the following galois connection
  --
  -- ((E →m D) × (D →m E) , ≤)
  --        H₂ ↓ ⊣ ↑ I₂
  --   ((E →m D) × E , ≤)

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


module _ {C D : Poset} where
  open PosetPoly D
  -- probably monoidal is not a right word for this property (it only refers to multiplication and not to unit)

  IsLaxMonoidal : (_⊗C_ : Op₂ ∣ C ∣) (_⊗D_ : Op₂ ∣ D ∣) (F : C →mono D)  → Set
  IsLaxMonoidal _⊗C_ _⊗D_ F = (a b : ∣ C ∣ ) → ⟦ F ⟧ a ⊗D ⟦ F ⟧ b ≤ ⟦ F ⟧ (a ⊗C b)

  IsOplaxMonoidal : (_⊗C_ : Op₂ ∣ C ∣) (_⊗D_ : Op₂ ∣ D ∣) (F : C →mono D) → Set
  IsOplaxMonoidal _⊗C_ _⊗D_ F = (a b : ∣ C ∣ ) → ⟦ F ⟧ (a ⊗C b) ≤ ⟦ F ⟧ a ⊗D ⟦ F ⟧ b

  IsMonoidal : (_⊗C_ : Op₂ ∣ C ∣) (_⊗D_ : Op₂ ∣ D ∣) (F : C →mono D) → Set
  IsMonoidal _⊗C_ _⊗D_ F = (a b : ∣ C ∣ ) → ⟦ F ⟧ (a ⊗C b) ≈ ⟦ F ⟧ a ⊗D ⟦ F ⟧ b

  module _ {L : C →mono D} {R : D →mono C} where
    liftOpAlong⊣ : (L⊣R : L ⊣ R) (_⊗C_ : Op₂ ∣ C ∣) → Op₂ ∣ D ∣
    liftOpAlong⊣ L⊣R _⊗C_ a b = ⟦ L ⟧ (⟦ R ⟧ a ⊗C ⟦ R ⟧ b)


-- General results about ∩ and ⋈ and adjoints

module _
  (C≈ : Setoid) where
  -- general result about ∩ and ⊣

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

    -- right adjoint that sends 𝒫⊆ to any poset are lax monoidal wrt ∩
    [∩]-∩-right-adjoint-lax-monoidal : IsLaxMonoidal _[∩]_ _∩_ R
    [∩]-∩-right-adjoint-lax-monoidal a b = η (⟦ R ⟧ a ∩ ⟦ R ⟧ b)

    ∩-[∩]-left-adjoint-oplax-monoidal : IsOplaxMonoidal _∩_ _[∩]_ L
    ∩-[∩]-left-adjoint-oplax-monoidal S S' = L .Mono.mono ((∩-mono S (⟦ R ⟧ (⟦ L ⟧ S)) S' (⟦ R ⟧ (⟦ L ⟧ S')) (η S) (η S')))

    preRL-∩closed→∩∈imageR : ((S S' : Pred C≈) → S ∈ preRL → S' ∈ preRL → (S ∩ S') ∈ preRL) → ((a b : D) → Σ c ∶ D , (⟦ R ⟧ c ≐ (⟦ R ⟧ a ∩ ⟦ R ⟧ b)))
    preRL-∩closed→∩∈imageR preRL-∩closed a b =
      let
      Ra∩Rb∈preRL : (⟦ R ⟧ a ∩ ⟦ R ⟧ b) ∈ preRL
      Ra∩Rb∈preRL = preRL-∩closed (⟦ R ⟧ a) (⟦ R ⟧ b) (R∈preRL a) (R∈preRL b)
      in
      preRL⊆imageR Ra∩Rb∈preRL 
    
    ∩∈imageR→[∩]-∩-right-adjoint-oplax-monoidal :
      ((a b : D) → Σ c ∶ D , (⟦ R ⟧ c ≐ (⟦ R ⟧ a ∩ ⟦ R ⟧ b))) → IsOplaxMonoidal _[∩]_ _∩_ R
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

    preRL-∩closed→[∩]-∩-right-adjoint-oplax-monoidal : ((S S' : Pred C≈) → S ∈ preRL → S' ∈ preRL → (S ∩ S') ∈ preRL) → IsOplaxMonoidal _[∩]_ _∩_ R
    preRL-∩closed→[∩]-∩-right-adjoint-oplax-monoidal
      = ∩∈imageR→[∩]-∩-right-adjoint-oplax-monoidal
      ∘ preRL-∩closed→∩∈imageR

module _
  (Index : Set) where

  module _
    (P Q : Index → Index → Poset)
    (_⊗P_ : {C D E : Index} → ∣ P C D ∣ → ∣ P D E ∣ → ∣ P C E ∣)
    (_⊗Q_ : {C D E : Index} → ∣ Q C D ∣ → ∣ Q D E ∣ → ∣ Q C E ∣)
    (F : {C D : Index} → P C D →mono Q C D)
    where

    module _ (C D E : Index) where
      open PosetPoly (Q C E)
      IsIndexedLaxMonoidal : Set
      IsIndexedLaxMonoidal = (a : ∣ P C D ∣) → (b : ∣ P D E ∣) → ⟦ F ⟧ a ⊗Q ⟦ F ⟧ b ≤ ⟦ F ⟧ (a ⊗P b)

      IsIndexedOplaxMonoidal : Set
      IsIndexedOplaxMonoidal = (a : ∣ P C D ∣) → (b : ∣ P D E ∣) → ⟦ F ⟧ (a ⊗P b) ≤ ⟦ F ⟧ a ⊗Q ⟦ F ⟧ b 

      IsIndexedMonoidal : Set
      IsIndexedMonoidal = (a : ∣ P C D ∣) → (b : ∣ P D E ∣) → ⟦ F ⟧ (a ⊗P b) ≈ ⟦ F ⟧ a ⊗Q ⟦ F ⟧ b 

  module _ (P Q : Index → Index → Poset) where
    module _ {L : {C D : Index} → P C D →mono Q C D} {R : {C D : Index} → Q C D →mono P C D} where
      indexedLiftOpAlong⊣ : (L⊣R : {C D : Index} → L {C} {D} ⊣ R {C} {D})
       → ({C D E : Index} → ∣ P C D ∣ → ∣ P D E ∣ → ∣ P C E ∣)
       → ({C D E : Index} → ∣ Q C D ∣ → ∣ Q D E ∣ → ∣ Q C E ∣)
      indexedLiftOpAlong⊣ L⊣R _⊗P_ a b = ⟦ L ⟧ (⟦ R ⟧ a ⊗P ⟦ R ⟧ b)

  module _ (∣_∣Ix : Index → Setoid) where
    -- general results about ⋈ and ⊣
    private
      𝒫⊆ : Index → Index → Poset
      𝒫⊆ C D = Pred⊆-poset (∣ C ∣Ix ×-setoid ∣ D ∣Ix)

 
    module _ {P≤ : Index → Index → Poset}
      {L : {C D : Index} → 𝒫⊆ C D →mono P≤ C D}
      {R : {C D : Index} → P≤ C D →mono 𝒫⊆ C D}
      (L⊣R : {C D : Index} → L {C} {D} ⊣ R {C} {D}) where
      private
        _[⋈]_ : {C D E : Index} → ∣ P≤ C D ∣ → ∣ P≤ D E ∣ → ∣ P≤ C E ∣
        _[⋈]_ = indexedLiftOpAlong⊣  𝒫⊆ P≤ L⊣R _⋈_

      private module _ {C D : Index} where
        open GaloisConnection (L⊣R {C} {D}) public

      [⋈]-⋈-right-adjoint-lax-monoidal : ∀ {C D E} → IsIndexedLaxMonoidal P≤ 𝒫⊆ _[⋈]_ _⋈_ R C D E
      [⋈]-⋈-right-adjoint-lax-monoidal a b = η (⟦ R ⟧ a ⋈ ⟦ R ⟧ b)

      ⋈-[⋈]-left-adjoint-oplax-monoidal : ∀ {C D E} → IsIndexedOplaxMonoidal 𝒫⊆ P≤ _⋈_ _[⋈]_ L C D E
      ⋈-[⋈]-left-adjoint-oplax-monoidal S S' = L .Mono.mono (⋈-mono S (⟦ R ∘-mono L ⟧ S) S' (⟦ R ∘-mono L ⟧ S') (η S) (η S'))

      module _ (C D E : Index) where
        private
          C≈ = ∣ C ∣Ix
          D≈ = ∣ D ∣Ix
          E≈ = ∣ E ∣Ix

        PreRL⋈Closed = ((S : Pred (C≈ ×-setoid D≈)) (S' : Pred (D≈ ×-setoid E≈)) → S ∈ preRL → S' ∈ preRL → (S ⋈ S') ∈ preRL)
        ⋈∈ImageR = ((a : ∣ P≤ C D ∣) (b : ∣ P≤ D E ∣) → Σ c ∶ ∣ P≤ C E ∣ , (⟦ R ⟧ c ≐ (⟦ R ⟧ a ⋈ ⟦ R ⟧ b)))

        preRL-⋈closed→⋈∈imageR : PreRL⋈Closed → ⋈∈ImageR
        preRL-⋈closed→⋈∈imageR preRL-⋈closed a b =
          let
          Ra⋈Rb∈preRL : (⟦ R ⟧ a ⋈ ⟦ R ⟧ b) ∈ preRL
          Ra⋈Rb∈preRL = preRL-⋈closed (⟦ R ⟧ a) (⟦ R ⟧ b) (R∈preRL a) (R∈preRL b)
          in
          preRL⊆imageR Ra⋈Rb∈preRL 
   
        ⋈∈imageR→[⋈]-⋈-right-adjoint-oplax-monoidal : ⋈∈ImageR → IsIndexedOplaxMonoidal P≤ 𝒫⊆ _[⋈]_ _⋈_ R C D E
        ⋈∈imageR→[⋈]-⋈-right-adjoint-oplax-monoidal ⋈∈imageR a b =
            let
            (c , Rc≐Ra⋈Rb) = ⋈∈imageR a b
            _ : typeOf Rc≐Ra⋈Rb ≡ (⟦ R ⟧ c ≐ (⟦ R ⟧ a ⋈ ⟦ R ⟧ b)) -- debug
            _ = ≡.refl
            open PosetReasoning (Pred⊆-poset (∣ C ∣Ix ×-setoid ∣ E ∣Ix))
            in
            begin
            ⟦ R ⟧ (a [⋈] b)                      ≡⟨⟩
            ⟦ R ∘-mono L ⟧ (⟦ R ⟧ a ⋈ ⟦ R ⟧ b)   ≈˘⟨ (R ∘-mono L) .Mono.cong Rc≐Ra⋈Rb ⟩
            ⟦ R ∘-mono L ⟧ (⟦ R ⟧ c)             ≈⟨ RLR≈R c  ⟩
            ⟦ R ⟧ c                              ≈⟨ Rc≐Ra⋈Rb ⟩
            ⟦ R ⟧ a ⋈ ⟦ R ⟧ b                    ∎ 
  
        preRL-⋈closed→[⋈]-⋈-right-adjoint-oplax-monoidal : PreRL⋈Closed → IsIndexedOplaxMonoidal P≤ 𝒫⊆ _[⋈]_ _⋈_ R C D E 
        preRL-⋈closed→[⋈]-⋈-right-adjoint-oplax-monoidal
          = ⋈∈imageR→[⋈]-⋈-right-adjoint-oplax-monoidal
          ∘ preRL-⋈closed→⋈∈imageR


module _ where
  -- Here we check the oplax-monoidality of G G₀ G₁ G₂ G₃, wrt ∩ and [∩], ⋈ and [⋈]

  module _ (C⨆ : SLat) where
    private
      C≤ = SLat.poset C⨆
      C≈ = SLat.Eq.setoid C⨆
      C = ∣ C⨆ ∣
      open SLat C⨆
      open 𝒫⊆-and-Endo C⨆
      open GaloisConnection F⊣G
      _[∩]_ = liftOpAlong⊣ F⊣G _∩_

    ∩-⨆closed : (R R' : Pred C≈) → Is⨆Closed C⨆ R → Is⨆Closed C⨆ R' → Is⨆Closed C⨆ (R ∩ R')
    ∩-⨆closed R R' R-⨆closed R'-⨆closed S S⊆R∩R' = (R-⨆closed S (proj₁ ∘ S⊆R∩R') , R'-⨆closed S (proj₂ ∘ S⊆R∩R'))

    ∩-preGF-closed : (R R' : Pred C≈) → R ∈ preRL → R' ∈ preRL → (R ∩ R') ∈ preRL
    ∩-preGF-closed R R' R∈preGF R'∈preGF =
      preGF-characterization (R ∩ R') .proj₂
        (∩-⨆closed R R'
          (preGF-characterization R .proj₁ R∈preGF)
          (preGF-characterization R' .proj₁ R'∈preGF))
      
    [∩]-∩-oplax-monoidal : IsOplaxMonoidal _[∩]_ _∩_ G
    [∩]-∩-oplax-monoidal = preRL-∩closed→[∩]-∩-right-adjoint-oplax-monoidal C≈ F⊣G ∩-preGF-closed
      
  module _ where
    private
      module _ {C⨆ D⨆ : SLat} where
        open 𝒫⊆-and-Endo (C⨆ ×-slat D⨆) public
        open GaloisConnection F⊣G public
      _[⋈]_ = indexedLiftOpAlong⊣ SLat (\C D → 𝒫⊆ {C} {D}) (\C D → Endo {C} {D}) (\{C} {D} → F⊣G {C} {D}) _⋈_

    module _ (C⨆ D⨆ E⨆ : SLat) where
      private
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
      ⋈-⨆closed R R' R-⨆closed R'-⨆closed S S⊆R⋈R' =
        (d , {!!} , {!!})
        where
        SRR' : Pred (C≈ ×-setoid (D≈ ×-setoid E≈)) 
        Pred.⟦ SRR' ⟧ (c , d , e) = (c , e) ∈ S × (c , d) ∈ R × (d , e) ∈ R'
        SRR' .Pred.isWellDefined (c≈c' , d≈d' , e≈e') (ce∈S , cd∈R , de∈R') = (S .Pred.isWellDefined (c≈c' , e≈e') ce∈S , R .Pred.isWellDefined (c≈c' , d≈d') cd∈R , R' .Pred.isWellDefined (d≈d' , e≈e') de∈R')

        triple : C × D × E
        triple = SLat.⨆ (C⨆ ×-slat (D⨆ ×-slat E⨆)) SRR'

        c = let (c , d , e) = triple in c
        d = let (c , d , e) = triple in d
        e = let (c , d , e) = triple in e
        _ : SLat._≈_ (C⨆ ×-slat E⨆) (c , e) ( SLat.⨆ (C⨆ ×-slat E⨆) (S ∩ (R ⋈ R')))
        _ = {!!}
        
          


