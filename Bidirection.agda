{-# OPTIONS --type-in-type --postfix-projections #-}

module Bidirection where

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
open import Data.List
open import Data.List.Relation.Unary.All

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
  open BinRMorph renaming (IsOrderHomomorphism to IsMono ; IsRelHomomorphism to IsCong) public
  module Cong = BinRMorph.SetoidHomomorphism renaming (isRelHomomorphism to isCongruent)
  module Mono = BinRMorph.PosetHomomorphism renaming (isOrderHomomorphism to isMonotone)

  _→cong_ = BinRMorph.SetoidHomomorphism
  _→mono_ = BinRMorph.PosetHomomorphism

record HasBracket (A : Set) (B : Set) : Set where
  field
    ⟦_⟧ : A → B

open HasBracket {{...}} public

instance
  cong-map : {x y : Setoid} → HasBracket (x →cong y) (∣ x ∣ → ∣ y ∣)
  HasBracket.⟦ cong-map ⟧ = Cong.⟦_⟧

  mono-map : {x y : Poset} → HasBracket (x →mono y) (∣ x ∣ → ∣ y ∣)
  HasBracket.⟦ mono-map ⟧ = Mono.⟦_⟧

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
  pred-map : {X : Setoid} → HasBracket (Pred X) (∣ X ∣ → Set)
  HasBracket.⟦ pred-map ⟧ = Pred.⟦_⟧

Rel : Set → Set
Rel X = RelPoly X lzero

module _ {X≈ : Setoid} where
  open SetoidPoly X≈
  private
    X = ∣ X≈ ∣

  ≈→↔ : (P : Pred X≈) → {x y : X} → x ≈ y → (⟦ P ⟧ x) ↔ (⟦ P ⟧ y)
  ≈→↔ P x≈y = (Pred.isWellDefined P x≈y) , (Pred.isWellDefined P (sym x≈y))

  _∈_ : X → Pred X≈ → Set
  x ∈ P = x UniR.∈ ⟦ P ⟧

  ∅ : Pred X≈
  Pred.⟦ ∅ ⟧ = UniR.∅
  Pred.isWellDefined ∅ _ ()

  ｛_｝ : X → Pred X≈
  Pred.⟦  ｛ x ｝ ⟧ y = x ≈ y
  ｛ x ｝ .Pred.isWellDefined {y} {z} y≈z x≈y = trans x≈y y≈z



  U : Pred X≈
  Pred.⟦ U ⟧ = UniR.U
  U .Pred.isWellDefined _ _ = _

  _⊆_ : Pred X≈ → Pred X≈ → Set
  P ⊆ Q = ⟦ P ⟧ UniR.⊆ ⟦ Q ⟧


  U-max : (P : Pred X≈) → P ⊆ U
  U-max _ _ = _

  _≐_ : Pred X≈ → Pred X≈ → Set
  P ≐ Q = ⟦ P ⟧ UniR.≐ ⟦ Q ⟧

  ∀↔→≐ : {P Q : Pred X≈} → ((x : X) → x ∈ P ↔ x ∈ Q) → P ≐ Q
  ∀↔→≐ φ = ((λ {x} → φ x .proj₁) , (λ {x} → φ x .proj₂))


  _∩_ : Pred X≈ → Pred X≈ → Pred X≈
  (P ∩ Q) .Pred.⟦_⟧ = (⟦ P ⟧ UniR.∩ ⟦ Q ⟧)
  (P ∩ Q) .Pred.isWellDefined = λ{ x≈y (x∈P , x∈Q) → P.isWellDefined x≈y x∈P , Q.isWellDefined x≈y x∈Q }
    where private
      module P = Pred P
      module Q = Pred Q

  ∩-⊆-l : (S T : Pred X≈) → (S ∩ T) ⊆ S
  ∩-⊆-l S T (d∈S , d∈T) = d∈S

  ∩-⊆-r : (S T : Pred X≈) → (S ∩ T) ⊆ T
  ∩-⊆-r S T (d∈S , d∈T) = d∈T


  ∩-mono-l : (P Q S : Pred X≈) → P ⊆ Q → (P ∩ S) ⊆ (Q ∩ S)
  ∩-mono-l P Q S P⊆Q = (λ (x∈P , x∈S) → (P⊆Q x∈P , x∈S))

  ∩-mono-r : (P Q S : Pred X≈) → P ⊆ Q → (S ∩ P) ⊆ (S ∩ Q)
  ∩-mono-r P Q S P⊆Q = (λ (x∈S , x∈P) → (x∈S , P⊆Q x∈P))

  ∩-mono : (P Q S R : Pred X≈) → P ⊆ Q → S ⊆ R → (P ∩ S) ⊆ (Q ∩ R)
  ∩-mono P Q S R P⊆Q S⊆R = (λ (x∈P , x∈S) → (P⊆Q x∈P , S⊆R x∈S))

  ∩-cong-l : (P Q S : Pred X≈) → P ≐ Q → (P ∩ S) ≐ (Q ∩ S)
  ∩-cong-l P Q S P≐Q = ∩-mono-l P Q S (P≐Q .proj₁) , ∩-mono-l Q P S (P≐Q .proj₂)

  ∩-cong-r : (P Q S : Pred X≈) → P ≐ Q → (S ∩ P) ≐ (S ∩ Q)
  ∩-cong-r P Q S P≐Q = ∩-mono-r P Q S (P≐Q .proj₁) , ∩-mono-r Q P S (P≐Q .proj₂)

  _∪_ : Pred X≈ → Pred X≈ → Pred X≈
  Pred.⟦ P ∪ Q ⟧ = ⟦ P ⟧ UniR.∪ ⟦ Q ⟧
  (P ∪ Q) .Pred.isWellDefined {x} {y} x≈y (inj₁ x∈P) = inj₁ (P .Pred.isWellDefined x≈y x∈P)
  (P ∪ Q) .Pred.isWellDefined {x} {y} x≈y (inj₂ x∈Q) = inj₂ (Q .Pred.isWellDefined x≈y x∈Q)

  ｛_،_｝ : X → X → Pred X≈
  ｛ x ، y ｝ = ｛ x ｝ ∪ ｛ y ｝

  ∪-⊆-l : (S T : Pred X≈) → S ⊆ (S ∪ T)
  ∪-⊆-l S T x∈S = (inj₁ x∈S)

  ∪-⊆-r : (S T : Pred X≈) → T ⊆ (S ∪ T)
  ∪-⊆-r S T x∈T = (inj₂ x∈T)

  listToPred : List X → Pred X≈
  listToPred [] = ∅
  listToPred (x ∷ ls) = ｛ x ｝ ∪ listToPred ls

record FinSubset (X : Setoid) : Set where
  field
    pred : Pred X
    list : List ∣ X ∣
  open SetoidPoly X
  field
    list≈ : listToPred list ≐ pred

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

  imageR-mono : (R : Pred (X≈ ×-setoid Y≈)) → (S S' : Pred X≈) → S ⊆ S' → imageR R S ⊆ imageR R S'
  imageR-mono R S S' S⊆S' {y} (x , xy∈R , x∈S) = (x , xy∈R , S⊆S' x∈S)

  preimageR-raw : UniR.Pred (X × Y) lzero → UniR.Pred Y lzero → UniR.Pred X lzero
  preimageR-raw R Q x = Σ y ∶ Y , R (x , y) × Q y

  preimageR : Pred (X≈ ×-setoid Y≈) → Pred Y≈ → Pred X≈
  Pred.⟦ preimageR R Q ⟧ = preimageR-raw ⟦ R ⟧ ⟦ Q ⟧
  preimageR R Q .Pred.isWellDefined {x} {x'} x≈x' (y , xy∈R , y∈Q) = (y , R .Pred.isWellDefined (x≈x' , Y.refl) xy∈R , y∈Q)

  preimageR-mono : (R : Pred (X≈ ×-setoid Y≈)) → (S S' : Pred Y≈) → S ⊆ S' → preimageR R S ⊆ preimageR R S'
  preimageR-mono R S S' S⊆S' {x} (y , xy∈R , y∈S) = (y , xy∈R , S⊆S' y∈S)

  liftFR-raw : (X → Y) → UniR.Pred (X × Y) lzero
  liftFR-raw f (x , y) = f x Y.≈ y

  liftFR : (X≈ →cong Y≈) → Pred (X≈ ×-setoid Y≈)
  Pred.⟦ liftFR f≈ ⟧ = liftFR-raw ⟦ f≈ ⟧
  liftFR f≈ .Pred.isWellDefined {(x , y)} {(x' , y')} (x≈x' , y≈y') fx≈y = Y.trans (f≈ .Cong.cong (X.sym x≈x')) (Y.trans fx≈y y≈y')

  ⃗ : (X≈ →cong Y≈) → Pred X≈ → Pred Y≈
  ⃗ f = imageR (liftFR f)

  ⃗-mono : (f : X≈ →cong Y≈) → (S S' : Pred X≈) → S ⊆ S' → ⃗ f S ⊆ ⃗ f S'
  ⃗-mono f = imageR-mono (liftFR f)

  ⃗single : (f : X≈ →cong Y≈) → ∀ x →  ⃗ f ｛ x ｝ ≐ ｛ ⟦ f ⟧ x ｝
  ⃗single f x =
    ( (λ {y} (x' , fx'≈y , x≈x') → Y.trans (f .Cong.cong x≈x') fx'≈y)
    , (λ {y} fx≈y → (x , fx≈y , X.refl)))

  ⃗pair  : (f : X≈ →cong Y≈) → ∀ x x' →  ⃗ f ｛ x ، x' ｝ ≐ ｛ ⟦ f ⟧ x ، ⟦ f ⟧ x' ｝
  ⃗pair f x x' =
    ( (λ { {y} (x'' , fx''≈y , inj₁ x≈x'') → inj₁ (Y.trans (f .Cong.cong x≈x'') fx''≈y) ; {y} (x'' , fx''≈y , inj₂ x'≈x'') → inj₂ (Y.trans (f .Cong.cong x'≈x'') fx''≈y)})
    , (λ { {y} (inj₁ fx≈y) → (x , fx≈y , inj₁ X.refl) ; {y} (inj₂ fx'≈y) → (x' , fx'≈y , inj₂ X.refl) }))


  ⃖ : (X≈ →cong Y≈) → Pred Y≈ → Pred X≈
  ⃖ f = preimageR (liftFR f)

  ⃖-mono : (f : X≈ →cong Y≈) → (S S' : Pred Y≈) → S ⊆ S' → ⃖ f S ⊆ ⃖ f S'
  ⃖-mono f = preimageR-mono (liftFR f)

module _ (C≤ : Poset) where
  open PosetPoly C≤
  private
    C = ∣ C≤ ∣
    C≈ = PosetPoly.Eq.setoid C≤

  IsUpwardClosed : Pred C≈ → Set
  IsUpwardClosed S = ∀ x y → x ≤ y → x ∈ S → y ∈ S

  IsDownwardClosed : Pred C≈ → Set
  IsDownwardClosed S = ∀ x y → x ≤ y → y ∈ S → x ∈ S

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
    D = ∣ D≤ ∣
  principal-downset : ∣ D≤ ∣ → Pred D≈
  Pred.⟦ principal-downset d ⟧ d' = d' ≤ d
  Pred.isWellDefined (principal-downset d) d'≈d'' d'≤d = trans (reflexive (Eq.sym d'≈d'')) d'≤d

  principal-downset-mono : (d d' : ∣ D≤ ∣) → D≤ .PosetPoly._≤_ d d' → principal-downset d ⊆ principal-downset d'
  principal-downset-mono d d' d≤d' = (λ d''≤d → trans d''≤d d≤d')

  principal-downset-cong : (d d' : ∣ D≤ ∣) → D≤ .PosetPoly._≈_ d d' → principal-downset d ≐ principal-downset d'
  principal-downset-cong d d' d≈d' = principal-downset-mono d d' (reflexive d≈d') , principal-downset-mono d' d (reflexive (Eq.sym d≈d'))

  lowerbounds : Pred D≈ → Pred D≈
  Pred.⟦ lowerbounds S ⟧ d = ∀ x → x ∈ S → d ≤ x
  lowerbounds S .Pred.isWellDefined d≈d' φ x x∈S = trans (reflexive (Eq.sym d≈d')) (φ x x∈S)

  downset : Pred D≈ → Pred D≈
  Pred.⟦ downset S ⟧ d = Σ x ∶ D , (x ∈ S × d ≤ x)
  downset S .Pred.isWellDefined d≈d' (x , x∈S , d≤x) = (x , x∈S , trans (reflexive (Eq.sym d≈d')) d≤x)

  principal-upset : D → Pred D≈
  Pred.⟦ principal-upset d ⟧ d' = d ≤ d'
  Pred.isWellDefined (principal-upset d) d'≈d'' d≤d' = trans d≤d' (reflexive d'≈d'')

  principal-upset-mono : (d d' : D) → D≤ .PosetPoly._≤_ d d' → principal-upset d' ⊆ principal-upset d
  principal-upset-mono d d' d≤d' = \d'≤d'' → trans d≤d' d'≤d''

  principal-upset-cong : (d d' : D) → D≤ .PosetPoly._≈_ d d' → principal-upset d ≐ principal-upset d'
  principal-upset-cong d d' d≈d' = principal-upset-mono d' d (reflexive (Eq.sym d≈d')) , principal-upset-mono d d' (reflexive d≈d')

  upperbounds : Pred D≈ → Pred D≈
  Pred.⟦ upperbounds S ⟧ u = ∀ x → x ∈ S → x ≤ u
  upperbounds S .Pred.isWellDefined u≈u' φ x x∈S = trans (φ x x∈S) (reflexive u≈u')

  upset : Pred D≈ → Pred D≈
  Pred.⟦ upset S ⟧ u = Σ x ∶ D , (x ∈ S × x ≤ u)
  upset S .Pred.isWellDefined u≈u' (x , x∈S , x≤u) = (x , x∈S , trans x≤u (reflexive u≈u'))

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
    ⨆-sup : ∀ S → (∀ x → x ∈ S → x ≤ ⨆ S) × (∀ y → (∀ x → x ∈ S → x ≤ y) → ⨆ S ≤ y)


  ↓! : Carrier → Pred Eq.setoid
  ↓! = principal-downset poset

  ↓!-mono : ∀ x y → x ≤ y → ↓! x ⊆ ↓! y
  ↓!-mono = principal-downset-mono poset

  ↓!-cong : ∀ x y → x ≈ y → ↓! x ≐ ↓! y
  ↓!-cong = principal-downset-cong poset

  ↑! : Carrier → Pred Eq.setoid
  ↑! = principal-upset poset

  ↑!-mono : ∀ x y → x ≤ y → ↑! y ⊆ ↑! x
  ↑!-mono = principal-upset-mono poset

  ↑!-cong : ∀ x y → x ≈ y → ↑! x ≐ ↑! y
  ↑!-cong = principal-upset-cong poset

  ↓ : Pred Eq.setoid → Pred Eq.setoid
  ↓ = downset poset

  ↑ : Pred Eq.setoid → Pred Eq.setoid
  ↑ = upset poset

  ⨆-ub : ∀ S x → x ∈ S → x ≤ ⨆ S
  ⨆-ub S = ⨆-sup S .proj₁

  ⨆-least : ∀ S y → (∀ x → x ∈ S → x ≤ y) → ⨆ S ≤ y
  ⨆-least S = ⨆-sup S .proj₂

  ⨆-mono : ∀ S S' → S ⊆ S' → ⨆ S ≤ ⨆ S'
  ⨆-mono S S' S⊆S' = ⨆-least S (⨆ S') (\ x x∈S → ⨆-ub S' x (S⊆S' x∈S))

  ⨆-cong : ∀ S S' → S ≐ S' → ⨆ S ≈ ⨆ S'
  ⨆-cong S S' (S⊆S' , S⊇S')  = Po.antisym (⨆-mono S S' S⊆S') (⨆-mono S' S S⊇S')

  ⨆-↓!-≥ : ∀ x → x ≤ ⨆ (↓! x)
  ⨆-↓!-≥ x = ⨆-ub (↓! x) x (Po.reflexive Eq.refl)

  ⨆-↓!-≤ : ∀ x → ⨆ (↓! x) ≤ x
  ⨆-↓!-≤ x = ⨆-least (↓! x) x \x' x'∈↓!x → x'∈↓!x

  ⨆-↓! : ∀ x → ⨆ (↓! x) ≈ x
  ⨆-↓! x = Po.antisym (⨆-↓!-≤ x) (⨆-↓!-≥ x)

  ⊥ : Carrier
  ⊥ = ⨆ ∅

  ⊥-min : Minimum _≤_ ⊥
  ⊥-min x = ⨆-least ∅ x x-ub
    where
    x-ub : ∀ y → Empty.⊥ → y ≤ x
    x-ub y ()

  _⊔_ : Op₂ Carrier
  x ⊔ y = ⨆ ｛ x ، y ｝

  ⊔-comm : ∀ x y → (x ⊔ y) ≈ (y ⊔ x)
  ⊔-comm x y = ⨆-cong (｛ x ، y ｝) (｛ y ، x ｝)
    ( (λ{ (inj₁ x≈) → inj₂ x≈ ; (inj₂ y≈) → inj₁ y≈})
    , (λ{ (inj₁ y≈) → inj₂ y≈ ; (inj₂ x≈) → inj₁ x≈}))


  ⊔-ub-l : ∀ x y → x ≤ (x ⊔ y)
  ⊔-ub-l x y = ⨆-ub _ _ (inj₁ Eq.refl)

  ⊔-ub-r : ∀ x y → y ≤ (x ⊔ y)
  ⊔-ub-r x y = ⨆-ub _ _ (inj₂ Eq.refl)

  ⊔-least : ∀ x y → (∀ z → x ≤ z → y ≤ z → (x ⊔ y) ≤ z)
  ⊔-least x y z x≤z y≤z = ⨆-least _ _ z-ub
    where
    z-ub : ∀ w → (x ≈ w) ⊎ (y ≈ w) → w ≤ z
    z-ub w (inj₁ x≈w) = Po.trans (Po.reflexive (Eq.sym x≈w)) x≤z
    z-ub w (inj₂ y≈w) = Po.trans (Po.reflexive (Eq.sym y≈w)) y≤z

  ⨆-⊔-comm : ∀ P Q → (⨆ P ⊔ ⨆ Q) ≈ ⨆ (P ∪ Q)
  ⨆-⊔-comm P Q = Po.antisym (⨆-least ｛ ⨆ P ، ⨆ Q ｝ (⨆ (P ∪ Q)) ⨆P∪Q-ub ) (⨆-least (P ∪ Q) (⨆ ｛ ⨆ P ، ⨆ Q ｝) ⨆P⊔⨆Q-ub)
    where
    ⨆P∪Q-ub : ∀ x → x ∈ ｛_،_｝{Eq.setoid} (⨆ P) (⨆ Q) → x ≤ ⨆ (P ∪ Q)
    ⨆P∪Q-ub x (inj₁ ⨆P≈x) = Po.reflexive (Eq.sym ⨆P≈x) ⟨ Po.trans ⟩ ⨆-mono P (P ∪ Q) (∪-⊆-l P Q)
    ⨆P∪Q-ub x (inj₂ ⨆Q≈x) = Po.reflexive (Eq.sym ⨆Q≈x) ⟨ Po.trans ⟩ ⨆-mono Q (P ∪ Q) (∪-⊆-r P Q)
    ⨆P⊔⨆Q-ub : ∀ x → x ∈ (P ∪ Q) → x ≤ (⨆ P ⊔ ⨆ Q)
    ⨆P⊔⨆Q-ub x (inj₁ x∈P) = ⨆-ub P x x∈P ⟨ Po.trans ⟩ ⊔-ub-l (⨆ P) (⨆ Q)
    ⨆P⊔⨆Q-ub x (inj₂ x∈Q) = ⨆-ub Q x x∈Q ⟨ Po.trans ⟩ ⊔-ub-r (⨆ P) (⨆ Q)

  ≤→⊔-≈ : ∀ x y → x ≤ y → (x ⊔ y) ≈ y
  ≤→⊔-≈ x y x≤y = Po.antisym (⊔-least x y y x≤y Po.refl) (⊔-ub-r x y)


  ⊤ : Carrier
  ⊤ = ⨆ U

  ⊤-max : Maximum _≤_ ⊤
  ⊤-max x = ⨆-ub U x tt

  ⊤≈⨆U : ⊤ ≈ ⨆ U
  ⊤≈⨆U = Po.antisym (⨆-ub U _ tt ) (⊤-max (⨆ U))

  ⨆≤→∀≤ : ∀ S x → ⨆ S ≤ x → ∀ x' → x' ∈ S → x' ≤ x
  ⨆≤→∀≤ S x ⨆S≤x x' x'∈S = Po.trans (⨆-ub _ _ x'∈S) ⨆S≤x

  ⨆≤←∀≤ : ∀ S x → (∀ x' → x' ∈ S → x' ≤ x) → ⨆ S ≤ x
  ⨆≤←∀≤ = ⨆-least

  ⨆≤↔∀≤ : ∀ S x → ⨆ S ≤ x ↔ (∀ x' → x' ∈ S → x' ≤ x)
  ⨆≤↔∀≤ S x .proj₁ = ⨆≤→∀≤ S x
  ⨆≤↔∀≤ S x .proj₂ = ⨆≤←∀≤ S x

  ⨅ : Pred Eq.setoid → Carrier
  ⨅ S = ⨆ (lowerbounds poset S)

  ⨅-lb : ∀ S x → x ∈ S → ⨅ S ≤ x
  ⨅-lb S x x∈S = ⨆-least (lowerbounds poset S) x x-ub
    where
    x-ub : ∀ y → y ∈ lowerbounds poset S → y ≤ x
    x-ub y y∈lbS = y∈lbS x x∈S

  ⨅-greatest : ∀ S y → (∀ x → x ∈ S → y ≤ x) → y ≤ ⨅ S
  ⨅-greatest S y y-lower = ⨆-ub (lowerbounds poset S) y y-lower

  ⨅-inf : ∀ S → (∀ x → x ∈ S → ⨅ S ≤ x) × (∀ y → (∀ x → x ∈ S → y ≤ x) → y ≤ ⨅ S)
  ⨅-inf S = (⨅-lb S ,  ⨅-greatest S)

  _⊓_ : Op₂ Carrier
  x ⊓ y = ⨅  (｛ x ｝ ∪ ｛ y ｝)

  ⊓-lb-l : ∀ x y → (x ⊓ y) ≤ x
  ⊓-lb-l x y = ⨅-lb (｛ x ｝ ∪ ｛ y ｝) x (inj₁ Eq.refl )

  ⊓-lb-r : ∀ x y → (x ⊓ y) ≤ y
  ⊓-lb-r x y = ⨅-lb (｛ x ｝ ∪ ｛ y ｝) y (inj₂ Eq.refl)

  ⊓-greatest : ∀ x y z → z ≤ x → z ≤ y → z ≤ (x ⊓ y)
  ⊓-greatest x y z z≤x z≤y = ⨅-greatest (｛ x ｝ ∪ ｛ y ｝) z z-lb
    where
    z-lb : ∀ w → (x ≈ w) ⊎ (y ≈ w) → z ≤ w
    z-lb w (inj₁ x≈w) = Po.trans z≤x (Po.reflexive x≈w)
    z-lb w (inj₂ y≈w) = Po.trans z≤y (Po.reflexive y≈w)

  ⊓-inf : Infimum _≤_ _⊓_
  ⊓-inf x y = ⊓-lb-l x y , ⊓-lb-r x y , ⊓-greatest x y

  ⊓-mono-l : ∀ y x x' → x ≤ x' → (x ⊓ y) ≤ (x' ⊓ y)
  ⊓-mono-l y x x' x≤x' = ⊓-greatest x' y (x ⊓ y) (Po.trans (⊓-lb-l x y) x≤x') (⊓-lb-r x y)

  ⊓-mono-r : ∀ x y y' → y ≤ y' → (x ⊓ y) ≤ (x ⊓ y')
  ⊓-mono-r x y y' y≤y' = ⊓-greatest x y' (x ⊓ y) (⊓-lb-l x y) (Po.trans (⊓-lb-r x y) y≤y')

  ⊓-mono : ∀ x y x' y' → x ≤ x' → y ≤ y' → (x ⊓ y) ≤ (x' ⊓ y')
  ⊓-mono x y x' y' x≤x' y≤y' = ⊓-greatest x' y' (x ⊓ y) (Po.trans (⊓-lb-l x y) x≤x') (Po.trans (⊓-lb-r x y) y≤y')

  ⊓-cong :  ∀ x y x' y' → x ≈ x' → y ≈ y' → (x ⊓ y) ≈ (x' ⊓ y')
  ⊓-cong x y x' y' x≈x' y≈y' =
    Po.antisym
      (⊓-mono x y x' y' (Po.reflexive x≈x') (Po.reflexive y≈y'))
      (⊓-mono x' y' x y (Po.reflexive (Eq.sym x≈x')) (Po.reflexive (Eq.sym y≈y')))

  ≤⊓→≤× : ∀ y z x → x ≤ (y ⊓ z) → x ≤ y × x ≤ z
  ≤⊓→≤× y z x x≤y⊓z = (Po.trans x≤y⊓z (⊓-lb-l y z)) , (Po.trans x≤y⊓z (⊓-lb-r y z))

  ≤⊓←≤× : ∀ y z x → x ≤ y × x ≤ z → x ≤ (y ⊓ z)
  ≤⊓←≤× y z x (x≤y , x≤z) = ⊓-greatest y z x x≤y x≤z

  ≤⊓↔≤× : ∀ y z x → (x ≤ (y ⊓ z)) ↔ (x ≤ y × x ≤ z)
  ≤⊓↔≤× y z x = ≤⊓→≤× y z x , ≤⊓←≤× y z x


  ⊓≈⨆∩↓! : ∀ x y → (x ⊓ y) ≈ ⨆ (↓! x ∩ ↓! y)
  ⊓≈⨆∩↓! x y = Po.antisym
    (⨆-ub (↓! x ∩ ↓! y) (x ⊓ y) (⊓-inf x y .proj₁ , ⊓-inf x y .proj₂ .proj₁))
    (⊓-inf x y .proj₂ .proj₂ (⨆ (↓! x ∩ ↓! y)) (⨆-least (↓! x ∩ ↓! y) x (\_ p → p .proj₁)) ( (⨆-least (↓! x ∩ ↓! y) y (\_ p → p .proj₂))))

  ⨆↓!≈⨆↓!∩ : ∀ x S → x ∈ S → ⨆ (↓! x) ≈ ⨆ (↓! x ∩ S)
  ⨆↓!≈⨆↓!∩ x S x∈S = Po.antisym
    (⨆-ub (↓! x ∩ S) (⨆ (↓! x)) (⨆-↓!-≤ x , Pred.isWellDefined S (Eq.sym (⨆-↓! x)) x∈S))
    (⨆-mono (↓! x ∩ S) (↓! x) proj₁)

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
      f x      ≤⟨ f≤ .Mono.mono (⨆-ub (post≤ f≈) x x≤fx) ⟩
      f (ν f≈) ∎

    R : ν f≈ ≤ f (ν f≈)
    R =
      begin
      ν f≈     ≤⟨ ⨆-least (post≤ f≈) (f (ν f≈)) ι ⟩
      f (ν f≈) ∎

    L : f (ν f≈) ≤ ν f≈
    L =
      begin
      f (ν f≈) ≤⟨ ⨆-ub (post≤ f≈) (f (ν f≈)) (f≤ .Mono.mono (⨆-least (post≤ f≈) (f (ν f≈)) ι)) ⟩
      ν f≈     ∎

  ν-gfp f≤ .proj₂ x' x'∈fixf = u -- proof that ν f is the greatest fixed point
    where
    f≈ = ⟦ f≤ ⟧cong
    f = ⟦ f≤ ⟧
    open PosetReasoning poset
    u =
      begin
      x'   ≤⟨ ⨆-ub (post≤ f≈) x' (Po.reflexive x'∈fixf) ⟩
      ν f≈ ∎

  ν-mono : (f≈ g≈ : Eq.setoid →cong Eq.setoid) → ((x : Carrier) → ⟦ f≈ ⟧ x ≤ ⟦ g≈ ⟧ x) → ν f≈ ≤ ν g≈
  ν-mono f≈ g≈ f≤g = ⨆-mono (post≤ f≈) (post≤ g≈) (λ {d} d≤fd → Po.trans d≤fd (f≤g d))

  μ : (Eq.setoid →cong Eq.setoid) → Carrier
  μ f = ⨅ (pre poset f)

  IsCompact : (x : Carrier)  → Set
  IsCompact x = ∀ S → x ≤ ⨆ S → Σ xs ∶ List Carrier , All (_∈ S) xs × x ≤ ⨆ (listToPred xs)

  IsDirected : (S : Pred Eq.setoid) → Set
  IsDirected S = ∀ (xs : List Carrier) → All (λ x → x ∈ S) xs → Σ u ∶ Carrier , (u ∈ S × All (λ x → x ≤ u) xs)

  IsChain : (S : Pred Eq.setoid) → Set
  IsChain S = ∀ x y → x ∈ S → y ∈ S → x ≤ y ⊎ y ≤ x

  -- Scott open [Taylor, 2010, A lambda calculus for real analysis, Def. 3.1]
  IsScottOpen : (S : Pred Eq.setoid) → Set
  IsScottOpen S = IsUpwardClosed poset S × (∀ T → (⨆ T) ∈ S → Σ xs ∶ List Carrier , listToPred xs ⊆ T × ⨆ (listToPred xs) ∈ S)


instance
  slat-has-carrier : HasCarrier (SLat)
  slat-has-carrier .HasCarrier.Carrier = SLat.Carrier

module _ (D⨆ E⨆ : SLat) where
  private
    module D = SLat D⨆
    D≤ = D.poset
    D≈ = D.Eq.setoid
    D = ∣ D⨆ ∣

    module E = SLat E⨆
    E≤ = E.poset
    E≈ = E.Eq.setoid
    E = ∣ E⨆ ∣

  IsScottContinuous : (D≈ →cong E≈) → Set
  IsScottContinuous f≈ = (S : Pred E≈) → E.IsScottOpen S → D.IsScottOpen (⃖ f≈ S)

  Is⨆Preserving : (D≈ →cong E≈) → Set
  Is⨆Preserving f≈ = (S : Pred D≈) → ⟦ f≈ ⟧ (D.⨆ S) E.≈ E.⨆ (⃗ f≈ S)

  Is⨅Preserving : (D≈ →cong E≈) → Set
  Is⨅Preserving f≈ = (S : Pred D≈) → ⟦ f≈ ⟧ (D.⨅ S) E.≈ E.⨅ (⃗ f≈ S)




  record Cont : Set where
    field
      ⟦_⟧cong' : D≈ →cong E≈
      cont : Is⨆Preserving ⟦_⟧cong'


module _ (D⨆ : SLat) where
  open SLat D⨆
  private
    D≤ = poset
    D≈ = Eq.setoid
    D = ∣ D⨆ ∣

  ⨆S↓!⨆S : (S↓! S : Pred D≈) → (∀ d → d ∈ S↓! → Σ d' ∶ D , d' ∈ S × d ≤ d') → ⨆ S↓! ≤ ⨆ S
  ⨆S↓!⨆S S↓! S d∈S↓!→d≤d'∈S = ⨆-least S↓! (⨆ S) P₁
    where
    open PosetReasoning D≤
    P₁ : (d : D) → d ∈ S↓! → d ≤ ⨆ S
    P₁ d d∈S↓! =
      let
      (d' , d'∈S , d≤d') = d∈S↓!→d≤d'∈S d d∈S↓!
      in
      begin
      d ≤⟨ d≤d' ⟩
      d' ≤⟨ ⨆-ub S d' d'∈S ⟩
      ⨆ S ∎

  ⨆-endomono : (f : D≤ →mono D≤) (S : Pred D≈) → ((d : D) → d ∈ S → d ≤ ⟦ f ⟧ d) → ((d : D) → ( ⨆ (↓! d ∩ S) ≤ ⟦ f ⟧ d))
  ⨆-endomono f S ∈S→postfix-of-f d = ⨆-least (↓! d ∩ S) (⟦ f ⟧ d) ↓!d∩S⇒≤fd
    where
    ↓!d∩S⇒≤fd : ∀ d' → d' ∈ (↓! d ∩ S) → d' ≤ ⟦ f ⟧ d
    ↓!d∩S⇒≤fd d' (d'≤d , d'∈S) = Po.trans (∈S→postfix-of-f d' d'∈S) (Mono.mono f d'≤d)

  ⨆-endomono' : (f : D≤ →mono D≤) (S : Pred D≈) → ((d : D) → ( ⨆ (↓! d ∩ S) ≤ ⟦ f ⟧ d)) → ((d : D) → d ∈ S → d ≤ ⟦ f ⟧ d)
  ⨆-endomono' f S ⨆↓!-∩S≤f- d d∈S = Po.trans (⨆-ub (↓! d ∩ S) d (Po.refl , d∈S)) (⨆↓!-∩S≤f- d)

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
  {-
  (D ×-slat E) ._⊓_ (d , e) (d' , e') = (D ._⊓_ d d' , E ._⊓_ e e')
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
    -}
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

module _ (D⨆ : SLat) (E⨆ : SLat) where
  private
    module D = SLat D⨆
    module E = SLat E⨆
  open SLat (D⨆ ×-slat E⨆)

  ⊔-componentwise : ∀ d e d' e' → ((d , e) ⊔ (d' , e')) ≈ (d D.⊔ d' , e E.⊔ e')
  ⊔-componentwise d e d' e' = Po.antisym
    (⨆-least (｛(d , e)｝ ∪ ｛(d' , e')｝) (d D.⊔ d' , e E.⊔ e')
       λ { p (inj₁ de≈p) → Po.trans (Po.reflexive (Eq.sym de≈p)) (D.⊔-ub-l d d' , E.⊔-ub-l e e')
         ; p (inj₂ d'e'≈p) → Po.trans (Po.reflexive (Eq.sym d'e'≈p)) (D.⊔-ub-r d d' , E.⊔-ub-r e e')})
    ( D.⨆-mono (｛ d ｝ ∪ ｛ d' ｝) ((｛ (d , e) ｝ ∪ ｛ (d' , e') ｝) ∣₁) (λ{ (inj₁ d≈) → (e , inj₁ (d≈ , E.Eq.refl)) ; (inj₂ d'≈) → (e' , inj₂ (d'≈ , E.Eq.refl))})
    , E.⨆-mono (｛ e ｝ ∪ ｛ e' ｝) ((｛ (d , e) ｝ ∪ ｛ (d' , e') ｝) ∣₂) (λ{ (inj₁ e≈) → (d , inj₁ (D.Eq.refl , e≈)) ; (inj₂ e'≈) → (d' , inj₂ (D.Eq.refl , e'≈))}))

IsCoclosure : (D : Poset) (f : ∣ D ∣ → ∣ D ∣) → Set
IsCoclosure D f = ∀ d → f d ≤ d × f d ≤ f (f d)
  where open PosetPoly D

Is⨆Closed : (D : SLat) → Pred (SLat.Eq.setoid D) → Set
Is⨆Closed D S = ∀ S' → S' ⊆ S → (SLat.⨆ D S') ∈ S

Is⊔Closed : (D : SLat) → Pred (SLat.Eq.setoid D) → Set
Is⊔Closed D S = ∀ x y → x ∈ S → y ∈ S → (SLat._⊔_ D x y) ∈ S

⨆closed→⊔closed : (D : SLat) → (S : Pred (SLat.Eq.setoid D)) → Is⨆Closed D S → Is⊔Closed D S
⨆closed→⊔closed D S ⨆closed x y x∈S y∈S = ⨆closed (｛ x ｝ ∪ ｛ y ｝) λ{ (inj₁ x≈) → S .Pred.isWellDefined x≈ x∈S ; (inj₂ y≈) → S .Pred.isWellDefined y≈ y∈S}

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

  module _ {C : Poset} {D : Poset} (L : C →mono D ) (R : D →mono C) where
    module _ (L⊣R : L ⊣ R) where
      open GaloisConnection L⊣R
      private
        module C = PosetPoly C
        module D = PosetPoly D

        -- L ⊣ R → R d = max (L⁻¹ ↓ d)
        R-belongs : ∀ d → ⟦ R ⟧ d ∈ ⃖ ⟦ L ⟧cong (principal-downset D d)
        R-belongs d = ⟦ L ⟧ (⟦ R ⟧ d) , (D.Eq.refl , ε d)

        R-greatest : ∀ d c → c ∈ ⃖ ⟦ L ⟧cong (principal-downset D d) → c C.≤ ⟦ R ⟧ d
        R-greatest d c (d' , Lc≈d' , d'≤d) = C.trans (ψ c d' .proj₁ (D.reflexive (Lc≈d'))) (R .Mono.mono d'≤d)

  module _ (C⨆ D⨆ : SLat) where
    private
      module C = SLat C⨆
      C≤ = C.poset
      C≈ = C.Eq.setoid
      C = ∣ C⨆ ∣
      module D = SLat D⨆
      D≤ = D.poset
      D≈ = D.Eq.setoid
      D = ∣ D⨆ ∣

    ⨆m≤m⨆ : (m : C≤ →mono D≤) → (S : Pred C≈) → D.⨆ (⃗ ⟦ m ⟧cong S) D.≤ ⟦ m ⟧ (C.⨆ S)
    ⨆m≤m⨆ m S = D.⨆-least (⃗ ⟦ m ⟧cong S) (⟦ m ⟧ (C.⨆ S)) m⨆S-upper
      where
      m⨆S-upper : ∀ d → d ∈ ⃗ ⟦ m ⟧cong S → d D.≤ ⟦ m ⟧ (C.⨆ S)
      m⨆S-upper d (c , mc≈d , c∈S) =
        let open PosetReasoning D≤ in
        begin
        d              ≈˘⟨ mc≈d ⟩
        ⟦ m ⟧ c        ≤⟨ m .Mono.mono (C.⨆-ub S c c∈S) ⟩
        ⟦ m ⟧ (C.⨆ S) ∎

    m⨅≤⨅m : (m : D≤ →mono C≤) → (S : Pred D≈) → ⟦ m ⟧ (D.⨅ S) C.≤ C.⨅ (⃗ ⟦ m ⟧cong S)
    m⨅≤⨅m m S = C.⨅-greatest (⃗ ⟦ m ⟧cong S) (⟦ m ⟧ (D.⨅ S)) m⨅S-lower
      where
      m⨅S-lower : ∀ c → c ∈ ⃗ ⟦ m ⟧cong S → ⟦ m ⟧ (D.⨅ S) C.≤ c
      m⨅S-lower c (d , md≈c , d∈S) =
        let open PosetReasoning C≤ in
        begin
        ⟦ m ⟧ (D.⨅ S) ≤⟨ m .Mono.mono (D.⨅-lb S d d∈S) ⟩
        ⟦ m ⟧ d        ≈⟨ md≈c ⟩
        c              ∎

    module _ (L : C≤ →mono D≤) (R : D≤ →mono C≤) (L⊣R : L ⊣ R) where
      open GaloisConnection L⊣R
      left-adjunction→⨆preserving : Is⨆Preserving C⨆ D⨆ ⟦ L ⟧cong
      left-adjunction→⨆preserving S = D.Po.antisym L⨆≤⨆L (⨆m≤m⨆ L S)
        where
        d : D
        d = D.⨆ (⃗ ⟦ L ⟧cong S)

        Rd-upper : ∀ c → c ∈ S → c C.≤ ⟦ R ⟧ d
        Rd-upper c c∈S = ψ c d .proj₁ (D.⨆-ub (⃗ ⟦ L ⟧cong S) (⟦ L ⟧ c) (c , (D.Eq.refl , c∈S)))

        L⨆≤⨆L : ⟦ L ⟧ (C.⨆ S) D.≤ d -- non-trivial
        L⨆≤⨆L =
          let open PosetReasoning D≤ in
          begin
          ⟦ L ⟧ (C.⨆ S)       ≤⟨ L .Mono.mono (C.⨆-least S (⟦ R ⟧ d) Rd-upper) ⟩
          ⟦ L ⟧ (⟦ R ⟧ d)      ≤⟨ ε d ⟩
          D.⨆ (⃗ ⟦ L ⟧cong S) ∎

      right-adjunction→⨅preserving : Is⨅Preserving D⨆ C⨆ ⟦ R ⟧cong
      right-adjunction→⨅preserving S = C.Po.antisym (m⨅≤⨅m R S) ⨅R≤R⨅
        where
        c : C
        c = C.⨅ (⃗ ⟦ R ⟧cong S)

        Lc-lower : ∀ d → d ∈ S → ⟦ L ⟧ c D.≤ d
        Lc-lower d d∈S = ψ c d .proj₂ (C.⨅-lb (⃗ ⟦ R ⟧cong S) (⟦ R ⟧ d) (d , (C.Eq.refl , d∈S)))

        ⨅R≤R⨅ : C.⨅ (⃗ ⟦ R ⟧cong S) C.≤ ⟦ R ⟧ (D.⨅ S)
        ⨅R≤R⨅ =
          let open PosetReasoning C≤ in
          begin
          C.⨅ (⃗ ⟦ R ⟧cong S) ≤⟨ η c ⟩
          ⟦ R ⟧ (⟦ L ⟧ c)      ≤⟨ R .Mono.mono (D.⨅-greatest S (⟦ L ⟧ c) Lc-lower) ⟩
          ⟦ R ⟧ (D.⨅ S)       ∎


    module _ (L : C≤ →mono D≤) (L-⨆preserving : Is⨆Preserving C⨆ D⨆ ⟦ L ⟧cong) where

      private
        R : D≤ →mono C≤
        ⟦ R ⟧ d = C.⨆ (⃖ ⟦ L ⟧cong (D.↓! d))
        R .isMonotone .IsMono.mono {d} {d'} d≤d' = C.⨆-mono (⃖ ⟦ L ⟧cong (D.↓! d)) (⃖ ⟦ L ⟧cong (D.↓! d')) (⃖-mono ⟦ L ⟧cong (D.↓! d) (D.↓! d')
          (λ x≤d → D.Po.trans x≤d d≤d' ))
        R .isMonotone .IsMono.cong d≈d' = C.Po.antisym
          (R .isMonotone .IsMono.mono (D.Po.reflexive d≈d'))
          (R .isMonotone .IsMono.mono (D.Po.reflexive (D.Eq.sym d≈d')))

      ⨆preserving→left-transpose : ∀ c d → c C.≤ ⟦ R ⟧ d → ⟦ L ⟧ c D.≤ d
      ⨆preserving→left-transpose c d = α
        where
        β : ⃗ ⟦ L ⟧cong (⃖ ⟦ L ⟧cong (D.↓! d)) ⊆ D.↓! d
        β {d'} d'∈LL⁻¹↓d@(c' , Lc'≈d' , d'' , Lc'≈d'' , d''≤d) =
          let open PosetReasoning D≤ in
          begin
          d'       ≈˘⟨ Lc'≈d' ⟩
          ⟦ L ⟧ c' ≈⟨ Lc'≈d'' ⟩
          d''      ≤⟨ d''≤d ⟩
          d        ∎

        α : c C.≤ ⟦ R ⟧ d → ⟦ L ⟧ c D.≤ d
        α c≤Rd =
          let open PosetReasoning D≤ in
          begin
          ⟦ L ⟧ c ≤⟨ L .isMonotone .IsMono.mono c≤Rd ⟩
          ⟦ L ⟧ (⟦ R ⟧ d) ≈⟨ L-⨆preserving (⃖ ⟦ L ⟧cong (D.↓! d)) ⟩
          D.⨆ (⃗ ⟦ L ⟧cong (⃖ ⟦ L ⟧cong (D.↓! d))) ≤⟨ D.⨆-mono (⃗ ⟦ L ⟧cong (⃖ ⟦ L ⟧cong (D.↓! d))) (D.↓! d) β ⟩
          D.⨆ (D.↓! d) ≈⟨ D.⨆-↓! d ⟩
          d ∎

    module _ (L : C≤ →mono D≤) where

      private
        R : D≤ →mono C≤
        ⟦ R ⟧ d = C.⨆ (⃖ ⟦ L ⟧cong (D.↓! d))
        R .isMonotone .IsMono.mono {d} {d'} d≤d' = C.⨆-mono (⃖ ⟦ L ⟧cong (D.↓! d)) (⃖ ⟦ L ⟧cong (D.↓! d')) (⃖-mono ⟦ L ⟧cong (D.↓! d) (D.↓! d')
          (λ x≤d → D.Po.trans x≤d d≤d' ))
        R .isMonotone .IsMono.cong d≈d' = C.Po.antisym
          (R .isMonotone .IsMono.mono (D.Po.reflexive d≈d'))
          (R .isMonotone .IsMono.mono (D.Po.reflexive (D.Eq.sym d≈d')))

      module _
        (left-transpose : ∀ c d → c C.≤ ⟦ R ⟧ d → ⟦ L ⟧ c D.≤ d) where

        left-transpose→⨆preserving : Is⨆Preserving C⨆ D⨆ ⟦ L ⟧cong
        left-transpose→⨆preserving S = D.Po.antisym L⨆S≤⨆LS ⨆LS≤L⨆S
          where
          L⨆S≤⨆LS : ⟦ L ⟧ (C.⨆ S) D.≤ D.⨆ (⃗ ⟦ L ⟧cong S)
          L⨆S≤⨆LS = left-transpose (C.⨆ S) (D.⨆ (⃗ ⟦ L ⟧cong S)) (C.⨆-mono S (⃖ ⟦ L ⟧cong (D.↓! (D.⨆ (⃗ ⟦ L ⟧cong S)))) S⊆L⁻¹↓[⨆LS])
            where
            S⊆L⁻¹↓[⨆LS] : S ⊆ ⃖ ⟦ L ⟧cong (D.↓! (D.⨆ (⃗ ⟦ L ⟧cong S)))
            S⊆L⁻¹↓[⨆LS] {c} c∈S = (⟦ L ⟧ c , D.Eq.refl , D.⨆-ub (⃗ ⟦ L ⟧cong S) (⟦ L ⟧ c) (c , D.Eq.refl , c∈S))

          ⨆LS≤L⨆S : D.⨆ (⃗ ⟦ L ⟧cong S) D.≤ ⟦ L ⟧ (C.⨆ S)
          ⨆LS≤L⨆S = D.⨆-least (⃗ ⟦ L ⟧cong S) (⟦ L ⟧ (C.⨆ S)) L⨆S-upper
            where
            L⨆S-upper : ∀ d → d ∈ ⃗ ⟦ L ⟧cong S → d D.≤ ⟦ L ⟧ (C.⨆ S)
            L⨆S-upper d (c , Lc≈d , c∈S) =
              let open PosetReasoning D≤ in
              begin
              d              ≈˘⟨ Lc≈d ⟩
              ⟦ L ⟧ c        ≤⟨ L .Mono.mono (C.⨆-ub S c c∈S) ⟩
              ⟦ L ⟧ (C.⨆ S) ∎ -- d (c , Lc≈d , c∈S) = {!!}



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
  --        F ↓! ⊣ ↑! G
  --  ((D × E →m D × E) , ≤)
  --
  -- This is followed by adjoint poset map between subsets and endo monotone functions (general setting)
  --    (𝒫 (C) , ⊆)
  --     F ↓! ⊣ ↑! G
  --   ((C →m C) , ≤)

  -- F : (Pred⊆-poset D≈) →mono (D≤ →mono≤-poset D≤)
  -- G : (D≤ →mono≤-poset D≤) →mono (Pred⊆-poset D≈)
  -- F⊣G : F ⊣ G

  F-raw : Pred C≈ → C → C
  F-raw S d = ⨆ (↓! d ∩ S)

  F-mono : Pred C≈ → (C≤ →mono C≤)
  Mono.⟦ F-mono S ⟧ = F-raw S
  F-mono S .Mono.isMonotone .IsMono.mono {d} {d'}
    = ⨆-mono (↓! d ∩ S) (↓! d' ∩ S)
    ∘ ∩-mono-l (↓! d) (↓! d') S
    ∘ ↓!-mono d d'
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
    = ⨆-mono (↓! d ∩ P) (↓! d ∩ Q)
             (∩-mono-r P Q (↓! d) P⊆Q)
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
  F⊣G .GaloisConnection.ψ P f .proj₁ FP≤f {d} d∈P = Po.trans (⨆-ub (↓! d ∩ P) d (Po.refl , d∈P)) (FP≤f d)
  F⊣G .GaloisConnection.ψ P f .proj₂ P⊆Gf d = ⨆-least (↓! d ∩ P) (⟦ f ⟧ d) \d' (d'≤d , d'∈P) → Po.trans (P⊆Gf d'∈P) (Mono.mono f d'≤d)
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
    (∀ x → f x ≤ ⨆ (↓! x ∩ post C≤ f≈ )) ≈⟨ lift↔ _ _ ψ ⟩
    (∀ x → f x ≤ x × (f x ≤ f (f x))) ≡⟨⟩
    IsCoclosure C≤ f ∎
    where
    f≈ = ⟦ f≤ ⟧cong
    f = ⟦ f≤ ⟧
    ψ : ∀ d → (f d ≤ ⨆ (↓! d ∩ post C≤ f≈)) ↔ ((f d ≤ d) × (f d ≤ f (f d)))
    ψ d = Product.< ε , δ > , uncurry φ
      where
      ε : f d ≤ ⨆ (↓! d ∩ post C≤ f≈) → f d ≤ d
      ε φ =
        let open PosetReasoning C≤ in
        begin
        f d  ≤⟨ φ ⟩
        ⨆ (↓! d ∩ post C≤ f≈)  ≤⟨ ⨆-mono (↓! d ∩ post C≤ f≈) (↓! d) (∩-⊆-l (↓! d) (post C≤ f≈)) ⟩
        ⨆ (↓! d) ≈⟨ ⨆-↓! d ⟩
        d  ∎
      δ : f d ≤ ⨆ (↓! d ∩ post C≤ f≈) → f d ≤ f (f d)
      δ φ =
        let open PosetReasoning C≤ in
        begin
        f d  ≤⟨ φ ⟩
        ⨆ (↓! d ∩ post C≤ f≈)  ≤⟨ ⨆-least (↓! d ∩ post C≤ f≈) (f (f d)) P2' ⟩
        f (f d)  ∎
        where
        P2' : ∀ d' → d' ∈ (↓! d ∩ post C≤ f≈) → d' ≤ f (f d)
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

      φ : f d ≤ d → f d ≤ f (f d) → f d ≤ ⨆ (↓! d ∩ post C≤ f≈)
      φ fd≤d fd≤ffd =
        let open PosetReasoning C≤ in
        begin
        f d ≤⟨ ⨆-ub (↓! d ∩ post C≤ f≈) (f d) (fd≤d , fd≤ffd) ⟩
        ⨆ (↓! d ∩ post C≤ f≈) ∎

  all-subset-is-postGF : (R : Pred C≈) → (R ∈ post (Pred⊆-poset C≈) ⟦ G ∘-mono F ⟧cong)
  all-subset-is-postGF R = GaloisConnection.η F⊣G R

  module _ where
    open GaloisConnection
    preGF-characterization : (R : Pred C≈) → R ∈ preRL F⊣G ↔ Is⨆Closed C⨆ R
    preGF-characterization R =
      let open SetoidReasoning (Prop↔-setoid) in
      begin
      R ∈ preRL F⊣G ≡⟨⟩
      (G-pred ∘ F-mono) R ⊆ R ≈⟨ λ- , _$- ⟩
      (∀ d → d ≤ ⨆ (↓! d ∩ R) → d ∈ R) ≈⟨ γ , γ⁻¹ ⟩
      (∀ S → S ⊆ R → ⨆ S ∈ R) ≡⟨⟩
      Is⨆Closed C⨆ R ∎
      where
      γ : (∀ d → d ≤ ⨆ (↓! d ∩ R) → d ∈ R) → ∀ S → S ⊆ R → ⨆ S ∈ R
      γ φ S S⊆R = φ (⨆ S) (⨆-mono S (↓! (⨆ S) ∩ R) \ {d} d∈S → ⨆-ub S d d∈S  , S⊆R d∈S)

      γ⁻¹ : (∀ S → S ⊆ R → ⨆ S ∈ R) → ∀ d → d ≤ ⨆ (↓! d ∩ R) → d ∈ R
      γ⁻¹ ψ d d≤⨆↓!d∩R = R .Pred.isWellDefined (Po.antisym χ χ⁻¹)  (ψ (↓! d ∩ R) (∩-⊆-r (↓! d) R))
        where
        χ : ⨆ (↓! d ∩ R) ≤ d
        χ = Po.trans (⨆-mono _ _ (∩-⊆-l (↓! d) R)) (⨆-↓!-≤ d)

        χ⁻¹ : d ≤ ⨆ (↓! d ∩ R)
        χ⁻¹ = d≤⨆↓!d∩R

  -- Hypothesis
  {-
  hypothesis : (R : Pred C≈) → Is⨆Closed C⨆ R → Is⨆Preserving C⨆ C⨆ (⟦ F-mono R ⟧cong) → IsChain R
  hypothesis R R-⨆closed FR-⨆preserving x y x∈R y∈R = x-y-related
    where
    n : (x ⊔ y) ≈ ⨆ (↓! (x ⊔ y))
    n = Eq.sym (⨆-↓! (x ⊔ y))
    o : ⨆ (↓! (x ⊔ y)) ≈ ⨆ (↓! (x ⊔ y) ∩ R)
    o = Po.antisym
      (⨆-ub (↓! (x ⊔ y) ∩ R) (⨆ (↓! (x ⊔ y)))
        ((↓! (x ⊔ y) ∩ R) .Pred.isWellDefined n
          ( Po.refl
          , (R-⨆closed ｛ x ، y ｝ (λ { {z} (inj₁ x≈z) → R .Pred.isWellDefined x≈z x∈R ; {z} (inj₂ y≈z) → R .Pred.isWellDefined y≈z y∈R})))))
      (⨆-mono (↓! (x ⊔ y) ∩ R) (↓! (x ⊔ y)) proj₁)
    p :  ⨆ (↓! (x ⊔ y) ∩ R) ≈ ⨆ (⃗ ⟦ F-mono R ⟧cong (｛ x ، y ｝))
    p = FR-⨆preserving (｛ x ، y ｝)
    q : (⃗ ⟦ F-mono R ⟧cong (｛ x ، y ｝)) ≐ ｛  F-raw R x ،  F-raw R y  ｝
    q = ⃗pair ⟦ F-mono R ⟧cong x y
    r : ⨆ (⃗ ⟦ F-mono R ⟧cong (｛ x ، y ｝)) ≈ ( F-raw R x ⊔ F-raw R y)
    r = ⨆-cong (⃗ ⟦ F-mono R ⟧cong (｛ x ، y ｝)) (｛  F-raw R x ،  F-raw R y  ｝) q
    s : ( F-raw R x ⊔ F-raw R y) ≡ (⨆ (↓! x ∩ R) ⊔ ⨆ (↓! y ∩ R))
    s = _≡_.refl
    t : (⨆ (↓! x ∩ R) ⊔ ⨆ (↓! y ∩ R)) ≈ ⨆ ((↓! x ∩ R) ∪ (↓! y ∩ R)) -- (⨆ P ⊔ ⨆ Q) = ⨆ { ⨆ P , ⨆ Q } = ⨆ (P ∪ Q)
    t = ⨆-⊔-comm _ _
    u : ⨆ ((↓! x ∩ R) ∪ (↓! y ∩ R)) ≈ ⨆ (↓! x ∪ ↓! y) -- use x∈R and y∈R or maybe use destribution law in the internal step
    u = Po.antisym {!!} {!!}
    n-u : (x ⊔ y) ≈ ⨆ (↓! x ∪ ↓! y)
    n-u = n ⟨ Eq.trans ⟩ o ⟨ Eq.trans ⟩ p ⟨ Eq.trans ⟩ r ⟨ Eq.trans ⟩ t ⟨ Eq.trans ⟩ u
    v : (⨆ (↓! x ∪ ↓! y) ≈ x) ⊎ (⨆ (↓! x ∪ ↓! y) ≈ y) --
    v = {!⨆!}
    x⊔y=x⊎x⊔y=y : ((x ⊔ y) ≈ x) ⊎ ((x ⊔ y) ≈ y)
    x⊔y=x⊎x⊔y=y = case v of λ where
      (inj₁ z≈x) → inj₁ (n-u ⟨ Eq.trans ⟩ z≈x)
      (inj₂ z≈y) → inj₂ (n-u ⟨ Eq.trans ⟩ z≈y)
    x-y-related : x ≤ y ⊎ y ≤ x
    x-y-related = case x⊔y=x⊎x⊔y=y of λ where
      (inj₁ x⊔y≈x) → inj₂ (⊔-ub-r x y ⟨ Po.trans ⟩ Po.reflexive x⊔y≈x)
      (inj₂ x⊔y≈y) → inj₁ (⊔-ub-l x y ⟨ Po.trans ⟩ Po.reflexive x⊔y≈y)
    -}


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
    preGF-explicit : (R : Pred (D≈ ×-setoid E≈)) → R ∈ preRL F⊣G ↔ (((d , e) : D × E) → (d D.≤ D.⨆ ((↓! (d , e) ∩ R) ∣₁)) × (e E.≤ E.⨆ ((↓! (d , e) ∩ R) ∣₂)) → (d , e) ∈ R)
    preGF-explicit R =
      let open SetoidReasoning (Prop↔-setoid) in
      begin
      R ∈ preRL F⊣G                                                                                             ≡⟨⟩
      (G-raw ∘ F-raw) R UniR.⊆ Pred.⟦ R ⟧                                                                        ≈⟨ λ- , _$- ⟩
      (((d , e) : D × E) → d D.≤ D.⨆ ((↓! (d , e) ∩ R) ∣₁) × (e E.≤ E.⨆ ((↓! (d , e) ∩ R) ∣₂)) → (d , e) ∈ R) ∎

    preGF→⊔closed : (R : Pred (D≈ ×-setoid E≈))
                  → (((d , e) : D × E) → (d D.≤ D.⨆ ((↓! (d , e) ∩ R) ∣₁)) × (e E.≤ E.⨆ ((↓! (d , e) ∩ R) ∣₂)) → (d , e) ∈ R)
                  → (((d , e) : D × E) ((d₀ , e₀) : D × E) → (d₀ , e₀) ≤ (d , e) → (d₀ , e) ∈ R × (d , e₀) ∈ R → (d , e) ∈ R)
    preGF→⊔closed R ≤⨆↓!∩→∈ (d , e) (d₀ , e₀) (d₀≤d , e₀≤e) (d₀e∈R , de₀∈R) = ≤⨆↓!∩→∈ (d , e)
      ( D.⨆-ub ((↓! (d , e) ∩ R) ∣₁) d (e₀ , (D.Po.refl , e₀≤e) , de₀∈R)
      , E.⨆-ub ((↓! (d , e) ∩ R) ∣₂) e (d₀ , (d₀≤d , E.Po.refl) , d₀e∈R))

  IsMonotoneRelation : (R : Pred (D≈ ×-setoid E≈)) → Set
  IsMonotoneRelation R = ∀ d₀ d₁ e₀ e₁
    → (d₀ , e₀) ∈ R → (d₁ , e₁) ∈ R → d₀ D.≤ d₁ → e₀ E.≤ e₁

  IsSquareFilling : (R : Pred (D≈ ×-setoid E≈)) → Set
  IsSquareFilling R = ∀ d₀ d₁ e₀ e₁
    → (d₀ , e₀) ∈ R → (d₁ , e₁) ∈ R
    → d₀ D.≤ d₁ → e₀ E.≤ e₁
    → ∀ d → d₀ D.≤ d → d D.≤ d₁ → Σ e ∶ E , e₀ E.≤ e × e E.≤ e₁ × (d , e) ∈ R

  -- We define the following galois connection
  --
  --     (D × E →m D × E , ≤)
  --        H₀ ↓! ⊣ ↑! I₀
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

  -- The Galois connection between relations and lenses

  F₀ : 𝒫⊆ →mono (((D≤ ×-poset E≤) →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤))
  F₀ = H₀ ∘-mono F

  G₀ : (((D≤ ×-poset E≤) →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤)) →mono 𝒫⊆
  G₀ = G ∘-mono I₀

  F₀⊣G₀ : F₀ ⊣ G₀
  F₀⊣G₀ = F⊣G ∘-galois H₀⊣I₀

  IsTiltBowTie : (R : Pred (D≈ ×-setoid E≈)) → (d : D) (e : E) (d₀ : D) (e₀ : E) (e₁ : E) → Set
  IsTiltBowTie R d e d₀ e₀ e₁ = (d₀ D.≤ d) × (e₀ E.≤ e) × (e E.≤ e₁) × (d₀ , e₁) ∈ R × (d , e₀) ∈ R

  tiltbowtie→≤⨆ : (R : Pred (D≈ ×-setoid E≈)) → ∀ d e → Σ d₀ ∶ D , Σ e₀ ∶ E , Σ e₁ ∶ E , IsTiltBowTie R d e d₀ e₀ e₁ → d D.≤ (D.⨆ ((↓! (d , e) ∩ R) ∣₁)) × e E.≤ (E.⨆ ((↓! (d , E.⊤) ∩ R) ∣₂))
  tiltbowtie→≤⨆ R d e (d₀ , e₀ , e₁ , d₀≤d , e₀≤e , e≤e₁ , d₀e₁∈R , de₀∈R) =
    ( D.⨆-ub ((↓! (d , e) ∩ R) ∣₁) d (e₀ , (D.Po.refl , e₀≤e) , de₀∈R)
    , E.Po.trans e≤e₁ (E.⨆-ub ((↓! (d , E.⊤) ∩ R) ∣₂) e₁ (d₀ , (d₀≤d , E.⊤-max _) , d₀e₁∈R)))

  IsTiltBowTieConnecting : (R : Pred (D≈ ×-setoid E≈)) → Set
  IsTiltBowTieConnecting R = (∀ d e d₀ e₀ e₁ → IsTiltBowTie R d e d₀ e₀ e₁ → (d , e) ∈ R)

  -- the property TiltBowtieConecting is not closed under ⋈ but by adding an extra condition
  -- it becomes closed under ⋈ (TODO: proof)
  Is⋈FriendlyTiltBowTieConnecting : (R : Pred (D≈ ×-setoid E≈)) → Set
  Is⋈FriendlyTiltBowTieConnecting R = IsTiltBowTieConnecting R × IsMonotoneRelation R

  module _ where
    open GaloisConnection
    preG₀F₀-explicit : (R : Pred (D≈ ×-setoid E≈)) → (R ∈ preRL F₀⊣G₀) ↔ (((d , e) : D × E) → (d D.≤ D.⨆ ((↓! (d , e) ∩ R) ∣₁)) × (e E.≤ E.⨆ ((↓! (d , E.⊤) ∩ R) ∣₂)) → (d , e) ∈ R)
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
     α⁻¹ (tiltbowtie→R , ⨆closed) {(d , e)} (d≤⨆↓!de∩R∣₁ , e≤⨆↓!d⊤∩R∣₂) =
        tiltbowtie→R d e (D.⨆ ((↓! (d , E.⊤) ∩ R) ∣₁)) (E.⨆ ((↓! (d , e) ∩ R) ∣₂)) (E.⨆ ((↓! (d , E.⊤) ∩ R) ∣₂))
          ( d≥⨆↓!d⊤∩R∣₁
          , e≥⨆↓!de∩R∣₂
          , e≤⨆↓!d⊤∩R∣₂
          , ⨆closed (↓! (d , E.⊤) ∩ R) (∩-⊆-r (↓! (d , E.⊤)) R)
          , R .Pred.isWellDefined (D.Eq.sym d≈⨆↓!de∩R∣₁ , E.Eq.refl) (⨆closed (↓! (d , e) ∩ R) (∩-⊆-r (↓! (d , e)) R)))
        where
        d≥⨆↓!d⊤∩R∣₁ : D.⨆ ((↓! (d , E.⊤) ∩ R) ∣₁) D.≤ d
        d≥⨆↓!d⊤∩R∣₁ = D.⨆-least ((↓! (d , E.⊤) ∩ R) ∣₁) d (λ d₀ (e₀ , (d₀≤d , e₀≤e) , d₀e₀∈R) → d₀≤d)

        e≥⨆↓!de∩R∣₂ : E.⨆ ((↓! (d , e) ∩ R) ∣₂) E.≤ e
        e≥⨆↓!de∩R∣₂ = E.⨆-least ((↓! (d , e) ∩ R) ∣₂) e (λ d₀ (e₀ , (d₀≤d , e₀≤e) , d₀e₀∈R) → e₀≤e)

        d≥⨆↓!de∩R∣₁ : D.⨆ ((↓! (d , e) ∩ R) ∣₁) D.≤ d
        d≥⨆↓!de∩R∣₁ = D.⨆-least ((↓! (d , e) ∩ R) ∣₁) d (λ d₀ (e₀ , (d₀≤d , e₀≤e) , d₀e₀∈R) → d₀≤d)

        d≈⨆↓!de∩R∣₁ : d D.≈ D.⨆ ((↓! (d , e) ∩ R) ∣₁)
        d≈⨆↓!de∩R∣₁ = D.Po.antisym d≤⨆↓!de∩R∣₁ d≥⨆↓!de∩R∣₁


  -- We define the following galois connection
  --
  -- ((D × E →mono D) × (D →mono E) , ≤)
  --        H₁ ↓! ⊣ ↑! I₁
  -- ((E →mono D) × (D →mono E) , ≤)

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

  -- The Galois connection between relations and bidirectional functions

  F₁ : 𝒫⊆ →mono ((E≤ →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤))
  F₁ = H₁ ∘-mono F₀

  G₁ : ((E≤ →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤)) →mono 𝒫⊆
  G₁ = G₀ ∘-mono I₁

  F₁⊣G₁ : F₁ ⊣ G₁
  F₁⊣G₁ = F₀⊣G₀ ∘-galois H₁⊣I₁

  IsBowTie : (R : Pred (D≈ ×-setoid E≈)) → (d : D) (e : E) (d₀ : D) (e₀ : E) (d₁ : D) (e₁ : E) → Set
  IsBowTie R d e d₀ e₀ d₁ e₁ = d₀ D.≤ d × e₀ E.≤ e × d D.≤ d₁ × e E.≤ e₁ × (d₀ , e₁) ∈ R × (d₁ , e₀) ∈ R

  IsBowTieConnecting : (R : Pred (D≈ ×-setoid E≈)) → Set
  IsBowTieConnecting R = ∀ d e d₀ e₀ d₁ e₁ → IsBowTie R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R

  -- the property BowtieConecting is not closed under ⋈ but by adding monotonicity and square filling property
  -- it becomes closed under ⋈ (TODO: proof)
  -- This class seems quite narrow (possibly it only carries information as much as the unidirectional case does)
  Is⋈FriendlyBowTieConnecting : (R : Pred (D≈ ×-setoid E≈)) → Set
  Is⋈FriendlyBowTieConnecting R = IsTiltBowTieConnecting R × IsMonotoneRelation R × IsSquareFilling R

  bowtie→≤⨆ : (R : Pred (D≈ ×-setoid E≈)) → ∀ d e → Σ d₀ ∶ D , Σ e₀ ∶ E , Σ d₁ ∶ D , Σ e₁ ∶ E , IsBowTie R d e d₀ e₀ d₁ e₁ → d D.≤ (D.⨆ ((↓! (D.⊤ , e) ∩ R) ∣₁)) × e E.≤ (E.⨆ ((↓! (d , E.⊤) ∩ R) ∣₂))
  bowtie→≤⨆ R d e (d₀ , e₀ , d₁ , e₁ , d₀≤d , e₀≤e , d≤d₁ , e≤e₁ , d₀e₁∈R , d₁e₀∈R) =
    ( D.Po.trans d≤d₁ (D.⨆-ub ((↓! (D.⊤ , e) ∩ R) ∣₁) d₁ (e₀ , (D.⊤-max _ , e₀≤e) , d₁e₀∈R))
    , E.Po.trans e≤e₁ (E.⨆-ub ((↓! (d , E.⊤) ∩ R) ∣₂) e₁ (d₀ , (d₀≤d , E.⊤-max _) , d₀e₁∈R)))


  module _ where
    open GaloisConnection
    preG₁F₁-explicit : (R : Pred (D≈ ×-setoid E≈))
      → (R ∈ preRL F₁⊣G₁)
      ↔ (((d , e) : D × E) → (d D.≤ D.⨆ ((↓! (D.⊤ , e) ∩ R) ∣₁)) × (e E.≤ E.⨆ ((↓! (d , E.⊤) ∩ R) ∣₂)) → (d , e) ∈ R)
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
      α⁻¹ (bowtie→R , ⨆closed) {(d , e)} (d≤⨆↓!⊤e∩R∣₁ , e≤⨆↓!d⊤∩R∣₂) =
         bowtie→R d e
           (D.⨆ ((↓! (d , E.⊤) ∩ R) ∣₁)) (E.⨆ ((↓! (D.⊤ , e) ∩ R) ∣₂))
           (D.⨆ ((↓! (D.⊤ , e) ∩ R) ∣₁)) (E.⨆ ((↓! (d , E.⊤) ∩ R) ∣₂))
           ( d≥⨆↓!d⊤∩R∣₁ , e≥⨆↓!⊤e∩R∣₂
           , d≤⨆↓!⊤e∩R∣₁ , e≤⨆↓!d⊤∩R∣₂
           , ⨆closed (↓! (d , E.⊤) ∩ R) (∩-⊆-r (↓! (d , E.⊤)) R)
           , ⨆closed (↓! (D.⊤ , e) ∩ R) (∩-⊆-r (↓! (D.⊤ , e)) R))
         where
         d≥⨆↓!d⊤∩R∣₁ : D.⨆ ((↓! (d , E.⊤) ∩ R) ∣₁) D.≤ d
         d≥⨆↓!d⊤∩R∣₁ = D.⨆-least ((↓! (d , E.⊤) ∩ R) ∣₁) d (λ d₀ (e₀ , (d₀≤d , e₀≤e) , d₀e₀∈R) → d₀≤d)

         e≥⨆↓!⊤e∩R∣₂ : E.⨆ ((↓! (D.⊤ , e) ∩ R) ∣₂) E.≤ e
         e≥⨆↓!⊤e∩R∣₂ = E.⨆-least ((↓! (D.⊤ , e) ∩ R) ∣₂) e (λ d₀ (e₀ , (d₀≤d , e₀≤e) , d₀e₀∈R) → e₀≤e)


  -- H₂ : ((E≤ →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤)) →mono ((E≤ →mono≤-poset D≤) ×-poset E≤)
  -- I₂ : ((E≤ →mono≤-poset D≤) ×-poset E≤) →mono ((E≤ →mono≤-poset D≤) ×-poset (D≤ →mono≤-poset E≤))

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

  -- The Galois connection between relations and backward functions with forward constants

  F₂ : 𝒫⊆ →mono ((E≤ →mono≤-poset D≤) ×-poset E≤)
  F₂ = H₂ ∘-mono F₁

  G₂ : ((E≤ →mono≤-poset D≤) ×-poset E≤) →mono 𝒫⊆
  G₂ = G₁ ∘-mono I₂

  F₂⊣G₂ : F₂ ⊣ G₂
  F₂⊣G₂ = F₁⊣G₁ ∘-galois H₂⊣I₂

  IsLooseBowTie : (R : Pred (D≈ ×-setoid E≈)) → (d : D) (e : E) (d₀ : D) (e₀ : E) (d₁ : D) (e₁ : E) → Set
  IsLooseBowTie R d e d₀ e₀ d₁ e₁ = e₀ E.≤ e × d D.≤ d₁ × e E.≤ e₁ × (d₀ , e₁) ∈ R × (d₁ , e₀) ∈ R

  IsLooseBowTieConnecting : (R : Pred (D≈ ×-setoid E≈)) → Set
  IsLooseBowTieConnecting R = ∀ d e d₀ e₀ d₁ e₁ → IsLooseBowTie R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R

  IsFanOut : (R : Pred (D≈ ×-setoid E≈)) → (d : D) (e : E) (e₀ : E) (e₁ : E) → Set
  IsFanOut R d e e₀ e₁ = e₀ E.≤ e × e E.≤ e₁ × (d , e₁) ∈ R × (d , e₀) ∈ R

  IsFanOutConnecting : (R : Pred (D≈ ×-setoid E≈)) → Set
  IsFanOutConnecting R = ∀ d e e₀ e₁ → IsFanOut R d e e₀ e₁ → (d , e) ∈ R

  IsLowerIn : (R : Pred (D≈ ×-setoid E≈)) → (d : D) (e : E) (d₁ : D) → Set
  IsLowerIn R d e d₁ = d D.≤ d₁ × (d₁ , e) ∈ R

  IsLowerInConnecting : (R : Pred (D≈ ×-setoid E≈)) → Set
  IsLowerInConnecting R = ∀ d e d₁ → IsLowerIn R d e d₁ → (d , e) ∈ R

  ⨆closed→loosebowtieconnecting↔fanoutconnecting×lowerinconnecting : (R : Pred (D≈ ×-setoid E≈)) → Is⨆Closed (D⨆ ×-slat E⨆) R → IsLooseBowTieConnecting R ↔ IsFanOutConnecting R × IsLowerInConnecting R
  ⨆closed→loosebowtieconnecting↔fanoutconnecting×lowerinconnecting R R-⨆closed .proj₁ φ .proj₁ d e e₀ e₁ (e₀≤e , e≤e₁ , de₁∈R , de₀∈R) = φ d e d e₀ d e₁ (e₀≤e , D.Po.refl , e≤e₁ , de₁∈R , de₀∈R)
  ⨆closed→loosebowtieconnecting↔fanoutconnecting×lowerinconnecting R R-⨆closed .proj₁ φ .proj₂ d e d₁ (d≤d₁ , d₁e∈R) = φ d e d₁ e d₁ e (E.Po.refl , d≤d₁ , E.Po.refl , d₁e∈R , d₁e∈R)
  ⨆closed→loosebowtieconnecting↔fanoutconnecting×lowerinconnecting R R-⨆closed .proj₂ (α , β) d e d₀ e₀ d₁ e₁ (e₀≤e , d≤d₁ , e≤e₁ , d₀e₁∈R , d₁e₀∈R)
    = de∈R
    where
    R-⊔closed : Is⊔Closed (D⨆ ×-slat E⨆) R
    R-⊔closed = ⨆closed→⊔closed (D⨆ ×-slat E⨆) R R-⨆closed

    d' : D
    d' = d₀ D.⊔ d₁

    d₀e₁⊔d₁e₀≈d'e₁ : ((d₀ , e₁) ⊔ (d₁ , e₀)) ≈ (d' , e₁)
    d₀e₁⊔d₁e₀≈d'e₁ = Eq.trans
      (⊔-componentwise D⨆ E⨆ d₀ e₁ d₁ e₀)
      (D.Eq.refl , E.Eq.trans (E.⊔-comm e₁ e₀) (E.≤→⊔-≈ e₀ e₁ (E.Po.trans e₀≤e e≤e₁)))

    d₀e₁⊔d₁e₀∈R : ((d₀ , e₁) ⊔ (d₁ , e₀)) ∈ R
    d₀e₁⊔d₁e₀∈R = R-⊔closed (d₀ , e₁) (d₁ , e₀) d₀e₁∈R d₁e₀∈R

    d'e₁∈R : (d' , e₁) ∈ R
    d'e₁∈R = R .Pred.isWellDefined d₀e₁⊔d₁e₀≈d'e₁ d₀e₁⊔d₁e₀∈R

    de₁∈R : (d , e₁) ∈ R
    de₁∈R = β d e₁ d' (D.Po.trans d≤d₁ (D.⊔-ub-r d₀ d₁) , d'e₁∈R)

    de₀∈R : (d , e₀) ∈ R
    de₀∈R = β d e₀ d₁ (d≤d₁ , d₁e₀∈R)

    de∈R : (d , e) ∈ R
    de∈R = α d e e₀ e₁ (e₀≤e , e≤e₁ , de₁∈R , de₀∈R)

  loosebowtie→≤⨆ : (R : Pred (D≈ ×-setoid E≈))
    → ∀ d e
    → Σ d₀ ∶ D , Σ e₀ ∶ E , Σ d₁ ∶ D , Σ e₁ ∶ E , IsLooseBowTie R d e d₀ e₀ d₁ e₁
    → d D.≤ D.⨆ ((↓! (D.⊤ , e) ∩ R) ∣₁) × e E.≤ E.⨆ ((↓! (D.⊤ , E.⊤) ∩ R) ∣₂)
  loosebowtie→≤⨆ R d e (d₀ , e₀ , d₁ , e₁ , e₀≤e , d≤d₁ , e≤e₁ , d₀e₁∈R , d₁e₀∈R) =
    ( D.Po.trans d≤d₁ (D.⨆-ub ((↓! (D.⊤ , e) ∩ R) ∣₁) d₁ (e₀ , (D.⊤-max _ , e₀≤e) , d₁e₀∈R))
    , E.Po.trans e≤e₁ (E.⨆-ub ((↓! (D.⊤ , E.⊤) ∩ R) ∣₂) e₁ (d₀ , (D.⊤-max _ , E.⊤-max _) , d₀e₁∈R)))

  module _ where
    open GaloisConnection
    preG₂F₂-explicit : (R : Pred (D≈ ×-setoid E≈))
      → (R ∈ preRL F₂⊣G₂)
      ↔ (((d , e) : D × E) →  d D.≤ D.⨆ ((↓! (D.⊤ , e) ∩ R) ∣₁) × e E.≤ E.⨆ ((↓! (D.⊤ , E.⊤) ∩ R) ∣₂) → (d , e) ∈ R)
    preG₂F₂-explicit R = (λ- , _$-)

    preG₂F₂-characterization : (R : Pred (D≈ ×-setoid E≈))
      → (R ∈ preRL F₂⊣G₂)
      ↔ ((∀ d e d₀ e₀ d₁ e₁ → IsLooseBowTie R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R) × (Is⨆Closed (D⨆ ×-slat E⨆) R))
    preG₂F₂-characterization R = (α , α⁻¹)
     where
     α₁ : (R ∈ preRL F₂⊣G₂) → (∀ d e d₀ e₀ d₁ e₁ → IsLooseBowTie R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R)
     α₁ R∈preG₂F₂ d e d₀ e₀ d₁ e₁ fan = R∈preG₂F₂ (loosebowtie→≤⨆ R d e (d₀ , e₀ , d₁ , e₁ , fan))

     α₂ : (R ∈ preRL F₂⊣G₂) → Is⨆Closed (D⨆ ×-slat E⨆) R
     α₂ = preGF-characterization R .proj₁ ∘ preRL-∘-⊆ F⊣G (H₀⊣I₀ ∘-galois H₁⊣I₁ ∘-galois H₂⊣I₂) {R}

     α : (R ∈ preRL F₂⊣G₂) → (∀ d e d₀ e₀ d₁ e₁ → IsLooseBowTie R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R) × Is⨆Closed (D⨆ ×-slat E⨆) R
     α = Product.< α₁ , α₂ >

     α⁻¹ : ((∀ d e d₀ e₀ d₁ e₁ → IsLooseBowTie R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R) × Is⨆Closed (D⨆ ×-slat E⨆) R) → (R ∈ preRL F₂⊣G₂)
     α⁻¹ (fan→R , ⨆closed) {(d , e)} (d≤⨆↓!⊤e∩R∣₁ , e≤⨆↓!⊤⊤∩R∣₂) =
       fan→R d e
         (D.⨆ ((↓! (D.⊤ , E.⊤) ∩ R) ∣₁)) (E.⨆ ((↓! (D.⊤ , e) ∩ R) ∣₂))
         (D.⨆ ((↓! (D.⊤ , e) ∩ R) ∣₁)) (E.⨆ ((↓! (D.⊤ , E.⊤) ∩ R) ∣₂))
         ( E.⨆-least _ _ (λ e₀ (d₀ , (d₀≤⊤ , e₀≤e) , d₀e₀∈R) → e₀≤e)
         , d≤⨆↓!⊤e∩R∣₁
         , e≤⨆↓!⊤⊤∩R∣₂
         , ⨆closed (↓! (D.⊤ , E.⊤) ∩ R) (∩-⊆-r (↓! (D.⊤ , E.⊤)) R)
         , ⨆closed (↓! (D.⊤ , e) ∩ R) (∩-⊆-r (↓! (D.⊤ , e)) R))

  -- We define the following galois connection
  --
  -- ((E →m D) × E , ≤)
  --   H₃ ↓! ⊣ ↑! I₃
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

  -- The Galois connection between relations and backward functions
  F₃ : 𝒫⊆ →mono (E≤ →mono≤-poset D≤)
  F₃ = H₃ ∘-mono F₂

  G₃ : (E≤ →mono≤-poset D≤) →mono 𝒫⊆
  G₃ = G₂ ∘-mono I₃

  F₃⊣G₃ : F₃ ⊣ G₃
  F₃⊣G₃ = F₂⊣G₂ ∘-galois H₃⊣I₃

  IsTilt : (R : Pred (D≈ ×-setoid E≈)) → (d : D) (e : E) (e₀ : E) (d₁ : D) → Set
  IsTilt R d e e₀ d₁ = e₀ E.≤ e × d D.≤ d₁ × (d₁ , e₀) ∈ R

  IsTiltConnecting : (R : Pred (D≈ ×-setoid E≈)) → Set
  IsTiltConnecting R = ∀ d e e₀ d₁ → IsTilt R d e e₀ d₁ → (d , e) ∈ R

  tilt→≤⨆ : (R : Pred (D≈ ×-setoid E≈)) → ∀ d e → (Σ e₀ ∶ E , Σ d₁ ∶ D , IsTilt R d e e₀ d₁) → d D.≤ D.⨆ ((↓! (D.⊤ , e) ∩ R) ∣₁) × e E.≤ E.⊤
  tilt→≤⨆ R d e (e₀ , d₁ , e₀≤e , d≤d₁ , d₁e₀∈R) =
    ( D.Po.trans d≤d₁ (D.⨆-ub ((↓! (D.⊤ , e) ∩ R) ∣₁) d₁ (e₀ , ((D.⊤-max d₁ , e₀≤e) , d₁e₀∈R)))
    , E.⊤-max e)

  module _ where
    open GaloisConnection
    preG₃F₃-explicit : (R : Pred (D≈ ×-setoid E≈))
      → (R ∈ preRL F₃⊣G₃)
      ↔ (((d , e) : D × E) → d D.≤ D.⨆ ((↓! (D.⊤ , e) ∩ R) ∣₁) × e E.≤ E.⊤ → (d , e) ∈ R)
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
      α⁻¹ (tilt→R , ⨆closed) {(d , e)} (d≤⨆↓!⊤e∩R∣₁ , e≤⊤) =
        tilt→R d e
          (proj₂ (⨆ (↓! (D.⊤ , e) ∩ R))) (proj₁ (⨆ (↓! (D.⊤ , e) ∩ R)))
          (e≥⨆↓!⊤e∩R∣₂ , d≤⨆↓!⊤e∩R∣₁ , ⨆closed (↓! (D.⊤ , e) ∩ R) (∩-⊆-r (↓! (D.⊤ , e)) R))
        where
        e≥⨆↓!⊤e∩R∣₂ : E.⨆ ((↓! (D.⊤ , e) ∩ R) ∣₂) E.≤ e
        e≥⨆↓!⊤e∩R∣₂ = E.⨆-least ((↓! (D.⊤ , e) ∩ R) ∣₂) e (λ e₀ (d₁ , ((d₁≤⊤ , e₀≤e) , d₁e₀∈R)) → e₀≤e)

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

  lax∧oplax→monoidal : (_⊗C_ : Op₂ ∣ C ∣) (_⊗D_ : Op₂ ∣ D ∣)
    → IsLaxMonoidal _⊗C_ _⊗D_
    → IsOplaxMonoidal _⊗C_ _⊗D_
    → IsMonoidal _⊗C_ _⊗D_
  lax∧oplax→monoidal _⊗C_ _⊗D_ lax oplax a b = antisym (oplax a b) (lax a b)


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

    preRL-∩closed→[∩]-∩-right-adjoint-oplax-monoidal :
      ((S S' : Pred C≈) → S ∈ preRL → S' ∈ preRL → (S ∩ S') ∈ preRL)
      → IsOplaxMonoidal R _[∩]_ _∩_
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
      module C = SLat C⨆
      C≤ = SLat.poset C⨆
      C≈ = SLat.Eq.setoid C⨆
      C = ∣ C⨆ ∣
      open SLat C⨆
      open 𝒫⊆-and-Endo C⨆
      open GaloisConnection F⊣G
      -- naive operation for nondeterministic choice
      _[∩]_ : Op₂ ∣ Endo ∣
      _[∩]_ = liftOpAlong⊣ F⊣G _∩_

      h : ∣ Endo ∣ → ∣ Endo ∣ → C → C≈ →cong C≈
      Cong.⟦ h f g p₀ ⟧ p = p₀ ⊓ (⟦ f ⟧ p ⊓ ⟦ g ⟧ p)
      h f g p₀ .Cong.isCongruent .IsCong.cong {p} {p'} p≈p' =
        ⊓-cong p₀ (⟦ f ⟧ p ⊓ ⟦ g ⟧ p) p₀ (⟦ f ⟧ p' ⊓ ⟦ g ⟧ p')
          C.Eq.refl
          (⊓-cong (⟦ f ⟧ p) (⟦ g ⟧ p) (⟦ f ⟧ p') (⟦ g ⟧ p')
                  (f .Mono.cong p≈p') (g .Mono.cong p≈p'))

    -- [∩] can be written by ν
    [∩]-ν-representation : ∀ f g p₀ → ⟦ f [∩] g ⟧ p₀ ≈ ν (h f g p₀)
    [∩]-ν-representation f g p₀ =
      ⨆-cong (↓! p₀ ∩ (⟦ G ⟧ f ∩ ⟦ G ⟧ g)) (post poset (h f g p₀))
        (∀↔→≐ {X≈ = C≈} {↓! p₀ ∩ (⟦ G ⟧ f ∩ ⟦ G ⟧ g)} {post poset (h f g p₀)} φ)
      where
      lhs = λ p → p ≤ p₀ × (p ≤ ⟦ f ⟧ p) × (p ≤ ⟦ g ⟧ p)
      rhs = λ p → p ≤ (p₀ ⊓ (⟦ f ⟧ p ⊓ ⟦ g ⟧ p))
      φ : ∀ p → lhs p ↔ rhs p
      φ p =
        let open SetoidReasoning Prop↔-setoid in
        begin
        (p ≤ p₀ × ((p ≤ ⟦ f ⟧ p) × (p ≤ ⟦ g ⟧ p))) ≈˘⟨ ( (id , id) ×-↔ ≤⊓↔≤× _ _ _) ⟩
        (p ≤ p₀ × (p ≤ (⟦ f ⟧ p ⊓ ⟦ g ⟧ p))) ≈˘⟨ ≤⊓↔≤× _ _ _ ⟩
        (p ≤ (p₀ ⊓ (⟦ f ⟧ p ⊓ ⟦ g ⟧ p))) ∎



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

    [∩]-∩-lax-monoidal : IsLaxMonoidal G _[∩]_ _∩_
    [∩]-∩-lax-monoidal = [∩]-∩-right-adjoint-lax-monoidal C≈ F⊣G

    [∩]-∩-monoidal : IsMonoidal G _[∩]_ _∩_
    [∩]-∩-monoidal = lax∧oplax→monoidal G _[∩]_ _∩_ [∩]-∩-lax-monoidal [∩]-∩-oplax-monoidal

    -- show exsistance of cheaper (efficient) version of operation that is also oplax-monoidal
    private
      _[⊓]_ : Op₂ ∣ Endo ∣ -- The pointwise meet (_⊓_)
      Mono.⟦ f [⊓] g ⟧ c = ⟦ f ⟧ c ⊓ ⟦ g ⟧ c
      (f [⊓] g) .Mono.isMonotone .IsMono.mono c≤c' = ⊓-mono _ _ _ _ (f .Mono.mono c≤c') (g .Mono.mono c≤c')
      (f [⊓] g) .Mono.isMonotone .IsMono.cong c≈c' = Po.antisym ((f [⊓] g) .Mono.isMonotone .IsMono.mono (Po.reflexive c≈c')) (((f [⊓] g) .Mono.isMonotone .IsMono.mono (Po.reflexive (Eq.sym c≈c'))))

      [∩]≤[⊓] : (f g : ∣ Endo ∣) → (c : C) → ⟦ f [∩] g ⟧ c ≤ ⟦ f [⊓] g ⟧ c
      [∩]≤[⊓] f g c = ⨆-mono (↓! c ∩ (⟦ G ⟧ f ∩ ⟦ G ⟧ g)) (lowerbounds poset (｛ ⟦ f ⟧ c ｝ ∪ ｛ ⟦ g ⟧ c ｝)) ⊆
        where
        open PosetReasoning C≤
        ⊆ : (↓! c ∩ (⟦ G ⟧ f ∩ ⟦ G ⟧ g)) ⊆ (lowerbounds poset (｛ ⟦ f ⟧ c ｝ ∪ ｛ ⟦ g ⟧ c ｝))
        ⊆ {x} (x≤c , x≤fx , x≤gx) x' (inj₁ fc≈x') = begin x ≤⟨ x≤fx ⟩ ⟦ f ⟧ x ≤⟨ f .Mono.mono x≤c ⟩ ⟦ f ⟧ c ≈⟨ fc≈x' ⟩ x' ∎
        ⊆ {x} (x≤c , x≤fx , x≤gx) x' (inj₂ gc≈x') = begin x ≤⟨ x≤gx ⟩ ⟦ g ⟧ x ≤⟨ g .Mono.mono x≤c ⟩ ⟦ g ⟧ c ≈⟨ gc≈x' ⟩ x' ∎

      [⊓]-∩-oplax-monoidal : IsOplaxMonoidal G _[⊓]_ _∩_
      [⊓]-∩-oplax-monoidal f g =
        let open PosetReasoning 𝒫⊆ in
        begin
        ⟦ G ⟧ (f [⊓] g) ≤⟨ (λ {x} → φ x) ⟩
        (⟦ G ⟧ f ∩ ⟦ G ⟧ g ) ∎
        where
        f⊓g : Endo .PosetPoly.Carrier
        Mono.⟦ f⊓g ⟧ c = ⟦ f ⟧ c ⊓ ⟦ g ⟧ c
        f⊓g .Mono.isMonotone .IsMono.mono {c} {c'} c≤c' = ⊓-mono (⟦ f ⟧ c) (⟦ g ⟧ c) (⟦ f ⟧ c') (⟦ g ⟧ c') (f .Mono.mono c≤c') (g .Mono.mono c≤c')
        f⊓g .Mono.isMonotone .IsMono.cong c≈c' = Po.antisym
          (f⊓g .Mono.isMonotone .IsMono.mono (Po.reflexive c≈c'))
          (f⊓g .Mono.isMonotone .IsMono.mono (Po.reflexive (Eq.sym c≈c')))

        φ : ∀ x → x ∈ (⟦ G ⟧ (f [⊓] g)) → x ∈ (⟦ G ⟧ f ∩ ⟦ G ⟧ g)
        φ x x∈G[f⊓g] =
          ( G .Mono.mono {f⊓g} {f} (λ c → ⊓-lb-l (⟦ f ⟧ c) (⟦ g ⟧ c)) x∈G[f⊓g]
          , G .Mono.mono {f⊓g} {g} (λ c → ⊓-lb-r (⟦ f ⟧ c) (⟦ g ⟧ c)) x∈G[f⊓g])

      [⊓]-∩-lax-monoidal : IsLaxMonoidal G _[⊓]_ _∩_
      [⊓]-∩-lax-monoidal f g =
        let open PosetReasoning 𝒫⊆ in
        begin
        (⟦ G ⟧ f ∩ ⟦ G ⟧ g) ≈˘⟨ [∩]-∩-monoidal f g  ⟩
        ⟦ G ⟧ (f [∩] g) ≤⟨ G .Mono.mono {f[∩]g} {f⊓g} ([∩]≤[⊓] f g) ⟩
        ⟦ G ⟧ (f [⊓] g) ∎
        where
        f[∩]g : ∣ Endo ∣
        Mono.⟦ f[∩]g ⟧ c = ⟦ f [∩] g ⟧ c
        f[∩]g .Mono.isMonotone .IsMono.mono {c} {c'} c≤c' = ⨆-mono (↓! c ∩ (⟦ G ⟧ f ∩ ⟦ G ⟧ g)) (↓! c' ∩ (⟦ G ⟧ f ∩ ⟦ G ⟧ g)) λ {x} (x≤c , P) → (Po.trans x≤c c≤c' , P)
        f[∩]g .Mono.isMonotone .IsMono.cong {c} {c'} c≈c' = Po.antisym
          (f[∩]g .Mono.isMonotone .IsMono.mono (Po.reflexive c≈c'))
          (f[∩]g .Mono.isMonotone .IsMono.mono (Po.reflexive (Eq.sym c≈c')))

        f⊓g : ∣ Endo ∣
        Mono.⟦ f⊓g ⟧ c = ⟦ f ⟧ c ⊓ ⟦ g ⟧ c
        f⊓g .Mono.isMonotone .IsMono.mono {c} {c'} c≤c' = ⊓-mono (⟦ f ⟧ c) (⟦ g ⟧ c) (⟦ f ⟧ c') (⟦ g ⟧ c') (f .Mono.mono c≤c') (g .Mono.mono c≤c')
        f⊓g .Mono.isMonotone .IsMono.cong c≈c' = Po.antisym
          (f⊓g .Mono.isMonotone .IsMono.mono (Po.reflexive c≈c'))
          (f⊓g .Mono.isMonotone .IsMono.mono (Po.reflexive (Eq.sym c≈c')))


      [⊓]-∩-monoidal : IsMonoidal G _[⊓]_ _∩_
      [⊓]-∩-monoidal = lax∧oplax→monoidal G _[⊓]_ _∩_ [⊓]-∩-lax-monoidal [⊓]-∩-oplax-monoidal


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
        → IsTiltBowTieConnecting D⨆ E⨆ R → IsTiltBowTieConnecting D⨆ E⨆ R' → IsTiltBowTieConnecting D⨆ E⨆ (R ∩ R')
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
        → IsBowTieConnecting D⨆ E⨆ R → IsBowTieConnecting D⨆ E⨆ R' → IsBowTieConnecting D⨆ E⨆ (R ∩ R')
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
        _[⋈]_ : ∣ Endo C⨆ D⨆ ∣ → ∣ Endo D⨆ E⨆ ∣ → ∣ Endo C⨆ E⨆ ∣
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

        -- We define a subset T ⊆ C × D × E where eath tuple (c , d , e) ∈ T ,  (c,e) ∈ S and d mediates c and d , i.e, (c,d) ∈ R (d,e) ∈ R'.
        -- Note: Sinse S ⊆ R ⋈ R', (c,e)∈S already implies existence of the mediator d n D.
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

      -- TODO: show cheaper (efficient) version of oplax-monoidal operation
      private
        h : ∣ Endo C⨆ D⨆ ∣ → ∣ Endo D⨆ E⨆ ∣ → (C × E) → D≈ →cong D≈
        Cong.⟦ h f g (c₀ , e₀) ⟧  d = (⟦ f ⟧ (c₀ , d) .proj₂) D.⊓ (⟦ g ⟧ (d , e₀) .proj₁)
        h f g (c₀ , e₀) .Cong.isCongruent .IsCong.cong {d} {d'} d≈d' =
          D.⊓-cong (⟦ f ⟧ (c₀ , d) .proj₂) (⟦ g ⟧ (d , e₀) .proj₁) (⟦ f ⟧ (c₀ , d') .proj₂) (⟦ g ⟧ (d' , e₀) .proj₁)
            (proj₂-mono C≤ D≤ .IsMono.cong (f .Mono.cong (C.Eq.refl , d≈d')))
            (proj₁-mono D≤ E≤ .IsMono.cong (g .Mono.cong (d≈d' , E.Eq.refl)))

        _⊠_ : ∣ Endo C⨆ D⨆ ∣ → ∣ Endo D⨆ E⨆ ∣ → ∣ Endo C⨆ E⨆ ∣
        Mono.⟦ f ⊠ g ⟧ (c₀ , e₀) = (⟦ f ⟧ (c₀ , d₀ (c₀ , e₀)) .proj₁ , ⟦ g ⟧ (d₀ (c₀ , e₀) , e₀) .proj₂)
          where
          d₀ : C × E → D
          d₀ (c₀ , e₀) = D.ν (h f g (c₀ , e₀))

        (f ⊠ g) .Mono.isMonotone .IsMono.mono {(c , e)} {(c' , e')} (c≤c' , e≤e')
          = proj₁-mono C≤ D≤ .IsMono.mono (f .Mono.mono
            ( c≤c'
            , D.ν-mono (h f g (c , e)) (h f g (c' , e'))
                       (λ d →
                         D.⊓-mono (⟦ f ⟧ (c , d) .proj₂) (⟦ g ⟧ (d , e) .proj₁) (⟦ f ⟧ (c' , d) .proj₂) (⟦ g ⟧ (d , e') .proj₁)
                                  (proj₂-mono C≤ D≤ .IsMono.mono (f .Mono.mono (c≤c' , D.Po.refl)))
                                  (proj₁-mono D≤ E≤ .IsMono.mono (g .Mono.mono (D.Po.refl , e≤e'))))))
          , proj₂-mono D≤ E≤ .IsMono.mono (g .Mono.mono
            ( D.ν-mono (h f g (c , e)) (h f g (c' , e'))
                       (λ d →
                         D.⊓-mono (⟦ f ⟧ (c , d) .proj₂) (⟦ g ⟧ (d , e) .proj₁) (⟦ f ⟧ (c' , d) .proj₂) (⟦ g ⟧ (d , e') .proj₁)
                                  (proj₂-mono C≤ D≤ .IsMono.mono (f .Mono.mono (c≤c' , D.Po.refl)))
                                  (proj₁-mono D≤ E≤ .IsMono.mono (g .Mono.mono (D.Po.refl , e≤e'))))
            , e≤e'))
        (f ⊠ g) .Mono.isMonotone .IsMono.cong ce≈ce' = PosetPoly.antisym (C≤ ×-poset E≤)
          ((f ⊠ g) .Mono.isMonotone .IsMono.mono (PosetPoly.reflexive (C≤ ×-poset E≤) ce≈ce'))
          ((f ⊠ g) .Mono.isMonotone .IsMono.mono (PosetPoly.reflexive (C≤ ×-poset E≤) (PosetPoly.Eq.sym (C≤ ×-poset E≤) ce≈ce')))

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

      ⋈-⨆closed×loosebowtieconnecting : (R : Pred (C≈ ×-setoid D≈)) (R' : Pred (D≈ ×-setoid E≈))
        → IsLooseBowTieConnecting C⨆ D⨆ R × Is⨆Closed (C⨆ ×-slat D⨆) R
        → IsLooseBowTieConnecting D⨆ E⨆ R' × Is⨆Closed (D⨆ ×-slat E⨆) R'
        → IsLooseBowTieConnecting C⨆ E⨆ (R ⋈ R') × Is⨆Closed (C⨆ ×-slat E⨆) (R ⋈ R')
      ⋈-⨆closed×loosebowtieconnecting R R' (R-loosebowtieconnecting , R-⨆closed) (R'-loosebowtieconnecting , R'-⨆closed) = R⋈R'-loosebowtieconnecting , R⋈R'-⨆closed
        where
        R⋈R'-⨆closed = F⊣G.⋈-⨆closed C⨆ D⨆ E⨆ R R' R-⨆closed R'-⨆closed

        R-fanoutconnecting = ⨆closed→loosebowtieconnecting↔fanoutconnecting×lowerinconnecting C⨆ D⨆ R R-⨆closed .proj₁ R-loosebowtieconnecting .proj₁
        R-lowerinconnecting = ⨆closed→loosebowtieconnecting↔fanoutconnecting×lowerinconnecting C⨆ D⨆ R R-⨆closed .proj₁ R-loosebowtieconnecting .proj₂

        R'-fanoutconnecting = ⨆closed→loosebowtieconnecting↔fanoutconnecting×lowerinconnecting D⨆ E⨆ R' R'-⨆closed .proj₁ R'-loosebowtieconnecting .proj₁
        R'-lowerinconnecting = ⨆closed→loosebowtieconnecting↔fanoutconnecting×lowerinconnecting D⨆ E⨆ R' R'-⨆closed .proj₁ R'-loosebowtieconnecting .proj₂

        R⋈R'-lowerinconnecting : IsLowerInConnecting C⨆ E⨆ (R ⋈ R')
        R⋈R'-lowerinconnecting c e c₁ (c≤c₁ , c₁e∈R⋈R' @ (d , c₁d∈R , de∈R')) = d , R-lowerinconnecting c d c₁ (c≤c₁ , c₁d∈R) , de∈R'

        R⋈R'-fanoutconnecting : IsFanOutConnecting C⨆ E⨆ (R ⋈ R')
        R⋈R'-fanoutconnecting c e e₀ e₁ (e₀≤e , e≤e₁ , (ce₁∈R⋈R' @ (d₁ , cd₁∈R , d₁e₁∈R')) , (ce₀∈R⋈R' @ (d₀ , cd₀∈R , d₀e₀∈R'))) = ce∈R⋈R'
          where
          d' = d₀ D.⊔ d₁

          private module _ where
            open SLat (D⨆ ×-slat E⨆)

            R'-⊔closed : Is⊔Closed (D⨆ ×-slat E⨆) R'
            R'-⊔closed = ⨆closed→⊔closed (D⨆ ×-slat E⨆) R' R'-⨆closed

            d₀e₀⊔d₁e₀∈R' : ((d₀ , e₀) ⊔ (d₁ , e₁)) ∈ R'
            d₀e₀⊔d₁e₀∈R' = R'-⊔closed  (d₀ , e₀)  (d₁ , e₁) d₀e₀∈R' d₁e₁∈R'

            d₀e₀⊔d₁e₁≈d'e₁ : ((d₀ , e₀) ⊔ (d₁ , e₁)) ≈ (d' , e₁)
            d₀e₀⊔d₁e₁≈d'e₁ = Eq.trans
              (⊔-componentwise D⨆ E⨆ d₀ e₀ d₁ e₁)
              (D.Eq.refl , E.≤→⊔-≈ e₀ e₁ (E.Po.trans e₀≤e e≤e₁))

            d'e₁∈R' : (d' , e₁) ∈ R'
            d'e₁∈R' = R' .Pred.isWellDefined d₀e₀⊔d₁e₁≈d'e₁ d₀e₀⊔d₁e₀∈R'

          d₀≤d' : d₀ D.≤ d'
          d₀≤d' = D.⊔-ub-l d₀ d₁

          d₀e₁∈R' : (d₀ , e₁) ∈ R'
          d₀e₁∈R' = R'-lowerinconnecting d₀ e₁ d' (d₀≤d' , d'e₁∈R')

          d₀e∈R' : (d₀ , e) ∈ R'
          d₀e∈R' = R'-fanoutconnecting d₀ e e₀ e₁ (e₀≤e , e≤e₁ , d₀e₁∈R' , d₀e₀∈R')

          ce∈R⋈R' : (c , e) ∈ (R ⋈ R')
          ce∈R⋈R' = d₀ , cd₀∈R , d₀e∈R'

        R⋈R'-loosebowtieconnecting = ⨆closed→loosebowtieconnecting↔fanoutconnecting×lowerinconnecting C⨆ E⨆ (R ⋈ R') R⋈R'-⨆closed .proj₂ (R⋈R'-fanoutconnecting , R⋈R'-lowerinconnecting)

      ⋈-preRL-closed : (R : Pred (C≈ ×-setoid D≈)) (R' : Pred (D≈ ×-setoid E≈)) → R ∈ preRL C⨆ D⨆ → R' ∈ preRL D⨆ E⨆ → (R ⋈ R') ∈ preRL C⨆ E⨆
      ⋈-preRL-closed R R' R∈preRL R'∈preRL =
        preG₂F₂-characterization C⨆ E⨆ (R ⋈ R') .proj₂
          (⋈-⨆closed×loosebowtieconnecting R R'
            (preG₂F₂-characterization C⨆ D⨆ R .proj₁ R∈preRL)
            (preG₂F₂-characterization D⨆ E⨆ R' .proj₁ R'∈preRL))

      [⋈]-⋈-oplax-monoidal :  IsIndexedOplaxMonoidal SLat _ 𝒫⊆ G₂ C⨆ D⨆ E⨆ _[⋈]_ _⋈_
      [⋈]-⋈-oplax-monoidal = preRL-⋈closed→[⋈]-⋈-right-adjoint-oplax-monoidal SLat SLat.Eq.setoid _ F₂⊣G₂ C⨆ D⨆ E⨆ ⋈-preRL-closed

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

      ⋈-tiltclosed : (R : Pred (C≈ ×-setoid D≈)) (R' : Pred (D≈ ×-setoid E≈)) → IsTiltConnecting C⨆ D⨆ R → IsTiltConnecting D⨆ E⨆ R' → IsTiltConnecting C⨆ E⨆ (R ⋈ R')
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

      [⋈]-⋈-oplax-monoidal :  IsIndexedOplaxMonoidal SLat _ 𝒫⊆ G₃ C⨆ D⨆ E⨆ _[⋈]_ _⋈_
      [⋈]-⋈-oplax-monoidal = preRL-⋈closed→[⋈]-⋈-right-adjoint-oplax-monoidal SLat SLat.Eq.setoid _ F₃⊣G₃ C⨆ D⨆ E⨆ ⋈-preRL-closed
