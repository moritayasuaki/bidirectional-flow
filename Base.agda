{-# OPTIONS --type-in-type --postfix-projections #-}

module Base where

open import Agda.Primitive hiding (Prop) renaming (lzero to lzero ; _⊔_ to lmax ; Set to Set ; Setω to Setω) public
open import Algebra as Algebra
import Data.Unit as Unit
import Data.Empty as Empty
open import Data.Sum as Sum
open import Data.Sum.Properties as SumProps
import Data.Product as Product
open Product renaming (Σ to Σ')
open import Data.Product.Properties as ProductProps
import Data.Product.Relation.Binary.Pointwise.NonDependent as ProductBinR renaming (Pointwise to Componentwise)
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

module SetoidProps (setoid : Setoid) where
  open SetoidPoly setoid public
  open import Relation.Binary.Properties.Setoid setoid public

Poset : Set
Poset = PosetPoly lzero lzero lzero

module PosetProps (poset : Poset) where
  open PosetPoly poset public
  open import Relation.Binary.Properties.Poset poset public

  ≈→≤ : ∀ {d d'} → d ≈ d' → d ≤ d'
  ≈→≤ = reflexive 

  ≈→≥ : ∀ {d d'} → d ≈ d' → d' ≤ d
  ≈→≥ = reflexive ∘ Eq.sym

instance
  setoid-carrier : HasCarrier Setoid
  setoid-carrier .HasCarrier.Carrier = SetoidPoly.Carrier

  poset-carrier : HasCarrier Poset
  poset-carrier .HasCarrier.Carrier = PosetPoly.Carrier

module _ where
  import Relation.Binary.Morphism as BinRMorph
  open BinRMorph renaming (IsOrderHomomorphism to IsMono ; IsRelHomomorphism to IsCong ; mkPosetHomo to mkMono) public
  module Cong = BinRMorph.SetoidHomomorphism renaming (isRelHomomorphism to isCongruent)
  module Mono = BinRMorph.PosetHomomorphism renaming (isOrderHomomorphism to isMonotone)

  infixr 0 _→cong_ _→mono_
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

∀↔→Σ↔ : {A : Set} {f g : A → Set} → (∀ x → f x ↔ g x) → Σ f ↔ Σ g
∀↔→Σ↔ p = ((λ (x , fx) → x , p x .proj₁ fx) , (λ (x , gx) → x , p x .proj₂ gx))

module _ where
  -- open ProductBinR
  module _ where
    open SetoidPoly

    _×-setoid_ : (D : Setoid) (E : Setoid) → Setoid
    (D ×-setoid E) .Carrier = ∣ D ∣ × ∣ E ∣
    (D ×-setoid E) ._≈_ = ProductBinR.Componentwise (D ._≈_) (E ._≈_)
    (D ×-setoid E) .isEquivalence = ProductBinR.×-isEquivalence (D .isEquivalence) (E .isEquivalence)

  module _ where
    open PosetPoly

    _×-poset_ : (D : Poset) (E : Poset) → Poset
    (D ×-poset E) .Carrier = ∣ D ∣ × ∣ E ∣
    (D ×-poset E) ._≈_ = ProductBinR.Componentwise (D ._≈_) (E ._≈_)
    (D ×-poset E) ._≤_ = ProductBinR.Componentwise (D ._≤_) (E ._≤_)
    (D ×-poset E) .isPartialOrder = ProductBinR.×-isPartialOrder (D .isPartialOrder) (E .isPartialOrder)

swap-cong : {D≈ E≈ : Setoid} → (D≈ ×-setoid E≈) →cong (E≈ ×-setoid D≈)
Cong.⟦ swap-cong ⟧ = Product.swap
swap-cong .Cong.isCongruent .IsCong.cong = Product.swap

flip-cong : {D≈ E≈ C≈ : Setoid} → (D≈ ×-setoid E≈) →cong C≈ → (E≈ ×-setoid D≈) →cong C≈
flip-cong f = f ∘-cong swap-cong

curry-cong : {D≈ E≈ C≈ : Setoid} → (D≈ ×-setoid E≈) →cong C≈ → ∣ D≈ ∣ → E≈ →cong C≈
curry-cong {D≈} {E≈} {C≈} f d = partially-applied
  where
  partially-applied : E≈ →cong C≈
  Cong.⟦ partially-applied ⟧ = curry ⟦ f ⟧ d
  partially-applied .Cong.isCongruent .IsCong.cong e≈e' = f .Cong.cong ((SetoidPoly.refl D≈) , e≈e')

curry-flip-cong : {D≈ E≈ C≈ : Setoid} → (D≈ ×-setoid E≈) →cong C≈ → ∣ E≈ ∣ → (D≈ →cong C≈)
curry-flip-cong f≈ = curry-cong (flip-cong f≈)

Rel : Set → Set
Rel X = RelPoly X lzero

Pointwise : {D : Set} (C : Set) → Rel D → Rel (C → D)
Pointwise C _R_ f g = (c : C) → (f c) R (g c)

module FunBinR where
  open IsPartialOrder using (isPreorder)
  open IsPreorder using (isEquivalence)


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



module _ (D : Setoid) (E : Setoid) where
  private
    module D = SetoidProps D
    module E = SetoidProps E
    module D×E = SetoidProps (D ×-setoid E)

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



  U : Pred X≈
  Pred.⟦ U ⟧ = UniR.U
  U .Pred.isWellDefined _ _ = _

  _⊆_ : Pred X≈ → Pred X≈ → Set
  P ⊆ Q = ⟦ P ⟧ UniR.⊆ ⟦ Q ⟧


  U-max : (P : Pred X≈) → P ⊆ U
  U-max _ _ = _

  _≐_ : Pred X≈ → Pred X≈ → Set
  P ≐ Q = ⟦ P ⟧ UniR.⊆ ⟦ Q ⟧ × ⟦ Q ⟧ UniR.⊆ ⟦ P ⟧

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


  ∪-mono-l : (P Q S : Pred X≈) → P ⊆ Q → (P ∪ S) ⊆ (Q ∪ S)
  ∪-mono-l P Q S P⊆Q (inj₁ x∈P) = inj₁ (P⊆Q x∈P)
  ∪-mono-l P Q S P⊆Q (inj₂ x∈S) = inj₂ x∈S

  ∪-mono-r : (P Q S : Pred X≈) → P ⊆ Q → (S ∪ P) ⊆ (S ∪ Q)
  ∪-mono-r P Q S P⊆Q (inj₁ x∈S) = inj₁ x∈S
  ∪-mono-r P Q S P⊆Q (inj₂ x∈P) = inj₂ (P⊆Q x∈P)

  ∪-⊆-l : (S T : Pred X≈) → S ⊆ (S ∪ T)
  ∪-⊆-l S T x∈S = (inj₁ x∈S)

  ∪-⊆-r : (S T : Pred X≈) → T ⊆ (S ∪ T)
  ∪-⊆-r S T x∈T = (inj₂ x∈T)

  ∪-∅-runit : (P : Pred X≈) → (P ∪ ∅) ≐ P
  ∪-∅-runit P .proj₁ (inj₁ x∈P) = x∈P
  ∪-∅-runit P .proj₂ x∈P = inj₁ x∈P


module _ (X≈ : Setoid) where
  open SetoidPoly X≈
  private
    X = ∣ X≈ ∣

  singleton : X → Pred X≈
  Pred.⟦ singleton x ⟧ y = x ≈ y
  singleton x .Pred.isWellDefined {y} {z} y≈z x≈y = trans x≈y y≈z

  doubleton : X → X → Pred X≈
  doubleton x y = singleton x ∪ singleton y


  singleton-belongs : ∀ x (S : Pred X≈) → singleton x ⊆ S ↔ x ∈ S
  singleton-belongs x S .proj₁ [x]⊆S = [x]⊆S {x} refl
  singleton-belongs x S .proj₂ x∈S x≈y = S .Pred.isWellDefined x≈y x∈S

  listToPred : List X → Pred X≈
  listToPred [] = ∅
  listToPred (x ∷ ls) = singleton x ∪ listToPred ls

module _ where
  open PosetPoly

  _→pw_ : (C : Set) (D : Poset) → Poset
  _→pw_ C D .Carrier = C → ∣ D ∣
  _→pw_ C D ._≈_ = Pointwise C (D ._≈_)
  _→pw_ C D ._≤_ = Pointwise C (D ._≤_)
  _→pw_ C D .isPartialOrder = FunBinR.→isPartialOrder C (D .isPartialOrder)

  _→mono-pw_ : (C : Poset) (D : Poset) → Poset
  _→mono-pw_ C D .Carrier = C →mono D
  _→mono-pw_ C D ._≈_ f g = Pointwise ∣ C ∣ (D ._≈_) ⟦ f ⟧ ⟦ g ⟧
  _→mono-pw_ C D ._≤_ f g = Pointwise ∣ C ∣ (D ._≤_) ⟦ f ⟧ ⟦ g ⟧
  _→mono-pw_ C D .isPartialOrder = FunBinR.→mono-isPartialOrder C D

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

  Pred→Prop : (D : Setoid) → Pred D → Set
  Pred→Prop D P = ∀ d → d ∈ P

  Pred⊆-→mono-Prop→ : (D : Setoid) → Pred⊆-poset D →mono Prop→-poset
  Pred⊆-→mono-Prop→ D = mkMono (Pred⊆-poset D) Prop→-poset (Pred→Prop D)
    (λ {P} {Q} P⊆Q ∀d→d∈P d → P⊆Q (∀d→d∈P d))

module _ {X≈ : Setoid} where
  open SetoidPoly X≈
  private
    X = ∣ X≈ ∣

  ∩-∘-mono₂ : (Pred⊆-poset X≈ ×-poset Pred⊆-poset X≈) →mono Pred⊆-poset X≈
  ∩-∘-mono₂ = mkMono (Pred⊆-poset X≈ ×-poset Pred⊆-poset X≈) (Pred⊆-poset X≈)
    (uncurry _∩_)
    (λ {(x , y)} {(z , w)} → uncurry (∩-mono x z y w))

record FinSubset (X : Setoid) : Set where
  field
    pred : Pred X
    list : List ∣ X ∣
  open SetoidPoly X
  field
    list≈ : listToPred X list ≐ pred

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

  ⃗single : (f : X≈ →cong Y≈) → ∀ x →  ⃗ f (singleton X≈ x) ≐ singleton Y≈ (⟦ f ⟧ x)
  ⃗single f x =
    ( (λ {y} (x' , fx'≈y , x≈x') → Y.trans (f .Cong.cong x≈x') fx'≈y)
    , (λ {y} fx≈y → (x , fx≈y , X.refl)))

  ⃗pair  : (f : X≈ →cong Y≈) → ∀ x x' →  ⃗ f (doubleton X≈ x x') ≐ doubleton Y≈ (⟦ f ⟧ x) (⟦ f ⟧ x')
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
    open SetoidPoly (X≈ ×-setoid Y≈)

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

  doubleton-proj₁ : ∀ (x x' : X) (y y' : Y) → ((doubleton _ (x , y) (x' , y')) ∣₁) ≐ doubleton _ x x'
  doubleton-proj₁ x x' y y' = ∀↔→≐ {X≈} {(doubleton _ (x , y) (x' , y')) ∣₁} {doubleton _ x x'}
    (λ _ → Sum.map proj₁ proj₁ ∘ proj₂ , λ { (inj₁ x≈) → (y , inj₁ (x≈ , Y.refl)) ; (inj₂ x'≈) → (y' , inj₂ (x'≈ , Y.refl))})

  doubleton-proj₂ : ∀ (x x' : X) (y y' : Y) → ((doubleton _ (x , y) (x' , y')) ∣₂) ≐ doubleton _ y y'
  doubleton-proj₂ x x' y y' = ∀↔→≐ {Y≈} {(doubleton _ (x , y) (x' , y')) ∣₂} {doubleton _ y y'}
    (λ _ → Sum.map proj₂ proj₂ ∘ proj₂ , λ { (inj₁ y≈) → (x , inj₁ (X.refl , y≈)) ; (inj₂ y'≈) → (x' , inj₂ (X.refl , y'≈))})

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

  infix 3 _≤_ _≈_

  poset : Poset
  poset = record {isPartialOrder = ≤-po}

  module Po = PosetPoly poset
  module Eq = Po.Eq

  field
    ⨆ :  Pred Eq.setoid → Carrier
    ⨆-sup : ∀ S → (∀ x → x ∈ S → x ≤ ⨆ S) × (∀ y → (∀ x → x ∈ S → x ≤ y) → ⨆ S ≤ y)

  ubs : Pred Eq.setoid → Pred Eq.setoid
  ubs = upperbounds poset

  lbs : Pred Eq.setoid → Pred Eq.setoid
  lbs = lowerbounds poset


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

  ｛_｝ : Carrier → Pred Eq.setoid
  ｛_｝ = singleton Eq.setoid

  ｛_،_｝ : Carrier → Carrier → Pred (Eq.setoid)
  ｛_،_｝ = doubleton Eq.setoid

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

  ⊔-mono-l : ∀ z x y → x ≤ y → x ⊔ z ≤ y ⊔ z
  ⊔-mono-l z x y x≤y = ⊔-least x z (y ⊔ z) (Po.trans x≤y (⊔-ub-l y z)) (⊔-ub-r y z)

  ⊔-mono-r : ∀ z x y → x ≤ y → z ⊔ x ≤ z ⊔ y
  ⊔-mono-r z x y x≤y = ⊔-least z x (z ⊔ y) (⊔-ub-l z y) (Po.trans x≤y (⊔-ub-r z y))

  ⊔-mono : ∀ x y z w → x ≤ z → y ≤ w → x ⊔ y ≤ z ⊔ w
  ⊔-mono x y z w x≤z y≤w = ⊔-least x y (z ⊔ w) (Po.trans x≤z (⊔-ub-l z w)) (Po.trans y≤w (⊔-ub-r z w))

  ⨆-⊔-comm : ∀ P Q → (⨆ P ⊔ ⨆ Q) ≈ ⨆ (P ∪ Q)
  ⨆-⊔-comm P Q = Po.antisym (⨆-least ｛ ⨆ P ، ⨆ Q ｝ (⨆ (P ∪ Q)) ⨆P∪Q-ub ) (⨆-least (P ∪ Q) (⨆ ｛ ⨆ P ، ⨆ Q ｝) ⨆P⊔⨆Q-ub)
    where
    ⨆P∪Q-ub : ∀ x → x ∈ ｛ ⨆ P ، ⨆ Q ｝ → x ≤ ⨆ (P ∪ Q)
    ⨆P∪Q-ub x (inj₁ ⨆P≈x) = Po.reflexive (Eq.sym ⨆P≈x) ⟨ Po.trans ⟩ ⨆-mono P (P ∪ Q) (∪-⊆-l P Q)
    ⨆P∪Q-ub x (inj₂ ⨆Q≈x) = Po.reflexive (Eq.sym ⨆Q≈x) ⟨ Po.trans ⟩ ⨆-mono Q (P ∪ Q) (∪-⊆-r P Q)
    ⨆P⊔⨆Q-ub : ∀ x → x ∈ (P ∪ Q) → x ≤ (⨆ P ⊔ ⨆ Q)
    ⨆P⊔⨆Q-ub x (inj₁ x∈P) = ⨆-ub P x x∈P ⟨ Po.trans ⟩ ⊔-ub-l (⨆ P) (⨆ Q)
    ⨆P⊔⨆Q-ub x (inj₂ x∈Q) = ⨆-ub Q x x∈Q ⟨ Po.trans ⟩ ⊔-ub-r (⨆ P) (⨆ Q)

  ≤⨆→≤ubs : ∀ x S → x ≤ ⨆ S → (∀ u → u ∈ ubs S → x ≤ u)
  ≤⨆→≤ubs x S x≤⨆S u u∈ubsS = Po.trans x≤⨆S (⨆-least S u u∈ubsS)

  ≤⨆←≤ubs : ∀ x S → (∀ u → u ∈ ubs S → x ≤ u) → x ≤ ⨆ S
  ≤⨆←≤ubs x S x≤ubs = x≤ubs (⨆ S) (λ x' x'∈S → ⨆-ub S x' x'∈S)

  ≤⨆↔≤ubs : ∀ x S → x ≤ ⨆ S ↔ (∀ u → u ∈ ubs S → x ≤ u)
  ≤⨆↔≤ubs x S = (≤⨆→≤ubs x S , ≤⨆←≤ubs x S)

  ≤→⊔-≈ : ∀ x y → x ≤ y → (x ⊔ y) ≈ y
  ≤→⊔-≈ x y x≤y = Po.antisym (⊔-least x y y x≤y Po.refl) (⊔-ub-r x y)


  ⊤ : Carrier
  ⊤ = ⨆ U

  ⊤-max : Maximum _≤_ ⊤
  ⊤-max x = ⨆-ub U x _

  ⊤≈⨆U : ⊤ ≈ ⨆ U
  ⊤≈⨆U = Po.antisym (⨆-ub U _ _ ) (⊤-max (⨆ U))

  ⨆≤→∀≤ : ∀ S x → ⨆ S ≤ x → ∀ x' → x' ∈ S → x' ≤ x
  ⨆≤→∀≤ S x ⨆S≤x x' x'∈S = Po.trans (⨆-ub _ _ x'∈S) ⨆S≤x

  ⨆≤←∀≤ : ∀ S x → (∀ x' → x' ∈ S → x' ≤ x) → ⨆ S ≤ x
  ⨆≤←∀≤ = ⨆-least

  ⨆≤↔∀≤ : ∀ S x → ⨆ S ≤ x ↔ (∀ x' → x' ∈ S → x' ≤ x)
  ⨆≤↔∀≤ S x .proj₁ = ⨆≤→∀≤ S x
  ⨆≤↔∀≤ S x .proj₂ = ⨆≤←∀≤ S x

  ⨅ : Pred Eq.setoid → Carrier
  ⨅ S = ⨆ (lbs S)

  ⨅-lb : ∀ S x → x ∈ S → ⨅ S ≤ x
  ⨅-lb S x x∈S = ⨆-least (lbs S) x x-ub
    where
    x-ub : ∀ y → y ∈ lbs S → y ≤ x
    x-ub y y∈lbS = y∈lbS x x∈S

  ⨅-greatest : ∀ S y → (∀ x → x ∈ S → y ≤ x) → y ≤ ⨅ S
  ⨅-greatest S y y-lower = ⨆-ub (lbs S) y y-lower

  ⨅-inf : ∀ S → (∀ x → x ∈ S → ⨅ S ≤ x) × (∀ y → (∀ x → x ∈ S → y ≤ x) → y ≤ ⨅ S)
  ⨅-inf S = (⨅-lb S ,  ⨅-greatest S)

  ⨅-anti : ∀ S S' → S ⊆ S' → ⨅ S' ≤ ⨅ S
  ⨅-anti S S' S⊆S' = ⨅-greatest S (⨅ S') (\ x x∈S → ⨅-lb S' x (S⊆S' x∈S))

  ⨅-cong : ∀ S S' → S ≐ S' → ⨅ S ≈ ⨅ S'
  ⨅-cong S S' S≐S' = Po.antisym (⨅-anti S' S (proj₂ S≐S')) (⨅-anti S S' (proj₁ S≐S'))


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

  ν-fp : (f≤ : poset →mono poset) → ν ⟦ f≤ ⟧cong ∈ (fix Eq.setoid ⟦ f≤ ⟧cong)
  ν-fp f≤ =
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

  ν-ubfp : (f≈ : Eq.setoid →cong Eq.setoid) → ν f≈ ∈ ubs (fix Eq.setoid f≈)
  ν-ubfp f≈ x x∈fixf = ⨆-ub (post≤ f≈) x (Po.reflexive x∈fixf)

  ν-gfp : (f≤ : poset →mono poset) → ν (⟦ f≤ ⟧cong) ∈ gfp poset (⟦ f≤ ⟧cong)
  ν-gfp f≤ = (ν-fp f≤ , ν-ubfp (⟦ f≤ ⟧cong))

  ν-mono : (f≈ g≈ : Eq.setoid →cong Eq.setoid) → ((x : Carrier) → ⟦ f≈ ⟧ x ≤ ⟦ g≈ ⟧ x) → ν f≈ ≤ ν g≈
  ν-mono f≈ g≈ f≤g = ⨆-mono (post≤ f≈) (post≤ g≈) (λ {d} d≤fd → Po.trans d≤fd (f≤g d))

  ≈→≤↔≤-l : ∀ x y → x ≈ y → ∀ z → x ≤ z ↔ y ≤ z
  ≈→≤↔≤-l x y x≈y z = (Po.trans (Po.reflexive (Eq.sym x≈y)) , Po.trans (Po.reflexive x≈y))

  ≈→≤↔≤-r : ∀ x y → x ≈ y → ∀ z → z ≤ x ↔ z ≤ y
  ≈→≤↔≤-r x y x≈y z = (flip Po.trans (Po.reflexive x≈y) , flip Po.trans (Po.reflexive (Eq.sym x≈y)))

  μ : (Eq.setoid →cong Eq.setoid) → Carrier
  μ f = ⨅ (pre poset f)

  IsCompact : (x : Carrier)  → Set
  IsCompact x = ∀ S → x ≤ ⨆ S → Σ xs ∶ List Carrier , All (_∈ S) xs × x ≤ ⨆ (listToPred _ xs)

  IsDirected : (S : Pred Eq.setoid) → Set
  IsDirected S = ∀ (xs : List Carrier) → All (λ x → x ∈ S) xs → Σ u ∶ Carrier , (u ∈ S × All (λ x → x ≤ u) xs)

  IsChain : (S : Pred Eq.setoid) → Set
  IsChain S = ∀ x y → x ∈ S → y ∈ S → x ≤ y ⊎ y ≤ x

  -- Scott open [Taylor, 2010, A lambda calculus for real analysis, Def. 3.1]
  IsScottOpen : (S : Pred Eq.setoid) → Set
  IsScottOpen S = IsUpwardClosed poset S × (∀ T → (⨆ T) ∈ S → Σ xs ∶ List Carrier , listToPred _ xs ⊆ T × ⨆ (listToPred _ xs) ∈ S)

instance
  slat-has-carrier : HasCarrier (SLat)
  slat-has-carrier .HasCarrier.Carrier = SLat.Carrier

module _ (C⨆ : SLat) where
  open SLat C⨆
  private
    C = Carrier
    C≈ = Eq.setoid
    C≤ = poset

  module _ (f≈ : C≈ →cong C≈) (c : C) where
    private
      f = ⟦ f≈ ⟧
      c* = ν f≈

    post→≤ν : c ≤ f c → c ≤ c*
    post→≤ν c-post-f = ⨆-ub (post≤ f≈) c c-post-f

    module _ (fc-ub-of-post-f : ∀ x → x ≤ f x → x ≤ f c) where
      app-ub-of-post∧≤ν→post : c ≤ c* → c ≤ f c
      app-ub-of-post∧≤ν→post c≤νf = Po.trans c≤νf (⨆-least (post≤ f≈) (f c) fc-ub-of-post-f)

      app-ub-of-post→≤ν↔post : c ≤ c* ↔ c ≤ f c
      app-ub-of-post→≤ν↔post = ( app-ub-of-post∧≤ν→post , post→≤ν)

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
  (D ×-slat E) ._≈_ = Componentwise (D ._≈_) (E ._≈_)
  (D ×-slat E) ._≤_ = Componentwise (D ._≤_) (E ._≤_)
  (D ×-slat E) .≤-po = ×-isPartialOrder (D .≤-po) (E .≤-po)
  (D ×-slat E) .⨆ R =  D .⨆ (R ∣₁) , E .⨆ (R ∣₂)
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
    D≤ = D.poset
    D≈ = D.Eq.setoid
    D = D.Carrier
    module E = SLat E⨆
    E≤ = E.poset
    E≈ = E.Eq.setoid
    E = E.Carrier

  open SLat (D⨆ ×-slat E⨆)

  lbs-proj₁ : ∀ S → (lbs S ∣₁) ≐ (D.lbs (S ∣₁))
  lbs-proj₁ S = ∀↔→≐ {D≈} {lbs S ∣₁} {D.lbs (S ∣₁)}
    λ d →
      ( (λ d∈lbsS∣₁@(e , de∈lbsS) d' (e' , d'e'∈S) → proj₁ (de∈lbsS (d' , e') d'e'∈S))
      , (λ d∈lbsS∣₁ → E.⨅ (S ∣₂) , (λ p'@(d' , e') d'e'∈S → (d∈lbsS∣₁ d' (e' , d'e'∈S) , E.⨅-lb (S ∣₂) e' (d' , d'e'∈S)))))

  lbs-proj₂ : ∀ S → (lbs S ∣₂) ≐ (E.lbs (S ∣₂))
  lbs-proj₂ S = ∀↔→≐ {E≈} {lbs S ∣₂} {E.lbs (S ∣₂)}
    λ e →
      ( (λ e∈lbsS∣₂@(d , de∈lbsS) e' (d' , d'e'∈S) → proj₂ (de∈lbsS (d' , e') d'e'∈S))
      , (λ e∈lbsS∣₂ → D.⨅ (S ∣₁) , (λ p'@(d' , e') d'e'∈S → (D.⨅-lb (S ∣₁) d' (e' , d'e'∈S) , e∈lbsS∣₂ e' (d' , d'e'∈S)))))


  ⊔-componentwise : ∀ d e d' e' → ((d , e) ⊔ (d' , e')) ≈ (d D.⊔ d' , e E.⊔ e')
  ⊔-componentwise d e d' e' =
    ( D.⨆-cong (｛ d , e ، d' , e' ｝ ∣₁) D.｛ d ، d' ｝ (doubleton-proj₁ {D≈} {E≈} d d' e e')
    , E.⨆-cong (｛ d , e ، d' , e' ｝ ∣₂) E.｛ e ، e' ｝ (doubleton-proj₂ {D≈} {E≈} d d' e e'))

  ⨅-componentwise : ∀ (S : Pred (D≈ ×-setoid E≈)) → ⨅ S ≈ (D.⨅ (S ∣₁) , E.⨅ (S ∣₂))
  ⨅-componentwise S = (D.⨆-cong (lbs S ∣₁) (D.lbs (S ∣₁)) (lbs-proj₁ S)) , E.⨆-cong (lbs S ∣₂) (E.lbs (S ∣₂)) (lbs-proj₂ S)

  ⊓-componentwise : ∀ d e d' e' → ((d , e) ⊓ (d' , e')) ≈ (d D.⊓ d' , e E.⊓ e')
  ⊓-componentwise d e d' e' = Eq.trans (⨅-componentwise ｛ d , e ، d' , e' ｝)
    ( D.⨅-cong (｛ d , e ، d' , e' ｝ ∣₁) D.｛ d ، d' ｝ (doubleton-proj₁ {D≈} {E≈} d d' e e')
    , E.⨅-cong (｛ d , e ، d' , e' ｝ ∣₂) E.｛ e ، e' ｝ (doubleton-proj₂ {D≈} {E≈} d d' e e'))

  endo-proj₁ : ((D≈ ×-setoid E≈) →cong (D≈ ×-setoid E≈)) → D → D
  endo-proj₁ f≈ d = proj₁ (⟦ f≈ ⟧ (d , proj₂ (ν f≈)))

  endo-proj₁-cong : ((D≈ ×-setoid E≈) →cong (D≈ ×-setoid E≈)) → D≈ →cong D≈
  Cong.⟦ endo-proj₁-cong f≈ ⟧ = endo-proj₁ f≈
  endo-proj₁-cong f≈ .Cong.isCongruent .IsCong.cong {d} {d'} d≈d' = proj₁ (f≈ .Cong.cong (d≈d' , E.Eq.refl))

  endo-proj₂ : ((D≈ ×-setoid E≈) →cong (D≈ ×-setoid E≈)) → E → E
  endo-proj₂ f≈ e = proj₂ (⟦ f≈ ⟧ (proj₁ (ν f≈) , e))

  endo-proj₂-cong : ((D≈ ×-setoid E≈) →cong (D≈ ×-setoid E≈)) → E≈ →cong E≈
  Cong.⟦ endo-proj₂-cong f≈ ⟧ = endo-proj₂ f≈
  endo-proj₂-cong f≈ .Cong.isCongruent .IsCong.cong {e} {e'} e≈e' = proj₂ (f≈ .Cong.cong (D.Eq.refl , e≈e'))

  module _ (f≤ : (D≤ ×-poset E≤) →mono (D≤ ×-poset E≤)) where
    private
      f≈ = ⟦ f≤ ⟧cong
      f = ⟦ f≤ ⟧

      f∣₁≈ : D≈ →cong D≈
      f∣₁≈ = endo-proj₁-cong ⟦ f≤ ⟧cong

      f∣₁ : D → D
      f∣₁ = ⟦ f∣₁≈ ⟧

      f∣₂≈ : E≈ →cong E≈
      f∣₂≈ = endo-proj₂-cong ⟦ f≤ ⟧cong

      f∣₂ : E → E
      f∣₂ = ⟦ f∣₂≈ ⟧

      p* : D × E
      p* = ν f≈

      d* : D
      d* = D.ν f∣₁≈

      e* : E
      e* = E.ν f∣₂≈

    --
    proj₁ν≤νproj₁ : proj₁ p* D.≤ d*
    proj₁ν≤νproj₁ = D.ν-ubfp f∣₁≈ (proj₁ p*) (proj₁ (ν-fp f≤))


{-
    ≤νproj₁→≤proj₁ν : d* D.≤ proj₁ p*
    ≤νproj₁→≤proj₁ν = D.⨆-least (D.post≤ f∣₁≈) (proj₁ p*) λ d d≤proj₁[fd[proj₂-p*]] → proj₁ (⨆-ub (post≤ f≈) (d , _) ({!!} , {!!}))
-}
{-
    module _ (d : D) (d D.≤ d*where
      d D.≤ proj₁ (f (d , proj₂ p*)) → d D.≤ proj₁ p*

    ub-post→≤ν↔∈post-proj₁ : (d : D) →
       {!!} → d D.≤ (proj₁ p*) ↔ d D.≤ proj₁ (f (d , proj₂ p*))
    ub-post→≤ν↔∈post-proj₁ d hoge =
      let open SetoidReasoning Prop↔-setoid in
      begin
      (d D.≤ proj₁ p*) ≡⟨⟩
      (d D.≤ proj₁ (ν f≈)) ≈⟨ D.≤⨆↔≤ubs d (post poset f≈ ∣₁) ⟩
      (∀ u → u ∈ D.ubs (post≤ f≈ ∣₁) → d D.≤ u) ≈⟨ d-is-lb-of-ubs-of-pofstfix-f∣₁→d-is-postfix-f∣₁ , P ⟩
      (d D.≤ f∣₁ d) ≡⟨⟩
      (d D.≤ proj₁ (f (d , (proj₂ p*)))) ∎
      where
      Z' : ∀ d' e' → (d' , e') ≤ f (d' , e') → proj₁ (f (d' , e')) D.≤ proj₁ (f (d , proj₂ p*))
      Z' d' e' x = {!!}
      Z : ∀ d' → (Σ e' ∶ E , (d' , e') ≤ f (d' , e')) → d' D.≤ f∣₁ d
      Z d' (e' , d'e'≤fd'e') = D.Po.trans (proj₁ d'e'≤fd'e') (Z' d' e' d'e'≤fd'e')

      d-is-lb-of-ubs-of-pofstfix-f∣₁→d-is-postfix-f∣₁ : (∀ u → u ∈ D.ubs (post≤ f≈ ∣₁) → d D.≤ u) → d D.≤ f∣₁ d
      d-is-lb-of-ubs-of-pofstfix-f∣₁→d-is-postfix-f∣₁ d-is-lb-of-ubs-of-pofstfix-f∣₁ = d-is-lb-of-ubs-of-pofstfix-f∣₁ (proj₁ (f (d , proj₂ (ν f≈)))) Z

      Q : d D.≤ proj₁ (f (d , proj₂ p*))
      Q = {!l!}
      Q' : proj₂ p* E.≤ proj₂ (f (d , proj₂ p*))
      Q' = {!!}
      P : d D.≤ proj₁ (f (d , proj₂ (ν f≈))) → ∀ u → u ∈ D.ubs (post≤ f≈ ∣₁) → d D.≤ u
      P d≤ u u-ub = u-ub d (proj₂ p* , Q , Q')
-}
{-
  ub-post→≤ν↔∈post : ∀ (f≈ : Eq.setoid →cong Eq.setoid) (c : Carrier) → ⟦ f≈ ⟧ c ∈ ubs (post≤ f≈) → c ≤ ν f≈ ↔ c ∈ post≤ f≈
  ub-post→≤ν↔∈post f≈ c fc∈ubpostf = let open SetoidReasoning (Prop↔-setoid) in
    begin
    (c ≤ ν f≈) ≈⟨  ≤⨆↔≤ubs c (post≤ f≈)  ⟩
    (∀ u → u ∈ ubs (post≤ f≈) → c ≤ u) ≈⟨ (λ c-lb-of-ubs → c-lb-of-ubs (⟦ f≈ ⟧ c) fc∈ubpostf) , (λ c∈postf u u-ub → u-ub c c∈postf) ⟩
    (c ≤ ⟦ f≈ ⟧ c) ∎
-}


{-
  νproj₁ : (D≈ ×-setoid E≈) →cong (D≈ ×-setoid E≈) → (D≈ →cong D≈)
  νproj₁ f = proj₁≈ _ _ ∘-cong (curry-flip-cong f (ν f .proj₂))

  νproj₂ : (D≈ ×-setoid E≈) →cong (D≈ ×-setoid E≈) → (E≈ →cong E≈)
  νproj₂ f = proj₂≈ _ _ ∘-cong (curry-cong f (ν f .proj₁))

  νproj₁-≈ : (f≤ : (D≤ ×-poset E≤) →mono (D≤ ×-poset E≤)) → D.ν (νproj₁ ⟦ f≤ ⟧cong) D.≈ ν ⟦ f≤ ⟧cong .proj₁
  νproj₁-≈ f≤ = D.⨆-cong (post D.poset (νproj₁ ⟦ f≤ ⟧cong)) (post poset ⟦ f≤ ⟧cong ∣₁) (P $- , Q $-) -- (P , Q)
    where
    P :  ∀ d → d D.≤ ⟦ νproj₁ ⟦ f≤ ⟧cong ⟧ d  → Σ e ∶ E , (d , e) ≤ ⟦ f≤ ⟧ (d , e)
    P d d≤νproj₁fd = (e* , (d≤νproj₁fd , P'))
      where
      e* = ν ⟦ f≤ ⟧cong .proj₂
      Q' : ∀ e → (Σ d ∶ D , (d , e) ≤ ⟦ f≤ ⟧ (d , e)) → e E.≤ proj₂ (⟦ f≤ ⟧ (⨆ (post≤ ⟦ f≤ ⟧cong)))
      Q' e (d , de≤fde) = E.Po.trans (proj₂ de≤fde) (proj₂-mono D≤ E≤ .IsMono.mono (f≤ .Mono.mono {!!}))
      G' : ∀ u → u ∈ (post≤ ⟦ f≤ ⟧cong ∣₁) → u D.≤ d
      G' u x = {!d≤νproj₁fd!}
      P' : E.⨆ ((post≤ ⟦ f≤ ⟧cong) ∣₂) E.≤ proj₂ (⟦ f≤ ⟧ (d , E.⨆ ((post≤ ⟦ f≤ ⟧cong) ∣₂)))
      P' = let open PosetReasoning E.poset in
        begin
        E.⨆ (post≤ ⟦ f≤ ⟧cong ∣₂) ≤⟨ E.⨆-least (post≤ ⟦ f≤ ⟧cong ∣₂) (proj₂ (⟦ f≤ ⟧ (⨆ (post≤ ⟦ f≤ ⟧cong)))) Q' ⟩
        proj₂ (⟦ f≤ ⟧ (⨆ (post≤ ⟦ f≤ ⟧cong))) ≤⟨ proj₂-mono D≤ E≤ .IsMono.mono (f≤ .Mono.mono (D.⨆-least (post≤ ⟦ f≤ ⟧cong ∣₁) d G'  , E.Po.refl)) ⟩
        proj₂ (⟦ f≤ ⟧ (d , E.⨆ ((post≤ ⟦ f≤ ⟧cong) ∣₂))) ∎

    Q : ∀ d → Σ e ∶ E , (d , e) ≤ ⟦ f≤ ⟧ (d , e) → d D.≤ ⟦ νproj₁ ⟦ f≤ ⟧cong ⟧ d
    Q d (e , de≤fde) = D.Po.trans (proj₁ de≤fde) (proj₁-mono D≤ E≤ .IsMono.mono (f≤ .Mono.mono (D.Po.refl , (E.Po.trans (proj₂ de≤fde) (E.⨆-ub (post poset ⟦ f≤ ⟧cong ∣₂) (proj₂ (⟦ f≤ ⟧ (d , e))) (⟦ f≤ ⟧ (d , e) .proj₁ , f≤ .Mono.mono de≤fde))))))
-}
IsCoclosure : (D : Poset) (f : ∣ D ∣ → ∣ D ∣) → Set
IsCoclosure D f = ∀ d → f d ≤ d × f d ≤ f (f d)
  where open PosetPoly D

Is⨆Closed : (D : SLat) → Pred (SLat.Eq.setoid D) → Set
Is⨆Closed D S = ∀ S' → S' ⊆ S → (SLat.⨆ D S') ∈ S

Is⊔Closed : (D : SLat) → Pred (SLat.Eq.setoid D) → Set
Is⊔Closed D S = ∀ x y → x ∈ S → y ∈ S → (SLat._⊔_ D x y) ∈ S

⨆closed→⊔closed : (D : SLat) → (S : Pred (SLat.Eq.setoid D)) → Is⨆Closed D S → Is⊔Closed D S
⨆closed→⊔closed D S ⨆closed x y x∈S y∈S = ⨆closed (doubleton _ x y) λ{ (inj₁ x≈) → S .Pred.isWellDefined x≈ x∈S ; (inj₂ y≈) → S .Pred.isWellDefined y≈ y∈S}

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

  IsOrderReflecting : {D : Poset} {C : Poset} → D →mono C → Set
  IsOrderReflecting {D} {C} f≤ = ∀ {d d'} → ⟦ f≤ ⟧ d C.≤ ⟦ f≤ ⟧ d' → d D.≤ d'
    where
    module C = PosetProps C
    module D = PosetProps D

  record OrderEmbedding {C : Poset} {D : Poset} (e : D →mono C) : Set where
    private module C = PosetProps C
    private module D = PosetProps D
    field
      reflecting : ∀ d d' → ⟦ e ⟧ d C.≤ ⟦ e ⟧ d' → d D.≤ d'

    injective : ∀ d d' → ⟦ e ⟧ d C.≈ ⟦ e ⟧ d' → d D.≈ d'
    injective d d' ed≈ed' = D.antisym (reflecting d d' (C.≈→≤ ed≈ed')) (reflecting d' d (C.≈→≥ ed≈ed'))

  module _ {C : Poset} {D : Poset} (L : C →mono D ) (R : D →mono C) where
    private
      module C = PosetProps C
      module D = PosetProps D

    module _ (L⊣R : L ⊣ R) where
      open GaloisConnection L⊣R

      private
        -- L ⊣ R → R d = max (L⁻¹ ↓ d)
        R-belongs : ∀ d → ⟦ R ⟧ d ∈ ⃖ ⟦ L ⟧cong (principal-downset D d)
        R-belongs d = ⟦ L ⟧ (⟦ R ⟧ d) , (D.Eq.refl , ε d)

        R-greatest : ∀ d c → c ∈ ⃖ ⟦ L ⟧cong (principal-downset D d) → c C.≤ ⟦ R ⟧ d
        R-greatest d c (d' , Lc≈d' , d'≤d) = C.trans (ψ c d' .proj₁ (D.reflexive (Lc≈d'))) (R .Mono.mono d'≤d)

      module _ (R-reflecting : IsOrderReflecting R) where
        L⊣R∧R-embedding→LR≈Id : ∀ d → ⟦ L ⟧ (⟦ R ⟧ d) D.≈ d
        L⊣R∧R-embedding→LR≈Id d = D.antisym LRd≤d LRd≥d
          where
          LRd≤d : ⟦ L ⟧ (⟦ R ⟧ d) D.≤ d
          LRd≤d = ε d
          LRd≥d : d D.≤ ⟦ L ⟧ (⟦ R ⟧ d)
          LRd≥d = R-reflecting (η (⟦ R ⟧ d))


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

    module _ (L : C≤ →mono D≤)  where
      LtoR-raw : D → C
      LtoR-raw d = C.⨆ (⃖ ⟦ L ⟧cong (D.↓! d))

      LtoR : D≤ →mono C≤
      LtoR = mkMono D≤ C≤ LtoR-raw
        (λ {d} {d'} d≤d' →  C.⨆-mono (⃖ ⟦ L ⟧cong (D.↓! d)) (⃖ ⟦ L ⟧cong (D.↓! d'))
          ((⃖-mono ⟦ L ⟧cong (D.↓! d) (D.↓! d') (λ x≤d → D.Po.trans x≤d d≤d' ))))

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
        R = LtoR L

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
        R = LtoR L

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

