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
import Data.Nat as Nat

open import predicate
open import complete-lattice
open import preorder
open import galois-connections

module compositions where

record preorder-enriched-cat : Set where
  field
    Ob : Set
    Hom : Ob → Ob → Set
    I : ∀{X} → Hom X X
    _⊗_ : ∀{X Y Z} → Hom X Y → Hom Y Z → Hom X Z
    _≤_ : ∀{X Y} → rel (Hom X Y) (Hom X Y)

  _≈_ : ∀{X Y} → rel (Hom X Y) (Hom X Y)
  _≈_ = iso-pair _≤_

  field
    Hom-is-preorder : ∀{X Y} → is-preorder (_≤_ {X} {Y})
    assoc : {X Y Z W : Ob} {a : Hom X Y} {b : Hom Y Z} {c : Hom Z W} → ((a ⊗ b) ⊗ c) ≈ (a ⊗ (b ⊗ c))
    lunit : {X Y : Ob} {a : Hom X Y} → (I ⊗ a) ≈ a
    runit : {X Y : Ob} {a : Hom X Y} → (a ⊗ I) ≈ a

module _ where
  open preorder-enriched-cat
  open monotone-func
  open complete-meet-semilattice
  open endo-function
  open transfer-function-pair

  module _ (X Y Z : complete-meet-semilattice)
    (let X×Z = X ×-cmlat Z)
    (let X×Y = X ×-cmlat Y)
    (let Y×Z = Y ×-cmlat Z)
    (let (cmlat XZ _≤XZ_ ⋀XZ XZ-prop) = X×Z)
    (let (cmlat XY _≤XY_ ⋀XY XY-prop) = X×Y)
    (let (cmlat YZ _≤YZ_ ⋀YZ YZ-prop) = Y×Z)
    (let XZ-pre = cmlat→pre (X ×-cmlat Z))
    (let XY-pre = cmlat→pre (X ×-cmlat Y))
    (let YZ-pre = cmlat→pre (Y ×-cmlat Z))
    (let _≈XZ_ = iso-pair _≤XZ_)
    (let _≈XY_ = iso-pair _≤XY_)
    (let _≈YZ_ = iso-pair _≤YZ_)
    where

    mendo-comp : monotone-func XY-pre XY-pre → monotone-func YZ-pre YZ-pre → monotone-func XZ-pre XZ-pre
    func (mendo-comp f g) (x , z) = ⋀XZ \{ (x' , z') → (x , z) ≤XZ (x' , z') × ∃ \ y' → f .func (x' , y') ≤XY (x' , y') × g .func (y' , z') ≤YZ (y' , z')  }
    property (mendo-comp f g) {xz} {x'z'} (xz≤x'z') = complete-meet-semilattice.property.bigmeet-monotone X×Z \{ {(x''z'')} ((x'z'≤x''z'') , Ey') → XZ-trans xz≤x'z' x'z'≤x''z'' , Ey'}
      where XZ-trans = preordered-set.property.rel-is-transitive XZ-pre
            XY-trans = preordered-set.property.rel-is-transitive XY-pre
            YZ-trans = preordered-set.property.rel-is-transitive YZ-pre

    rel2mendo∘⋈∘mendo2rel≈mendo-comp : (f : monotone-func XY-pre XY-pre) → (g : monotone-func YZ-pre YZ-pre)
      → ∀ xz → func (rel2mendo X×Z ((mendo2rel X×Y f) ⋈ (mendo2rel Y×Z g))) xz ≈XZ func (mendo-comp f g) xz
    forward (rel2mendo∘⋈∘mendo2rel≈mendo-comp f g (x , z)) = complete-meet-semilattice.property.bigmeet-monotone X×Z id
    backward (rel2mendo∘⋈∘mendo2rel≈mendo-comp f g (x , z)) = complete-meet-semilattice.property.bigmeet-monotone X×Z id

  cat-rel : preorder-enriched-cat
  Ob cat-rel = complete-meet-semilattice
  Hom cat-rel D E = preordered-set.carrier (pre-rel D E)
  I cat-rel {X} (x , x') = x ≡ x' -- maybe we should do x ≈ x' and relation to be well-defined
    where _~_ = iso-pair (complete-meet-semilattice.relation X)
  _⊗_ cat-rel = _⋈_
  _≤_ cat-rel = _⊆_
  Hom-is-preorder cat-rel = ⊆-is-preorder
  forward (assoc cat-rel) (z , (y , p , q) , r) = y , p , z , q , r
  backward (assoc cat-rel) (y , p , z , q , r) = z , (y , p , q) , r
  iso-pair.forward (lunit cat-rel) (x , ≡.refl , y) = y
  backward (lunit cat-rel) x =  _ , ≡.refl , x
  forward (runit cat-rel) (x , y , ≡.refl) = y
  backward (runit cat-rel) x = _ , x , ≡.refl

  cat-mfun : preorder-enriched-cat
  Ob cat-mfun = complete-meet-semilattice
  Hom cat-mfun D E = preordered-set.carrier (pre-mfun D E)
  I cat-mfun {X} = mono id id
  _⊗_ cat-mfun f g = pre-comp g f
  _≤_ cat-mfun {X} {Y} f g = _≤mfun_ X Y f g
  Hom-is-preorder cat-mfun {X} {Y} = ≤mfun-is-preorder X Y
  forward (assoc cat-mfun {W = W} {a} {b} {c}) x = W .property.rel-is-reflexive (c .func (b .func (a .func x)))
  backward (assoc cat-mfun {W = W} {a} {b} {c}) x = W .property.rel-is-reflexive (c .func (b .func (a .func x)))
  forward (lunit cat-mfun {Y = Y} {a}) x = Y .property.rel-is-reflexive (a .func x)
  backward (lunit cat-mfun {Y = Y} {a}) x = Y .property.rel-is-reflexive (a .func x)
  forward (runit cat-mfun {Y = Y} {a}) x = Y .property.rel-is-reflexive (a .func x)
  backward (runit cat-mfun {Y = Y} {a}) x = Y .property.rel-is-reflexive (a .func x)

  cat-mendo : preorder-enriched-cat
  Ob cat-mendo = complete-meet-semilattice
  Hom cat-mendo D E = preordered-set.carrier (pre-mendo (D ×-cmlat E))
  I cat-mendo = mono id id
  _⊗_ cat-mendo {X} {Y} {Z} f g = mendo-comp X Y Z f g
  _≤_ cat-mendo {X} {Y} f g = _≤mfun_ (X ×-cmlat Y) (X ×-cmlat Y) f g
  Hom-is-preorder cat-mendo {X} {Y} = ≤mfun-is-preorder (X ×-cmlat Y) (X ×-cmlat Y)
  assoc cat-mendo {X} {Y} {Z} {W} {a} {b} {c} = 
    let XYZ = rel2mendo∘⋈∘mendo2rel≈mendo-comp X Y Z a b
        YZW = rel2mendo∘⋈∘mendo2rel≈mendo-comp Y Z W b c
        XZW = (\ p → rel2mendo∘⋈∘mendo2rel≈mendo-comp X Z W p c)
        XYW = (\ p → rel2mendo∘⋈∘mendo2rel≈mendo-comp X Y W a p)
        _XWtrans_ = complete-meet-semilattice.property.rel-is-transitive (X ×-cmlat W)
    in \where
    .forward (x , w) → forward (XZW {!!} (x , w)) XWtrans (({!!} , {!!}) XWtrans forward (XYW {!!} (x , w)))
    .backward (x , w) → {!!}

  lunit cat-mendo {X} {Y} {a} =
    let F = rel2mendo∘⋈∘mendo2rel≈mendo-comp X X Y (mono id id) a in
    {!F _!}
  runit cat-mendo = {!!}

```
