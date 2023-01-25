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
open import function-pair

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

  module _ (X Y : complete-meet-semilattice)
    (let X-pre = cmlat→pre X)
    (let Y-pre = cmlat→pre Y)
    (let (cmlat X-carrier _≤X_ ⋀X X-prop) = X)
    (let (cmlat Y-carrier _≤Y_ ⋀Y Y-prop) = Y)
    (let X×Y = X ×-cmlat Y)
    (let (cmlat XY _≤XY_ ⋀XY XY-prop) = X×Y)
    (let XY-pre = cmlat→pre (X ×-cmlat Y))
    (let _≈XY_ = iso-pair _≤XY_)
    (let _≈X_ = iso-pair _≤X_)
    (let _≈Y_ = iso-pair _≤Y_)
    where

    _∩pair_ : func-pair X-carrier Y-carrier → func-pair X-carrier Y-carrier → func-pair X-carrier Y-carrier
    f ∩pair g = rel2pair X Y (pair2rel X Y f ∩ pair2rel X Y g)

    _∪pair_ : func-pair X-carrier Y-carrier → func-pair X-carrier Y-carrier → func-pair X-carrier Y-carrier
    f ∪pair g = rel2pair X Y (pair2rel X Y f ∪ pair2rel X Y g)

    _∩mpair_ : monotone-func-pair X-pre Y-pre → monotone-func-pair X-pre Y-pre → monotone-func-pair X-pre Y-pre
    (mfp' f f-mono) ∩mpair (mfp' g g-mono) = mfp' (f ∪pair g) P
      where
      ⋀-mono = complete-meet-semilattice.property.bigmeet-monotone
      ≤-trans = complete-meet-semilattice.property.rel-is-transitive
      P : is-monotone-pair (cmlat→pre X) (cmlat→pre Y) (f ∪pair g)
      P .fst {x} {x'} x≤x' = ⋀-mono Y \where
        (x'' , x'≤x'' , left l) → x'' , ≤-trans X x≤x' x'≤x'' , left l
        (x'' , x'≤x'' , right r) → x'' ,  ≤-trans X x≤x' x'≤x'' , right r
      P .snd {y} {y'} y≤y' = ⋀-mono X \where
        (y'' , y'≤y'' , left l) → y'' ,  ≤-trans Y y≤y' y'≤y'' , left l
        (y'' , y'≤y'' , right r) → y'' ,  ≤-trans Y y≤y' y'≤y'' , right r

  module _ (X Y Z : complete-meet-semilattice)
    (let X-pre = cmlat→pre X)
    (let Y-pre = cmlat→pre Y)
    (let Z-pre = cmlat→pre Z)
    (let (cmlat X-carrier _≤X_ ⋀X X-prop) = X)
    (let (cmlat Y-carrier _≤Y_ ⋀Y Y-prop) = Y)
    (let (cmlat Z-carrier _≤Z_ ⋀Z Z-prop) = Z)
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
    (let _≈X_ = iso-pair _≤X_)
    (let _≈Y_ = iso-pair _≤Y_)
    (let _≈Z_ = iso-pair _≤Z_)

    where

    module latprop (C : complete-meet-semilattice) where
      open complete-meet-semilattice.property C public

    module preprop (P : preordered-set) where
      open preordered-set.property P public


    mendo-comp : monotone-func XY-pre XY-pre → monotone-func YZ-pre YZ-pre → monotone-func XZ-pre XZ-pre
    func (mendo-comp f g) (x , z) = ⋀XZ \{ (x' , z') → (x , z) ≤XZ (x' , z') × ∃ \ y' → f .func (x' , y') ≤XY (x' , y') × g .func (y' , z') ≤YZ (y' , z')  }
    property (mendo-comp f g) {xz} {x'z'} (xz≤x'z') = latprop.bigmeet-monotone X×Z \{ {(x''z'')} ((x'z'≤x''z'') , Ey') → XZ-trans xz≤x'z' x'z'≤x''z'' , Ey'}
      where XZ-trans = preprop.rel-is-transitive XZ-pre
            XY-trans = preprop.rel-is-transitive XY-pre
            YZ-trans = preprop.rel-is-transitive YZ-pre

    rel2mendo∘⋈∘mendo2rel≈mendo-comp : (f : monotone-func XY-pre XY-pre) → (g : monotone-func YZ-pre YZ-pre)
      → ∀ xz → func (rel2mendo X×Z ((mendo2rel X×Y f) ⋈ (mendo2rel Y×Z g))) xz ≈XZ func (mendo-comp f g) xz
    forward (rel2mendo∘⋈∘mendo2rel≈mendo-comp f g (x , z)) = latprop.bigmeet-monotone X×Z id
    backward (rel2mendo∘⋈∘mendo2rel≈mendo-comp f g (x , z)) = latprop.bigmeet-monotone X×Z id

    _⋈pair_ : func-pair X-carrier Y-carrier → func-pair Y-carrier Z-carrier → func-pair X-carrier Z-carrier
    f ⋈pair g = rel2pair X Z (pair2rel X Y f ⋈ pair2rel Y Z g)

    _⋈pair'_ : func-pair X-carrier Y-carrier → func-pair Y-carrier Z-carrier → func-pair X-carrier Z-carrier
    (f , b) ⋈pair' (f' , b') = \where
      .fst x → ⋀Z \{ z → ∃ \ x' → x ≤X x' × ∃ \ y → (f x' ≤Y y × b y ≤X x') × (f' y ≤Z z × b' z ≤Y y) }
      .snd z → ⋀X \{ x → ∃ \ z' → z ≤Z z' × ∃ \ y → (f x ≤Y y × b y ≤X x) × (f' y ≤Z z' × b' z' ≤Y y) }

    ⋈pair≈⋈pair' : (f : func-pair X-carrier Y-carrier) → (g : func-pair Y-carrier Z-carrier)
      → (∀ x → fst (f ⋈pair' g) x ≈Z fst (f ⋈pair g) x)
      → (∀ z → snd (f ⋈pair' g) z ≈X snd (f ⋈pair g) z)
    forward (⋈pair≈⋈pair' f g x z) = latprop.bigmeet-monotone X id
    backward (⋈pair≈⋈pair' f g x z) = latprop.bigmeet-monotone X id

    _⋈fun_ : fun X-carrier Y-carrier → fun Y-carrier Z-carrier → fun X-carrier Z-carrier
    f ⋈fun g = rel2fun X Z (fun2rel X Y f ⋈ fun2rel Y Z g)

    _⋈fun'_ : fun X-carrier Y-carrier → fun Y-carrier Z-carrier → fun X-carrier Z-carrier
    (f ⋈fun' g) x = ⋀Z (\z → ∃ \ x' → x ≤X x' × ∃ \y → (f x' ≤Y y) × (g y ≤Z z))

    ⋈fun≈⋈fun' : (f : fun X-carrier Y-carrier) → (g : fun Y-carrier Z-carrier) → ∀ x → (f ⋈fun g) x ≈Z (f ⋈fun' g) x
    forward (⋈fun≈⋈fun' f g x) = latprop.bigmeet-monotone Z \where
      (x' , x≤x' , y , fx'≤y , gy≤z) → x' , x≤x' , y , (fx'≤y , (latprop.bigmeet-lowerbound X _ _ _)) , gy≤z , (latprop.bigmeet-lowerbound Y _ _ _)
    backward (⋈fun≈⋈fun' f g x) = latprop.bigmeet-monotone Z \where
       (x' , x≤x' , y , (fx'≤y , _) , (gy≤z , _)) → x' , x≤x' , y , fx'≤y , gy≤z

    module _ (mf : monotone-func X-pre Y-pre) (mg : monotone-func Y-pre Z-pre)
      (let (mono f f-mono) = mf) (let (mono g g-mono) = mg)
      (let _∙_ = preprop.rel-is-transitive Z-pre)
      (let refl = preprop.rel-is-reflexive)
      where
      ∘-⋀ : ∀ x → ⋀Z (\ z → g (f x) ≤Z z) ≈Z g (f x)
      forward (∘-⋀ x) = latprop.bigmeet-lowerbound Z _ _ (refl Z-pre _)
      backward (∘-⋀ x) = latprop.bigmeet-greatest Z _ _ \where
        z z∈gfx → z∈gfx

      ⋈fun'≈∘ : ∀ x → (f ⋈fun' g) x ≈Z g (f x)
      forward (⋈fun'≈∘ x) =  latprop.bigmeet-lowerbound Z _ _
        (x , preprop.rel-is-reflexive X-pre _ , f x , refl Y-pre _ , refl Z-pre _)
      backward (⋈fun'≈∘ x) = latprop.bigmeet-greatest Z _ _ \where
        z (x' , x≤x' , y , fx≤y , gy≤z) → g-mono (f-mono x≤x') ∙ (g-mono fx≤y ∙ gy≤z)

      ⋈fun≈∘ : ∀ x → (f ⋈fun g) x ≈Z (g ∘ f) x
      forward (⋈fun≈∘ x) = forward (⋈fun≈⋈fun' f g x) ∙ forward (⋈fun'≈∘ x)
      backward (⋈fun≈∘ x) = backward (⋈fun'≈∘ x) ∙ backward (⋈fun≈⋈fun' f g x)

  module _
    (pre-hom : (X Y : complete-meet-semilattice) → preordered-set)
    (gal : (X Y : complete-meet-semilattice) → antitone-galois-connection (pre-subset (X ×-cmlat Y)) (pre-hom X Y))
    (let L∘R = \(X Y : complete-meet-semilattice) → galois-connection.comonad-functor (gal X Y))
    where

    module _
      (X Y Z : complete-meet-semilattice)
      (let X-pre = cmlat→pre X)
      (let Y-pre = cmlat→pre Y)
      (let Z-pre = cmlat→pre Z)
      (let (cmlat X-carrier _≤X_ ⋀X X-prop) = X)
      (let (cmlat Y-carrier _≤Y_ ⋀Y Y-prop) = Y)
      (let (cmlat Z-carrier _≤Z_ ⋀Z Z-prop) = Z)
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
      (let _≈X_ = iso-pair _≤X_)
      (let _≈Y_ = iso-pair _≤Y_)
      (let _≈Z_ = iso-pair _≤Z_)
      where

      -- some references: https://ncatlab.org/nlab/show/adjoint+monad
      --  General adjoint algebras and coalgebras in End(A)
      -- https://ncatlab.org/nlab/show/lax+monoidal+category
      -- this must be obtained by galois connectionh
      -- lax monoidal functor does not mean functor on lax monoidal category
      -- multi functor lax monoidal category
      -- unbiased oplax monoidal category
      -- We have unbiased version
      functor-on-unbiased-oplax-monoidal-categories = ∀ r r' → monotone-func.func (L∘R X Z) (r ⋈ r') ⊆ monotone-func.func (L∘R X Y) r ⋈ monotone-func.func (L∘R Y Z) r'
      {-
      proof-⋈-unbiased-oplax-monoidal-category-preserving : ⋈-unbiased-oplax-monoidal-category-preserving
      proof-⋈-unbiased-oplax-monoidal-category-preserving r r' {x , z} join-first = ⋀Y (\y → r (x , y) × r' (y , z)) , \where
        .fst → {!!}
        .snd → {!!}
      -}

      functor-on-unbiased-normal-monoidal-categories = ∀ r r' → monotone-func.func (L∘R X Y) r ⋈ monotone-func.func (L∘R Y Z) r' ≅ monotone-func.func (L∘R X Z) (r ⋈ r')


      -- we still have other operations on relations, intersection and union.
      -- ⊗(⊗(x , y) , z) ≤ ⊗(x , y , z)
      -- ⊗(x , ⊗(y , z)) ≤ ⊗(x , y , z)
      -- ((x ⋈ y) ⋈ z) ∩ (x ⋈ (y ⋈ z)) ??


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

{-
  cat-mendo : preorder-enriched-cat
  Ob cat-mendo = complete-meet-semilattice
  Hom cat-mendo D E = preordered-set.carrier (pre-mendo (D ×-cmlat E))
  I cat-mendo = mono id id
  _⊗_ cat-mendo {X} {Y} {Z} f g = mendo-comp X Y Z f g
  _≤_ cat-mendo {X} {Y} f g = _≤mfun_ (X ×-cmlat Y) (X ×-cmlat Y) f g
  Hom-is-preorder cat-mendo {X} {Y} = ≤mfun-is-preorder (X ×-cmlat Y) (X ×-cmlat Y)
  cat-mendo .assoc = {!!}
  cat-mendo .lunit = {!!}
  cat-mendo .runit = {!!}
-}
```
