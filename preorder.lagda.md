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

module preorder where

open import predicate
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

fun : Set → Set → Set
fun X Y = X → Y

record monotone-func (D E : preordered-set) : Set where
  constructor mono
  open preordered-set D renaming (carrier to |D| ; property to ≤D-pre)
  open preordered-set E renaming (carrier to |E| ; property to ≤E-pre)
  field
    func : fun |D| |E|
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

is-order-isomorphism : {C D : preordered-set} (L : monotone-func D C) (R : monotone-func C D) → Set
is-order-isomorphism {C} {D} L R = (func L ∘ func R ⟨ pointwise (equiv C) ⟩ id) × (func R ∘ func L ⟨ pointwise (equiv D) ⟩ id)
  where open monotone-func
        open preordered-set

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

```
