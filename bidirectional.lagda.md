
Lattices, preorder, relation, subset, and monotone functions
------------------------------------------------------------

```agda
{-# OPTIONS --type-in-type #-}

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

comprehension-syntax : ∀ {X} → pred X → subset X
comprehension-syntax = \ { x → x }

sigma-syntax :  (X : Set) → (X → Set) → Set
sigma-syntax  = Σ

syntax comprehension-syntax (\ x → P) = ｛ x ∣ P ｝

{-# DISPLAY comprehension-syntax P = P #-}
{-# DISPLAY Σ-syntax D E = Σ D E #-}

｛_,_｝₂ : ∀ {X} → X → X → pred X
｛ x , x' ｝₂ = ｛ x ｝ ∪ ｛ x' ｝

rel : Set → Set → prop
rel X Y = REL X Y (level-of X ⊔ level-of Y)

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

module _ {X : Set} where

  is-reflexive : pred (rel X X)
  is-reflexive _~_ = ∀ x → x ~ x

  is-transitive : pred (rel X X)
  is-transitive _~_ = ∀ {x y z} → x ~ y → y ~ z → x ~ z

  is-symmetric : pred (rel X X)
  is-symmetric _~_ = ∀ {x y} → x ~ y → y ~ x

  is-antisymmetric : rel (rel X X) (rel X X)
  is-antisymmetric _≈_ _≤_ = ∀ {x y} → x ≤ y → y ≤ x → x ≈ y

  -- I use preorder instead of partial order and use equivalence a ≈ b := a ≤ b and b
  record is-preorder (_≤_ : rel X X) : Set where
    field
      rel-is-reflexive : is-reflexive _≤_
      rel-is-transitive : is-transitive _≤_

    identity-to-rel : ∀ {x y} → x ≡ y → x ≤ y
    identity-to-rel ≡.refl = rel-is-reflexive _

    ↑ : X → subset X
    ↑ x = x ≤_

    ↓ : X → subset X
    ↓ x = _≤ x

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
        _↔_ : rel prop prop
        _↔_ = iso-pair (\X Y → X → Y)

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


      is-welldefined-subset : pred (subset X)
      is-welldefined-subset R = ∀ {x y} → x ≈ y → R x ↔ R y

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

  record is-complete-meet-semilattice (_≤_ : rel X X) (⋀ : subsetop X) : prop where
    field
      rel-is-preorder : is-preorder _≤_
      op-is-bigmeet : ∀ S → is-infimum _≤_ S (⋀ S)

    private
      _≈_ = iso-pair _≤_
      _↔_ = iso-pair (\ X Y → X → Y)
    open is-preorder rel-is-preorder public
    module _ (S : subset X) where
      open is-greatest (op-is-bigmeet S) renaming (element to bigmeet-lowerbound; property to bigmeet-greatest) public

    bigmeet-up-iso : ∀ x → x ≈ ⋀ (↑ x)
    forward (bigmeet-up-iso x) = bigmeet-greatest (↑ x) x \_ → id
    backward (bigmeet-up-iso x) = bigmeet-lowerbound (↑ x) x (rel-is-reflexive x)

    bigmeet-up-intersection-iso : ∀ x S → S x → x ≈ ⋀ (↑ x ∩ S)
    forward (bigmeet-up-intersection-iso x S x∈S) = bigmeet-greatest (↑ x ∩ S) x \ _ → fst
    backward (bigmeet-up-intersection-iso x S x∈S) = bigmeet-lowerbound (↑ x ∩ S) x  (rel-is-reflexive x , x∈S)

    subset-largermeet : ∀ {S S'} → S ⊆ S' → ⋀ S' ≤ ⋀ S
    subset-largermeet {S} {S'} S⊆S' =
      let ⋀S-glb = bigmeet-greatest S
          ⋀S'-lb = bigmeet-lowerbound S'
      in
      begin-≤
      ⋀ S' ≤⟨ ⋀S-glb (⋀ S') (\ x x∈S → ⋀S'-lb x (S⊆S' x∈S)) ⟩
      ⋀ S ∎
      where open reasoning _ rel-is-preorder

    bigmeet-bounded : ∀ (S : subset X) x → x ∈ S → ⋀ S ≤ x → Σ _ (↓ x ∩ S)
    bigmeet-bounded S x x∈S ⋀S≤x = x , rel-is-reflexive x , x∈S


  is-op-closed-subset : (_≤_ : rel X X) (⋀ : subsetop X) (S : subset X) → prop
  is-op-closed-subset _≤_ ⋀ S = ∀ S' → S' ⊆ S → ⋀ S' ∈ S

  is-meet-closed-subset :  {_≤_ : rel X X} {⋀ : subsetop X} → is-complete-meet-semilattice _≤_ ⋀ → pred (subset X)
  is-meet-closed-subset {_≤_} {⋀} cmlat = is-op-closed-subset _≤_ ⋀

  module _ {_≤_ : rel X X} {⋀ : subsetop X}
    {superset-is-cmlat : is-complete-meet-semilattice _≤_ ⋀}
    {S : subset X} (S-meet-closed : is-meet-closed-subset superset-is-cmlat S) where
    open is-complete-meet-semilattice superset-is-cmlat
    ↑restriction : ∀ x → is-op-closed-subset _≤_ ⋀ (↑ x ∩ S)
    fst (↑restriction x S' S'⊆↑x∩S) = bigmeet-greatest _ _ \ _ → fst ∘ S'⊆↑x∩S
    snd (↑restriction x S' S'⊆↑x∩S) = S-meet-closed S' (snd ∘ S'⊆↑x∩S)


record rel-set : Set where
  constructor rset
  field
    carrier : Set
    relation : rel carrier carrier

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

module _ {D E : Set} (_≤D_ : rel D D) (_≤E_ : rel E E) where
  private
    _≈D_ = iso-pair _≤D_
    _≈E_ = iso-pair _≤E_

  is-welldefined : pred (D → E)
  is-welldefined f = ∀ {d d'} → d ≈D d' → f d ≈E f d'

  is-monotone : pred (D → E)
  is-monotone f = ∀ {d d'} → d ≤D d' → f d ≤E f d'

module _ {D E : Set} {_≤D_ : rel D D} {_≤E_ : rel E E} where
  open iso-pair
  monotone2welldefined : {f : D → E} → is-monotone _≤D_ _≤E_ f → is-welldefined  _≤D_ _≤E_ f
  forward (monotone2welldefined {f} f-is-monotone d≈d') = f-is-monotone (forward d≈d')
  backward (monotone2welldefined {f} f-is-monotone d≈d') = f-is-monotone (backward d≈d')

record monotone-func (D E : rel-set) : Set where
  constructor mono
  open rel-set D renaming (carrier to |D| ; relation to _≤D_)
  open rel-set E renaming (carrier to |E| ; relation to _≤E_)
  field
    func : |D| → |E|
    func-is-monotone : is-monotone _≤D_ _≤E_ func

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
cmlat→pre (cmlat X _≤_ _ X-cmlat) = pre X _≤_ (X.rel-is-preorder)
  where
    module X = is-complete-meet-semilattice X-cmlat

pre→rset : preordered-set → rel-set
pre→rset (pre X _≤_ _) = rset X _≤_


cm2j : ∀ {X} → rel X X → subsetop X → binop X
cm2j _≤_ ⋀ x x' = ⋀ ((\ u → x ≤ u) ∩ (\ u → x' ≤ u))

cm2cj : ∀ {X} → rel X X → subsetop X → subsetop X
cm2cj _≤_ ⋀ S = ⋀ (is-upperbound _≤_ S)

{-
is-complete-meet-semilattice X _≤_ ⋀ props → is-join-semilattice X _≤_ (\ x
-}


-- complete meet semilattice is complete join semilattice
cmlat→cjlat : complete-meet-semilattice → complete-join-semilattice
cmlat→cjlat (cmlat X _≤_ ⋀ X-prop) =
  cjlat X _≤_
    (cm2cj _≤_ ⋀)
    X-cjlat
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
  pre (D × E)
      (\ de de' → (fst de) ≤D (fst de') × (snd de) ≤E (snd de'))
      ≤D×E-po
  where
    module ≤D = is-preorder ≤D-pre
    module ≤E = is-preorder ≤E-pre
    open is-preorder
    ≤D×E-po : is-preorder _
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

func-pair : Set → Set → Set
func-pair D E = (D → E) × (E → D)

module _ {D E : Set} where
  record is-monotone-pair (_≤D_ : rel D D) (_≤E_ : rel E E) (fb : func-pair D E) : prop where
    field
      foward-is-monotone : is-monotone _≤D_ _≤E_ (fst fb)
      backward-is-monotone : is-monotone _≤E_ _≤D_ (snd fb)

module _ where
  open is-preorder
  ⊆-is-preorder : ∀ {X : Set} → is-preorder {X = subset X} _⊆_
  rel-is-reflexive ⊆-is-preorder S x∈S = x∈S
  rel-is-transitive ⊆-is-preorder S⊆S' S'⊆S'' x∈S = S'⊆S'' (S⊆S' x∈S)

  ⊆₂-is-preorder : ∀ {X Y : Set} → is-preorder {X = rel X Y} _⊆₂_
  rel-is-reflexive ⊆₂-is-preorder S x∈S = x∈S
  rel-is-transitive ⊆₂-is-preorder S⊆S' S'⊆S'' x∈S = S'⊆S'' (S⊆S' x∈S)

module _
  {D : _} {_≤D_ : _} {⋀D : _} (D-is-cmlat : _)
  {E : _} {_≤E_ : _} {⋀E : _} (E-is-cmlat : _) where


  private
    D-cmlat = cmlat D _≤D_ ⋀D D-is-cmlat
    E-cmlat = cmlat E _≤E_ ⋀E E-is-cmlat
    D-pre = cmlat→pre D-cmlat
    E-pre = cmlat→pre E-cmlat
    D-rset = pre→rset D-pre
    E-rset = pre→rset E-pre
    module D = is-complete-meet-semilattice D-is-cmlat renaming (rel-is-preorder to ≤-pre ; rel-is-reflexive to ≤-refl ; rel-is-transitive to ≤-trans)
    module E = is-complete-meet-semilattice E-is-cmlat renaming (rel-is-preorder to ≤-pre ; rel-is-reflexive to ≤-refl ; rel-is-transitive to ≤-trans)
    D×E-cmlat = D-cmlat ×-cmlat E-cmlat
  private
    infix 1 _↔_
    _↔_ = iso-pair (\A B → A → B)

    _≈D_ = iso-pair _≤D_
    _≈E_ = iso-pair _≤E_

  open complete-meet-semilattice D×E-cmlat renaming (operation to ⋀ ; relation to _≤_)
  open is-complete-meet-semilattice (complete-meet-semilattice.property D×E-cmlat) renaming (rel-is-preorder to ≤-pre ; rel-is-reflexive to ≤-refl ; rel-is-transitive to ≤-trans)


  fst-≤ : {p p' : D × E} → p ≤ p' → fst p ≤D fst p'
  fst-≤ x = fst x

  snd-≤ : {p p' : D × E} → p ≤ p' → snd p ≤E snd p'
  snd-≤ x = snd x

  -- d₀≤d → fd≤e → fd₀≤e
  mono-≤ : {f : D → E} (f-mono : is-monotone _≤D_ _≤E_ f) → ∀ {d e d₀} → d₀ ≤D d → f d ≤E e → f d₀ ≤E e
  mono-≤ {f} f-mono {d} {e} {d₀} d≤d₀ fd≤e =
    begin-≤
    f d₀ ≤⟨ f-mono d≤d₀ ⟩
    f d ≤⟨ fd≤e ⟩
    e ∎
    where
      open reasoning _  E.≤-pre

  -- f (⋀S) ≤ ⋀ (f S)
  mono-meet≤meet-mono : {f : D → E} (f-mono : is-monotone _≤D_ _≤E_ f) → (S : subset D) → f (⋀D S) ≤E ⋀E (fimage f S)
  mono-meet≤meet-mono {f} f-mono S =
    begin-≤
    f (⋀D S) ≤⟨ E.bigmeet-greatest _ _ (\ {e (d , d∈S , fd≡e) →  ≡.subst (f (⋀D S) ≤E_) fd≡e (f-mono (D.bigmeet-lowerbound S d d∈S)) }) ⟩
    ⋀E (fimage f S) ∎
    where
      open reasoning _  E.≤-pre

  bigmeet-≡-≤ : {f : D → E} (f-mono : is-monotone _≤D_ _≤E_ f)
    (d₀ : D) → ⋀E ｛ e ∣ Σ[ d ∈ D ] (d₀ ≤D d × f d ≡ e) ｝ ≤E ⋀E ｛ e ∣ Σ[ d ∈ D ] (d₀ ≤D d × f d ≤E e) ｝
  bigmeet-≡-≤ f-mono d₀ = E.bigmeet-greatest _ _ (\ {e (d , d₀≤d , fd≤e) →  E.bigmeet-lowerbound _ _ (d , (d₀≤d , ≡.refl)) ⟨ E.≤-trans ⟩ fd≤e})

  bigmeet-≡-≤' : {f : D → E} (f-mono : is-monotone _≤D_ _≤E_ f)
    (S' : subset (D × E)) → ⋀E ｛ e ∣ Σ[ d ∈ D ] ((Σ[ e' ∈ E ] ((d , e') ∈ S')) × f d ≡ e) ｝ ≤E ⋀E ｛ e ∣ Σ[ d ∈ D ] ((Σ[ e' ∈ E ] (d , e') ∈ S') × f d ≤E e) ｝
  bigmeet-≡-≤' f-mono S' = E.bigmeet-greatest _ _ (\ {e (d , p , fd≤e) →  E.bigmeet-lowerbound _ _ (d , (p , ≡.refl)) ⟨ E.≤-trans ⟩ fd≤e})

  module _ (f : D → E) (b : E → D) where

    -- f d ≤ e × b e ≤ d ↔ b (f d) ≤ d
    mono-pair-backforward : (b-mono : is-monotone _≤E_ _≤D_ b) → ∀ d → (Σ[ e ∈ E ] (f d ≤E e) × (b e ≤D d)) ↔ (b (f d) ≤D d)
    forward (mono-pair-backforward b-mono d) (e , fd≤e , be≤d) =
      begin-≤
      b (f d) ≤⟨ b-mono fd≤e ⟩
      b e ≤⟨ be≤d ⟩
      d ∎
      where
        open reasoning _ D.≤-pre
    backward (mono-pair-backforward _ d) bfd≤d = f d , E.≤-refl (f d) , bfd≤d


    -- f d ≤ e × b e ≤ d ↔ f (b e) ≤ e
    mono-pair-forwardback : (f-mono : is-monotone _≤D_ _≤E_ f) → ∀ e → (Σ[ d ∈ D ] (f d ≤E e) × (b e ≤D d)) ↔ (f (b e) ≤E e)
    forward (mono-pair-forwardback f-mono e) (d , fd≤e , be≤d) =
      begin-≤
      f (b e) ≤⟨ f-mono be≤d ⟩
      f d ≤⟨ fd≤e ⟩
      e ∎
      where
        open reasoning _ E.≤-pre
    backward (mono-pair-forwardback _ e) fbe≤e = b e , fbe≤e , D.≤-refl (b e)



```

2 poset
-------

  https://ncatlab.org/nlab/show/2-poset

  LatRel
    objects: complete lattices, D , E , F , ...
    morphisms: relations between objects, R , R' , R'' , ...
    compositions: relation composition, R;R'
    2-morphisms: inclusion R ⊆ R'

  LatMFP
    objects: complete lattices, D , E , F , ...
    morphisms: pairs of forward and backward monotone functions, (f , b) , (f' , b') , ...
    compositions: composition of forward and backward monotone functions, (f , b) ∘ (f' , b') = (f ∘ f' , b' ∘ b)
    2-morphisms: pointwise ordering, (f , b) ≤ (f' , b') := (∀ d, f d ≤ f' d) ∧ (∀ e , b e ≤ b' e)

  There is an adjunction

              R ⊆ f2r fb
  r2f ⊣ f2r   ==========
              r2f R ≥ fb


  Monoidal product?

  (D , E , R) ⊗ (E , F , R') → (D , F , R ; R')

  (D , E , fb) ⊗ (E , F , fb') → (D , F  fb ∘ fb')

              r2f
             <----
      LatMFP   ⊥   LatRel
        |    ---->     |
        |     f2r      |
        |              |
      LatMFP ==== LatMeetClosed
       Fix         Butterfly

```agda

module _
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

  -- Left adjoin
  r2f : rel D E → func-pair D E
  fst (r2f _R_) d₀ = ⋀E ｛ e ∣ Σ[ d ∈ D ] (d₀ ≤D d × d R e) ｝
  snd (r2f _R_) e₀ = ⋀D ｛ d ∣ Σ[ e ∈ E ] (e₀ ≤E e × d R e) ｝

  -- Right adjoint
  f2r : func-pair D E → rel D E
  f2r (f , b) d e = f d ≤E e × b e ≤D d

  _≤fp_ : rel (func-pair D E) (func-pair D E)
  (f , b) ≤fp (f' , b') = (∀ d → f d ≤E f' d) × (∀ e → b e ≤D b' e)

  private
    infix 1 _↔_
    _↔_ = iso-pair (\A B → A → B)
    _≈D_ = iso-pair _≤D_
    _≈E_ = iso-pair _≤E_
    _≈_ = iso-pair _≤_

  _≈₂_ : ∀ {X Y} → rel (rel X Y) (rel X Y)
  _≈₂_ = iso-pair _⊆₂_

  _≈fp_ = iso-pair _≤fp_

  module _ {f : D → E} {b : E → D}
    (f-is-mono : is-monotone _≤D_ _≤E_ f) (b-is-mono : is-monotone _≤E_ _≤D_ b) where
    f2r-mono-join-closed : is-meet-closed-subset D×E-is-cmlat (rel2subset (f2r (f , b)))
    fst (f2r-mono-join-closed S' S'⊆) =
      begin-≤
      f (fst (⋀ S')) ≡⟨⟩
      f (⋀D ｛ d ∣ Σ[ e ∈ E ] ((d , e) ∈ S')｝) ≤⟨ mono-meet≤meet-mono D-is-cmlat E-is-cmlat f-is-mono ｛ d ∣ Σ[ e ∈ E ] ((d , e) ∈ S')｝ ⟩
      ⋀E (fimage f ｛ d ∣ Σ[ e ∈ E ] ((d , e) ∈ S')｝) ≡⟨⟩
      ⋀E ｛ e ∣ Σ[ d ∈ D ] ((Σ[ e' ∈ E ](S' (d , e'))) × f d ≡ e)｝ ≤⟨ bigmeet-≡-≤' D-is-cmlat E-is-cmlat f-is-mono S' ⟩
      ⋀E ｛ e ∣ Σ[ d ∈ D ] ((Σ[ e' ∈ E ](S' (d , e'))) × f d ≤E e)｝ ≤⟨ E.subset-largermeet (\ { {e} (d , de∈S') → d , ((e , de∈S') , fst (S'⊆ de∈S')) }) ⟩
      ⋀E ｛ e ∣ Σ[ d ∈ D ] ((d , e) ∈ S')｝ ≡⟨⟩
      snd (⋀ S') ∎
      where open ≤E-reasoning
    snd (f2r-mono-join-closed S' S'⊆) =
      begin-≤
      b (snd (⋀ S')) ≡⟨⟩
      b (⋀E ｛ e ∣ Σ[ d ∈ D ] ((d , e) ∈ S')｝) ≤⟨ mono-meet≤meet-mono E-is-cmlat D-is-cmlat b-is-mono ｛ e ∣ Σ[ d ∈ D ] ((d , e) ∈ S')｝ ⟩
      ⋀D (fimage b ｛ e ∣ Σ[ d ∈ D ] ((d , e) ∈ S')｝) ≡⟨⟩
      ⋀D ｛ d ∣ Σ[ e ∈ E ] ((Σ[ d' ∈ D ](S' (d' , e))) × b e ≡ d)｝ ≤⟨ bigmeet-≡-≤' E-is-cmlat D-is-cmlat b-is-mono (S' ∘ Data.Product.swap) ⟩
      ⋀D ｛ d ∣ Σ[ e ∈ E ] ((Σ[ d' ∈ D ](S' (d' , e))) × b e ≤D d)｝ ≤⟨ D.subset-largermeet (\ { {d} (e , de∈S') → e , ((d , de∈S') , snd (S'⊆ de∈S')) }) ⟩
      ⋀D ｛ d ∣ Σ[ e ∈ E ] ((d , e) ∈ S')｝ ≡⟨⟩
      fst (⋀ S') ∎
      where open ≤D-reasoning

  module _ (R : rel D E) where
    r2f-monotone : let (f , b) = r2f R in is-monotone _≤D_ _≤E_ f × is-monotone _≤E_ _≤D_ b
    fst r2f-monotone {d} {d'} d≤d' =
      begin-≤
      fst (r2f R) d ≤⟨ E.subset-largermeet (\ { {e} (d'' , d'≤d'' , Rd''e) → d'' , (d≤d' ⟨ D.≤-trans ⟩ d'≤d'') , Rd''e }) ⟩
      fst (r2f R) d' ∎
      where open ≤E-reasoning
    snd r2f-monotone {e} {e'} e≤e' =
      begin-≤
      snd (r2f R) e ≤⟨ D.subset-largermeet (\ { {d} (e'' , e'≤e'' , Rde'') → e'' , (e≤e' ⟨ E.≤-trans ⟩ e'≤e'') , Rde'' }) ⟩
      snd (r2f R) e' ∎
      where open ≤D-reasoning

  module _ where
    open is-preorder
    ≤fp-is-preorder : is-preorder _≤fp_
    fst (rel-is-reflexive ≤fp-is-preorder (f , b)) d = E.≤-refl (f d)
    snd (rel-is-reflexive ≤fp-is-preorder (f , b)) e = D.≤-refl (b e)
    fst (rel-is-transitive ≤fp-is-preorder fb≤fb' fb'≤fb'') d = E.≤-trans (fst fb≤fb' d) (fst fb'≤fb'' d)
    snd (rel-is-transitive ≤fp-is-preorder fb≤fb' fb'≤fb'') e = D.≤-trans (snd fb≤fb' e) (snd fb'≤fb'' e)

  module galois-connection
    (R : rel D E)
    {f : D → E} {b : E → D}
    (f-is-mono : is-monotone _≤D_ _≤E_ f) (b-is-mono : is-monotone _≤E_ _≤D_ b) where


    f-is-wd : is-welldefined _≤D_ _≤E_ f
    f-is-wd = monotone2welldefined f-is-mono
    b-is-wd : is-welldefined _≤E_ _≤D_ b
    b-is-wd = monotone2welldefined b-is-mono

    left-transpose : R ⊆₂ f2r (f , b) → (f , b) ≤fp r2f R
    fst (left-transpose R⊆f2r[fb]) d₀ =
      begin-≤
      f d₀                                         ≈⟨ f-is-wd (D.bigmeet-up-iso d₀) ⟩
      f (⋀D (D.↑ d₀))                              ≤⟨ mono-meet≤meet-mono D-is-cmlat E-is-cmlat f-is-mono (D.↑ d₀) ⟩
      ⋀E (fimage f (D.↑ d₀))                       ≤⟨ E.subset-largermeet (λ { {e} (d , d₀≤d , fd=e ) → d , d₀≤d , fd=e}) ⟩
      ⋀E ｛ e ∣ Σ[ d ∈ D ] (d₀ ≤D d × f d ≡ e) ｝   ≤⟨ bigmeet-≡-≤ D-is-cmlat E-is-cmlat f-is-mono d₀ ⟩
      ⋀E ｛ e ∣ Σ[ d ∈ D ] (d₀ ≤D d × f d ≤E e) ｝  ≤⟨ E.subset-largermeet (\ { (d' , d₀≤d' , d'Re') → d' , d₀≤d' , fst (R⊆f2r[fb] d'Re')}) ⟩
      ⋀E ｛ e ∣ Σ[ d ∈ D ] (d₀ ≤D d × R d e) ｝     ≡⟨⟩
      fst (r2f R) d₀ ∎
        where open ≤E-reasoning
    snd (left-transpose R⊆f2r[fb]) e₀ =
      begin-≤
      b e₀                                         ≈⟨ b-is-wd (E.bigmeet-up-iso e₀) ⟩
      b (⋀E (E.↑ e₀))                              ≤⟨ mono-meet≤meet-mono E-is-cmlat D-is-cmlat b-is-mono (E.↑ e₀) ⟩
      ⋀D (fimage b (E.↑ e₀))                       ≤⟨ D.subset-largermeet (λ { {d} (e , e₀≤e , be=d ) → e , e₀≤e , be=d}) ⟩
      ⋀D ｛ d ∣ Σ[ e ∈ E ] (e₀ ≤E e × b e ≡ d) ｝   ≤⟨ bigmeet-≡-≤ E-is-cmlat D-is-cmlat b-is-mono e₀ ⟩
      ⋀D ｛ d ∣ Σ[ e ∈ E ] (e₀ ≤E e × b e ≤D d) ｝  ≤⟨ D.subset-largermeet (\ { (e' , e₀≤e' , d'Re') → e' , e₀≤e' , snd (R⊆f2r[fb] d'Re')}) ⟩
      ⋀D ｛ d ∣ Σ[ e ∈ E ] (e₀ ≤E e × R d e) ｝     ≡⟨⟩
      snd (r2f R) e₀ ∎
        where open ≤D-reasoning

    right-transpose : (f , b) ≤fp r2f R → R ⊆₂ f2r (f , b)
    fst (right-transpose (f≤ , b≤) {d} {e} dRe) =
      begin-≤
      f d ≤⟨ f≤ d ⟩
      fst (r2f R) d ≤⟨ E.bigmeet-lowerbound _ _ (d , D.≤-refl d , dRe) ⟩
      e ∎
        where open ≤E-reasoning
    snd (right-transpose (f≤ , b≤) {d} {e} dRe) =
      begin-≤
      b e ≤⟨ b≤ e ⟩
      snd (r2f R) e ≤⟨ D.bigmeet-lowerbound _ _ (e , E.≤-refl e , dRe) ⟩
      d ∎
        where open ≤D-reasoning

    galois-connection : R ⊆₂ f2r (f , b) ↔ (f , b) ≤fp r2f R
    forward galois-connection = left-transpose
    backward galois-connection = right-transpose

    unit : ((f , b) ≤fp r2f R) → (f , b) ≤fp r2f R
    unit = left-transpose ∘ right-transpose

    counit : R ⊆₂ f2r (f , b) → R ⊆₂ f2r (f , b)
    counit = right-transpose ∘ left-transpose

  module unit (R : rel D E) where


    f2r-r2f-increasing : R ⊆₂ f2r (r2f R)
    fst (f2r-r2f-increasing {d₀} {e₀} d₀Re₀) =
      begin-≤
      fst (r2f R) d₀                                     ≡⟨⟩
      ⋀E ｛ e ∣ Σ[ d ∈ D ] (d₀ ≤D d × R d e) ｝              ≤⟨ E.subset-largermeet (\ { (d , (d₀≤d , e₀≤e) , dRe) → d , d₀≤d , dRe }) ⟩
      snd (⋀ (↑ (d₀ , e₀) ∩ ｛ de ∣ R (fst de) (snd de) ｝)) ≤⟨ snd (backward (bigmeet-up-intersection-iso (d₀ , e₀) (\(d , e) → R d e) d₀Re₀)) ⟩
      e₀ ∎
      where open ≤E-reasoning
    snd (f2r-r2f-increasing {d₀} {e₀} d₀Re₀) =
      begin-≤
      snd (r2f R) e₀                                    ≡⟨⟩
      ⋀D ｛ d ∣ Σ[ e ∈ E ] (e₀ ≤E e × R d e) ｝              ≤⟨ D.subset-largermeet (\ { (e , (d₀≤d , e₀≤e) , dRe) → e , e₀≤e , dRe }) ⟩
      fst (⋀ (↑ (d₀ , e₀) ∩ ｛ de ∣ R (fst de) (snd de) ｝)) ≤⟨ fst (backward (bigmeet-up-intersection-iso (d₀ , e₀) (\(d , e) → R d e) d₀Re₀)) ⟩
      d₀ ∎
      where open ≤D-reasoning

    butterfly : rel D E → prop
    butterfly R = ∀ d₀ e₀ {d e d' e'}
      → d' ≤D d₀ → d₀ ≤D d
      → e' ≤E e₀ → e₀ ≤E e
      → R d' e → R d e' → R d₀ e₀

    f2r-r2f-butterfly : f2r (r2f R) ⊆₂ R → butterfly R
    f2r-r2f-butterfly r2rR⊆R d₀ e₀ {d} {e} {d'} {e'} d'≤d₀ d₀≤d e'≤e₀ e₀≤e d'Re dRe' =  r2rR⊆R (⋀E≤e₀ , ⋀D≤d₀)
      where
      ⋀E≤e₀ : fst (r2f R) d₀ ≤E e₀
      ⋀E≤e₀ =
        begin-≤
        fst (r2f R) d₀ ≡⟨⟩
        ⋀E ｛ e ∣ Σ[ d ∈ D ] (d₀ ≤D d × R d e) ｝ ≤⟨ E.bigmeet-lowerbound _ _ (d , d₀≤d , dRe') ⟩
        e' ≤⟨ e'≤e₀ ⟩
        e₀ ∎
        where open ≤E-reasoning
      ⋀D≤d₀ : snd (r2f R) e₀ ≤D d₀
      ⋀D≤d₀ =
        begin-≤
        snd (r2f R) e₀ ≡⟨⟩
        ⋀D ｛ d ∣ Σ[ e ∈ E ] (e₀ ≤E e × R d e) ｝ ≤⟨  D.bigmeet-lowerbound _ _ (e , e₀≤e , d'Re) ⟩
        d' ≤⟨ d'≤d₀ ⟩
        d₀ ∎
        where open ≤D-reasoning

    [R] = (\de → fst de ∈ fst-rel R × snd de ∈ snd-rel R)
    R⊆[R] : rel2subset R ⊆ [R]
    R⊆[R] {d , e} de∈R = (e , de∈R) , (d , de∈R)

    R' = f2r (r2f R)
    R'-meet-closed : is-meet-closed-subset D×E-is-cmlat (rel2subset (f2r (r2f R)))
    R'-meet-closed = f2r-mono-join-closed (fst (r2f-monotone R)) (snd (r2f-monotone R))

    module _ (R-meet-closed : is-meet-closed-subset D×E-is-cmlat (rel2subset R)) (R-welldefined : is-welldefined-subset _≤_ (rel2subset R)) where

      proj-bigmeet-≈ : ⋀ (rel2subset R) ≈ ⋀ [R]
      fst (forward proj-bigmeet-≈) = D.subset-largermeet \{ (_ , P , _) → P }
      snd (forward proj-bigmeet-≈) = E.subset-largermeet \{ (_ , _ , Q) → Q }
      fst (backward proj-bigmeet-≈) =
        begin-≤
        fst (⋀ (\ de → fst de ∈ fst-rel R × snd de ∈ snd-rel R)) ≤⟨ D.bigmeet-lowerbound _ _ ((snd (⋀ (rel2subset R))) , R⊆[R] (R-meet-closed _ id)) ⟩
        fst (⋀ (rel2subset R)) ∎
        where open ≤D-reasoning
      snd (backward proj-bigmeet-≈) =
        begin-≤
        snd (⋀ (\ de → fst de ∈ fst-rel R × snd de ∈ snd-rel R)) ≤⟨ E.bigmeet-lowerbound _ _ ((fst (⋀ (rel2subset R))) , R⊆[R] (R-meet-closed _ id)) ⟩
        snd (⋀ (rel2subset R)) ∎
        where open ≤E-reasoning

      -- These require choice?
      postulate fstR-meet-closed : is-meet-closed-subset D-is-cmlat (fst-rel R)
      postulate sndR-meet-closed : is-meet-closed-subset E-is-cmlat (snd-rel R)

      butterfly-f2r-r2f : butterfly R → f2r (r2f R) ⊆₂ R
      butterfly-f2r-r2f R-butterfly {d₀} {e₀} d₀R'e₀ = R-butterfly d₀ e₀ d'≤d₀ d₀≤d e'≤e₀ e₀≤e d'Re dRe'
        where
          P : rel D E
          P d e = d₀ ≤D d × e ≤E e₀ × R' d e
          Q : rel D E
          Q d e = e₀ ≤E e × d ≤D d₀ × R' d e
          de' : D × E
          de' = ⋀ (rel2subset P)
          d'e : D × E
          d'e = ⋀ (rel2subset Q)
          d'≤d₀ : fst d'e ≤D d₀
          d'≤d₀ =
            begin-≤
            fst d'e ≤⟨ D.bigmeet-lowerbound _ _ (e₀ , E.≤-refl e₀ , D.≤-refl d₀ , d₀R'e₀) ⟩
            d₀ ∎
            where open ≤D-reasoning
          d₀≤d : d₀ ≤D fst de'
          d₀≤d =
            begin-≤
            d₀ ≤⟨ D.bigmeet-greatest _ _ (\{ d (e , de∈) → fst de∈ }) ⟩
            fst de' ∎
            where open ≤D-reasoning
          e'≤e₀ : snd de' ≤E e₀
          e'≤e₀ =
            begin-≤
            snd de' ≤⟨ E.bigmeet-lowerbound _ _ (d₀ , D.≤-refl d₀ , E.≤-refl e₀ , d₀R'e₀) ⟩
            e₀ ∎
            where open ≤E-reasoning
          e₀≤e : e₀ ≤E snd d'e
          e₀≤e =
            begin-≤
            e₀ ≤⟨ E.bigmeet-greatest _ _ (\{ e (d , de∈) → fst de∈ }) ⟩
            snd d'e ∎
            where open ≤E-reasoning
          d'Re : d'e ∈ rel2subset R
          d'Re = {!!}
          dRe' : de' ∈ rel2subset R
          dRe' = {!!}

  module counit (f : D → E) (b : E → D)
    (f-mono : is-monotone _≤D_ _≤E_ f)
    (b-mono : is-monotone _≤E_ _≤D_ b) where


    open galois-connection
    r2f-f2r-increasing : (f , b) ≤fp r2f (f2r (f , b))
    r2f-f2r-increasing = left-transpose (f2r (f , b)) f-mono b-mono id

    a : D → D
    a d₀ = ⋀D ｛ d ∣ Σ _ (\ e → d₀ ≤D d × f d ≤E e × b e ≤D d) ｝

    p : E → E
    p e₀ = ⋀E ｛ e ∣ Σ _ (\ d → e₀ ≤E e × f d ≤E e × b e ≤D d) ｝

    id≤a : ∀ d₀ → d₀ ≤D a d₀
    id≤a d₀ = D.bigmeet-greatest _ _ (\ { d (e , d₀≤d , fd≤e , be≤d) → d₀≤d})

    bf≤a : ∀ d₀ →  b (f d₀) ≤D a d₀
    bf≤a d₀ =
      begin-≤
      b (f d₀) ≤⟨ D.bigmeet-greatest _ _ (\{ d (e , d₀≤d , fd≤e , be≤d) → b-mono (f-mono d₀≤d) ⟨ D.≤-trans ⟩ b-mono fd≤e ⟨ D.≤-trans ⟩ be≤d }) ⟩
      ⋀D (\ d → ∃ \ e → d₀ ≤D d × f d ≤E e × b e ≤D d) ≡⟨⟩
      a d₀ ∎
      where open ≤D-reasoning

    ap→r2f-f2r : (f ∘ a , b ∘ p) ≤fp (f , b) → r2f (f2r (f , b)) ≤fp (f , b)
    fst (ap→r2f-f2r (f'≤f , b'≤b)) d₀ =
      begin-≤ fst (r2f (f2r (f , b))) d₀ ≡⟨⟩
      ⋀E (\ e → ∃ \ d → d₀ ≤D d × f d ≤E e × b e ≤D d) ≤⟨ E.bigmeet-lowerbound _ _ (a d₀ , id≤a d₀ , f'≤f d₀ , bf≤a d₀) ⟩
      f d₀ ∎
      where open ≤E-reasoning
    snd (ap→r2f-f2r (f'≤f , b'≤b)) e = {!!}
      where open ≤D-reasoning


    f' : D → E
    f' d₀ = f (b (f d₀) ∨D d₀)
    b' : E → D
    b' e₀ = b (f (b e₀) ∨E e₀)

    r2f-f2r→ap : r2f (f2r (f , b)) ≤fp (f , b) → (f ∘ a , b ∘ p) ≤fp (f , b)
    fst (r2f-f2r→ap (f'≤f , b'≤b)) d₀ =
      begin-≤
      (f ∘ a) d₀ ≡⟨⟩
      f (⋀D (\ d → ∃ \ e → d₀ ≤D d × f d ≤E e × b e ≤D d)) ≤⟨ f-mono (D.bigmeet-lowerbound _ _ (p (f d₀) , D.≤-refl d₀ , {!!} , {!f'≤f!})) ⟩
      f d₀ ∎
      where
      open ≤E-reasoning

    snd (r2f-f2r→ap (f , b)) e = {!!}

```
