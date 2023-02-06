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
open import preorder

module complete-lattice where

module _ {X : Set} where
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

record complete-join-semilattice : Set where
  constructor cjlat
  field
    carrier : Set
    relation : rel carrier carrier
    operation : subsetop carrier
    property : is-complete-join-semilattice relation operation
  module property = is-complete-join-semilattice property

record complete-meet-semilattice : Set where
  constructor cmlat
  field
    carrier : Set
    relation : rel carrier carrier
    operation : subsetop carrier
    property : is-complete-meet-semilattice relation operation
  module property = is-complete-meet-semilattice property
  is-meet-closed-subset' : pred (subset carrier)
  is-meet-closed-subset' = is-meet-closed-subset property

record join-semilattice : Set where
  constructor jlat
  field
    carrier : Set
    relation : rel carrier carrier
    operation : binop carrier
    property : is-join-semilattice relation operation
  module property = is-join-semilattice property

record meet-semilattice : Set where
  constructor m-slat
  field
    carrier : Set
    relation : rel carrier carrier
    operation : binop carrier
    property : is-meet-semilattice relation operation
  open is-meet-semilattice property public

cmlat→pre : complete-meet-semilattice → preordered-set
cmlat→pre (cmlat _ _ _ X-cmlat) = pre _ _ X.rel-is-preorder
  where
    module X = is-complete-meet-semilattice X-cmlat

cm2j : ∀ {X} → rel X X → subsetop X → binop X
cm2j _≤_ ⋀ x x' = ⋀ ((\ u → x ≤ u) ∩ (\ u → x' ≤ u))

cm2cj : ∀ {X} → rel X X → subsetop X → subsetop X
cm2cj _≤_ ⋀ S = ⋀ (is-upperbound _≤_ S)

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
-- binary complete meet semilattice product

module _ (D-cmlat E-cmlat : complete-meet-semilattice)
  (let (cmlat D _≤D_ ⋀D D-prop) = D-cmlat)
  (let (cmlat E _≤E_ ⋀E E-prop) = E-cmlat)
  (let D-pre = cmlat→pre D-cmlat)
  (let E-pre = cmlat→pre E-cmlat)
  (let D×E-pre = D-pre ×-pre E-pre) where
  _×-cmlat_ : complete-meet-semilattice
  _×-cmlat_ =
    cmlat
      (D × E)
      (preordered-set.relation D×E-pre)
      (\ S → ⋀D (fst-subset S) , ⋀E (snd-subset S))
      property
    where
    open is-complete-meet-semilattice D-prop renaming (rel-is-preorder to ≤D-is-preorder ; op-is-bigmeet to ⋀D-is-bigmeet ; ↑ to ↑D)
    open is-complete-meet-semilattice E-prop renaming (rel-is-preorder to ≤E-is-preorder ; op-is-bigmeet to ⋀E-is-bigmeet ; ↑ to ↑E)
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

module derive-∧⋁∨⊤⊥ {X} (_≤_ : rel X X) (⋀ : subsetop X) where
  ⋁ : subsetop X
  ⋁ S = ⋀ (is-upperbound _≤_ S)

  _∧_ : binop X
  _∧_ x x' = ⋀ ((\ u → x ≤ u) ∩ (\ u → x' ≤ u))

  _∨_ : binop X
  _∨_ x x' = ⋁ ((\ d → d ≤ x) ∩ (\ d → d ≤ x'))

  ⊤ : X
  ⊤ = ⋀ ∅

  ⊥ : X
  ⊥ = ⋀ U

module _
  (X-cmlat : complete-meet-semilattice)
  (let (cmlat X _≤_ ⋀ X-prop) = X-cmlat)
  (let X-pre = cmlat→pre X-cmlat)
  where

  open complete-meet-semilattice
  open is-complete-meet-semilattice
  open is-preorder
  open is-greatest

  subset-complete-lattice : complete-meet-semilattice
  carrier subset-complete-lattice = subset X
  relation subset-complete-lattice = _⊆_
  operation subset-complete-lattice ss x = ∀ s → s ∈ ss → x ∈ s
  rel-is-reflexive (rel-is-preorder (property subset-complete-lattice)) r = id
  rel-is-transitive (rel-is-preorder (property subset-complete-lattice)) s s' p = s' (s p)
  element (op-is-bigmeet (property subset-complete-lattice) ss) s s∈ss s→s∈ss→x∈s = s→s∈ss→x∈s s s∈ss
  property (op-is-bigmeet (property subset-complete-lattice) ss) d d-is-lowerbound x∈d s s∈ss = d-is-lowerbound s s∈ss x∈d

  module _ (T : Set) where
    endo-complete-lattice : complete-meet-semilattice
    carrier endo-complete-lattice = T → X
    relation endo-complete-lattice f g = ∀ x → f x ≤ g x
    operation endo-complete-lattice S x = ⋀ \{ y → ∃ \ f → f ∈ S × f x ≤ y }
    rel-is-reflexive (rel-is-preorder (property endo-complete-lattice)) _ _ = preordered-set.property.rel-is-reflexive X-pre _
    rel-is-transitive (rel-is-preorder (property endo-complete-lattice)) f≤f' f'≤f'' _ = preordered-set.property.rel-is-transitive X-pre (f≤f' _) (f'≤f'' _)
    element (op-is-bigmeet (property endo-complete-lattice) S) f f∈S x =
      complete-meet-semilattice.property.bigmeet-lowerbound X-cmlat _ _ (f , f∈S , preordered-set.property.rel-is-reflexive X-pre _)
    property (op-is-bigmeet (property endo-complete-lattice) S) f f-is-lowerbound x =
      complete-meet-semilattice.property.bigmeet-greatest X-cmlat _ _ \ { y (f' , f'∈S , f'x≤y) → preordered-set.property.rel-is-transitive X-pre (f-is-lowerbound f' f'∈S x) f'x≤y}

```
