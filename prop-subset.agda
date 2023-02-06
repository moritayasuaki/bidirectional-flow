{-# OPTIONS --prop #-}

open import Agda.Primitive
open import Agda.Builtin.Nat renaming (_<_ to _Nat<_)
open import Agda.Builtin.Sigma
module prop-subset where

private
  variable
    𝓅 𝓅'  𝓆 𝓆' 𝓇 𝓇' : Level
    ℓ ℓ' ℓ'' : Level

data pfalse {𝓅} : Prop 𝓅 where
record ptrue {𝓅} : Prop 𝓅 where

infixr 1 ¬_
¬_ : Prop 𝓅 → Prop 𝓅
¬_ {𝓅} p = p → pfalse {𝓅}

_≤Nat_ : {𝓅 : Level} → Nat → Nat → Prop 𝓅
zero ≤Nat _ = ptrue
suc m ≤Nat zero = ptrue
suc m ≤Nat suc n = m ≤Nat n

-- prop and
infixr 1 _&_
record _&_  (X : Prop 𝓅) (Y : Prop 𝓆) : Prop (𝓅 ⊔ 𝓆) where
  constructor _,_
  field
    fst : X
    snd : Y
open _&_

-- prop or
data _∥_ (X : Prop 𝓅) (Y : Prop 𝓆) : Prop (𝓅 ⊔ 𝓆) where
  left : X → X ∥ Y
  right : Y → X ∥ Y

-- set product
infixr 1 _×_
_×_ : Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ')
A × B = Σ A \_ → B

id : {X : Set ℓ} → X → X
id x = x

flip : {X : Set ℓ} {Y : Set ℓ'} {Z : Set ℓ''} → (X → Y → Z) → Y → X → Z
flip f y x = f x y

record Subtype (A : Set ℓ) (P : A → Prop 𝓅) : Set (ℓ ⊔ lsuc 𝓅) where
  constructor _with-property_
  field
    structure : A
    property : P structure

open Subtype

∣_∣ : Set ℓ → Prop (ℓ ⊔ lsuc 𝓅)
∣_∣ {𝓅 = 𝓅} T = (P : Prop 𝓅) → (T → P) → P

lift : ∀ 𝓆 → Prop 𝓅 → Prop (𝓅 ⊔ 𝓆)
lift 𝓆 P = {ptrue {𝓆}} → P

∃ : {A : Set ℓ} → (P : A → Prop 𝓅) → Prop (lsuc (ℓ ⊔ lsuc 𝓅))
∃ {A = A} P = ∣ Subtype A P ∣


-- types of operations
module _ (A : Set ℓ) where
  Point = A
  Nulop = A
  Uniop = A → A
  Binop = A → A → A

-- tyeps of predicates and relations
module _ (𝓅) (A : Set ℓ) where
  Pred = A → Prop 𝓅
  Rel = A → A → Prop 𝓅


-- types of subsets
module _ (𝓅) (A : Set ℓ) where
  Subset = A → Prop 𝓅
  Subsetop = Subset → A

  set-comprehension = id
  syntax set-comprehension (\ x → p) = [[ x ∣ p ]]

infix 80 _∈_
_∈_ : {A : Set ℓ} → A → Subset 𝓅 A → Prop _
x ∈ s = s x

infix 1 _⊆_
_⊆_ : {A : Set ℓ} → Subset 𝓅 A → Subset 𝓅' A → Prop (ℓ ⊔ 𝓅 ⊔ 𝓅')
s ⊆ s' = ∀ a → a ∈ s → a ∈ s'

∅ : {A : Set ℓ} → Subset 𝓅 A
∅ _ = pfalse

U : {A : Set ℓ} → Subset 𝓅 A
U _ = ptrue

infixr 2 _∩_
_∩_ : {A : Set ℓ} → Subset 𝓅 A → Subset 𝓅' A → Subset _ A
s ∩ s' = \ a → a ∈ s & a ∈ s'

⋂ : {A : Set ℓ} → Subset 𝓅 (Subset 𝓅' A) → Subset (ℓ ⊔ 𝓅 ⊔ lsuc 𝓅') A
⋂ S x = ∀ s → s ∈ S → x ∈ s

infixr 2 _∪_
_∪_ : {A : Set ℓ} → Subset 𝓅 A → Subset 𝓅' A → Subset _ A
s ∪ s' = \ a → a ∈ s ∥ a ∈ s'

⋃ : {A : Set ℓ} → Subset 𝓅 (Subset 𝓅' A) → Subset _ A
⋃ S x = ∃ \ s → s ∈ S & x ∈ s

_⋈'_ : {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} → Subset 𝓅 (A × B) → Subset 𝓅' (B × C) → Subset _ (A × B × C)
r ⋈' r' = \ {( x , y , z) → (x , y) ∈ r & (y , z) ∈ r'}


liftPred : ∀ 𝓆 {A : Set ℓ} → Pred 𝓅 A → Pred (𝓅 ⊔ 𝓆) A
liftPred 𝓆 P x = lift 𝓆 (P x)

liftSubop : ∀ 𝓅 {𝓆} {A : Set ℓ} → Subsetop (𝓅 ⊔ 𝓆) A → Subsetop 𝓆 A
liftSubop 𝓅 ⋀ s = ⋀ (liftPred 𝓅 s)


{-
record RelSet ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor [_,_]
  field
    carrier : Set ℓ
    _≤_ : Rel 𝓅 carrier
-}

record RelSet ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mkRelSet
  field
    X : Set ℓ
    _≤_ : X → X → Prop 𝓅


record 2RelSet ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mk2RelSet
  field
    X : Set ℓ
    _≈_ : X → X → Prop 𝓅
    _≤_ : X → X → Prop 𝓅

record RelBinopSet ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mkRelBinopSet
  field
    X : Set ℓ
    _∧_ : X → X → X
    _≤_ : X → X → Prop 𝓅

record PointedRelBinopSet ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mkPointedRelBinopSet
  field
    X : Set ℓ
    _∧_ : X → X → X
    ⊤ : X
    _≤_ : X → X → Prop 𝓅

record 2PointedRel2BinopSet ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mk2PointedRel2BinopSet
  field
    X : Set ℓ
    _∧_ : X → X → X
    _∨_ : X → X → X
    ⊤ : X
    ⊥ : X
    _≤_ : X → X → Prop 𝓅

record RelSubopSet ℓ 𝓅 𝓆 : Set (lsuc (ℓ ⊔ 𝓅 ⊔ 𝓆)) where
  constructor mkRelSubopSet
  field
    X : Set ℓ
    ⋀ : Subset 𝓆 X → X
    _≤_ : X → X → Prop 𝓅

record PointedSet ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mkPointedSet
  field
    X : Set ℓ
    ⊤ : X

record PointedRelSet ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mkPointedRelSet
  field
    X : Set ℓ
    ⊤ : X
    _≤_ : X → X → Prop 𝓅

record PointedRelSubopSet ℓ 𝓅 𝓆 : Set (lsuc (ℓ ⊔ 𝓅 ⊔ 𝓆)) where
  constructor mkPointedRelSubopSet
  field
    X : Set ℓ
    ⊤ : X
    ⋀ : Subset 𝓆 X → X
    _≤_ : X → X → Prop 𝓅

record 2PointedRel2SubopSet ℓ 𝓅 𝓆 : Set (lsuc (ℓ ⊔ 𝓅 ⊔ 𝓆)) where
  constructor mk2PointedRel2SubopSet
  field
    X : Set ℓ
    ⊥ : X
    ⊤ : X
    ⋀ : Subset 𝓆 X → X
    ⋁ : Subset 𝓆 X → X
    _≤_ : X → X → Prop 𝓅

module RelSetProps (relset : RelSet ℓ 𝓅) where
  open RelSet relset
  is-transitive = {a1 a2 a3 : _} → (a1≤a2 : a1 ≤ a2) → (a2≤a3 : a2 ≤ a3) → a1 ≤ a3
  is-reflexive = {a : _} → a ≤ a
  is-symmetric = {a1 a2 : _} → (a1≤a2 : a1 ≤ a2) → a2 ≤ a1

  record is-preorder : Prop (ℓ ⊔ 𝓅) where
    field
      trans : is-transitive
      refl : is-reflexive

  open is-preorder public

  record is-equivalence : Prop (ℓ ⊔ 𝓅) where
    field
      preorder : is-preorder
      sym : is-symmetric

  open is-equivalence public


  record is-greatest (s : Subset 𝓆 X) (a : X) : Prop (ℓ ⊔ 𝓆 ⊔ 𝓅) where
    field
      belongs : a ∈ s
      greatest : {x : _} → (x∈s : x ∈ s) → x ≤ a
  open is-greatest public

  record is-least (s : Subset 𝓆 X) (a : X) : Prop (ℓ ⊔ 𝓆 ⊔ 𝓅) where
    field
      belongs : a ∈ s
      least : {x : _} → (x∈s : s x) → a ≤ x
  open is-least public

  module SubsetProps where
    is-lowerbound : Subset 𝓆 X → Pred _ X
    is-lowerbound s a = {x : _} → (x∈s : s x) → a ≤ x

    is-greatest-lowerbound : Subset 𝓆 X → X → Prop _
    is-greatest-lowerbound s a = is-greatest (is-lowerbound s) a

    is-meet = is-greatest-lowerbound

    is-upperbound : Subset 𝓆 X → Pred _ X
    is-upperbound s a = {x : _} → (x∈s : x ∈ s) → x ≤ a

    is-leastupperbound : Subset 𝓆 X → Pred _ X
    is-leastupperbound s a = is-least (is-upperbound s) a

    is-join = is-leastupperbound

  module BinaryProps where
    is-lowerbound : X → X → Pred _ X
    is-lowerbound x1 x2 a = (a ≤ x1) & (a ≤ x2)

    is-greatest-lowerbound : X → X → Pred _ X
    is-greatest-lowerbound x1 x2 a = is-greatest (is-lowerbound x1 x2) a

    is-meet = is-greatest-lowerbound

    is-upperbound : X → X → Pred _ X
    is-upperbound x1 x2 a = (x1 ≤ a) & (x2 ≤ a)

    is-leastupperbound : X → X → Pred _ X
    is-leastupperbound x1 x2 a = is-least (is-upperbound x1 x2) a

    is-join = is-leastupperbound

module PointedRelSetProps (pointedrelset : PointedRelSet ℓ 𝓅) where
  open PointedRelSet pointedrelset renaming (⊤ to pt)

  is-maximum : Prop _
  is-maximum = ∀ x → x ≤ pt

  is-minimum : Prop _
  is-minimum = ∀ x → pt ≤ x

module DeriveSymrel (relset : RelSet ℓ 𝓅) where
  open RelSet relset
  open RelSetProps relset

  _≥_ = \x y → y ≤ x
  record _≈_ (a1 a2 : X) : Prop 𝓅 where
    field
      ≤ : a1 ≤ a2
      ≥ : a1 ≥ a2

  _<_ : Rel 𝓅 X
  x < y = x ≤ y & (¬ x ≥ y)

  _>_ : Rel 𝓅 X
  x > y = (¬ x ≤ y) & x ≥ y

  open _≈_ public

module 2RelSetProps (2relset : 2RelSet ℓ 𝓅) where
  open 2RelSet 2relset
  module ≈ = RelSetProps (record { X = X ; _≤_ = _≈_})
  module ≤ = RelSetProps (record { X = X ; _≤_ = _≤_})

  is-antisymmetric = {a1 a2 : _} → (a1≤a2 : a1 ≤ a2) → (a2≤a1 : a2 ≤ a1) → a1 ≈ a2

  record is-partialorder : Prop (ℓ ⊔ 𝓅) where
    field
      equiv : ≈.is-equivalence
      preorder : ≤.is-preorder
      antisym : is-antisymmetric

  open is-partialorder public

record Preoset ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mkPreoset
  field
    relset : RelSet ℓ 𝓅
    preorder : RelSetProps.is-preorder relset

  open RelSet relset public
  module Preorder = RelSetProps.is-preorder preorder

record Setoid ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mkSetoid
  field
    relset : RelSet ℓ 𝓅
    equiv : RelSetProps.is-equivalence relset

  open RelSet relset renaming (_≤_ to _≈_) public
  module Equiv = RelSetProps.is-equivalence equiv

record Poset ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mkPoset
  field
    2relset : 2RelSet ℓ 𝓅
    po : 2RelSetProps.is-partialorder 2relset

  open 2RelSet 2relset public
  module Po = 2RelSetProps.is-partialorder po

DerivePoset : (preoset : Preoset ℓ 𝓅) → Poset ℓ 𝓅
DerivePoset preoset = poset
  module DerivePoset where
    open Preoset preoset
    open DeriveSymrel (mkRelSet X _≤_)
    open 2RelSetProps (record {X = X; _≤_ = _≤_ ; _≈_ = _≈_})
    open ≤.is-preorder (preoset .Preoset.preorder)

    ≈-equiv : ≈.is-equivalence
    ≈-equiv .≈.preorder .≈.trans a1≈a2 a2≈a3 .≤ = trans (a1≈a2 .≤) (a2≈a3 .≤)
    ≈-equiv .≈.preorder .≈.trans a1≈a2 a2≈a3 .≥ = trans (a2≈a3 .≥) (a1≈a2 .≥)
    ≈-equiv .≈.preorder .≈.refl .≤ = refl
    ≈-equiv .≈.preorder .≈.refl .≥ = refl
    ≈-equiv .≈.sym a1≈a2 .≤ = a1≈a2 .≥
    ≈-equiv .≈.sym a1≈a2 .≥ = a1≈a2 .≤

    ≤-≈-antisym : is-antisymmetric
    ≤-≈-antisym a1≤a2 a2≤a1 .≤ = a1≤a2
    ≤-≈-antisym a1≤a2 a2≤a1 .≥ = a2≤a1

    poset : Poset _ _
    poset = mkPoset (mk2RelSet X _≈_ _≤_) \where
      .equiv → ≈-equiv
      .preorder → (preoset .Preoset.preorder)
      .antisym → ≤-≈-antisym

module _ (relX : RelSet ℓ 𝓅) (relY : RelSet ℓ' 𝓅') where
  open RelSet relX renaming (X to X; _≤_ to _≤X_)
  open RelSet relY renaming (X to Y; _≤_ to _≤Y_)
  is-preserving : (f : X → Y) → Prop _
  is-preserving f = {a1 a2 : _} → (a1≤a2 : a1 ≤X a2) → f a1 ≤Y f a2

record PreservingFunction (relset : RelSet ℓ 𝓅) (relset' : RelSet ℓ' 𝓅') : Set (ℓ ⊔ ℓ' ⊔ 𝓅 ⊔ 𝓅') where
  constructor mkPreservingFunction
  open RelSet relset renaming (X to X; _≤_ to _≤X_)
  open RelSet relset' renaming (X to Y; _≤_ to _≤Y_)
  field
    f : X → Y
    preserving : is-preserving relset relset' f

module RelBinopSetProps (relbinopset : RelBinopSet ℓ 𝓅) where
  open RelBinopSet relbinopset renaming (_∧_ to _op_)
  open RelSetProps.BinaryProps (mkRelSet X _≤_)

  is-meetclosed = (x x' : X) → is-meet x x' (x op x')
  is-joinclosed = (x x' : X) → is-meet x x' (x op x')

module RelSubopSetProps (relsubopset : RelSubopSet ℓ 𝓅 𝓆) where
  open RelSubopSet relsubopset renaming (⋀ to Op)
  open RelSetProps.SubsetProps (mkRelSet X _≤_)

  is-meetclosed = (s : Subset 𝓆 X) → is-meet s (Op s)
  is-joinclosed = (s : Subset 𝓆 X) → is-join s (Op s)

record MeetSemilattice ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mkMeetSemilat
  field
    relbinopset : RelBinopSet ℓ 𝓅
    meetclosed : RelBinopSetProps.is-meetclosed relbinopset

record CompleteMeetSemilattice ℓ 𝓅 𝓆 : Set (lsuc (ℓ ⊔ 𝓅 ⊔ 𝓆)) where
  constructor mkCompleteMeetSemilattice
  field
    relsubopset : RelSubopSet ℓ 𝓅 𝓆
    meetclosed : RelSubopSetProps.is-meetclosed relsubopset

  open RelSubopSet relsubopset public
  module MeetClosed s = RelSetProps.is-greatest (meetclosed s)

module PointedRelBinopSetProps (ptrelbinopset : PointedRelBinopSet ℓ 𝓅) where
  open PointedRelBinopSet ptrelbinopset renaming (_∧_ to _op_ ; ⊤ to pt)
  open PointedRelSetProps (mkPointedRelSet X pt _≤_)
  open RelBinopSetProps (mkRelBinopSet X _op_ _≤_)

  record is-bounded-meetsemilattice : Prop (ℓ ⊔ 𝓅) where
    field
      ∧-meet : is-meetclosed
      ⊤-maximum : is-maximum

  open is-bounded-meetsemilattice public

  record is-bounded-joinsemilattice : Prop (ℓ ⊔ 𝓅) where
    field
      ∨-join : is-joinclosed
      ⊥-minimum : is-minimum

  open is-bounded-joinsemilattice public

record BoundedMeetSemilattice ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mkBoundMeetSemilat
  field
    ptrelbinopset : PointedRelBinopSet ℓ 𝓅
    bounded-meetsemialttice : PointedRelBinopSetProps.is-bounded-meetsemilattice ptrelbinopset

module PointedRelSubopSetProps (ptrelsubopset : PointedRelSubopSet ℓ 𝓅 𝓆) where
  open PointedRelSubopSet ptrelsubopset renaming (⋀ to Op ; ⊤ to pt)
  open PointedRelSetProps (mkPointedRelSet X pt _≤_)
  open RelSubopSetProps (mkRelSubopSet X Op _≤_)

  record is-bounded-meetsemilattice : Prop (ℓ ⊔ 𝓅 ⊔ lsuc 𝓆) where
    field
      ⋀-meet : is-meetclosed
      ⊤-maximum : is-maximum

  open is-bounded-meetsemilattice public

  record is-bounded-joinsemilattice : Prop (ℓ ⊔ 𝓅 ⊔ lsuc 𝓆) where
    field
      ⋁-join : is-joinclosed
      ⊥-minimum : is-minimum

  open is-bounded-joinsemilattice public

module derive-binaryop (relsubopset : RelSubopSet ℓ 𝓅 𝓅) where
  open RelSubopSet relsubopset
  open DeriveSymrel (mkRelSet X _≤_)

  _∧_ : X → X → X
  a1 ∧ a2 = ⋀ \ x → ((x ≈ a1) ∥ (x ≈ a2))

module 2PointedRel2SubopSetProps (2pointedrel2subopset : 2PointedRel2SubopSet ℓ 𝓅 𝓆) where
  open 2PointedRel2SubopSet 2pointedrel2subopset
  open PointedRelSubopSetProps (mkPointedRelSubopSet X ⊤ ⋀ _≤_) using (is-bounded-meetsemilattice)
  open PointedRelSubopSetProps (mkPointedRelSubopSet X ⊥ ⋁ _≤_) using (is-bounded-joinsemilattice)

  record is-complete-lattice : Prop (ℓ ⊔ 𝓅 ⊔ lsuc 𝓆) where
    field
      ⋀-⊤-lattice : is-bounded-meetsemilattice
      ⋁-⊥-lattice : is-bounded-joinsemilattice
  open is-complete-lattice public

record CompleteLattice ℓ 𝓅 𝓆 : Set (lsuc (ℓ ⊔ 𝓅 ⊔ 𝓆)) where
  constructor mkCompleteLttice
  field
    2pointedrel2subopset : 2PointedRel2SubopSet ℓ 𝓅 𝓆
    completelattice : 2PointedRel2SubopSetProps.is-complete-lattice 2pointedrel2subopset

  open 2PointedRel2SubopSet 2pointedrel2subopset public
  module CompLat = 2PointedRel2SubopSetProps.is-complete-lattice completelattice
  module MeetSemiLat = PointedRelSubopSetProps.is-bounded-meetsemilattice (CompLat.⋀-⊤-lattice)
  module JoinSemiLat = PointedRelSubopSetProps.is-bounded-joinsemilattice (CompLat.⋁-⊥-lattice)
  module MeetClosed s = RelSetProps.is-greatest (MeetSemiLat.⋀-meet s)
  module JoinClosed s = RelSetProps.is-least (JoinSemiLat.⋁-join s)

DeriveCompleteLattice : (complete-meet-semilattice : CompleteMeetSemilattice ℓ (ℓ ⊔ 𝓅) (ℓ ⊔ 𝓅)) → CompleteLattice ℓ (ℓ ⊔ 𝓅) (ℓ ⊔ 𝓅)
DeriveCompleteLattice complete-meet-semilattice = complete-lattice
  module DeriveCompleteLattice where
    open CompleteMeetSemilattice complete-meet-semilattice
    open RelSubopSetProps
    open RelSetProps
    open PointedRelSetProps

    ⋁ : Pred _ X → X
    ⋁ s = ⋀ (SubsetProps.is-upperbound (mkRelSet X _≤_) s)

    ⊥ = ⋀ U
    ⊤ = ⋀ ∅

    open 2PointedRel2SubopSetProps
    open PointedRelSubopSetProps.is-bounded-meetsemilattice
    open PointedRelSubopSetProps.is-bounded-joinsemilattice
    open is-complete-lattice
    open CompleteLattice using (2pointedrel2subopset ; completelattice)
    complete-lattice : CompleteLattice _ _ _
    complete-lattice .2pointedrel2subopset = mk2PointedRel2SubopSet X ⊥ ⊤ ⋀ ⋁ _≤_
    complete-lattice .completelattice .⋀-⊤-lattice .⋀-meet = meetclosed
    complete-lattice .completelattice .⋀-⊤-lattice .⊤-maximum _ = MeetClosed.greatest _ \()
    complete-lattice .completelattice .⋁-⊥-lattice .⋁-join s .belongs x∈s = MeetClosed.greatest (SubsetProps.is-upperbound (mkRelSet X _≤_) s) \ x∈↑s → x∈↑s x∈s
    complete-lattice .completelattice .⋁-⊥-lattice .⋁-join s .least x∈↓s = MeetClosed.belongs (SubsetProps.is-upperbound (mkRelSet X _≤_) s)  \ x∈s → x∈↓s x∈s
    complete-lattice .completelattice .⋁-⊥-lattice .⊥-minimum _ = MeetClosed.belongs _ _

-- DeriveSemilattice : (complete-semilattice : CompleteMeetSemilattice ℓ 𝓅 𝓆) → BoundedMeetSemilattice ℓ (ℓ

module Endo (setoid : Setoid ℓ 𝓅) where
  open Setoid setoid renaming (_≈_ to _≈_)
  EndoFunction : Set _
  EndoFunction = PreservingFunction (mkRelSet X _≈_) (mkRelSet X _≈_)

  FixedPoint : EndoFunction → Subset _ X
  FixedPoint endo x = f x ≈ x
    where open PreservingFunction endo renaming (f to f)

module Endo≤ (preoset : Preoset ℓ 𝓅) where
  open Preoset preoset
  MonotoneFunction = PreservingFunction relset relset

  PostfixPoint : MonotoneFunction → Subset _ X
  PostfixPoint endo x = f x ≤ x
    where open PreservingFunction endo renaming (f to f)

  PrefixPoint : MonotoneFunction → Subset _ X
  PrefixPoint endo x = x ≤ f x
    where open PreservingFunction endo renaming (f to f)

  open Poset (DerivePoset preoset)
  open Endo (mkSetoid (mkRelSet _ _≈_) Po.equiv) public

  DeriveEndo : MonotoneFunction → EndoFunction
  DeriveEndo mono = endo
    module DeriveEndo where
      open DeriveSymrel
      open PreservingFunction mono
      endo : EndoFunction
      endo .f = f
      endo .preserving a1≈a2 .≤ = preserving (a1≈a2 .≤)
      endo .preserving a1≈a2 .≥ = preserving (a1≈a2 .≥)

module EndoRel (preoset : Preoset ℓ 𝓅) where
  open Poset (DerivePoset preoset)
  open Endo≤ preoset public

  module _ (e : EndoFunction) where
    LeastFixedPoint : Subset _ X
    LeastFixedPoint = RelSetProps.is-least (mkRelSet X _≤_) (FixedPoint e)

    GreatestFixedPoint : Subset _ X
    GreatestFixedPoint = RelSetProps.is-greatest (mkRelSet X _≤_) (FixedPoint e)

module LatticeTheory (completemeetsemilattice : CompleteMeetSemilattice ℓ (ℓ ⊔ 𝓅) (ℓ ⊔ 𝓅)) where
  open CompleteLattice (DeriveCompleteLattice {ℓ = ℓ} {𝓅 = 𝓅} completemeetsemilattice)

  ⋀-monotone : ∀ s s' → (s⊆s' : s ⊆ s') → ⋀ s' ≤ ⋀ s
  ⋀-monotone s s' s⊆s' = MeetClosed.greatest s \ x∈s → MeetClosed.belongs s' (s⊆s' _ x∈s)

  ⋁-monotone : ∀ s s' → (s⊆s' : s ⊆ s') → ⋁ s ≤ ⋁ s'
  ⋁-monotone s s' s⊆s' = JoinClosed.least s \ x∈s → JoinClosed.belongs s' (s⊆s' _ x∈s)

  module _ (preorder : RelSetProps.is-preorder (mkRelSet X _≤_)) where
    private
      X≤ = (mkRelSet X _≤_)
      module X≤ = RelSetProps X≤

    open EndoRel (mkPreoset X≤ preorder)
    module _ (m : MonotoneFunction) where
      open PreservingFunction m renaming (f to f)
      open DeriveSymrel X≤
      f[⋀post]∈↓post : X≤.SubsetProps.is-lowerbound (PostfixPoint m) (f (⋀ (PostfixPoint m)))
      f[⋀post]∈↓post x∈s = preserving (MeetClosed.belongs _ x∈s) ∙ x∈s
        where open X≤.is-preorder preorder renaming (trans to _∙_)

      private e = DeriveEndo m

      lfp⋀post : ⋀ (PostfixPoint m) ∈ LeastFixedPoint e
      lfp⋀post .X≤.belongs .≤ = MeetClosed.greatest (PostfixPoint m) f[⋀post]∈↓post
      lfp⋀post .X≤.belongs .≥ = MeetClosed.belongs (PostfixPoint m) (preserving (MeetClosed.greatest (PostfixPoint m) f[⋀post]∈↓post))
      lfp⋀post .X≤.least x∈s = MeetClosed.belongs (PostfixPoint m) (x∈s .≤)

      ⋀fix≈⋀post : ⋀ (FixedPoint e) ≈ ⋀ (PostfixPoint m)
      ⋀fix≈⋀post .≤ = MeetClosed.belongs (FixedPoint e) \where
        .≤ → MeetClosed.greatest (PostfixPoint m) f[⋀post]∈↓post
        .≥ → MeetClosed.belongs (PostfixPoint m) (preserving (MeetClosed.greatest (PostfixPoint m) f[⋀post]∈↓post))
      ⋀fix≈⋀post .≥ = ⋀-monotone (FixedPoint e) (PostfixPoint m) \ x x∈fix → x∈fix .≤

module RelConnection (relset : RelSet ℓ 𝓅) (relset' : RelSet ℓ' 𝓅') (prefun : PreservingFunction relset relset') (prefun' : PreservingFunction relset' relset) where
  module C = RelSet relset
  module D = RelSet relset'
  module R = PreservingFunction prefun
  module L = PreservingFunction prefun'

  record Connection : Set (ℓ ⊔ 𝓅 ⊔ ℓ' ⊔ 𝓅') where
    field
      r : (c : C.X) (d : D.X) → L.f d C.≤ c → d D.≤ R.f c
      l : (c : C.X) (d : D.X) → d D.≤ R.f c → L.f d C.≤ c

module SubsetTheory (X : Set ℓ) where
  subset⊆ : RelSet _ _
  RelSet.X subset⊆ = Subset ℓ X
  RelSet._≤_ subset⊆ s s' = s ⊆ s'

  subset⊆preo : Preoset _ _
  Preoset.relset subset⊆preo = subset⊆
  RelSetProps.trans (Preoset.preorder subset⊆preo) a1⊆a2 a2⊆a3 x x∈a1 = a2⊆a3 _ (a1⊆a2 _ x∈a1)
  RelSetProps.refl (Preoset.preorder subset⊆preo) x x∈a = x∈a

  subset⊆∩ : RelBinopSet (lsuc 𝓅 ⊔ ℓ) (𝓅 ⊔ ℓ)
  RelBinopSet.X (subset⊆∩ {𝓅 = 𝓅}) = Subset 𝓅 X
  RelBinopSet._∧_ subset⊆∩ = _∩_
  RelBinopSet._≤_ subset⊆∩ = _⊆_

  subset⊆∩⊤ : PointedRelBinopSet (lsuc 𝓅 ⊔ ℓ) (𝓅 ⊔ ℓ)
  PointedRelBinopSet.X (subset⊆∩⊤ {𝓅 = 𝓅}) = Subset 𝓅 X
  PointedRelBinopSet._∧_ subset⊆∩⊤ = _∩_
  PointedRelBinopSet._≤_ subset⊆∩⊤ = _⊆_
  PointedRelBinopSet.⊤ subset⊆∩⊤ = U
