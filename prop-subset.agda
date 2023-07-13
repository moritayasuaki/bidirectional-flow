{-# OPTIONS --prop --safe --exact-split #-}

open import Agda.Primitive
open import Agda.Builtin.Nat renaming (_<_ to _Nat<_)
open import Agda.Builtin.Sigma
module prop-subset where


private
  variable
    𝓅 𝓅' 𝓅''  𝓆 𝓆' 𝓇 𝓇' : Level
    ℓ ℓ' ℓ'' ℓ''' : Level

data Empty {ℓ} : Set ℓ where
record Unit {ℓ} : Set ℓ where

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
infixr 2 _∥_
data _∥_ (X : Prop 𝓅) (Y : Prop 𝓆) : Prop (𝓅 ⊔ 𝓆) where
  left : X → X ∥ Y
  right : Y → X ∥ Y

-- set disjoint or
infixr 2 _⊎_
data _⊎_ (X : Set 𝓅) (Y : Set 𝓆) : Set (𝓅 ⊔ 𝓆) where
  left : X → X ⊎ Y
  right : Y → X ⊎ Y

data Id 𝓅 {ℓ} {X : Set ℓ} : X → X → Set (ℓ ⊔ 𝓅) where
  Id-refl : ∀ {x} → Id 𝓅 x x

_≡_ = Id lzero

data Idp 𝓅 {X : Set ℓ} (x : X) : X → Prop 𝓅 where
  _ : Idp 𝓅 x x

-- set product
infixr 1 _×_
_×_ : Set ℓ → Set ℓ' → Set (ℓ ⊔ ℓ')
A × B = Σ A \_ → B

id : {X : Set ℓ} → X → X
id x = x

idp : {X : Prop 𝓅} → X → X
idp x = x

flip : {X : Set ℓ} {Y : Set ℓ'} {Z : Set ℓ''} → (X → Y → Z) → Y → X → Z
flip f y x = f x y

flipp : {X : Prop 𝓅} {Y : Prop 𝓅'} {Z : Prop 𝓅''} → (X → Y → Z) → Y → X → Z
flipp f y x = f x y

∣_∣ : Set ℓ → Prop (ℓ ⊔ lsuc 𝓅)
∣_∣ {𝓅 = 𝓅} T = (P : Prop 𝓅) → (T → P) → P

lift : ∀ 𝓆 → Prop 𝓅 → Prop (𝓅 ⊔ 𝓆)
lift 𝓆 P = {ptrue {𝓆}} → P

record TT {ℓ} (P : Prop 𝓅) : Set (ℓ ⊔ 𝓅) where
  constructor fact
  field
    proof : P


-- types of operations
module _ (A : Set ℓ) where
  Point = A
  Nulop = A
  Uniop = A → A
  Binop = A → A → A

-- tyeps of predicates and relations
module _ (𝓅) (A : Set ℓ) where
  Pred = A → Prop 𝓅
  Binrel = A → A → Prop 𝓅

record ∃ {A : Set ℓ} (X : Pred 𝓅 A) : Set (ℓ ⊔ 𝓅) where
  constructor _,_
  field
    fst : A
    snd : X fst

record Subset 𝓅 (A : Set ℓ) : Set (ℓ ⊔ lsuc 𝓅) where
  constructor mksubset
  field
    pred : Pred 𝓅 A

-- types of subsets
-- Subset : (ℓ' : Level) → Set ℓ → Set _
-- Subset ℓ' A = A → Set ℓ'

Powop : ∀ 𝓅 → (A : Set ℓ) → Set _
Powop 𝓅 A = Pred 𝓅 A → A

set2prop : {𝓅 : Level} → Set ℓ → Prop (ℓ ⊔ lsuc 𝓅)
set2prop {𝓅 = 𝓅} S = {P : Prop 𝓅} → (S → P) → P

prop2set : {ℓ : Level} → Prop 𝓅 → Set (ℓ ⊔ 𝓅)
prop2set {𝓅 = 𝓅} {ℓ = ℓ} P = TT {𝓅 = 𝓅} {ℓ = ℓ} P

set-comprehension = id
syntax set-comprehension (\ x → p) = [[ x ∣ p ]]

infix 80 _∈_
_∈_ : {A : Set ℓ} → A → Subset 𝓅 A → Prop _
_∈_ {𝓅 = 𝓅} x s = Subset.pred s x

infix 0 _⇒_
_⇒_ : {A : Set ℓ} → Pred 𝓅 A → Pred 𝓅' A → Prop _
p ⇒ p' = ∀ a → p a → p' a

infixr 1 _∥'_
_∥'_ : {A : Set ℓ} → Pred 𝓅 A → Pred 𝓅' A → Pred _ A
s ∥' s' = \ a → s a ∥ s' a

infixr 3 _&'_
_&'_ : {A : Set ℓ} → Pred 𝓅 A → Pred 𝓅' A → Pred _ A
s &' s' = \ a → s a & s' a

pfalse' : {A : Set ℓ} → Pred 𝓅 A
pfalse' _ = pfalse

ptrue' : {A : Set ℓ} → Pred 𝓅 A
ptrue' _ = ptrue

infix 1 _⊆_
_⊆_ : {A : Set ℓ} → Subset 𝓅 A → Subset 𝓅' A → Prop _
s ⊆ s' = ∀ a → a ∈ s → a ∈ s'

∅ : {A : Set ℓ} → Subset 𝓅 A
∅ = mksubset pfalse'

U : {A : Set ℓ} → Subset 𝓅 A
U = mksubset ptrue'

infixr 2 _∩_
_∩_ : {A : Set ℓ} → Subset 𝓅 A → Subset 𝓅' A → Subset _ A
s ∩ s' = mksubset \ a → a ∈ s & a ∈ s'

⋂ : {A : Set ℓ} → Subset 𝓅 (Subset 𝓅' A) → Subset _ A
⋂ S = mksubset \ a → ∀ s → s ∈ S → a ∈ s

infixr 2 _∪_
_∪_ : {A : Set ℓ} → Subset 𝓅 A → Subset 𝓅' A → Subset _ A
s ∪ s' = mksubset \ a → a ∈ s ∥ a ∈ s'

⋃ : {A : Set ℓ} → Subset 𝓅 (Subset 𝓅' A) → Subset _ A
⋃ S = mksubset \ a → set2prop (∃ \ s → s ∈ S & a ∈ s)

infixr 10 _⋈_
_⋈_ : {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''} → Subset 𝓅 (A × B) → Subset 𝓅' (B × C) → Subset _ (A × C)
r ⋈ r' = mksubset \(x , z) → set2prop (∃ \ y → (x , y) ∈ r & (y , z) ∈ r')

Δ : {A : Set ℓ} → Subset ℓ (A × A)
Δ = mksubset \ (x , x') → Idp _ x x'

record ≤-Set ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mk≤-Set
  infix 5 _≤_
  field
    X : Set ℓ
    _≤_ : Binrel 𝓅 X

record ≈≤-Set ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mk≈≤-Set
  infix 5 _≈_ _≤_
  field
    X : Set ℓ
    _≈_ _≤_ : Binrel 𝓅 X

record RelBinopSet ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mkRelBinopSet
  infixr 10 _∧_
  infix 5 _≤_
  field
    X : Set ℓ
    _∧_ : Binop X
    _≤_ : Binrel 𝓅 X

record PointedRelBinopSet ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mkPointedRelBinopSet
  infixr 10 _∧_
  infix 5 _≤_
  field
    X : Set ℓ
    _∧_ : Binop X
    ⊤ : X
    _≤_ : Binrel 𝓅 X

record 2PointedRel2BinopSet ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mk2PointedRel2BinopSet
  infix 10 _∧_
  infix 5 _≤_
  field
    X : Set ℓ
    _∧_ _∨_ : Binop X
    ⊤ ⊥ : X
    _≤_ : Binrel 𝓅 X

record PowopSet ℓ 𝓆 : Set (lsuc (ℓ ⊔ 𝓆)) where
  constructor mkPowopSet
  field
    X : Set ℓ
    ⋀ : Powop 𝓆 X

record RelPowopSet ℓ 𝓅 𝓆 : Set (lsuc (ℓ ⊔ 𝓅 ⊔ 𝓆)) where
  constructor mkRelPowopSet
  infix 5 _≤_
  field
    X : Set ℓ
    ⋀ : Powop 𝓆 X
    _≤_ : Binrel 𝓅 X

record PointedSet ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mkPointedSet
  field
    X : Set ℓ
    ⊤ : X

record Pointed≤-Set ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mkPointed≤-Set
  infix 5 _≤_
  field
    X : Set ℓ
    ⊤ : X
    _≤_ : Binrel 𝓅 X

record PointedRelPowopSet ℓ 𝓅 𝓆 : Set (lsuc (ℓ ⊔ 𝓅 ⊔ 𝓆)) where
  constructor mkPointedRelPowopSet
  infix 5 _≤_
  field
    X : Set ℓ
    ⊤ : X
    ⋀ : Powop 𝓆 X
    _≤_ : Binrel 𝓅 X

record 2PointedRel2PowopSet ℓ 𝓅 𝓆 : Set (lsuc (ℓ ⊔ 𝓅 ⊔ 𝓆)) where
  constructor mk2PointedRel2PowopSet
  infix 5 _≤_
  field
    X : Set ℓ
    ⊥ ⊤ : X
    ⋀ ⋁ : Powop 𝓆 X
    _≤_ : Binrel 𝓅 X

record 2PointedRel2PowopBinopSet ℓ 𝓅 𝓆 : Set (lsuc (ℓ ⊔ 𝓅 ⊔ 𝓆)) where
  constructor mk2PointedRel2PowopBinopSet
  infix 5 _≤_
  infixr 10 _⊢_
  field
    X : Set ℓ
    ⊥ ⊤ : X
    _⊢_ : Binop X
    ⋀ ⋁ : Powop 𝓆 X
    _≤_ : Binrel 𝓅 X

record 2PointedRel3BinopSet ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mk2PointedRel3BinopSet
  infix 5 _≤_
  infixr 10 _∧_ _∨_ _⊢_
  field
    X : Set ℓ
    ⊥ ⊤ : X
    _∧_ _∨_ _⊢_ : Binop X
    _≤_ : Binrel 𝓅 X


module ≤-SetProps (relset : ≤-Set ℓ 𝓅) where
  open ≤-Set relset
  is-transitive = {a1 a2 a3 : _} → (a1≤a2 : a1 ≤ a2) → (a2≤a3 : a2 ≤ a3) → a1 ≤ a3
  is-reflexive = {a : _} → a ≤ a
  is-symmetric = {a1 a2 : _} → (a1≤a2 : a1 ≤ a2) → a2 ≤ a1
  is-right-euclidean = {a1 a2 a3 : _} → a1 ≤ a2 → a1 ≤ a3 → a2 ≤ a3
  is-left-euclidean = {a1 a2 a3 : _} → a2 ≤ a1 → a3 ≤ a1 → a2 ≤ a3
  is-antisymmetric = {a1 a2 : _} → (a1≤a2 : a1 ≤ a2) → (a2≤a1 : a2 ≤ a1) → Idp 𝓅 a1 a2

  is-pid = {a1 a2 : _} → a1 ≤ a2 → a1 ≡ a2

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


  record is-po : Prop (ℓ ⊔ 𝓅) where
    field
      preorder : is-preorder
      antisymmetric : is-antisymmetric

  record is-greatest (s : Pred 𝓆 X) (a : X) : Prop (ℓ ⊔ lsuc 𝓆 ⊔ 𝓅) where
    field
      satisfies : s a
      greatest : {x : _} → s x → x ≤ a
  open is-greatest public

  record is-least (s : Pred 𝓆 X) (a : X) : Prop (ℓ ⊔ lsuc 𝓆 ⊔ 𝓅) where
    field
      satisfies : s a
      least : {x : _} → s x → a ≤ x
  open is-least public

  module SubsetProps where
    is-lowerbound : Pred 𝓆 X → Pred _ X
    is-lowerbound s a = {x : _} → (x∈s : s x) → a ≤ x

    is-greatest-lowerbound : Pred 𝓆 X → Pred _ X
    is-greatest-lowerbound s a = is-greatest (is-lowerbound s) a

    is-meet = is-greatest-lowerbound

    is-upperbound : Pred 𝓆 X → Pred _ X
    is-upperbound s a = {x : _} → (x∈s : s x) → x ≤ a

    is-leastupperbound : Pred 𝓆 X → Pred _ X
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

  ↑₁ : (x : X) → Pred 𝓅 X
  ↑₁ x u = x ≤ u

  ↑₂ : (x y : X) → Pred 𝓅 X
  ↑₂ x y u = x ≤ u & y ≤ u

  ↑ : Pred 𝓅 X → Pred (ℓ ⊔ 𝓅) X
  ↑ p u = ∀ x → p x → x ≤ u

  op : ≤-Set ℓ 𝓅
  ≤-Set.X op = X
  ≤-Set._≤_ op x y = y ≤ x

module Pointed≤-SetProps (pointedrelset : Pointed≤-Set ℓ 𝓅) where
  open Pointed≤-Set pointedrelset renaming (⊤ to pt)

  is-maximum : Prop _
  is-maximum = {x : _} → x ≤ pt

  is-minimum : Prop _
  is-minimum = {x : _} → pt ≤ x

module DeriveSymrel (relset : ≤-Set ℓ 𝓅) where
  open ≤-Set relset
  open ≤-SetProps relset

  infix 5 _≥_ _<_ _>_
  _≥_ = \x y → y ≤ x
  record _≈_ (a1 a2 : X) : Prop 𝓅 where
    field
      proj≤ : a1 ≤ a2
      proj≥ : a1 ≥ a2

  _<_ : Binrel 𝓅 X
  x < y = x ≤ y & (¬ x ≥ y)

  _>_ : Binrel 𝓅 X
  x > y = (¬ x ≤ y) & x ≥ y

  open _≈_ public

module _ {𝓅} {X : Set ℓ} where
  private
    module M = DeriveSymrel (mk≤-Set (Subset 𝓅 X) _⊆_)
  infix 2 _⊇_ _⊃_ _⊂_ _≅_
  _⊇_ = M._≥_
  _⊃_ = M._>_
  _⊂_ = M._<_
  _≅_ = M._≈_

module _ {𝓅} where
  private
    module M = DeriveSymrel (mk≤-Set (Prop 𝓅) (\ X Y → X → Y))
  infix 0 _←_  _←absurd_  _absurd→_ _↔_
  _←_ = M._≥_
  _absurd→_ = M._<_
  _←absurd_ = M._>_
  _↔_ = M._≈_

module _ {X : Set ℓ} {𝓅} where
  open DeriveSymrel (mk≤-Set (Pred 𝓅 X) _⇒_) public
    renaming (_≥_ to _⇐_; _<_ to _⇐⇐_; _>_ to _⇒⇒_ ; _≈_ to _⇔_)

⋈-assoc : {A B C D : Set ℓ}
  (rab : Subset ℓ (A × B)) (rbc : Subset ℓ (B × C)) (rcd : Subset ℓ (C × D))
  → ∀ x → ((rab ⋈ rbc) ⋈ rcd) x → (rab ⋈ (rbc ⋈ rcd)) x
⋈-assoc rab rbc rcd (a , d) (c , (b , ab∈rab , bc∈rbc) , cd∈rcd) = b , ab∈rab , (c , bc∈rbc , cd∈rcd)

Δ-lunit : {A B : Set ℓ}
  (rab : Subset ℓ (A × B)) → ∀ x → (Δ ⋈ rab) x → rab x
Δ-lunit rab (a , b) (.a , Id-refl , ab∈rab) = ab∈rab

module ≈≤-SetProps (2relset : ≈≤-Set ℓ 𝓅) where
  open ≈≤-Set 2relset
  module ≈ = ≤-SetProps (record { X = X ; _≤_ = _≈_})
  module ≤ = ≤-SetProps (record { X = X ; _≤_ = _≤_})

  is-weakantisymmetric = {a1 a2 : _} → (a1≤a2 : a1 ≤ a2) → (a2≤a1 : a2 ≤ a1) → a1 ≈ a2

  record is-partialorder : Prop (ℓ ⊔ 𝓅) where
    field
      equiv : ≈.is-equivalence
      preorder : ≤.is-preorder
      antisym : is-weakantisymmetric

  open is-partialorder public

record Proset ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mkProset
  field
    relset : ≤-Set ℓ 𝓅

  open ≤-Set relset public

  field
    ≤-preorder : ≤-SetProps.is-preorder relset

  module Preorder = ≤-SetProps.is-preorder ≤-preorder

module ProsetProps (proset : Proset ℓ 𝓅) where
  open Proset proset
  open ≤-SetProps (mk≤-Set X _≤_) public
  ≡⇒≤ : {x y : _} → x ≡ y → x ≤ y
  ≡⇒≤ Id-refl = Preorder.refl

record Setoid ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mkSetoid
  field
    relset : ≤-Set ℓ 𝓅
    ≈-equiv : ≤-SetProps.is-equivalence relset

  open ≤-Set relset renaming (_≤_ to _≈_) public
  module Equiv = ≤-SetProps.is-equivalence ≈-equiv

module _ (setoid : Setoid ℓ 𝓅) (setoid' : Setoid ℓ' 𝓅') where
  module S = Setoid setoid
  module S' = Setoid setoid'
  is-welldefind : Pred _ (S.X → S'.X)
  is-welldefind f = ∀ x x' → x S.≈ x' → f x S'.≈ f x'

record Posetoid ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mkPosetoid
  field
    2relset : ≈≤-Set ℓ 𝓅
  open ≈≤-Set 2relset public

  field
    ≈-≤-po : ≈≤-SetProps.is-partialorder 2relset

  module ≈-≤-po = ≈≤-SetProps.is-partialorder ≈-≤-po

module PosetoidProps (posetoid : Posetoid ℓ 𝓅) where
  open Posetoid posetoid

  proset : Proset ℓ 𝓅
  Proset.relset proset = mk≤-Set X _≤_
  Proset.≤-preorder proset = ≈-≤-po.preorder

  open ProsetProps proset public



DerivePosetoid : (proset : Proset ℓ 𝓅) → Posetoid ℓ 𝓅
DerivePosetoid proset = posetoid
  module DerivePosetoid where
    open Proset proset
    open DeriveSymrel (mk≤-Set X _≤_)
    open ≈≤-SetProps (record {X = X; _≤_ = _≤_ ; _≈_ = _≈_})
    open ≤.is-preorder (proset .Proset.≤-preorder)

    ≈-equiv : ≈.is-equivalence
    ≈-equiv .≈.preorder .≈.trans a1≈a2 a2≈a3 .proj≤ = trans (a1≈a2 .proj≤) (a2≈a3 .proj≤)
    ≈-equiv .≈.preorder .≈.trans a1≈a2 a2≈a3 .proj≥ = trans (a2≈a3 .proj≥) (a1≈a2 .proj≥)
    ≈-equiv .≈.preorder .≈.refl .proj≤ = refl
    ≈-equiv .≈.preorder .≈.refl .proj≥ = refl
    ≈-equiv .≈.sym a1≈a2 .proj≤ = a1≈a2 .proj≥
    ≈-equiv .≈.sym a1≈a2 .proj≥ = a1≈a2 .proj≤

    ≤-≈-antisym : is-weakantisymmetric
    ≤-≈-antisym a1≤a2 a2≤a1 .proj≤ = a1≤a2
    ≤-≈-antisym a1≤a2 a2≤a1 .proj≥ = a2≤a1

    posetoid : Posetoid _ _
    posetoid = mkPosetoid (mk≈≤-Set X _≈_ _≤_) \where
      .equiv → ≈-equiv
      .preorder → (proset .Proset.≤-preorder)
      .antisym → ≤-≈-antisym

record Poset ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mkPoset
  field
    relset : ≤-Set ℓ 𝓅
  open ≤-Set relset public

  field
    ≤-preo : ≤-SetProps.is-preorder relset
    ≤-antisym : ≤-SetProps.is-antisymmetric relset

  module ≤-preo = ≤-SetProps.is-preorder ≤-preo

module _ (relX : ≤-Set ℓ 𝓅) (relY : ≤-Set ℓ' 𝓅') where
  open ≤-Set relX renaming (X to X; _≤_ to _≤X_)
  open ≤-Set relY renaming (X to Y; _≤_ to _≤Y_)
  is-preserving : (f : X → Y) → Prop _
  is-preserving f = {a1 a2 : _} → (a1≤a2 : a1 ≤X a2) → f a1 ≤Y f a2

record PreservingFunction (relset : ≤-Set ℓ 𝓅) (relset' : ≤-Set ℓ' 𝓅') : Set (ℓ ⊔ ℓ' ⊔ 𝓅 ⊔ 𝓅') where
  constructor mkPreservingFunction
  open ≤-Set relset renaming (X to X; _≤_ to _≤X_)
  open ≤-Set relset' renaming (X to Y; _≤_ to _≤Y_)
  field
    f : X → Y
    preserving : is-preserving relset relset' f

module PreservingFunctionProp {X : ≤-Set ℓ 𝓅} {Y : ≤-Set ℓ' 𝓅'} {Z : ≤-Set ℓ'' 𝓅''}
  (pxy : PreservingFunction X Y) (pyz : PreservingFunction Y Z) where
  module pxy = PreservingFunction pxy
  module pyz = PreservingFunction pyz
  open PreservingFunction

  _∘_ : PreservingFunction X Z
  _∘_ .f x = pyz.f (pxy.f x)
  _∘_ .preserving r = pyz.preserving (pxy.preserving r)

module RelBinopSetProps (relbinopset : RelBinopSet ℓ 𝓅) where
  open RelBinopSet relbinopset renaming (_∧_ to _op_)
  open ≤-SetProps.BinaryProps (mk≤-Set X _≤_)

  is-meetclosed = (x x' : X) → is-meet x x' (x op x')
  is-joinclosed = (x x' : X) → is-join x x' (x op x')

module RelPowopSetProps (relpowopset : RelPowopSet ℓ 𝓅 𝓆) where
  open RelPowopSet relpowopset renaming (⋀ to Op)
  open ≤-SetProps.SubsetProps (mk≤-Set X _≤_)

  is-meetclosed = (p : Pred 𝓆 X) → is-meet p (Op p)
  is-joinclosed = (p : Pred 𝓆 X) → is-join p (Op p)

record MeetClosed ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mkMeetClosed
  field
    relbinopset : RelBinopSet ℓ 𝓅
    ∧-closed : RelBinopSetProps.is-meetclosed relbinopset

record CompleteMeetClosed ℓ 𝓅 𝓆 : Set (lsuc (ℓ ⊔ 𝓅 ⊔ lsuc 𝓆)) where
  constructor mkCompleteMeetClosed
  field
    relsubopset : RelPowopSet ℓ 𝓅 𝓆
  open RelPowopSet relsubopset public

  field
    ⋀-closed : RelPowopSetProps.is-meetclosed relsubopset

  module ⋀-closed s = ≤-SetProps.is-greatest (⋀-closed s) renaming (satisfies to lowerbound)


module CompleteMeetClosedProps (compmeetclosed : CompleteMeetClosed ℓ 𝓅 𝓆) where
  open CompleteMeetClosed compmeetclosed
  open ≤-SetProps

  ⋀-mono : ∀ p p' → p ⇒ p' → ⋀ p' ≤ ⋀ p
  ⋀-mono p p' p⇒p' = ⋀-closed.greatest p \ px → ⋀-closed.lowerbound p' (p⇒p' _ px)


record CompleteMeetSemilat ℓ 𝓅 𝓆 : Set (lsuc (ℓ ⊔ 𝓅 ⊔ lsuc 𝓆)) where
  constructor mkCompleteMeetSemilat
  field
    relsubopset : RelPowopSet ℓ 𝓅 𝓆

  open RelPowopSet relsubopset public

  field
    ⋀-closed : RelPowopSetProps.is-meetclosed relsubopset
    ≤-preorder : ≤-SetProps.is-preorder (mk≤-Set X _≤_)

  module ⋀-closed s = ≤-SetProps.is-greatest (⋀-closed s) renaming (satisfies to lowerbound)
  module ≤-preorder = ≤-SetProps.is-preorder ≤-preorder
  open DeriveSymrel (mk≤-Set X _≤_) public

module CompleteMeetSemilatProps (completemeetsemilat : CompleteMeetSemilat ℓ 𝓅 𝓅) where
  open CompleteMeetSemilat completemeetsemilat
  completemeetclosed : CompleteMeetClosed ℓ 𝓅 𝓅
  completemeetclosed = record { CompleteMeetSemilat completemeetsemilat }

  preorder : Proset ℓ 𝓅
  Proset.relset preorder = mk≤-Set X _≤_
  Proset.≤-preorder preorder = ≤-preorder

  posetoid = DerivePosetoid preorder

  open CompleteMeetClosedProps completemeetclosed public
  open PosetoidProps posetoid public hiding (preorder)

  ≈⋀↑₁ : ∀ x → x ≈ ⋀ (↑₁ x)
  ≈⋀↑₁ x .proj≤ = ⋀-closed.greatest (↑₁ x) idp
  ≈⋀↑₁ x .proj≥ = ⋀-closed.lowerbound (↑₁ x) ≤-preorder.refl

  ⋀-welldefined : ∀ s s' → s ⇔ s' → ⋀ s' ≈ ⋀ s
  ⋀-welldefined s s' s⇔s' .proj≤ = ⋀-mono s s' (s⇔s' .proj≤)
  ⋀-welldefined s s' s⇔s' .proj≥ = ⋀-mono s' s (s⇔s' .proj≥)

record StrictCompleteMeetSemilat ℓ 𝓅 𝓆 : Set (lsuc (ℓ ⊔ 𝓅 ⊔ lsuc 𝓆)) where
  constructor mkStrictCompleteMeetSemilat
  field
    relsubopset : RelPowopSet ℓ 𝓅 𝓆

  open RelPowopSet relsubopset public

  field
    ⋀-closed : RelPowopSetProps.is-meetclosed relsubopset
    ≤-po : ≤-SetProps.is-po (mk≤-Set X _≤_)

  module ⋀-closed s = ≤-SetProps.is-greatest (⋀-closed s) renaming (satisfies to lowerbound)
  module ≤-po = ≤-SetProps.is-po ≤-po
  open DeriveSymrel (mk≤-Set X _≤_) public

module StrictCompleteMeetSemilatProps (strictcompmeetsemilat : StrictCompleteMeetSemilat ℓ 𝓅 𝓆) where
  open StrictCompleteMeetSemilat strictcompmeetsemilat
  completemeetsemilat : CompleteMeetSemilat ℓ 𝓅 𝓆
  completemeetsemilat = record { StrictCompleteMeetSemilat strictcompmeetsemilat ; ≤-preorder = ≤-po.preorder }

module PointedRelBinopSetProps (ptrelbinopset : PointedRelBinopSet ℓ 𝓅) where
  open PointedRelBinopSet ptrelbinopset renaming (_∧_ to _op_ ; ⊤ to pt)
  open Pointed≤-SetProps (mkPointed≤-Set X pt _≤_)
  open RelBinopSetProps (mkRelBinopSet X _op_ _≤_)

  record is-bounded-meetclosed : Prop (lsuc (ℓ ⊔ 𝓅)) where
    field
      ∧-meet : is-meetclosed
      ⊤-maximum : is-maximum

  open is-bounded-meetclosed public

  record is-bounded-joinsemilattice : Prop (lsuc (ℓ ⊔ 𝓅)) where
    field
      ∨-join : is-joinclosed
      ⊥-minimum : is-minimum

  open is-bounded-joinsemilattice public

module 2PointedRel2BinopSetProps (2ptrel2binopset : 2PointedRel2BinopSet ℓ 𝓅) where
  open 2PointedRel2BinopSet 2ptrel2binopset
  module ∧-⊤-props = PointedRelBinopSetProps (mkPointedRelBinopSet X _∧_ ⊤ _≤_)
  module ∨-⊥-props = PointedRelBinopSetProps (mkPointedRelBinopSet X _∨_ ⊥ _≤_)

  record is-bounded-lattice : Prop (lsuc (ℓ ⊔ 𝓅)) where
    field
      ∧-⊤-semilattice : ∧-⊤-props.is-bounded-meetclosed
      ∨-⊥-semilattice : ∨-⊥-props.is-bounded-joinsemilattice

record BoundedMeetClosed ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mkBoundMeetClosed
  field
    ptrelbinopset : PointedRelBinopSet ℓ 𝓅
    bounded-meetclosed : PointedRelBinopSetProps.is-bounded-meetclosed ptrelbinopset

record BoundedJoinClosed ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mkBoundJoinClose
  field
    ptrelbinopset : PointedRelBinopSet ℓ 𝓅
    bounded-joinsemilattice : PointedRelBinopSetProps.is-bounded-joinsemilattice ptrelbinopset

module PointedRelPowopSetProps (ptrelsubopset : PointedRelPowopSet ℓ 𝓅 𝓆) where
  open PointedRelPowopSet ptrelsubopset renaming (⋀ to Op ; ⊤ to pt)
  open Pointed≤-SetProps (mkPointed≤-Set X pt _≤_)
  open RelPowopSetProps (mkRelPowopSet X Op _≤_)

  record is-bounded-meetclosed : Prop (lsuc (ℓ ⊔ 𝓅 ⊔ lsuc 𝓆)) where
    field
      ⋀-meet : is-meetclosed
      ⊤-maximum : is-maximum

  open is-bounded-meetclosed public

  record is-bounded-joinclosed : Prop (lsuc (ℓ ⊔ 𝓅 ⊔ lsuc 𝓆)) where
    field
      ⋁-join : is-joinclosed
      ⊥-minimum : is-minimum

  open is-bounded-joinclosed public

module DeriveBinop {ℓ} {𝓅} (powopset : PowopSet ℓ (ℓ ⊔ 𝓅)) where
  open PowopSet powopset

  infixr 10 _∧_
  _∧_ : X → X → X
  _∧_ a1 a2 = ⋀ \ x → (Idp (ℓ ⊔ 𝓅) x a1 ∥ Idp (ℓ ⊔ 𝓅) x a2)

module 2PointedRel2PowopSetProps (2pointedrel2subopset : 2PointedRel2PowopSet ℓ 𝓅 𝓆) where
  open 2PointedRel2PowopSet 2pointedrel2subopset
  open PointedRelPowopSetProps (mkPointedRelPowopSet X ⊤ ⋀ _≤_) using (is-bounded-meetclosed)
  open PointedRelPowopSetProps (mkPointedRelPowopSet X ⊥ ⋁ _≤_) using (is-bounded-joinclosed)

  record is-complete-closed : Prop (lsuc (ℓ ⊔ 𝓅 ⊔ lsuc 𝓆)) where
    field
      ⋀-⊤-closed : is-bounded-meetclosed
      ⋁-⊥-closed : is-bounded-joinclosed
  open is-complete-closed public

record BoundedClosed ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor mkBoundedClosed
  field
    2pointedrel2binopset : 2PointedRel2BinopSet ℓ 𝓅
    boundedlattice : 2PointedRel2BinopSetProps.is-bounded-lattice 2pointedrel2binopset

record CompleteClosed ℓ 𝓅 𝓆 : Set (lsuc (ℓ ⊔ 𝓅 ⊔ lsuc 𝓆)) where
  constructor mkCompleteClosed
  field
    2pointedrel2subopset : 2PointedRel2PowopSet ℓ 𝓅 𝓆
  open 2PointedRel2PowopSet 2pointedrel2subopset public
  field
    ⋀-⋁-closed : 2PointedRel2PowopSetProps.is-complete-closed 2pointedrel2subopset

  module ⋀-⋁-closed = 2PointedRel2PowopSetProps.is-complete-closed ⋀-⋁-closed
  module ⋀-⊤-closed = PointedRelPowopSetProps.is-bounded-meetclosed (⋀-⋁-closed.⋀-⊤-closed)
  module ⋁-⊥-closed = PointedRelPowopSetProps.is-bounded-joinclosed (⋀-⋁-closed.⋁-⊥-closed)
  module ⋀-meet s = ≤-SetProps.is-greatest (⋀-⊤-closed.⋀-meet s) renaming (satisfies to lowerbound)
  module ⋁-join s = ≤-SetProps.is-least (⋁-⊥-closed.⋁-join s) renaming (satisfies to upperbound)

record StrictCompleteLattice ℓ 𝓅 𝓆 : Set (lsuc (ℓ ⊔ 𝓅 ⊔ lsuc 𝓆)) where
  constructor mkStrictCompleteLatticeCompleteLattice
  field
    2pointedrel2subopset : 2PointedRel2PowopSet ℓ 𝓅 𝓆

  open 2PointedRel2PowopSet 2pointedrel2subopset public
  field
    ⋀-⋁-closed : 2PointedRel2PowopSetProps.is-complete-closed 2pointedrel2subopset
    ≤-po : ≤-SetProps.is-po (mk≤-Set X _≤_)

record CompleteHeytingAlgebra ℓ 𝓅 : Set (lsuc (lsuc (ℓ ⊔ 𝓅))) where
  constructor mkCompHA
  field
    2pointedrel2subopbinopset : 2PointedRel2PowopBinopSet ℓ (ℓ ⊔ 𝓅) (ℓ ⊔ 𝓅)

  open 2PointedRel2PowopBinopSet 2pointedrel2subopbinopset public
  field
    ⋀-⋁-closed : 2PointedRel2PowopSetProps.is-complete-closed (mk2PointedRel2PowopSet X ⊥ ⊤ ⋀ ⋁ _≤_)
    ≤-po : ≤-SetProps.is-po (mk≤-Set X _≤_)

  open DeriveBinop {𝓅 = 𝓅} (mkPowopSet X ⋀)
  field
    ∧-⊢-iso : ∀ x a b → (x ∧ a) ≤ b ↔ x ≤ (a ⊢ b)

DeriveCompleteClosed : (complete-meet-semilattice : CompleteMeetClosed ℓ (ℓ ⊔ 𝓅) (ℓ ⊔ 𝓅)) → CompleteClosed ℓ (ℓ ⊔ 𝓅) (ℓ ⊔ 𝓅)
DeriveCompleteClosed {ℓ = ℓ} {𝓅 = 𝓅} complete-meet-semilattice = complete-closed
  module DeriveCompleteClosed where
    open CompleteMeetClosed complete-meet-semilattice
    open RelPowopSetProps
    open ≤-SetProps
    open Pointed≤-SetProps

    ⋁ : Pred (ℓ ⊔ 𝓅) X → X
    ⋁ s = ⋀ (\ x → (∀ x' → s x' → x' ≤ x))

    ⊥ = ⋀ ptrue'
    ⊤ = ⋀ pfalse'

    open 2PointedRel2PowopSetProps
    open PointedRelPowopSetProps.is-bounded-meetclosed
    open PointedRelPowopSetProps.is-bounded-joinclosed
    open is-complete-closed
    open CompleteClosed using (2pointedrel2subopset ; ⋀-⋁-closed)

    complete-closed : CompleteClosed _ _ _
    complete-closed .2pointedrel2subopset = mk2PointedRel2PowopSet X ⊥ ⊤ ⋀ ⋁ _≤_
    complete-closed .⋀-⋁-closed .⋀-⊤-closed .⋀-meet = ⋀-closed
    complete-closed .⋀-⋁-closed .⋀-⊤-closed .⊤-maximum = ⋀-closed.greatest _ \()
    complete-closed .⋀-⋁-closed .⋁-⊥-closed .⋁-join s .satisfies x∈s = ⋀-closed.greatest _ \ x∈↑s → x∈↑s _ x∈s
    complete-closed .⋀-⋁-closed .⋁-⊥-closed .⋁-join s .least x∈↓s = ⋀-closed.lowerbound _ \ _ x∈s → x∈↓s x∈s
    complete-closed .⋀-⋁-closed .⋁-⊥-closed .⊥-minimum = ⋀-closed.lowerbound _ _

DeriveStrictCompleteLattice : (strictcompletemeetsemilat : StrictCompleteMeetSemilat ℓ (ℓ ⊔ 𝓅) (ℓ ⊔ 𝓅)) → StrictCompleteLattice ℓ (ℓ ⊔ 𝓅) (ℓ ⊔ 𝓅)
DeriveStrictCompleteLattice {ℓ = ℓ} {𝓅 = 𝓅} strictcompletemeetsemilat = strict-complete-lattice
  module DeriveStrictCompleteLattice where
    open StrictCompleteMeetSemilat strictcompletemeetsemilat
    open StrictCompleteMeetSemilatProps strictcompletemeetsemilat
    open CompleteMeetSemilatProps completemeetsemilat
    completeclosed : CompleteClosed ℓ (ℓ ⊔ 𝓅) (ℓ ⊔ 𝓅)
    completeclosed = DeriveCompleteClosed {ℓ = ℓ} {𝓅 = 𝓅} completemeetclosed

    strict-complete-lattice : StrictCompleteLattice ℓ (ℓ ⊔ 𝓅) (ℓ ⊔ 𝓅)
    strict-complete-lattice = record { CompleteClosed completeclosed ; ≤-po = ≤-po}

-- DeriveSemilattice : (complete-semilattice : CompleteMeetSemilattice ℓ 𝓅 𝓆) → BoundedMeetSemilattice ℓ (ℓ

module Endo (setoid : Setoid ℓ 𝓅) where
  open Setoid setoid renaming (_≈_ to _≈_)
  EndoFunction : Set _
  EndoFunction = PreservingFunction (mk≤-Set X _≈_) (mk≤-Set X _≈_)

  FixedPoint : EndoFunction → Pred _ X
  FixedPoint endo x = f x ≈ x
    where open PreservingFunction endo renaming (f to f)

module Endo≤ (proset : Proset ℓ 𝓅) where
  open Proset proset
  MonotoneEndoFunction = PreservingFunction relset relset

  PostfixPoint : MonotoneEndoFunction → Pred _ X
  PostfixPoint endo x = f x ≤ x
    where open PreservingFunction endo renaming (f to f)

  PrefixPoint : MonotoneEndoFunction → Pred _ X
  PrefixPoint endo x = x ≤ f x
    where open PreservingFunction endo renaming (f to f)

  open Posetoid (DerivePosetoid proset)
  open Endo (mkSetoid (mk≤-Set _ _≈_) ≈-≤-po.equiv) public

  DeriveEndo : MonotoneEndoFunction → EndoFunction
  DeriveEndo mono = endo
    module DeriveEndo where
      open DeriveSymrel
      open PreservingFunction mono
      endo : EndoFunction
      endo .f = f
      endo .preserving a1≈a2 .proj≤ = preserving (a1≈a2 .proj≤)
      endo .preserving a1≈a2 .proj≥ = preserving (a1≈a2 .proj≥)

module EndoRel (proset : Proset ℓ 𝓅) where
  open Posetoid (DerivePosetoid proset)
  open Endo≤ proset public

  module _ (e : EndoFunction) where
    LeastFixedPoint : Pred _ X
    LeastFixedPoint = ≤-SetProps.is-least (mk≤-Set X _≤_) (FixedPoint e)

    GreatestFixedPoint : Pred _ X
    GreatestFixedPoint = ≤-SetProps.is-greatest (mk≤-Set X _≤_) (FixedPoint e)

module Fixpoints (completemeetsemilattice : CompleteMeetClosed ℓ (ℓ ⊔ 𝓅) (ℓ ⊔ 𝓅)) where
  open CompleteClosed (DeriveCompleteClosed {ℓ = ℓ} {𝓅 = 𝓅} completemeetsemilattice)

  ⋀-monotone : ∀ s s' → (s⊆s' : s ⇒ s') → ⋀ s' ≤ ⋀ s
  ⋀-monotone s s' s⊆s' = ⋀-meet.greatest s \ x∈s → ⋀-meet.lowerbound s' (s⊆s' _ x∈s)

  ⋁-monotone : ∀ s s' → (s⊆s' : s ⇒ s') → ⋁ s ≤ ⋁ s'
  ⋁-monotone s s' s⊆s' = ⋁-join.least s \ x∈s → ⋁-join.upperbound s' (s⊆s' _ x∈s)

  module _ (preorder : ≤-SetProps.is-preorder (mk≤-Set X _≤_)) where
    private
      X≤ = (mk≤-Set X _≤_)
      module X≤ = ≤-SetProps X≤

    open EndoRel (mkProset X≤ preorder)
    module _ (m : MonotoneEndoFunction) where
      open PreservingFunction m renaming (f to f)
      open DeriveSymrel X≤
      f[⋀post]∈↓post : X≤.SubsetProps.is-lowerbound (PostfixPoint m) (f (⋀ (PostfixPoint m)))
      f[⋀post]∈↓post x∈s = preserving (⋀-meet.lowerbound _ x∈s) ∙ x∈s
        where open X≤.is-preorder preorder renaming (trans to _∙_)

      private e = DeriveEndo m

      lfp⋀post :  LeastFixedPoint e (⋀ (PostfixPoint m))
      lfp⋀post .X≤.satisfies .proj≤ = ⋀-meet.greatest (PostfixPoint m) f[⋀post]∈↓post
      lfp⋀post .X≤.satisfies .proj≥ = ⋀-meet.lowerbound (PostfixPoint m) (preserving (⋀-meet.greatest (PostfixPoint m) f[⋀post]∈↓post))
      lfp⋀post .X≤.least x∈s = ⋀-meet.lowerbound (PostfixPoint m) (x∈s .proj≤)

      ⋀fix≈⋀post : ⋀ (FixedPoint e) ≈ ⋀ (PostfixPoint m)
      ⋀fix≈⋀post .proj≤ = ⋀-meet.lowerbound (FixedPoint e) \where
        .proj≤ → ⋀-meet.greatest (PostfixPoint m) f[⋀post]∈↓post
        .proj≥ → ⋀-meet.lowerbound (PostfixPoint m) (preserving (⋀-meet.greatest (PostfixPoint m) f[⋀post]∈↓post))
      ⋀fix≈⋀post .proj≥ = ⋀-monotone (FixedPoint e) (PostfixPoint m) \ x x∈fix → x∈fix .proj≤

record RelConnection ℓ ℓ' 𝓅 𝓅' : Set (lsuc (ℓ ⊔ ℓ' ⊔ 𝓅' ⊔ 𝓅)) where
  field
    C : ≤-Set ℓ 𝓅
    D : ≤-Set ℓ' 𝓅'
    L : PreservingFunction D C
    R : PreservingFunction C D
  module C = ≤-Set C
  module D = ≤-Set D
  module R = PreservingFunction R
  module L = PreservingFunction L

  field
    L-transpose : (c : C.X) (d : D.X) → (d D.≤ R.f c) → (L.f d C.≤ c)
    R-transpose : (c : C.X) (d : D.X) → (L.f d C.≤ c) → (d D.≤ R.f c)

record GaloisConnection ℓ ℓ' 𝓅 𝓅' : Set (lsuc (ℓ ⊔ ℓ' ⊔ 𝓅' ⊔ 𝓅)) where
  field
    C : Proset ℓ 𝓅
    D : Proset ℓ' 𝓅'

  module C = Proset C
  module D = Proset D

  field
    L : PreservingFunction D.relset C.relset
    R : PreservingFunction C.relset D.relset
  module R = PreservingFunction R
  module L = PreservingFunction L

  field
    L-transpose : (c : C.X) (d : D.X) → (d D.≤ R.f c) → (L.f d C.≤ c)
    R-transpose : (c : C.X) (d : D.X) → (L.f d C.≤ c) → (d D.≤ R.f c)

module PropHeytingAlgebra {ℓ} where
  struct : 2PointedRel3BinopSet (lsuc ℓ) ℓ
  2PointedRel3BinopSet.X struct = Prop ℓ
  2PointedRel3BinopSet.⊥ struct = pfalse
  2PointedRel3BinopSet.⊤ struct = ptrue
  2PointedRel3BinopSet._∧_ struct = _&_
  2PointedRel3BinopSet._∨_ struct = _∥_
  2PointedRel3BinopSet._⊢_ struct = \ X Y → X → Y
  2PointedRel3BinopSet._≤_ struct = \ X Y → X → Y

  open 2PointedRel3BinopSet struct hiding (X)
  open DeriveSymrel (mk≤-Set (Prop ℓ) _≤_)
  α : ∀ (a b c : Prop ℓ) → (a ∧ b ≤ c) ↔ (a ≤ b ⊢ c)
  α a b c .proj≤ a∧b≤c pa pb = a∧b≤c (pa , pb)
  α a b c .proj≥ a≤b⊢c (pa , pb) = a≤b⊢c pa pb

module PowersetHytingAlgebra {𝓅} (X : Set ℓ) where
  2ptrel2binopset : 2PointedRel3BinopSet (lsuc 𝓅 ⊔ ℓ) (𝓅 ⊔ ℓ)
  2PointedRel3BinopSet.X 2ptrel2binopset = Pred 𝓅 X
  2PointedRel3BinopSet._∧_ 2ptrel2binopset = _&'_
  2PointedRel3BinopSet._∨_ 2ptrel2binopset = _∥'_
  2PointedRel3BinopSet.⊤ 2ptrel2binopset = ptrue'
  2PointedRel3BinopSet.⊥ 2ptrel2binopset = pfalse'
  2PointedRel3BinopSet._⊢_ 2ptrel2binopset = \ P Q x → P x → Q x
  2PointedRel3BinopSet._≤_ 2ptrel2binopset = _⇒_

  open 2PointedRel3BinopSet 2ptrel2binopset hiding (X)
  open DeriveSymrel (mk≤-Set (Pred 𝓅 X) _≤_)
  α : ∀ (a b c : _) → (a ∧ b ≤ c) ↔ (a ≤ b ⊢ c)
  α a b c .proj≤ a∧b≤c x ax bx = a∧b≤c x (ax , bx)
  α a b c .proj≥ a≤b⊢c x (ax , bx) = a≤b⊢c x ax bx
  open BoundedClosed
