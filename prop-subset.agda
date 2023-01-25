{-# OPTIONS --prop --safe #-}

open import Agda.Primitive
open import Agda.Builtin.Nat
module prop-subset where

private
  variable
    𝓅 𝓅'  𝓆 𝓆' 𝓇 𝓇' : Level
    ℓ ℓ' : Level

data Fin : Nat → Set where
  fzero : ∀{n} → Fin (suc n)
  fsuc : ∀{n} → Fin n → Fin (suc n)

pattern #0 = fzero
pattern #1 = fsuc #0
pattern #2 = fsuc #1
pattern #3 = fsuc #2

plist :  (n : Nat) → (Fin n → Prop 𝓅) → Prop 𝓅
plist n props = ∀ ith → props ith

data False {ℓ} : Prop ℓ where

record True {ℓ} : Prop ℓ where

_≤Nat_ : Nat → Nat → Prop
zero ≤Nat _ = True
suc m ≤Nat zero = True
suc m ≤Nat suc n = m ≤Nat n

record _&_  (X : Prop 𝓅) (Y : Prop 𝓆) : Prop (𝓅 ⊔ 𝓆) where
  constructor _,_
  field
    fst : X
    snd : Y

data _∪_ (X : Prop 𝓅) (Y : Prop 𝓆) : Prop (𝓅 ⊔ 𝓆) where
  left : X → X ∪ Y
  right : Y → X ∪ Y
open _&_

infixr 10 _,_
record Σ {ℓ ℓ'} (A : Set ℓ) (B : A → Set ℓ') : Set (lsuc (ℓ ⊔ ℓ')) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ

_equipped-with_ = Σ

_×_ : Set ℓ → Set ℓ' → Set (lsuc (ℓ ⊔ ℓ'))
A × B = Σ A \_ → B

record Subtype (A : Set ℓ) (P : A → Prop 𝓅) : Set (ℓ ⊔ lsuc 𝓅) where
  constructor _with-property_
  field
    component : A
    property : P component

_such-that_ = Subtype

∣_∣ : Set ℓ → Prop (ℓ ⊔ lsuc 𝓅)
∣_∣ {𝓅 = 𝓅} T = ∀ (P : Prop 𝓅) → (T → P) → P

lift : ∀ 𝓆 → Prop 𝓅 → Prop (𝓅 ⊔ 𝓆)
lift 𝓆 P = {True {𝓆}} → P

∃ : {A : Set ℓ} → (P : A → Prop 𝓅) → Prop (lsuc (ℓ ⊔ lsuc 𝓅))
∃ {A = A} P = ∣ Subtype A P ∣


module _ (A : Set ℓ) where
  Point = A
  Nulop = A
  Uniop = A → A
  Binop = A → A → A

module _ (𝓅) (A : Set ℓ) where
  Pred = A → Prop 𝓅
  Rel = A → A → Prop 𝓅

  Subop = Pred → A


liftPred : ∀ 𝓆 {A : Set ℓ} → Pred 𝓅 A → Pred (𝓅 ⊔ 𝓆) A
liftPred 𝓆 P x = lift 𝓆 (P x)

liftSubop : ∀ 𝓅 {𝓆} {A : Set ℓ} → Subop (𝓅 ⊔ 𝓆) A → Subop 𝓆 A
liftSubop 𝓅 ⋀ s = ⋀ (liftPred 𝓅 s)

Structure : ∀ ℓ ℓ' → Set _
Structure ℓ ℓ' = Set ℓ → Set ℓ'
_⟨×⟩_ : ∀{ℓ ℓ' ℓ''} →  Structure ℓ ℓ' → Structure ℓ ℓ'' → Structure ℓ _
($1 ⟨×⟩ $2) = \ X → $1 X × $2 X

{-
record RelSet ℓ 𝓅 : Set (lsuc (ℓ ⊔ 𝓅)) where
  constructor [_,_]
  field
    carrier : Set ℓ
    _≤_ : Rel 𝓅 carrier
-}

RelSet : ∀ ℓ 𝓅 → Set _
RelSet ℓ 𝓅 = Set ℓ equipped-with (Rel 𝓅)

2RelSet : ∀ ℓ 𝓅 → Set _
2RelSet ℓ 𝓅 = Set ℓ equipped-with (Rel 𝓅 ⟨×⟩ Rel 𝓅)

RelSubopSet : ∀ ℓ 𝓅 𝓆 → Set _
RelSubopSet ℓ 𝓅 𝓆 = Set ℓ equipped-with (Rel 𝓅 ⟨×⟩ Subop 𝓆)

PointedSet : ∀ ℓ → Set _
PointedSet ℓ = Set ℓ equipped-with Point

PointedRelSet : ∀ ℓ 𝓅 → Set _
PointedRelSet ℓ 𝓅 = Set ℓ equipped-with (Point ⟨×⟩ Rel 𝓅)

module _ (A-r @ (A , _~_) : RelSet ℓ 𝓅) where
  Transitive = {a1 a2 a3 : A} → (a1~a2 : a1 ~ a2) → (a2~a3 : a2 ~ a3) → a1 ~ a3
  Reflexive = {a : A} → a ~ a
  Symmetric = {a1 a2 : A} → (a1~a2 : a1 ~ a2) → a2 ~ a1

  record Preorder : Prop (ℓ ⊔ 𝓅) where
    field
      trans : Transitive
      refl : Reflexive

  open Preorder public

  record Equivalence : Prop (ℓ ⊔ 𝓅) where
    field
      preorder : Preorder
      sym : Symmetric

  open Equivalence public


module SymPair (A-r @ (A , _≤_) : RelSet ℓ 𝓅) where
  record _≈_ (a1 a2 : A) : Prop 𝓅 where
    field
      id : a1 ≤ a2
      inv : a2 ≤ a1

  open _≈_ public

module _ (A-2r @ (A , _≈_ , _≤_) : 2RelSet ℓ 𝓅) where

  AntiSymmetric = {a1 a2 : _} → (a1≤a2 : a1 ≤ a2) → (a2≤a1 : a2 ≤ a1) → a1 ≈ a2

  record PartialOrder : Prop (ℓ ⊔ 𝓅) where
    field
      equiv : Equivalence (A , _≈_)
      preorder : Preorder (A , _≤_)
      antisym : AntiSymmetric

  open PartialOrder public

module _ (A-2r @ (A , _≤_) : RelSet ℓ 𝓅) where
  open SymPair (A , _≤_)

  symmetric-pair-equiv : Preorder (A , _≤_) → Equivalence (A , _≈_)
  symmetric-pair-equiv ≤-preorder = \where
    .preorder .trans a1~a2 a2~a3 .id → ≤-preorder .trans (a1~a2 .id) (a2~a3 .id) -- transitivity
    .preorder .trans a1~a2 a2~a3 .inv → ≤-preorder .trans (a2~a3 .inv) (a1~a2 .inv) -- transitivity
    .preorder .refl .id → ≤-preorder .refl -- reflexivity
    .preorder .refl .inv → ≤-preorder .refl -- reflexivity
    .sym a1~a2 .id → a1~a2 .inv -- symmetry
    .sym a1~a2 .inv → a1~a2 .id -- symmetry

  preorder-to-partialorder : Preorder (A , _≤_) → PartialOrder (A , _≈_ , _≤_)
  preorder-to-partialorder ≤-preorder = \where
    .equiv → symmetric-pair-equiv ≤-preorder -- equivalence
    .preorder → ≤-preorder -- preorder
    .antisym a1≤a2 a2≤a1 .id → a1≤a2 --
    .antisym a1≤a2 a2≤a1 .inv → a2≤a1 --

Preord : ∀ ℓ 𝓅 → Set _
Preord ℓ 𝓅 = RelSet ℓ 𝓅 such-that Preorder

Setoid : ∀ ℓ 𝓅 → Set _
Setoid ℓ 𝓅 = RelSet ℓ 𝓅 such-that Equivalence

Poset : ∀ ℓ 𝓅 → Set _
Poset ℓ 𝓅 = 2RelSet ℓ 𝓅 such-that PartialOrder

module _ (A-r @ (A , _≤A_) : RelSet ℓ 𝓅) (B-r @ (B , _≤B_) : RelSet ℓ' 𝓅')  where
  RelPreserving : (f : A → B) → Prop _
  RelPreserving f = {a1 a2 : _} → (a1≤a2 : a1 ≤A a2) → f a1 ≤B f a2

RelPreservingFun : RelSet ℓ 𝓅 → RelSet ℓ' 𝓅' → Set _
RelPreservingFun (A-r @ (A , _≤A_)) (B-r @(B , _≤B_)) = (A → B) such-that RelPreserving A-r B-r

module _ (A-rs @ (A , _≤_) : RelSet ℓ 𝓅) where
  LowerBound : ∀{𝓆} → Pred 𝓆 A → A → Prop _
  LowerBound s a =  {x : _} → (x∈s : s x) → a ≤ x

module _ {𝓆 : Level} (A-rs @ (A , _≤_) : RelSet ℓ 𝓅) where
  record Greatest (s : Pred 𝓆 A) (a : A) : Prop (ℓ ⊔ 𝓆 ⊔ 𝓅) where
    field
      belongs : s a
      greatest : {x : _} → (x∈s : s x) → x ≤ a
  open Greatest public

module _ (A-rs @ (A , _≤_) : RelSet ℓ 𝓅) where
  GreatestLowerBound : Pred 𝓆 A → A → Prop _
  GreatestLowerBound s a =  Greatest A-rs (LowerBound A-rs s) a
  Meet = GreatestLowerBound

module _ (A-rs @ (A , _≤_) : RelSet ℓ 𝓅) where
  UpperBound : ∀{𝓆} → Pred 𝓆 A → A → Prop _
  UpperBound s a = {x : _} → (x∈s : s x) → x ≤ a
  record Least (s : Pred 𝓆 A) (a : A) : Prop (ℓ ⊔ 𝓆 ⊔ 𝓅) where
    field
      belongs : s a
      least : {x : _} → (x∈s : s x) → a ≤ x
  open Least public

module _ (A-rs @ (A , _≤_) : RelSet ℓ 𝓅) where
  LeastUpperBound : ∀ {𝓆} → Pred 𝓆 A → A → Prop _
  LeastUpperBound s a = Least A-rs (UpperBound A-rs s) a

  Join = LeastUpperBound

  LowerBound2 = \(x y a : A) → (a ≤ x) & (a ≤ y)
  GreatestLowerBound2 = \(x y a : A) → LowerBound2 x y a & ∀ z → LowerBound2 x y z → z ≤ a
  UpperBound2 = \(x y a : A) → (x ≤ a) & (y ≤ a)
  LeastUpperBound2 = \(x y a : A) → UpperBound2 x y a & ∀ z → UpperBound2 x y z → a ≤ z

module _ (A-pr @ (A , p , _≤_) : PointedRelSet ℓ 𝓅)  where
  Minimum = (x : _) → p ≤ x
  Maximum = (x : _) → x ≤ p

module _ {𝓆} (A-rsop @ (A , _≤_ , ⋀) : RelSubopSet ℓ 𝓅 𝓆) where
  MeetClosed = (s : Pred 𝓆 A) → Meet (A , _≤_) s (⋀ s)

module _ {𝓆} (A-rsop @ (A , _≤_ , ⋁) : RelSubopSet ℓ 𝓅 𝓆) where
  JoinClosed = (s : Pred 𝓆 A) → Join (A , _≤_) s (⋁ s)

module DeriveBinaryOp (A-sop @ (A , _≈_ , ⋀) : RelSubopSet ℓ 𝓅 𝓅) where
  _∧_ : A → A → A
  a1 ∧ a2 = ⋀ \ x → ((x ≈ a1) ∪ (x ≈ a2))

module DeriveCompleteLattice {𝓅} (A-rsop @ (A , _≤_ , ⋀) : RelSubopSet ℓ (ℓ ⊔ 𝓅) (ℓ ⊔ 𝓅)) (⋀-meet : MeetClosed A-rsop) where
  ⋁ : Pred (ℓ ⊔ 𝓅) A → A
  ⋁ s = ⋀ (UpperBound (A , _≤_) {𝓆 = ℓ ⊔ 𝓅} s)
  ⊥ = ⋀ \_ → True
  ⊤ = ⋀ \_ → False

  ⋁-join : JoinClosed (A , _≤_ , ⋁)
  ⋁-join s .belongs x∈s = ⋀-meet (UpperBound (A , _≤_) s) .greatest \ x∈↑s → x∈↑s x∈s
  ⋁-join s .least x∈↓s = ⋀-meet (UpperBound (A , _≤_) s) .belongs \ x∈s → x∈↓s x∈s

  ⊥-minimum : Minimum (A , ⊥ , _≤_)
  ⊥-minimum _ = ⋀-meet _ .belongs _

  ⊤-maximum : Maximum (A , ⊤ , _≤_)
  ⊤-maximum _ = ⋀-meet _ .greatest \()

  -- open SymPair (A , _≤_)

MeetSemilattice : ∀ ℓ 𝓅 𝓆 → Set _
MeetSemilattice ℓ 𝓅 𝓆 = Subtype (RelSubopSet ℓ 𝓅 𝓆) \where
  (A , _≤_ , ⋀) → Preorder (A , _≤_) & MeetClosed (A , _≤_ , ⋀)

module _ {ℓ} {𝓅} (A-meetclosed @ ((A , _≤_ , ⋀) with-property (≤-preorder , ⋀-meet)) : MeetSemilattice ℓ (𝓅 ⊔ ℓ) (𝓅 ⊔ ℓ))
  (let 𝓊 = (𝓅 ⊔ ℓ))
  (f-rp @ (f with-property f-mono) : RelPreservingFun (A , _≤_) (A , _≤_))
  where
  open SymPair (A , _≤_)
  ⋀-mono : {s s' : Pred 𝓊 A} → (s⊆s' : {a : A} → s a → s' a) → ⋀ s' ≤ ⋀ s
  ⋀-mono s⊆s' = ⋀-meet _ .greatest \ x∈s → ⋀-meet _ .belongs (s⊆s' x∈s)

  FixedPoint : Pred (ℓ ⊔ 𝓅) A
  FixedPoint = \ x → f x ≈ x

  LeastFixedPoint : Pred (ℓ ⊔ 𝓅) A
  LeastFixedPoint = Least (A , _≤_) FixedPoint

  PostfixPoint : Pred (𝓅 ⊔ ℓ) A
  PostfixPoint = \ x → f x ≤ x

  PrefixPoint : Pred (ℓ ⊔ 𝓅)  A
  PrefixPoint = \ x → x ≤ f x

  -- ∀ x ∈ { x | f x ≤ x } , f (⋀ { x | f x ≤ x}) ≤ f x ≤ x
  f⋀postfp∈↓postfp : LowerBound (A , _≤_) PostfixPoint (f (⋀ PostfixPoint ))
  f⋀postfp∈↓postfp x∈postfp = ≤-preorder .trans
    (f-mono (⋀-meet _ .belongs x∈postfp))
    x∈postfp

  -- lfp f
  lfp-⋀-post : LeastFixedPoint (⋀ PostfixPoint)
  lfp-⋀-post .belongs .id = ⋀-meet _ .greatest f⋀postfp∈↓postfp
  lfp-⋀-post .belongs .inv = ⋀-meet _ .belongs (f-mono (⋀-meet _ .greatest f⋀postfp∈↓postfp))
  lfp-⋀-post .least x∈s = ⋀-meet _ .belongs (x∈s .id)

  ⋀fix≈⋀post : ⋀ FixedPoint ≈ ⋀ PostfixPoint
  ⋀fix≈⋀post .id = ⋀-meet _ .belongs \where
    .id → ⋀-meet _ .greatest f⋀postfp∈↓postfp
    .inv → ⋀-meet _ .belongs (f-mono (⋀-meet _ .greatest f⋀postfp∈↓postfp))
  ⋀fix≈⋀post .inv = ⋀-mono \ fx≈x → fx≈x .id

