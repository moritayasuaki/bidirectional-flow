{-# OPTIONS --type-in-type --postfix-projections #-}

module Continuity where

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
open import Bidirection

record ContLat : Set where
  field
    Carrier : Set
    _≈_ : Rel Carrier
    _≤_ : Rel Carrier
    ≤-po : IsPartialOrder _≈_ _≤_

  poset : Poset
  poset = record {isPartialOrder = ≤-po}

  module Po = PosetPoly poset
  module Eq = Po.Eq

  setoid : Setoid
  setoid = Eq.setoid

  field
    ⨆ :  Pred Eq.setoid → Carrier
    _⊓_ : Op₂ Carrier
    ⊤ : Carrier
    ⊓-inf : Infimum _≤_ _⊓_
    ⊤-max : Maximum _≤_ ⊤
    ⨆-sup : ∀ S → (∀ x → x ∈ S → x ≤ ⨆ S) × (∀ y → (∀ x → x ∈ S → x ≤ y) → ⨆ S ≤ y)

  slat : SLat
  slat = record {≤-po = ≤-po ; ⊓-inf = ⊓-inf ; ⊤-max = ⊤-max ; ⨆-sup = ⨆-sup}

  open SLat slat hiding (Carrier ; _≈_ ; _≤_ ; ⨆ ; _⊓_ ; ⊤)

  field
    continuous : ∀ x → Σ S ∶ (Pred setoid) , ((⨆ S ≈ x) × (∀ y → y ∈ S → IsCompact y))
