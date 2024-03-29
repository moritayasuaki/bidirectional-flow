{-# OPTIONS --type-in-type --postfix-projections #-}

module RelationComposition  where

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
open import Data.List.Relation.Unary.All
open import Relation.Binary.Consequences using (mono⇒cong)
open import Base
open import Bidirection

module _ where
  module _ (C⨆ D⨆ : SLat) where

    private
      C≤ = SLat.poset C⨆
      C≈ = SLat.Eq.setoid C⨆
      C = ∣ C⨆ ∣
      module C = SLat C⨆
      D≤ = SLat.poset D⨆
      D≈ = SLat.Eq.setoid D⨆
      D = ∣ D⨆ ∣
      module D = SLat D⨆

    mono→tbt-conn : (P : Pred (C≈ ×-setoid D≈)) → IsMonotoneRelation C⨆ D⨆ P → IsTiltedBowTieConnecting C⨆ D⨆ P
    mono→tbt-conn P P-mono c d c₀ d₀ d₁ tbt@(c₀≤c , d₀≤d , d≤d₁ , c₀d₁∈P , cd₀∈P)
      = cd∈P
      where
      d₁≤d₀ : d₁ D.≤ d₀
      d₁≤d₀ = P-mono c₀ c d₁ d₀ c₀d₁∈P cd₀∈P c₀≤c
      d≤d₀ : d D.≤ d₀
      d≤d₀ = D.Po.trans d≤d₁ d₁≤d₀
      d₀≈d : d₀ D.≈ d
      d₀≈d = D.Po.antisym d₀≤d d≤d₀
      cd∈P : (c , d) ∈ P
      cd∈P = P .Pred.isWellDefined (C.Eq.refl , d₀≈d) cd₀∈P

    private
      module Lens = PosetPoly (Lens C⨆ D⨆)

    module _ where
      open GaloisConnection (F₀⊣G₀ C⨆ D⨆)
      ⨆closed-mono→∈preG₀F₀ : ∀ (P : Pred (C≈ ×-setoid D≈))
        → Is⨆Closed (C⨆ ×-slat D⨆) P × IsMonotoneRelation C⨆ D⨆ P
        → P ∈ preRL
      ⨆closed-mono→∈preG₀F₀ P (P-⨆closed , P-mono) = preG₀F₀-characterization C⨆ D⨆ P .proj₂ (mono→tbt-conn P P-mono , P-⨆closed)

      image-of-⨆closed-mono→∈postF₀G₀ : ∀ (f : ∣ Lens C⨆ D⨆ ∣)
        → (Σ P ∶ Pred (C≈ ×-setoid D≈) , f Lens.≈ ⟦ F₀ C⨆ D⨆ ⟧ P × Is⨆Closed (C⨆ ×-slat D⨆) P × IsMonotoneRelation C⨆ D⨆ P )
        → f ∈ postLR
      image-of-⨆closed-mono→∈postF₀G₀ f (P , f≈F₀P , P-⨆closed-mono) = f∈postF₀G₀
        where
        f∈fixF₀G₀ : f Lens.≈ ⟦ F₀ C⨆ D⨆ ∘-mono G₀ C⨆ D⨆ ⟧ f
        f∈fixF₀G₀ = 
          let open SetoidReasoning (PosetPoly.Eq.setoid (Lens C⨆ D⨆)) in
          begin
          f ≈⟨  f≈F₀P ⟩
          ⟦ F₀ C⨆ D⨆ ⟧ P  ≈˘⟨ LRL≈L P ⟩
          ⟦ F₀ C⨆ D⨆ ∘-mono G₀ C⨆ D⨆ ∘-mono F₀ C⨆ D⨆ ⟧ P ≈˘⟨ (F₀ C⨆ D⨆ ∘-mono G₀ C⨆ D⨆) .Mono.cong {f} {⟦ F₀ C⨆ D⨆ ⟧ P} f≈F₀P ⟩
          ⟦ F₀ C⨆ D⨆ ∘-mono G₀ C⨆ D⨆ ⟧ f ∎

        f∈postF₀G₀ : f Lens.≤ ⟦ F₀ C⨆ D⨆ ∘-mono G₀ C⨆ D⨆ ⟧ f
        f∈postF₀G₀ = Lens.reflexive {f} {⟦ F₀ C⨆ D⨆ ∘-mono G₀ C⨆ D⨆ ⟧ f} f∈fixF₀G₀

      mono-explicit : ∀ (f : ∣ Lens C⨆ D⨆ ∣)
        → let (f⃖ , f⃗) = f
        in IsMonotoneRelation C⨆ D⨆ (⟦ G₀ C⨆ D⨆ ⟧ f)
        ↔ (∀ c₀ c₁ d₀ d₁ → c₀ C.≤ ⟦ f⃖ ⟧ (c₀ , d₀) × d₀ D.≤ ⟦ f⃗ ⟧ c₀ → c₁ C.≤ ⟦ f⃖ ⟧ (c₁ , d₁) × d₁ D.≤ ⟦ f⃗ ⟧ c₁ → c₀ C.≤ c₁ → d₀ D.≤ d₁)
      mono-explicit f = (id , id)

    mono×sqfill→bt-conn : (P : Pred (C≈ ×-setoid D≈))
      → IsMonotoneRelation C⨆ D⨆ P
      → IsSquareFilling C⨆ D⨆ P
      → IsBowTieConnecting C⨆ D⨆ P
    mono×sqfill→bt-conn P P-mono P-sqfill c d c₀ d₀ c₁ d₁ bowtie@(c₀≤c , d₀≤d , c≤c₁ , d≤d₁ , c₀d₁∈P , c₁d₀∈P)
      = cd∈P
      where
      c₀≤c₁ : c₀ C.≤ c₁
      c₀≤c₁ = C.Po.trans c₀≤c c≤c₁
      d₁≤d₀ : d₁ D.≤ d₀
      d₁≤d₀ = P-mono c₀ c₁ d₁ d₀ c₀d₁∈P c₁d₀∈P c₀≤c₁
      d≤d₀ : d D.≤ d₀
      d≤d₀ = D.Po.trans d≤d₁ d₁≤d₀
      d₁≤d : d₁ D.≤ d
      d₁≤d = D.Po.trans d₁≤d₀ d₀≤d
      d',d₁≤d',d'≤d₀,cd'∈P = P-sqfill c₀ c₁ d₁ d₀ c₀d₁∈P c₁d₀∈P c₀≤c₁ d₁≤d₀ c c₀≤c c≤c₁
      d' = d',d₁≤d',d'≤d₀,cd'∈P .proj₁
      d₁≤d' = d',d₁≤d',d'≤d₀,cd'∈P .proj₂ .proj₁
      d'≤d₀ = d',d₁≤d',d'≤d₀,cd'∈P .proj₂ .proj₂ .proj₁
      cd'∈P = d',d₁≤d',d'≤d₀,cd'∈P .proj₂ .proj₂ .proj₂
      d'≈d : d' D.≈ d
      d'≈d = D.Po.antisym (D.Po.trans d'≤d₀ d₀≤d) (D.Po.trans d≤d₁ d₁≤d')
      cd∈P : (c , d) ∈ P
      cd∈P = P .Pred.isWellDefined (C.Eq.refl , d'≈d) cd'∈P


module _ (C⨆ D⨆ : SLat) where
  private
    C≤ = SLat.poset C⨆
    C≈ = SLat.Eq.setoid C⨆
    C = ∣ C⨆ ∣
    module C = SLat C⨆
    D≤ = SLat.poset D⨆
    D≈ = SLat.Eq.setoid D⨆
    D = ∣ D⨆ ∣
    module D = SLat D⨆

    open SLat (C⨆ ×-slat D⨆)

  monotone-∩closed
    : (P : Pred (C≈ ×-setoid D≈)) → IsMonotoneRelation C⨆ D⨆ P
    → (Q : Pred (C≈ ×-setoid D≈)) → IsMonotoneRelation C⨆ D⨆ Q
    → IsMonotoneRelation C⨆ D⨆ (P ∩ Q)
  monotone-∩closed P P-mono Q Q-mono
    = P∩Q-mono
    where
    P∩Q-mono : IsMonotoneRelation C⨆ D⨆ (P ∩ Q)
    P∩Q-mono c₀ c₁ d₀ d₁ c₀d₀∈P∩Q@(c₀d₀∈P , c₀d₀∈Q) c₁d₁∈P∩Q@(c₁d₁∈P , c₁d₁∈Q) c₀≤c₁
      = P-mono c₀ c₁ d₀ d₁ c₀d₀∈P c₁d₁∈P c₀≤c₁

  squarefillingdown-∩closed
    : (P : Pred (C≈ ×-setoid D≈)) → IsSquareFillingDown C⨆ D⨆ P
    → (Q : Pred (C≈ ×-setoid D≈)) → IsSquareFillingDown C⨆ D⨆ Q
    → IsSquareFillingDown C⨆ D⨆ (P ∩ Q)
  squarefillingdown-∩closed P P-sqfill Q Q-sqfill
    = P∩Q-sqfill
    where
    P∩Q-sqfill : IsSquareFillingDown C⨆ D⨆ (P ∩ Q)
    P∩Q-sqfill c₀ c₁ d₀ d₁ c₀d₀∈P∩Q@(c₀d₀∈P , c₀d₀∈Q) c₁d₁∈P∩Q@(c₁d₁∈P , c₁d₁∈Q) c₀≤c₁ d₀≤d₁ c c₀≤c c≤c₁ =
      let
      cd₀∈P : (c , d₀) ∈ P
      cd₀∈P = P-sqfill c₀ c₁ d₀ d₁ c₀d₀∈P c₁d₁∈P c₀≤c₁ d₀≤d₁ c c₀≤c c≤c₁
      cd₀∈Q : (c , d₀) ∈ Q
      cd₀∈Q = Q-sqfill c₀ c₁ d₀ d₁ c₀d₀∈Q c₁d₁∈Q c₀≤c₁ d₀≤d₁ c c₀≤c c≤c₁
      in
      (cd₀∈P , cd₀∈Q)

  squarefillingup-∩closed
    : (P : Pred (C≈ ×-setoid D≈)) → IsSquareFillingUp C⨆ D⨆ P
    → (Q : Pred (C≈ ×-setoid D≈)) → IsSquareFillingUp C⨆ D⨆ Q
    → IsSquareFillingUp C⨆ D⨆ (P ∩ Q)
  squarefillingup-∩closed P P-sqfill Q Q-sqfill
    = P∩Q-sqfill
    where
    P∩Q-sqfill : IsSquareFillingUp C⨆ D⨆ (P ∩ Q)
    P∩Q-sqfill c₀ c₁ d₀ d₁ c₀d₀∈P∩Q@(c₀d₀∈P , c₀d₀∈Q) c₁d₁∈P∩Q@(c₁d₁∈P , c₁d₁∈Q) c₀≤c₁ d₀≤d₁ c c₀≤c c≤c₁ =
      let
      cd₁∈P : (c , d₁) ∈ P
      cd₁∈P = P-sqfill c₀ c₁ d₀ d₁ c₀d₀∈P c₁d₁∈P c₀≤c₁ d₀≤d₁ c c₀≤c c≤c₁
      cd₁∈Q : (c , d₁) ∈ Q
      cd₁∈Q = Q-sqfill c₀ c₁ d₀ d₁ c₀d₀∈Q c₁d₁∈Q c₀≤c₁ d₀≤d₁ c c₀≤c c≤c₁
      in
      (cd₁∈P , cd₁∈Q)

module _ (C⨆ D⨆ E⨆ : SLat) where
  private
    C≤ = SLat.poset C⨆
    C≈ = SLat.Eq.setoid C⨆
    C = ∣ C⨆ ∣
    module C = SLat C⨆
    D≤ = SLat.poset D⨆
    D≈ = SLat.Eq.setoid D⨆
    D = ∣ D⨆ ∣
    module D = SLat D⨆
    E≤ = SLat.poset E⨆
    E≈ = SLat.Eq.setoid E⨆
    E = ∣ E⨆ ∣
    module E = SLat E⨆

  monotone-⋈closed
    : (P : Pred (C≈ ×-setoid D≈)) → IsMonotoneRelation C⨆ D⨆ P
    → (Q : Pred (D≈ ×-setoid E≈)) → IsMonotoneRelation D⨆ E⨆ Q
    → IsMonotoneRelation C⨆ E⨆ (P ⋈ Q)
  monotone-⋈closed P P-mono Q Q-mono
    = P⋈Q-mono
    where
    P⋈Q-mono : IsMonotoneRelation C⨆ E⨆ (P ⋈ Q)
    P⋈Q-mono c₀ c₁ e₀ e₁ c₀e₀∈P⋈Q@(d₀ , c₀d₀∈P , d₀e₀∈Q) c₁e₁∈P⋈Q@(d₁ , c₁d₁∈P , d₁e₁∈Q) c₀≤c₁
      = e₀≤e₁
      where
      d₀≤d₁ : d₀ D.≤ d₁
      d₀≤d₁ = P-mono c₀ c₁ d₀ d₁ c₀d₀∈P c₁d₁∈P c₀≤c₁
      e₀≤e₁ : e₀ E.≤ e₁
      e₀≤e₁ = Q-mono d₀ d₁ e₀ e₁ d₀e₀∈Q d₁e₁∈Q d₀≤d₁

  monotone∧squirefilling-⋈closed
    : (P : Pred (C≈ ×-setoid D≈)) → IsMonotoneRelation C⨆ D⨆ P → IsSquareFilling C⨆ D⨆ P
    → (Q : Pred (D≈ ×-setoid E≈)) → IsMonotoneRelation D⨆ E⨆ Q → IsSquareFilling D⨆ E⨆ Q
    → IsMonotoneRelation C⨆ E⨆ (P ⋈ Q) × IsSquareFilling C⨆ E⨆ (P ⋈ Q)
  monotone∧squirefilling-⋈closed P P-mono P-sqfill Q Q-mono Q-sqfill
    = (P⋈Q-mono , P⋈Q-sqfill)
    where
    P⋈Q-mono : IsMonotoneRelation C⨆ E⨆ (P ⋈ Q)
    P⋈Q-mono c₀ c₁ e₀ e₁ c₀e₀∈P⋈Q@(d₀ , c₀d₀∈P , d₀e₀∈Q) c₁e₁∈P⋈Q@(d₁ , c₁d₁∈P , d₁e₁∈Q) c₀≤c₁
      = e₀≤e₁
      where
      d₀≤d₁ : d₀ D.≤ d₁
      d₀≤d₁ = P-mono c₀ c₁ d₀ d₁ c₀d₀∈P c₁d₁∈P c₀≤c₁
      e₀≤e₁ : e₀ E.≤ e₁
      e₀≤e₁ = Q-mono d₀ d₁ e₀ e₁ d₀e₀∈Q d₁e₁∈Q d₀≤d₁

    P⋈Q-sqfill : IsSquareFilling C⨆ E⨆ (P ⋈ Q)
    P⋈Q-sqfill c₀ c₁ e₀ e₁ c₀e₀∈P⋈Q@(d₀ , c₀d₀∈P , d₀e₀∈Q) c₁e₁∈P⋈Q@(d₁ , c₁d₁∈P , d₁e₁∈Q) c₀≤c₁ e₀≤e₁ c c₀≤c c≤c₁
      = (e , e₀≤e , e≤e₁ , ce∈P⋈Q)
      where
      d₀≤d₁ : d₀ D.≤ d₁
      d₀≤d₁ = P-mono c₀ c₁ d₀ d₁ c₀d₀∈P c₁d₁∈P c₀≤c₁
      d,d₀≤d,d≤d₁,cd∈P : Σ d ∶ D , ((d₀ D.≤ d) × (d D.≤ d₁) × ((c , d) ∈ P))
      d,d₀≤d,d≤d₁,cd∈P = P-sqfill c₀ c₁ d₀ d₁ c₀d₀∈P c₁d₁∈P c₀≤c₁ d₀≤d₁ c c₀≤c c≤c₁
      d : D
      d = d,d₀≤d,d≤d₁,cd∈P .proj₁
      d₀≤d : d₀ D.≤ d
      d₀≤d = d,d₀≤d,d≤d₁,cd∈P .proj₂ .proj₁
      d≤d₁ : d D.≤ d₁
      d≤d₁ = d,d₀≤d,d≤d₁,cd∈P .proj₂ .proj₂ .proj₁
      cd∈P : (c , d) ∈ P
      cd∈P = d,d₀≤d,d≤d₁,cd∈P .proj₂ .proj₂ .proj₂
      e,e₀≤e,e≤e₁,de∈Q : Σ e ∶ E , ((e₀ E.≤ e) × (e E.≤ e₁) × ((d , e) ∈ Q))
      e,e₀≤e,e≤e₁,de∈Q = Q-sqfill d₀ d₁ e₀ e₁ d₀e₀∈Q d₁e₁∈Q d₀≤d₁ e₀≤e₁ d d₀≤d d≤d₁
      e : E
      e = e,e₀≤e,e≤e₁,de∈Q .proj₁
      e₀≤e : e₀ E.≤ e
      e₀≤e = e,e₀≤e,e≤e₁,de∈Q .proj₂ .proj₁
      e≤e₁ : e E.≤ e₁
      e≤e₁ = e,e₀≤e,e≤e₁,de∈Q .proj₂ .proj₂ .proj₁
      de∈Q : (d , e) ∈ Q
      de∈Q = e,e₀≤e,e≤e₁,de∈Q .proj₂ .proj₂ .proj₂
      ce∈P⋈Q : (c , e) ∈ (P ⋈ Q)
      ce∈P⋈Q = (d , cd∈P , de∈Q)
