{-# OPTIONS --type-in-type --postfix-projections #-}

module Bidirection where

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
open import Base


-- First abstraction
module 𝒫⊆-and-Endo (C⨆ : SLat) where

  private
    C≤ = SLat.poset C⨆
    C≈ = SLat.Eq.setoid C⨆
    C = ∣ C⨆ ∣
    module C = SLat C⨆

  𝒫⊆ = Pred⊆-poset C≈
  Endo = C≤ →mono-pw C≤
  open SLat C⨆


  -- This module gives an adjoint poset map between binary relations and endo monotone functions on product
  --     (𝒫 (D × E) , ⊆)
  --        F ↓! ⊣ ↑! G
  --  ((D × E →m D × E) , ≤)
  --
  -- This is followed by adjoint poset map between subsets and endo monotone functions (general setting)
  --    (𝒫 (C) , ⊆)
  --     F ↓! ⊣ ↑! G
  --   ((C →m C) , ≤)

  -- F : (Pred⊆-poset D≈) →mono (D≤ →mono-pw D≤)
  -- G : (D≤ →mono-pw D≤) →mono (Pred⊆-poset D≈)
  -- F⊣G : F ⊣ G

  F-raw : Pred C≈ → C → C
  F-raw S d = ⨆ (↓! d ∩ S)

  F-mono : Pred C≈ → (C≤ →mono C≤)
  F-mono S = mkMono C≤ C≤ (F-raw S)
    (λ {d} {d'} → ⨆-mono (↓! d ∩ S) (↓! d' ∩ S)
      ∘ ∩-mono-l (↓! d) (↓! d') S
      ∘ ↓!-mono d d')

  G-raw : (C → C) → UniR.Pred C lzero
  G-raw f = post-raw C≤ f

  G-pred : (C≤ →mono C≤) → Pred C≈
  G-pred f = post C≤ ⟦ f ⟧cong

  F : 𝒫⊆ →mono Endo
  F = mkMono 𝒫⊆ Endo F-mono
    (λ {P} {Q} P⊆Q d → ⨆-mono (↓! d ∩ P) (↓! d ∩ Q)
             (∩-mono-r P Q (↓! d) P⊆Q))

  G-mono : G-pred Preserves Endo .PosetPoly._≤_ ⟶ _⊆_
  G-mono {f} {g} f≤g {c} c≤fc =
    C.Po.trans c≤fc (f≤g c)

  G : Endo →mono 𝒫⊆
  G = mkMono Endo 𝒫⊆ G-pred (λ {f} {g} → G-mono {f} {g})

  F⊣G : F ⊣ G
  F⊣G .GaloisConnection.ψ P f .proj₁ FP≤f {d} d∈P = Po.trans (⨆-ub (↓! d ∩ P) d (Po.refl , d∈P)) (FP≤f d)
  F⊣G .GaloisConnection.ψ P f .proj₂ P⊆Gf d = ⨆-least (↓! d ∩ P) (⟦ f ⟧ d) \d' (d'≤d , d'∈P) → Po.trans (P⊆Gf d'∈P) (Mono.mono f d'≤d)
    where
    private module M = PosetPoly (C≤ →mono-pw C≤)

  postFG-characterization : (f≤ : C≤ →mono C≤)
    → f≤ ∈ GaloisConnection.postLR F⊣G ↔ IsCoclosure C≤ ⟦ f≤ ⟧
  postFG-characterization f≤ =
    let open SetoidReasoning (Prop↔-setoid) in
    begin
    (f≤ ∈ post (C≤ →mono-pw C≤) ⟦ F ∘-mono G ⟧cong)     ≡⟨⟩
    (∀ x → f x ≤ ⨆ (↓! x ∩ post C≤ f≈ ))               ≈⟨ lift↔ _ _ ψ ⟩
    (∀ x → f x ≤ x × (f x ≤ f (f x)))                   ≡⟨⟩
    IsCoclosure C≤ f ∎
    where
    f≈ = ⟦ f≤ ⟧cong
    f = ⟦ f≤ ⟧
    ψ : ∀ d → (f d ≤ ⨆ (↓! d ∩ post C≤ f≈)) ↔ ((f d ≤ d) × (f d ≤ f (f d)))
    ψ d = Product.< ε , δ > , uncurry φ
      where
      ε : f d ≤ ⨆ (↓! d ∩ post C≤ f≈) → f d ≤ d
      ε φ =
        let open PosetReasoning C≤ in
        begin
        f d                     ≤⟨ φ ⟩
        ⨆ (↓! d ∩ post C≤ f≈)  ≤⟨ ⨆-mono (↓! d ∩ post C≤ f≈) (↓! d) (∩-⊆-l (↓! d) (post C≤ f≈)) ⟩
        ⨆ (↓! d)               ≈⟨ ⨆-↓! d ⟩
        d  ∎
      δ : f d ≤ ⨆ (↓! d ∩ post C≤ f≈) → f d ≤ f (f d)
      δ φ =
        let open PosetReasoning C≤ in
        begin
        f d                     ≤⟨ φ ⟩
        ⨆ (↓! d ∩ post C≤ f≈)  ≤⟨ ⨆-least (↓! d ∩ post C≤ f≈) (f (f d)) ξ ⟩
        f (f d)                 ∎
        where
        ξ : ∀ d' → d' ∈ (↓! d ∩ post C≤ f≈) → d' ≤ f (f d)
        ξ d' (d'≤d , d'≤fd') =
          let
          ffd'≤ffd = f≤ .Mono.mono (f≤ .Mono.mono d'≤d)
          fd'≤ffd' = f≤ .Mono.mono d'≤fd'
          open PosetReasoning C≤
          in
          begin
          d' ≤⟨ d'≤fd' ⟩
          f d' ≤⟨ fd'≤ffd' ⟩
          f (f d') ≤⟨ ffd'≤ffd ⟩
          f (f d) ∎

      φ : f d ≤ d → f d ≤ f (f d) → f d ≤ ⨆ (↓! d ∩ post C≤ f≈)
      φ fd≤d fd≤ffd =
        let open PosetReasoning C≤ in
        begin
        f d ≤⟨ ⨆-ub (↓! d ∩ post C≤ f≈) (f d) (fd≤d , fd≤ffd) ⟩
        ⨆ (↓! d ∩ post C≤ f≈) ∎

  all-subset-is-postGF : (R : Pred C≈) → (R ∈ post (Pred⊆-poset C≈) ⟦ G ∘-mono F ⟧cong)
  all-subset-is-postGF R = GaloisConnection.η F⊣G R

  module _ where
    open GaloisConnection
    preGF-characterization : (R : Pred C≈) → R ∈ preRL F⊣G ↔ Is⨆Closed C⨆ R
    preGF-characterization R =
      let open SetoidReasoning (Prop↔-setoid) in
      begin
      R ∈ preRL F⊣G                      ≡⟨⟩
      (G-pred ∘ F-mono) R ⊆ R             ≈⟨ λ- , _$- ⟩
      (∀ d → d ≤ ⨆ (↓! d ∩ R) → d ∈ R) ≈⟨ γ , γ⁻¹ ⟩
      (∀ S → S ⊆ R → ⨆ S ∈ R)          ≡⟨⟩
      Is⨆Closed C⨆ R ∎
      where
      γ : (∀ d → d ≤ ⨆ (↓! d ∩ R) → d ∈ R) → ∀ S → S ⊆ R → ⨆ S ∈ R
      γ φ S S⊆R = φ (⨆ S) (⨆-mono S (↓! (⨆ S) ∩ R) \ {d} d∈S → ⨆-ub S d d∈S  , S⊆R d∈S)

      γ⁻¹ : (∀ S → S ⊆ R → ⨆ S ∈ R) → ∀ d → d ≤ ⨆ (↓! d ∩ R) → d ∈ R
      γ⁻¹ ψ d d≤⨆↓!d∩R = R .Pred.isWellDefined (Po.antisym χ χ⁻¹)  (ψ (↓! d ∩ R) (∩-⊆-r (↓! d) R))
        where
        χ : ⨆ (↓! d ∩ R) ≤ d
        χ = Po.trans (⨆-mono _ _ (∩-⊆-l (↓! d) R)) (⨆-↓!-≤ d)

        χ⁻¹ : d ≤ ⨆ (↓! d ∩ R)
        χ⁻¹ = d≤⨆↓!d∩R

module _ (D⨆ E⨆ : SLat) where

  private
    D×E⨆ = D⨆ ×-slat E⨆

    D×E≤ = SLat.poset D×E⨆
    D×E≈ = SLat.Eq.setoid D×E⨆

    D≤ = SLat.poset D⨆
    D≈ = SLat.Eq.setoid D⨆
    D = ∣ D⨆ ∣

    E≤ = SLat.poset E⨆
    E≈ = SLat.Eq.setoid E⨆
    E = ∣ E⨆ ∣

    module D = SLat D⨆
    module E = SLat E⨆
  open SLat (D⨆ ×-slat E⨆)
  open 𝒫⊆-and-Endo (D⨆ ×-slat E⨆)

  module _ where
    open GaloisConnection
    preGF-explicit : (R : Pred (D≈ ×-setoid E≈)) → R ∈ preRL F⊣G ↔ (((d , e) : D × E) → (d D.≤ D.⨆ ((↓! (d , e) ∩ R) ∣₁)) × (e E.≤ E.⨆ ((↓! (d , e) ∩ R) ∣₂)) → (d , e) ∈ R)
    preGF-explicit R =
      let open SetoidReasoning (Prop↔-setoid) in
      begin
      R ∈ preRL F⊣G                                                                                             ≡⟨⟩
      (G-raw ∘ F-raw) R UniR.⊆ Pred.⟦ R ⟧                                                                        ≈⟨ λ- , _$- ⟩
      (((d , e) : D × E) → d D.≤ D.⨆ ((↓! (d , e) ∩ R) ∣₁) × (e E.≤ E.⨆ ((↓! (d , e) ∩ R) ∣₂)) → (d , e) ∈ R) ∎

    preGF→⊔closed : (R : Pred (D≈ ×-setoid E≈))
                  → (((d , e) : D × E) → (d D.≤ D.⨆ ((↓! (d , e) ∩ R) ∣₁)) × (e E.≤ E.⨆ ((↓! (d , e) ∩ R) ∣₂)) → (d , e) ∈ R)
                  → (((d , e) : D × E) ((d₀ , e₀) : D × E) → (d₀ , e₀) ≤ (d , e) → (d₀ , e) ∈ R × (d , e₀) ∈ R → (d , e) ∈ R)
    preGF→⊔closed R ≤⨆↓!∩→∈ (d , e) (d₀ , e₀) (d₀≤d , e₀≤e) (d₀e∈R , de₀∈R) = ≤⨆↓!∩→∈ (d , e)
      ( D.⨆-ub ((↓! (d , e) ∩ R) ∣₁) d (e₀ , (D.Po.refl , e₀≤e) , de₀∈R)
      , E.⨆-ub ((↓! (d , e) ∩ R) ∣₂) e (d₀ , (d₀≤d , E.Po.refl) , d₀e∈R))

  IsMonotoneRelation : (R : Pred (D≈ ×-setoid E≈)) → Set
  IsMonotoneRelation R = ∀ d₀ d₁ e₀ e₁
    → (d₀ , e₀) ∈ R → (d₁ , e₁) ∈ R → d₀ D.≤ d₁ → e₀ E.≤ e₁

  IsSquareFilling : (R : Pred (D≈ ×-setoid E≈)) → Set
  IsSquareFilling R = ∀ d₀ d₁ e₀ e₁
    → (d₀ , e₀) ∈ R → (d₁ , e₁) ∈ R
    → d₀ D.≤ d₁ → e₀ E.≤ e₁
    → ∀ d → d₀ D.≤ d → d D.≤ d₁ → Σ e ∶ E , e₀ E.≤ e × e E.≤ e₁ × (d , e) ∈ R

  -- We define the following galois connection
  --
  --     (D × E →m D × E , ≤)
  --        H₀ ↓! ⊣ ↑! I₀
  -- ((D × E →m D) × (D →m E) , ≤)

  -- H₀ : ((D≤ ×-poset E≤) →mono-pw (D≤ ×-poset E≤)) →mono (((D≤ ×-poset E≤) →mono-pw D≤) ×-poset (D≤ →mono-pw E≤))
  -- I₀ : (((D≤ ×-poset E≤) →mono-pw D≤) ×-poset (D≤ →mono-pw E≤)) →mono ((D≤ ×-poset E≤) →mono-pw (D≤ ×-poset E≤))
  -- H₀⊣I₀ : H₀ ⊣ I₀

  Lens = ((D≤ ×-poset E≤) →mono-pw D≤) ×-poset (D≤ →mono-pw E≤)

  H₀-raw : (D × E → D × E) → (D × E → D) × (D → E)
  H₀-raw f =
    ( (λ p → f p .proj₁)
    , (λ d → f (d , E.⊤) .proj₂))

  H₀-mono : ∣ Endo ∣ → ∣ Lens ∣
  H₀-mono f =
    ( (mkMono (D≤ ×-poset E≤) D≤
              (λ p → ⟦ f ⟧ p .proj₁) (λ p≤p' → f .Mono.mono p≤p' .proj₁))
    , (mkMono D≤ E≤
              (λ d → ⟦ f ⟧ (d , E.⊤) .proj₂) (λ d≤d' → f .Mono.mono (d≤d' , E.Po.refl) .proj₂)))

  I₀-raw : (D × E → D) × (D → E) → (D × E → D × E)
  I₀-raw (f⃖ , f⃗) (d , e) = (f⃖ (d , e) , f⃗ d)

  I₀-mono : ∣ Lens ∣ → ∣ Endo ∣
  I₀-mono (f⃖ , f⃗) = mkMono (D≤ ×-poset E≤) (D≤ ×-poset E≤) (I₀-raw (⟦ f⃖ ⟧ , ⟦ f⃗ ⟧))
    (λ {(d , d')} {(e , e')} (d≤d' , e≤e') → ((f⃖ .Mono.isMonotone .IsMono.mono (d≤d' , e≤e')) , (f⃗ .Mono.isMonotone .IsMono.mono d≤d')))

  H₀ : Endo →mono Lens
  H₀ = mkMono Endo Lens H₀-mono
    (λ f≤g → ((λ p → f≤g p .proj₁) , (λ d → f≤g (d , E.⊤) .proj₂)))

  I₀ : Lens →mono Endo
  I₀ = mkMono Lens Endo I₀-mono
    (λ (f⃖≈g⃖ , f⃗≈g⃗) (d , e) → (f⃖≈g⃖ (d , e) , f⃗≈g⃗ d))

  H₀⊣I₀ : H₀ ⊣ I₀
  H₀⊣I₀ .GaloisConnection.ψ f f⃡ .proj₁ H₀f≤f⃡ (d , e)
    = H₀f≤f⃡ .proj₁ (d , e) , E.Po.trans (IsMono.mono (proj₂-mono D≤ E≤) (f .Mono.mono (D.Po.refl , (E.⊤-max _))) ) (H₀f≤f⃡ .proj₂ d)
  H₀⊣I₀ .GaloisConnection.ψ f f⃡ .proj₂ f≤I₀f⃡
    = ((λ p → f≤I₀f⃡ p .proj₁) , (λ d → f≤I₀f⃡ (d , E.⊤) .proj₂))

  -- The Galois connection between relations and lenses

  F₀ : 𝒫⊆ →mono (((D≤ ×-poset E≤) →mono-pw D≤) ×-poset (D≤ →mono-pw E≤))
  F₀ = H₀ ∘-mono F

  G₀ : (((D≤ ×-poset E≤) →mono-pw D≤) ×-poset (D≤ →mono-pw E≤)) →mono 𝒫⊆
  G₀ = G ∘-mono I₀

  F₀⊣G₀ : F₀ ⊣ G₀
  F₀⊣G₀ = F⊣G ∘-galois H₀⊣I₀

  IsTiltBowTie : (R : Pred (D≈ ×-setoid E≈)) → (d : D) (e : E) (d₀ : D) (e₀ : E) (e₁ : E) → Set
  IsTiltBowTie R d e d₀ e₀ e₁ = (d₀ D.≤ d) × (e₀ E.≤ e) × (e E.≤ e₁) × (d₀ , e₁) ∈ R × (d , e₀) ∈ R

  tiltbowtie→≤⨆ : (R : Pred (D≈ ×-setoid E≈)) → ∀ d e → Σ d₀ ∶ D , Σ e₀ ∶ E , Σ e₁ ∶ E , IsTiltBowTie R d e d₀ e₀ e₁ → d D.≤ (D.⨆ ((↓! (d , e) ∩ R) ∣₁)) × e E.≤ (E.⨆ ((↓! (d , E.⊤) ∩ R) ∣₂))
  tiltbowtie→≤⨆ R d e (d₀ , e₀ , e₁ , d₀≤d , e₀≤e , e≤e₁ , d₀e₁∈R , de₀∈R) =
    ( D.⨆-ub ((↓! (d , e) ∩ R) ∣₁) d (e₀ , (D.Po.refl , e₀≤e) , de₀∈R)
    , E.Po.trans e≤e₁ (E.⨆-ub ((↓! (d , E.⊤) ∩ R) ∣₂) e₁ (d₀ , (d₀≤d , E.⊤-max _) , d₀e₁∈R)))

  IsTiltBowTieConnecting : (R : Pred (D≈ ×-setoid E≈)) → Set
  IsTiltBowTieConnecting R = (∀ d e d₀ e₀ e₁ → IsTiltBowTie R d e d₀ e₀ e₁ → (d , e) ∈ R)

  -- the property TiltBowtieConecting is not closed under ⋈ but by adding an extra condition
  -- it becomes closed under ⋈ (TODO: proof)
  Is⋈FriendlyTiltBowTieConnecting : (R : Pred (D≈ ×-setoid E≈)) → Set
  Is⋈FriendlyTiltBowTieConnecting R = IsTiltBowTieConnecting R × IsMonotoneRelation R

  module _ where
    open GaloisConnection
    preG₀F₀-explicit : (R : Pred (D≈ ×-setoid E≈)) → (R ∈ preRL F₀⊣G₀) ↔ (((d , e) : D × E) → (d D.≤ D.⨆ ((↓! (d , e) ∩ R) ∣₁)) × (e E.≤ E.⨆ ((↓! (d , E.⊤) ∩ R) ∣₂)) → (d , e) ∈ R)
    preG₀F₀-explicit R = (λ- , _$-)

    preG₀F₀-characterization : (R : Pred (D≈ ×-setoid E≈)) → (R ∈ preRL F₀⊣G₀) ↔ (∀ d e d₀ e₀ e₁ → IsTiltBowTie R d e d₀ e₀ e₁ → (d , e) ∈ R) × Is⨆Closed (D⨆ ×-slat E⨆) R
    preG₀F₀-characterization R = (α , α⁻¹)
     where
     α₁ : (R ∈ preRL F₀⊣G₀) → (∀ d e d₀ e₀ e₁ → IsTiltBowTie R d e d₀ e₀ e₁ → (d , e) ∈ R)
     α₁ R∈preG₀F₀ d e d₀ e₀ e₁ tiltbowtie = R∈preG₀F₀ (tiltbowtie→≤⨆ R d e (d₀ , e₀ , e₁ , tiltbowtie))

     α₂ : (R ∈ preRL F₀⊣G₀) → Is⨆Closed (D⨆ ×-slat E⨆) R
     α₂ = preGF-characterization R .proj₁ ∘ preRL-∘-⊆ F⊣G H₀⊣I₀ {R}

     α : (R ∈ preRL F₀⊣G₀) → (∀ d e d₀ e₀ e₁ → IsTiltBowTie R d e d₀ e₀ e₁ → (d , e) ∈ R) × Is⨆Closed (D⨆ ×-slat E⨆) R
     α = Product.< α₁ , α₂ >

     α⁻¹ : (∀ d e d₀ e₀ e₁ → IsTiltBowTie R d e d₀ e₀ e₁ → (d , e) ∈ R) × Is⨆Closed (D⨆ ×-slat E⨆) R → (R ∈ preRL F₀⊣G₀)
     α⁻¹ (tiltbowtie→R , ⨆closed) {(d , e)} (d≤⨆↓!de∩R∣₁ , e≤⨆↓!d⊤∩R∣₂) =
        tiltbowtie→R d e (D.⨆ ((↓! (d , E.⊤) ∩ R) ∣₁)) (E.⨆ ((↓! (d , e) ∩ R) ∣₂)) (E.⨆ ((↓! (d , E.⊤) ∩ R) ∣₂))
          ( d≥⨆↓!d⊤∩R∣₁
          , e≥⨆↓!de∩R∣₂
          , e≤⨆↓!d⊤∩R∣₂
          , ⨆closed (↓! (d , E.⊤) ∩ R) (∩-⊆-r (↓! (d , E.⊤)) R)
          , R .Pred.isWellDefined (D.Eq.sym d≈⨆↓!de∩R∣₁ , E.Eq.refl) (⨆closed (↓! (d , e) ∩ R) (∩-⊆-r (↓! (d , e)) R)))
        where
        d≥⨆↓!d⊤∩R∣₁ : D.⨆ ((↓! (d , E.⊤) ∩ R) ∣₁) D.≤ d
        d≥⨆↓!d⊤∩R∣₁ = D.⨆-least ((↓! (d , E.⊤) ∩ R) ∣₁) d (λ d₀ (e₀ , (d₀≤d , e₀≤e) , d₀e₀∈R) → d₀≤d)

        e≥⨆↓!de∩R∣₂ : E.⨆ ((↓! (d , e) ∩ R) ∣₂) E.≤ e
        e≥⨆↓!de∩R∣₂ = E.⨆-least ((↓! (d , e) ∩ R) ∣₂) e (λ d₀ (e₀ , (d₀≤d , e₀≤e) , d₀e₀∈R) → e₀≤e)

        d≥⨆↓!de∩R∣₁ : D.⨆ ((↓! (d , e) ∩ R) ∣₁) D.≤ d
        d≥⨆↓!de∩R∣₁ = D.⨆-least ((↓! (d , e) ∩ R) ∣₁) d (λ d₀ (e₀ , (d₀≤d , e₀≤e) , d₀e₀∈R) → d₀≤d)

        d≈⨆↓!de∩R∣₁ : d D.≈ D.⨆ ((↓! (d , e) ∩ R) ∣₁)
        d≈⨆↓!de∩R∣₁ = D.Po.antisym d≤⨆↓!de∩R∣₁ d≥⨆↓!de∩R∣₁

    postF₀G₀-explicit : ∀ (f : ∣ Lens ∣) → let (f⃖ , f⃗) = f
      in (f ∈ postLR F₀⊣G₀)
      ↔ ((∀ p → ⟦ f⃖ ⟧ p D.≤ D.⨆ ((↓! p ∩ post (D≤ ×-poset E≤) (⟦ I₀-mono f ⟧cong)) ∣₁)) × (∀ d → ⟦ f⃗ ⟧ d E.≤ E.⨆ ((↓! (d , E.⊤) ∩ post (D≤ ×-poset E≤) (⟦ I₀-mono f ⟧cong)) ∣₂) ))
    postF₀G₀-explicit f = (id , id)

    private
      l-law : (p₀ : D × E) → (f : (D × E → D) × (D → E)) → D × E → D × E
      l-law p₀ (f⃖ , f⃗) (d , e) = p₀ ⊓ (f⃖ (d , e) , f⃗ d)

      l : (p₀ : D × E) (f : ∣ Lens ∣) → ∣ Endo ∣
      l p₀ (f⃖ , f⃗) = mkMono (D≤ ×-poset E≤) (D≤ ×-poset E≤) (l-law p₀ (⟦ f⃖ ⟧ , ⟦ f⃗ ⟧))
        (λ {(d , e)} {(d' , e')} (d≤d' , e≤e') → ⊓-mono-r p₀ (⟦ f⃖ ⟧ (d , e) , ⟦ f⃗ ⟧ d) (⟦ f⃖ ⟧ (d' , e') , ⟦ f⃗ ⟧ d') ((f⃖ .Mono.mono (d≤d' , e≤e')) , (f⃗ .Mono.mono d≤d')))

      ⨆↓∩toνD : ∀ p₀ f → D.⨆ ((↓! p₀ ∩ post (D≤ ×-poset E≤) (⟦ I₀-mono f ⟧cong)) ∣₁) D.≈ proj₁ (ν (⟦ l p₀ f ⟧cong))
      ⨆↓∩toνD p₀ f@(f⃖ , f⃗) = D.⨆-cong _ _ (∀↔→≐ {_} {((↓! p₀ ∩ post (D≤ ×-poset E≤) ⟦ I₀-mono f ⟧cong) ∣₁)} {(post poset ⟦ l p₀ f ⟧cong ∣₁)} β)
        where
        γ : ∀ d e → ((d , e) ≤ p₀ × ((d , e) ≤ (⟦ f⃖ ⟧ (d , e) , ⟦ f⃗ ⟧ d))) ↔ ((d , e) ≤ (p₀ ⊓ (⟦ f⃖ ⟧ (d , e) , ⟦ f⃗ ⟧ d)))
        γ d e = Product.swap (≤⊓↔≤× p₀ (⟦ f⃖ ⟧ (d , e) , ⟦ f⃗ ⟧ d) (d , e))

        β : ∀ d → d ∈ ((↓! p₀ ∩ post (D≤ ×-poset E≤) ⟦ I₀-mono f ⟧cong) ∣₁) ↔ d ∈ (post poset ⟦ l p₀ f ⟧cong ∣₁)
        β d =
          let open SetoidReasoning Prop↔-setoid in
          begin
          (d ∈ ((↓! p₀ ∩ post (D≤ ×-poset E≤) ⟦ I₀-mono f ⟧cong) ∣₁)) ≡⟨⟩
          (Σ e ∶ E , (d , e) ≤ p₀ × ((d , e) ≤ (⟦ f⃖ ⟧ (d , e) , ⟦ f⃗ ⟧ d))) ≈⟨ ∀↔→Σ↔ (γ d) ⟩
          (Σ e ∶ E , (d , e) ≤ (p₀ ⊓ (⟦ f⃖ ⟧ (d , e) , ⟦ f⃗ ⟧ d))) ≡⟨⟩
          (d ∈ (post poset ⟦ l p₀ (f⃖ , f⃗) ⟧cong ∣₁)) ∎

      ⨆↓∩toνE : ∀ p₀ f → E.⨆ ((↓! p₀ ∩ post (D≤ ×-poset E≤) (⟦ I₀-mono f ⟧cong)) ∣₂) E.≈ proj₂ (ν (⟦ l p₀ f ⟧cong))
      ⨆↓∩toνE p₀ f@(f⃖ , f⃗) = E.⨆-cong _ _ (∀↔→≐ {_} {((↓! p₀ ∩ post (D≤ ×-poset E≤) ⟦ I₀-mono f ⟧cong) ∣₂)} {(post poset ⟦ l p₀ f ⟧cong ∣₂)} β)
        where
        γ : ∀ e d → ((d , e) ≤ p₀ × ((d , e) ≤ (⟦ f⃖ ⟧ (d , e) , ⟦ f⃗ ⟧ d))) ↔ ((d , e) ≤ (p₀ ⊓ (⟦ f⃖ ⟧ (d , e) , ⟦ f⃗ ⟧ d)))
        γ e d = Product.swap (≤⊓↔≤× p₀ (⟦ f⃖ ⟧ (d , e) , ⟦ f⃗ ⟧ d) (d , e))

        β : ∀ e → e ∈ ((↓! p₀ ∩ post (D≤ ×-poset E≤) ⟦ I₀-mono f ⟧cong) ∣₂) ↔ e ∈ (post poset ⟦ l p₀ f ⟧cong ∣₂)
        β e =
          let open SetoidReasoning (Prop↔-setoid) in
          begin
          (e ∈ ((↓! p₀ ∩ post (D≤ ×-poset E≤) ⟦ I₀-mono f ⟧cong) ∣₂)) ≡⟨⟩
          (Σ d ∶ D , (d , e) ≤ p₀ × ((d , e) ≤ (⟦ f⃖ ⟧ (d , e) , ⟦ f⃗ ⟧ d))) ≈⟨ ∀↔→Σ↔ (γ e) ⟩
          (Σ d ∶ D , (d , e) ≤ (p₀ ⊓ (⟦ f⃖ ⟧ (d , e) , ⟦ f⃗ ⟧ d))) ≡⟨⟩
          (e ∈ (post poset ⟦ l p₀ (f⃖ , f⃗) ⟧cong ∣₂)) ∎

{-
    postF₀G₀-characterization : ∀ (f : ∣ Lens ∣) → let (f⃖ , f⃗) = f
      in (f ∈ postLR F₀⊣G₀)
      ↔ {!!}
    postF₀G₀-characterization f@(f⃖ , f⃗) =
      let open SetoidReasoning (Prop↔-setoid) in
      begin
      ((f⃖ , f⃗) ∈ postLR F₀⊣G₀)                                                                   ≡⟨⟩
      ( (∀ p → ⟦ f⃖ ⟧ p D.≤ D.⨆ ((↓! p ∩ post (D≤ ×-poset E≤) (⟦ I₀-mono f ⟧cong)) ∣₁))
      × (∀ d → ⟦ f⃗ ⟧ d E.≤ E.⨆ ((↓! (d , E.⊤) ∩ post (D≤ ×-poset E≤) (⟦ I₀-mono f ⟧cong)) ∣₂)))  ≈⟨ (backward↔ ×-↔ {!forward↔!}) ⟩
      (Π backward × Π forward) ∎
      where
      backward : D × E → Set
      backward = λ p → {!!}
      forward : D → Set
      forward = λ d → {!!}
      backward↔' : ∀ p → ⟦ f⃖ ⟧ p D.≤ D.⨆ ((↓! p ∩ post (D≤ ×-poset E≤) (⟦ I₀-mono f ⟧cong)) ∣₁) ↔ backward p
      backward↔' p₀ =
        let open SetoidReasoning Prop↔-setoid in
        begin
        (⟦ f⃖ ⟧ p₀ D.≤ D.⨆ ((↓! p₀ ∩ post (D≤ ×-poset E≤) ⟦ I₀-mono (f⃖ , f⃗) ⟧cong) ∣₁)) ≈⟨ D.≤⨆↔≤ubs (⟦ f⃖ ⟧ p₀) ((↓! p₀ ∩ post (D≤ ×-poset E≤) ⟦ I₀-mono (f⃖ , f⃗) ⟧cong) ∣₁) ⟩
        (∀ du → du ∈ D.ubs ((↓! p₀ ∩ post (D≤ ×-poset E≤) ⟦ I₀-mono (f⃖ , f⃗) ⟧cong) ∣₁) → ⟦ f⃖ ⟧ p₀ D.≤ du) ≈⟨ lift↔ _ _ p1 ⟩
        (∀ du → (∀ d e → (d , e) ≤ p₀ → d D.≤ ⟦ f⃖ ⟧ (d , e) → e E.≤ ⟦ f⃗ ⟧ d → d D.≤ du) → ⟦ f⃖ ⟧ p₀ D.≤ du) ≈⟨ p' , p'' ⟩
        (∀ p → ⟦ f⃖ ⟧ p D.≤ ⟦ f⃖ ⟧ (p ⊓ (p .proj₁ , ⟦ f⃗ ⟧ (⟦ f⃖ ⟧ p)))) ∎
        where
        p1 : ∀ du → (du ∈ D.ubs ((↓! p₀ ∩ post (D≤ ×-poset E≤) ⟦ I₀-mono (f⃖ , f⃗) ⟧cong) ∣₁) → ⟦ f⃖ ⟧ p₀ D.≤ du) ↔ ((∀ d e → (d , e) ≤ p₀ → d D.≤ ⟦ f⃖ ⟧ (d , e) → e E.≤ ⟦ f⃗ ⟧ d → d D.≤ du) → ⟦ f⃖ ⟧ p₀ D.≤ du)
        p1 du .proj₁ g h = g (u h)
          where
          t : du ∈ D.ubs ((↓! p₀ ∩ post (D≤ ×-poset E≤) ⟦ I₀-mono (f⃖ , f⃗) ⟧cong) ∣₁) → (∀ d e → (d , e) ≤ p₀ → d D.≤ ⟦ f⃖ ⟧ (d , e) → e E.≤ ⟦ f⃗ ⟧ d → d D.≤ du)
          t du-ub d e de≤p₀ d≤f⃖de e≤f⃗d = du-ub d (e , (de≤p₀ , (d≤f⃖de , e≤f⃗d)))
          u : (∀ d e → (d , e) ≤ p₀ → d D.≤ ⟦ f⃖ ⟧ (d , e) → e E.≤ ⟦ f⃗ ⟧ d → d D.≤ du) → du ∈ D.ubs ((↓! p₀ ∩ post (D≤ ×-poset E≤) ⟦ I₀-mono (f⃖ , f⃗) ⟧cong) ∣₁)
          u ξ d (e , de≤p₀ , (d≤fde , e≤fd)) = ξ d e de≤p₀ d≤fde e≤fd

        p1 du .proj₂ g h = g (t h)
          where
          t : du ∈ D.ubs ((↓! p₀ ∩ post (D≤ ×-poset E≤) ⟦ I₀-mono (f⃖ , f⃗) ⟧cong) ∣₁) → (∀ d e → (d , e) ≤ p₀ → d D.≤ ⟦ f⃖ ⟧ (d , e) → e E.≤ ⟦ f⃗ ⟧ d → d D.≤ du)
          t du-ub d e de≤p₀ d≤f⃖de e≤f⃗d = du-ub d (e , (de≤p₀ , (d≤f⃖de , e≤f⃗d)))
          u : (∀ d e → (d , e) ≤ p₀ → d D.≤ ⟦ f⃖ ⟧ (d , e) → e E.≤ ⟦ f⃗ ⟧ d → d D.≤ du) → du ∈ D.ubs ((↓! p₀ ∩ post (D≤ ×-poset E≤) ⟦ I₀-mono (f⃖ , f⃗) ⟧cong) ∣₁)
          u ξ d (e , de≤p₀ , (d≤fde , e≤fd)) = ξ d e de≤p₀ d≤fde e≤fd

        p' : (∀ du → (∀ d e → (d , e) ≤ p₀ → d D.≤ ⟦ f⃖ ⟧ (d , e) → e E.≤ ⟦ f⃗ ⟧ d → d D.≤ du) → ⟦ f⃖ ⟧ p₀ D.≤ du)
          → (∀ (p : D × E) → ⟦ f⃖ ⟧ p D.≤ ⟦ f⃖ ⟧ (p ⊓ (p .proj₁ , ⟦ f⃗ ⟧ (⟦ f⃖ ⟧ p))))
        p' x p = {!!}
        p'' : (∀ (p : D × E) → ⟦ f⃖ ⟧ p D.≤ ⟦ f⃖ ⟧ (p ⊓ (p .proj₁ , ⟦ f⃗ ⟧ (⟦ f⃖ ⟧ p))))
          → (∀ du → (∀ d e → (d , e) ≤ p₀ → d D.≤ ⟦ f⃖ ⟧ (d , e) → e E.≤ ⟦ f⃗ ⟧ d → d D.≤ du) → ⟦ f⃖ ⟧ p₀ D.≤ du)
        p'' g du g' = g' (⟦ f⃖ ⟧ p₀) (p₀ .proj₂ E.⊓ ⟦ f⃗ ⟧ (⟦ f⃖ ⟧ p₀)) {!g p₀!} {!!} {!!}


      backward↔ :
        ( (∀ p → ⟦ f⃖ ⟧ p D.≤ D.⨆ ((↓! p ∩ post (D≤ ×-poset E≤) (⟦ I₀-mono f ⟧cong)) ∣₁))
        ↔ (∀ p → backward p))
      backward↔ = lift↔ _ _ {!backward↔'!}
-}



  -- We define the following galois connection
  --
  -- ((D × E →mono D) × (D →mono E) , ≤)
  --        H₁ ↓! ⊣ ↑! I₁
  -- ((E →mono D) × (D →mono E) , ≤)

  -- H₁ : (((D≤ ×-poset E≤) →mono-pw D≤) ×-poset (D≤ →mono-pw E≤)) →mono ((E≤ →mono-pw D≤) ×-poset (D≤ →mono-pw E≤))
  -- I₁ : ((E≤ →mono-pw D≤) ×-poset (D≤ →mono-pw E≤)) →mono (((D≤ ×-poset E≤) →mono-pw D≤) ×-poset (D≤ →mono-pw E≤))
  -- H₁⊣I₁ : H₁ ⊣ I₁

  module _ where
    -- aux definitions

    H₁-raw : (D × E → D) × (D → E) → (E → D) × (D → E)
    H₁-raw (f⃖ , f⃗) =
      ( (λ e → f⃖ (D.⊤ , e))
      , (λ d → f⃗ d))

    H₁-mono : ((D≤ ×-poset E≤) →mono D≤) × (D≤ →mono E≤) → (E≤ →mono D≤) × (D≤ →mono E≤)
    Mono.⟦ H₁-mono (f⃖ , f⃗) .proj₁ ⟧ = H₁-raw (⟦ f⃖ ⟧ , ⟦ f⃗ ⟧) .proj₁
    H₁-mono (f⃖ , f⃗) .proj₁ .Mono.isMonotone .IsMono.cong e≈e' = f⃖ .Mono.isMonotone .IsMono.cong (D.Eq.refl , e≈e')
    H₁-mono (f⃖ , f⃗) .proj₁ .Mono.isMonotone .IsMono.mono e≤e' = f⃖ .Mono.isMonotone .IsMono.mono (D.Po.refl , e≤e')
    Mono.⟦ H₁-mono (f⃖ , f⃗) .proj₂ ⟧ = H₁-raw (⟦ f⃖ ⟧ , ⟦ f⃗ ⟧) .proj₂
    H₁-mono (f⃖ , f⃗) .proj₂ .Mono.isMonotone .IsMono.cong d≈d' = f⃗ .Mono.isMonotone .IsMono.cong d≈d'
    H₁-mono (f⃖ , f⃗) .proj₂ .Mono.isMonotone .IsMono.mono d≤d' = f⃗ .Mono.isMonotone .IsMono.mono d≤d'

    I₁-raw : (E → D) × (D → E) → (D × E → D) × (D → E)
    I₁-raw (f⃖ , f⃗) = (λ p → f⃖ (p .proj₂)) , f⃗

    I₁-mono : (E≤ →mono D≤) × (D≤ →mono E≤) → ((D≤ ×-poset E≤) →mono D≤) × (D≤ →mono E≤)
    Mono.⟦ I₁-mono (f⃖ , f⃗) .proj₁ ⟧ = I₁-raw (⟦ f⃖ ⟧ , ⟦ f⃗ ⟧) .proj₁
    I₁-mono (f⃖ , f⃗) .proj₁ .Mono.isMonotone .IsMono.cong (d≈d' , e≈e') = f⃖ .Mono.isMonotone .IsMono.cong e≈e'
    I₁-mono (f⃖ , f⃗) .proj₁ .Mono.isMonotone .IsMono.mono (d≈d' , e≤e') = f⃖ .Mono.isMonotone .IsMono.mono e≤e'
    Mono.⟦ I₁-mono (f⃖ , f⃗) .proj₂ ⟧ = I₁-raw (⟦ f⃖ ⟧ , ⟦ f⃗ ⟧) .proj₂
    I₁-mono (f⃖ , f⃗) .proj₂ .Mono.isMonotone .IsMono.cong d≈d' = f⃗ .Mono.isMonotone .IsMono.cong d≈d'
    I₁-mono (f⃖ , f⃗) .proj₂ .Mono.isMonotone .IsMono.mono d≤d' = f⃗ .Mono.isMonotone .IsMono.mono d≤d'

  H₁ : (((D≤ ×-poset E≤) →mono-pw D≤) ×-poset (D≤ →mono-pw E≤)) →mono ((E≤ →mono-pw D≤) ×-poset (D≤ →mono-pw E≤))
  Mono.⟦ H₁ ⟧ = H₁-mono
  H₁ .Mono.isMonotone .IsMono.cong (f⃖≈g⃖ , f⃗≈g⃗) = ((λ e → f⃖≈g⃖ (D.⊤ , e)) , (λ d → f⃗≈g⃗ d))
  H₁ .Mono.isMonotone .IsMono.mono (f⃖≤g⃖ , f⃗≤g⃗) = ((λ e → f⃖≤g⃖ (D.⊤ , e)) , (λ d → f⃗≤g⃗ d))

  I₁ : ((E≤ →mono-pw D≤) ×-poset (D≤ →mono-pw E≤)) →mono (((D≤ ×-poset E≤) →mono-pw D≤) ×-poset (D≤ →mono-pw E≤))
  Mono.⟦ I₁ ⟧ = I₁-mono
  I₁ .Mono.isMonotone .IsMono.cong (f⃖≈g⃖ , f⃗≈g⃗) = ((λ p → f⃖≈g⃖ (p .proj₂)) , (λ d → f⃗≈g⃗ d))
  I₁ .Mono.isMonotone .IsMono.mono (f⃖≤g⃖ , f⃗≤g⃗) = ((λ p → f⃖≤g⃖ (p .proj₂)) , (λ d → f⃗≤g⃗ d))

  H₁⊣I₁ : H₁ ⊣ I₁
  H₁⊣I₁ .GaloisConnection.ψ f⃡ g⃡ .proj₁ H₁f⃡≤g⃡ = ((λ p → D.Po.trans (f⃡ .proj₁ .Mono.mono ((D.⊤-max _) , E.Po.refl)) (H₁f⃡≤g⃡ .proj₁ (p .proj₂))) , (λ d → H₁f⃡≤g⃡ .proj₂ d))
  H₁⊣I₁ .GaloisConnection.ψ f⃡ g⃡ .proj₂ f⃡≤I₁g⃡ = ((λ e → f⃡≤I₁g⃡ .proj₁ (D.⊤ , e)) , (λ d → f⃡≤I₁g⃡ .proj₂ d))

  -- The Galois connection between relations and bidirectional functions

  F₁ : 𝒫⊆ →mono ((E≤ →mono-pw D≤) ×-poset (D≤ →mono-pw E≤))
  F₁ = H₁ ∘-mono F₀

  G₁ : ((E≤ →mono-pw D≤) ×-poset (D≤ →mono-pw E≤)) →mono 𝒫⊆
  G₁ = G₀ ∘-mono I₁

  F₁⊣G₁ : F₁ ⊣ G₁
  F₁⊣G₁ = F₀⊣G₀ ∘-galois H₁⊣I₁

  IsBowTie : (R : Pred (D≈ ×-setoid E≈)) → (d : D) (e : E) (d₀ : D) (e₀ : E) (d₁ : D) (e₁ : E) → Set
  IsBowTie R d e d₀ e₀ d₁ e₁ = d₀ D.≤ d × e₀ E.≤ e × d D.≤ d₁ × e E.≤ e₁ × (d₀ , e₁) ∈ R × (d₁ , e₀) ∈ R

  IsBowTieConnecting : (R : Pred (D≈ ×-setoid E≈)) → Set
  IsBowTieConnecting R = ∀ d e d₀ e₀ d₁ e₁ → IsBowTie R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R

  -- the property BowtieConecting is not closed under ⋈ but by adding monotonicity and square filling property
  -- it becomes closed under ⋈ (TODO: proof)
  -- This class seems quite narrow (possibly it only carries information as much as the unidirectional case does)
  Is⋈FriendlyBowTieConnecting : (R : Pred (D≈ ×-setoid E≈)) → Set
  Is⋈FriendlyBowTieConnecting R = IsTiltBowTieConnecting R × IsMonotoneRelation R × IsSquareFilling R

  bowtie→≤⨆ : (R : Pred (D≈ ×-setoid E≈)) → ∀ d e → Σ d₀ ∶ D , Σ e₀ ∶ E , Σ d₁ ∶ D , Σ e₁ ∶ E , IsBowTie R d e d₀ e₀ d₁ e₁ → d D.≤ (D.⨆ ((↓! (D.⊤ , e) ∩ R) ∣₁)) × e E.≤ (E.⨆ ((↓! (d , E.⊤) ∩ R) ∣₂))
  bowtie→≤⨆ R d e (d₀ , e₀ , d₁ , e₁ , d₀≤d , e₀≤e , d≤d₁ , e≤e₁ , d₀e₁∈R , d₁e₀∈R) =
    ( D.Po.trans d≤d₁ (D.⨆-ub ((↓! (D.⊤ , e) ∩ R) ∣₁) d₁ (e₀ , (D.⊤-max _ , e₀≤e) , d₁e₀∈R))
    , E.Po.trans e≤e₁ (E.⨆-ub ((↓! (d , E.⊤) ∩ R) ∣₂) e₁ (d₀ , (d₀≤d , E.⊤-max _) , d₀e₁∈R)))


  module _ where
    open GaloisConnection
    preG₁F₁-explicit : (R : Pred (D≈ ×-setoid E≈))
      → (R ∈ preRL F₁⊣G₁)
      ↔ (((d , e) : D × E) → (d D.≤ D.⨆ ((↓! (D.⊤ , e) ∩ R) ∣₁)) × (e E.≤ E.⨆ ((↓! (d , E.⊤) ∩ R) ∣₂)) → (d , e) ∈ R)
    preG₁F₁-explicit R = (λ- , _$-)

    preG₁F₁-characterization : (R : Pred (D≈ ×-setoid E≈)) → (R ∈ preRL F₁⊣G₁) ↔ (∀ d e d₀ e₀ d₁ e₁ → IsBowTie R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R) × (Is⨆Closed (D⨆ ×-slat E⨆) R)
    preG₁F₁-characterization R = (α , α⁻¹)
      where
      α₁ : (R ∈ preRL F₁⊣G₁) → (∀ d e d₀ e₀ d₁ e₁ → IsBowTie R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R)
      α₁ R∈preG₀F₀ d e d₀ e₀ d₁ e₁ bowtie = R∈preG₀F₀ (bowtie→≤⨆ R d e (d₀ , e₀ , d₁ , e₁ , bowtie))

      α₂ : (R ∈ preRL F₁⊣G₁) → (Is⨆Closed (D⨆ ×-slat E⨆) R)
      α₂ = preGF-characterization R .proj₁ ∘ preRL-∘-⊆ F⊣G (H₀⊣I₀ ∘-galois H₁⊣I₁) {R}

      α : (R ∈ preRL F₁⊣G₁) → (∀ d e d₀ e₀ d₁ e₁ → IsBowTie R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R) × Is⨆Closed (D⨆ ×-slat E⨆) R
      α = Product.< α₁ , α₂ >

      α⁻¹ : (∀ d e d₀ e₀ d₁ e₁ → IsBowTie R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R) × Is⨆Closed (D⨆ ×-slat E⨆) R → (R ∈ preRL F₁⊣G₁)
      α⁻¹ (bowtie→R , ⨆closed) {(d , e)} (d≤⨆↓!⊤e∩R∣₁ , e≤⨆↓!d⊤∩R∣₂) =
         bowtie→R d e
           (D.⨆ ((↓! (d , E.⊤) ∩ R) ∣₁)) (E.⨆ ((↓! (D.⊤ , e) ∩ R) ∣₂))
           (D.⨆ ((↓! (D.⊤ , e) ∩ R) ∣₁)) (E.⨆ ((↓! (d , E.⊤) ∩ R) ∣₂))
           ( d≥⨆↓!d⊤∩R∣₁ , e≥⨆↓!⊤e∩R∣₂
           , d≤⨆↓!⊤e∩R∣₁ , e≤⨆↓!d⊤∩R∣₂
           , ⨆closed (↓! (d , E.⊤) ∩ R) (∩-⊆-r (↓! (d , E.⊤)) R)
           , ⨆closed (↓! (D.⊤ , e) ∩ R) (∩-⊆-r (↓! (D.⊤ , e)) R))
         where
         d≥⨆↓!d⊤∩R∣₁ : D.⨆ ((↓! (d , E.⊤) ∩ R) ∣₁) D.≤ d
         d≥⨆↓!d⊤∩R∣₁ = D.⨆-least ((↓! (d , E.⊤) ∩ R) ∣₁) d (λ d₀ (e₀ , (d₀≤d , e₀≤e) , d₀e₀∈R) → d₀≤d)

         e≥⨆↓!⊤e∩R∣₂ : E.⨆ ((↓! (D.⊤ , e) ∩ R) ∣₂) E.≤ e
         e≥⨆↓!⊤e∩R∣₂ = E.⨆-least ((↓! (D.⊤ , e) ∩ R) ∣₂) e (λ d₀ (e₀ , (d₀≤d , e₀≤e) , d₀e₀∈R) → e₀≤e)


  -- H₂ : ((E≤ →mono-pw D≤) ×-poset (D≤ →mono-pw E≤)) →mono ((E≤ →mono-pw D≤) ×-poset E≤)
  -- I₂ : ((E≤ →mono-pw D≤) ×-poset E≤) →mono ((E≤ →mono-pw D≤) ×-poset (D≤ →mono-pw E≤))

  module _ where
    H₂-raw : (E → D) × (D → E) → (E → D) × E
    H₂-raw (f⃖ , f⃗) = (f⃖ , f⃗ D.⊤)

    H₂-mono : (E≤ →mono D≤) × (D≤ →mono E≤) → (E≤ →mono D≤) × E
    Mono.⟦ H₂-mono (f⃖ , f⃗) .proj₁ ⟧ = H₂-raw (⟦ f⃖ ⟧ , ⟦ f⃗ ⟧) .proj₁
    H₂-mono (f⃖ , f⃗) .proj₁ .Mono.isMonotone .IsMono.cong e≈e' = f⃖ .Mono.isMonotone .IsMono.cong e≈e'
    H₂-mono (f⃖ , f⃗) .proj₁ .Mono.isMonotone .IsMono.mono e≤e' = f⃖ .Mono.isMonotone .IsMono.mono e≤e'
    H₂-mono (f⃖ , f⃗) .proj₂ = H₂-raw (⟦ f⃖ ⟧ , ⟦ f⃗ ⟧) .proj₂

    I₂-raw : (E → D) × E → (E → D) × (D → E)
    I₂-raw (f⃖ , e₀) = (f⃖ , const e₀)

    I₂-mono : (E≤ →mono D≤) × E → (E≤ →mono D≤) × (D≤ →mono E≤)
    Mono.⟦ I₂-mono (f⃖ , e₀) .proj₁ ⟧ = I₂-raw (⟦ f⃖ ⟧ , e₀) .proj₁
    I₂-mono (f⃖ , e₀) .proj₁ .Mono.isMonotone .IsMono.cong e≈e' = f⃖ .Mono.isMonotone .IsMono.cong e≈e'
    I₂-mono (f⃖ , e₀) .proj₁ .Mono.isMonotone .IsMono.mono e≤e' = f⃖ .Mono.isMonotone .IsMono.mono e≤e'
    Mono.⟦ I₂-mono (f⃖ , e₀) .proj₂ ⟧ = I₂-raw (⟦ f⃖ ⟧ , e₀) .proj₂
    I₂-mono (f⃖ , e₀) .proj₂ .Mono.isMonotone .IsMono.cong d≈d' = E.Eq.refl
    I₂-mono (f⃖ , e₀) .proj₂ .Mono.isMonotone .IsMono.mono d≤d' = E.Po.refl

  H₂ : ((E≤ →mono-pw D≤) ×-poset (D≤ →mono-pw E≤)) →mono ((E≤ →mono-pw D≤) ×-poset E≤)
  Mono.⟦ H₂ ⟧ = H₂-mono
  H₂ .Mono.isMonotone .IsMono.cong f⃡≈g⃡ = ((λ e → f⃡≈g⃡ .proj₁ e) , f⃡≈g⃡ .proj₂ D.⊤)
  H₂ .Mono.isMonotone .IsMono.mono f⃡≤g⃡ = ((λ e → f⃡≤g⃡ .proj₁ e) , f⃡≤g⃡ .proj₂ D.⊤)

  I₂ : ((E≤ →mono-pw D≤) ×-poset E≤) →mono ((E≤ →mono-pw D≤) ×-poset (D≤ →mono-pw E≤))
  Mono.⟦ I₂ ⟧ = I₂-mono
  I₂ .Mono.isMonotone .IsMono.cong (f≈g , e₀≈e₀') = (f≈g , const e₀≈e₀')
  I₂ .Mono.isMonotone .IsMono.mono (f≤g , e₀≤e₀') = (f≤g , const e₀≤e₀')

  H₂⊣I₂ : H₂ ⊣ I₂
  H₂⊣I₂ .GaloisConnection.ψ f⃡ g⃖e₀ .proj₁ H₂f⃡≤g⃖e₀ = ((λ e → H₂f⃡≤g⃖e₀ .proj₁ e) , (λ d → E.Po.trans (f⃡ .proj₂ .Mono.mono (D.⊤-max d)) (H₂f⃡≤g⃖e₀ .proj₂)))
  H₂⊣I₂ .GaloisConnection.ψ f⃡ g⃖e₀ .proj₂ f⃡≤I₂g⃖e₀ = ((λ e → f⃡≤I₂g⃖e₀ .proj₁ e) , f⃡≤I₂g⃖e₀ .proj₂ D.⊤)

  -- The Galois connection between relations and backward functions with forward constants

  F₂ : 𝒫⊆ →mono ((E≤ →mono-pw D≤) ×-poset E≤)
  F₂ = H₂ ∘-mono F₁

  G₂ : ((E≤ →mono-pw D≤) ×-poset E≤) →mono 𝒫⊆
  G₂ = G₁ ∘-mono I₂

  F₂⊣G₂ : F₂ ⊣ G₂
  F₂⊣G₂ = F₁⊣G₁ ∘-galois H₂⊣I₂

  IsLooseBowTie : (R : Pred (D≈ ×-setoid E≈)) → (d : D) (e : E) (d₀ : D) (e₀ : E) (d₁ : D) (e₁ : E) → Set
  IsLooseBowTie R d e d₀ e₀ d₁ e₁ = e₀ E.≤ e × d D.≤ d₁ × e E.≤ e₁ × (d₀ , e₁) ∈ R × (d₁ , e₀) ∈ R

  IsLooseBowTieConnecting : (R : Pred (D≈ ×-setoid E≈)) → Set
  IsLooseBowTieConnecting R = ∀ d e d₀ e₀ d₁ e₁ → IsLooseBowTie R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R

  IsFanOut : (R : Pred (D≈ ×-setoid E≈)) → (d : D) (e : E) (e₀ : E) (e₁ : E) → Set
  IsFanOut R d e e₀ e₁ = e₀ E.≤ e × e E.≤ e₁ × (d , e₁) ∈ R × (d , e₀) ∈ R

  IsFanOutConnecting : (R : Pred (D≈ ×-setoid E≈)) → Set
  IsFanOutConnecting R = ∀ d e e₀ e₁ → IsFanOut R d e e₀ e₁ → (d , e) ∈ R

  IsLowerIn : (R : Pred (D≈ ×-setoid E≈)) → (d : D) (e : E) (d₁ : D) → Set
  IsLowerIn R d e d₁ = d D.≤ d₁ × (d₁ , e) ∈ R

  IsLowerInConnecting : (R : Pred (D≈ ×-setoid E≈)) → Set
  IsLowerInConnecting R = ∀ d e d₁ → IsLowerIn R d e d₁ → (d , e) ∈ R

  ⨆closed→loosebowtieconnecting↔fanoutconnecting×lowerinconnecting : (R : Pred (D≈ ×-setoid E≈)) → Is⨆Closed (D⨆ ×-slat E⨆) R → IsLooseBowTieConnecting R ↔ IsFanOutConnecting R × IsLowerInConnecting R
  ⨆closed→loosebowtieconnecting↔fanoutconnecting×lowerinconnecting R R-⨆closed .proj₁ φ .proj₁ d e e₀ e₁ (e₀≤e , e≤e₁ , de₁∈R , de₀∈R) = φ d e d e₀ d e₁ (e₀≤e , D.Po.refl , e≤e₁ , de₁∈R , de₀∈R)
  ⨆closed→loosebowtieconnecting↔fanoutconnecting×lowerinconnecting R R-⨆closed .proj₁ φ .proj₂ d e d₁ (d≤d₁ , d₁e∈R) = φ d e d₁ e d₁ e (E.Po.refl , d≤d₁ , E.Po.refl , d₁e∈R , d₁e∈R)
  ⨆closed→loosebowtieconnecting↔fanoutconnecting×lowerinconnecting R R-⨆closed .proj₂ (α , β) d e d₀ e₀ d₁ e₁ (e₀≤e , d≤d₁ , e≤e₁ , d₀e₁∈R , d₁e₀∈R)
    = de∈R
    where
    R-⊔closed : Is⊔Closed (D⨆ ×-slat E⨆) R
    R-⊔closed = ⨆closed→⊔closed (D⨆ ×-slat E⨆) R R-⨆closed

    d' : D
    d' = d₀ D.⊔ d₁

    d₀e₁⊔d₁e₀≈d'e₁ : ((d₀ , e₁) ⊔ (d₁ , e₀)) ≈ (d' , e₁)
    d₀e₁⊔d₁e₀≈d'e₁ = Eq.trans
      (⊔-componentwise D⨆ E⨆ d₀ e₁ d₁ e₀)
      (D.Eq.refl , E.Eq.trans (E.⊔-comm e₁ e₀) (E.≤→⊔-≈ e₀ e₁ (E.Po.trans e₀≤e e≤e₁)))

    d₀e₁⊔d₁e₀∈R : ((d₀ , e₁) ⊔ (d₁ , e₀)) ∈ R
    d₀e₁⊔d₁e₀∈R = R-⊔closed (d₀ , e₁) (d₁ , e₀) d₀e₁∈R d₁e₀∈R

    d'e₁∈R : (d' , e₁) ∈ R
    d'e₁∈R = R .Pred.isWellDefined d₀e₁⊔d₁e₀≈d'e₁ d₀e₁⊔d₁e₀∈R

    de₁∈R : (d , e₁) ∈ R
    de₁∈R = β d e₁ d' (D.Po.trans d≤d₁ (D.⊔-ub-r d₀ d₁) , d'e₁∈R)

    de₀∈R : (d , e₀) ∈ R
    de₀∈R = β d e₀ d₁ (d≤d₁ , d₁e₀∈R)

    de∈R : (d , e) ∈ R
    de∈R = α d e e₀ e₁ (e₀≤e , e≤e₁ , de₁∈R , de₀∈R)

  loosebowtie→≤⨆ : (R : Pred (D≈ ×-setoid E≈))
    → ∀ d e
    → Σ d₀ ∶ D , Σ e₀ ∶ E , Σ d₁ ∶ D , Σ e₁ ∶ E , IsLooseBowTie R d e d₀ e₀ d₁ e₁
    → d D.≤ D.⨆ ((↓! (D.⊤ , e) ∩ R) ∣₁) × e E.≤ E.⨆ ((↓! (D.⊤ , E.⊤) ∩ R) ∣₂)
  loosebowtie→≤⨆ R d e (d₀ , e₀ , d₁ , e₁ , e₀≤e , d≤d₁ , e≤e₁ , d₀e₁∈R , d₁e₀∈R) =
    ( D.Po.trans d≤d₁ (D.⨆-ub ((↓! (D.⊤ , e) ∩ R) ∣₁) d₁ (e₀ , (D.⊤-max _ , e₀≤e) , d₁e₀∈R))
    , E.Po.trans e≤e₁ (E.⨆-ub ((↓! (D.⊤ , E.⊤) ∩ R) ∣₂) e₁ (d₀ , (D.⊤-max _ , E.⊤-max _) , d₀e₁∈R)))

  module _ where
    open GaloisConnection
    preG₂F₂-explicit : (R : Pred (D≈ ×-setoid E≈))
      → (R ∈ preRL F₂⊣G₂)
      ↔ (((d , e) : D × E) →  d D.≤ D.⨆ ((↓! (D.⊤ , e) ∩ R) ∣₁) × e E.≤ E.⨆ ((↓! (D.⊤ , E.⊤) ∩ R) ∣₂) → (d , e) ∈ R)
    preG₂F₂-explicit R = (λ- , _$-)

    preG₂F₂-characterization : (R : Pred (D≈ ×-setoid E≈))
      → (R ∈ preRL F₂⊣G₂)
      ↔ ((∀ d e d₀ e₀ d₁ e₁ → IsLooseBowTie R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R) × (Is⨆Closed (D⨆ ×-slat E⨆) R))
    preG₂F₂-characterization R = (α , α⁻¹)
     where
     α₁ : (R ∈ preRL F₂⊣G₂) → (∀ d e d₀ e₀ d₁ e₁ → IsLooseBowTie R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R)
     α₁ R∈preG₂F₂ d e d₀ e₀ d₁ e₁ fan = R∈preG₂F₂ (loosebowtie→≤⨆ R d e (d₀ , e₀ , d₁ , e₁ , fan))

     α₂ : (R ∈ preRL F₂⊣G₂) → Is⨆Closed (D⨆ ×-slat E⨆) R
     α₂ = preGF-characterization R .proj₁ ∘ preRL-∘-⊆ F⊣G (H₀⊣I₀ ∘-galois H₁⊣I₁ ∘-galois H₂⊣I₂) {R}

     α : (R ∈ preRL F₂⊣G₂) → (∀ d e d₀ e₀ d₁ e₁ → IsLooseBowTie R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R) × Is⨆Closed (D⨆ ×-slat E⨆) R
     α = Product.< α₁ , α₂ >

     α⁻¹ : ((∀ d e d₀ e₀ d₁ e₁ → IsLooseBowTie R d e d₀ e₀ d₁ e₁ → (d , e) ∈ R) × Is⨆Closed (D⨆ ×-slat E⨆) R) → (R ∈ preRL F₂⊣G₂)
     α⁻¹ (fan→R , ⨆closed) {(d , e)} (d≤⨆↓!⊤e∩R∣₁ , e≤⨆↓!⊤⊤∩R∣₂) =
       fan→R d e
         (D.⨆ ((↓! (D.⊤ , E.⊤) ∩ R) ∣₁)) (E.⨆ ((↓! (D.⊤ , e) ∩ R) ∣₂))
         (D.⨆ ((↓! (D.⊤ , e) ∩ R) ∣₁)) (E.⨆ ((↓! (D.⊤ , E.⊤) ∩ R) ∣₂))
         ( E.⨆-least _ _ (λ e₀ (d₀ , (d₀≤⊤ , e₀≤e) , d₀e₀∈R) → e₀≤e)
         , d≤⨆↓!⊤e∩R∣₁
         , e≤⨆↓!⊤⊤∩R∣₂
         , ⨆closed (↓! (D.⊤ , E.⊤) ∩ R) (∩-⊆-r (↓! (D.⊤ , E.⊤)) R)
         , ⨆closed (↓! (D.⊤ , e) ∩ R) (∩-⊆-r (↓! (D.⊤ , e)) R))

  -- We define the following galois connection
  --
  -- ((E →m D) × E , ≤)
  --   H₃ ↓! ⊣ ↑! I₃
  -- ((E →m D) , ≤)

  module _ where
    H₃-raw : (E → D) × E → (E → D)
    H₃-raw (f⃖ , e₀) = f⃖

    H₃-mono : (E≤ →mono D≤) × E → (E≤ →mono D≤)
    H₃-mono (f⃖ , e₀) = f⃖

    I₃-raw : (E → D) → (E → D) × E
    I₃-raw f⃖ = (f⃖ , E.⊤)

    I₃-mono : (E≤ →mono D≤) → (E≤ →mono D≤) × E
    I₃-mono f⃖ = (f⃖ , E.⊤)

  H₃ : ((E≤ →mono-pw D≤) ×-poset E≤) →mono (E≤ →mono-pw D≤)
  Mono.⟦ H₃ ⟧ = H₃-mono
  H₃ .Mono.isMonotone .IsMono.cong f⃖ᶜ≈g⃖ᶜ e = f⃖ᶜ≈g⃖ᶜ .proj₁ e
  H₃ .Mono.isMonotone .IsMono.mono f⃖ᶜ≤g⃖ᶜ e = f⃖ᶜ≤g⃖ᶜ .proj₁ e

  I₃ : (E≤ →mono-pw D≤) →mono ((E≤ →mono-pw D≤) ×-poset E≤)
  Mono.⟦ I₃ ⟧ = I₃-mono
  I₃ .Mono.isMonotone .IsMono.cong f⃖≈g⃖ = f⃖≈g⃖ , E.Eq.refl
  I₃ .Mono.isMonotone .IsMono.mono f⃖≤g⃖ = f⃖≤g⃖ , E.Po.refl

  H₃⊣I₃ : H₃ ⊣ I₃
  H₃⊣I₃ .GaloisConnection.ψ f⃖ᶜ f⃖ .proj₁ H₃f⃖ᶜ≤f⃖ = (λ e → H₃f⃖ᶜ≤f⃖ e) , E.⊤-max _
  H₃⊣I₃ .GaloisConnection.ψ f⃖ᶜ f⃖ .proj₂ f⃖ᶜ≤I₃f⃖ e = f⃖ᶜ≤I₃f⃖ .proj₁ e

  -- The Galois connection between relations and backward functions
  F₃ : 𝒫⊆ →mono (E≤ →mono-pw D≤)
  F₃ = H₃ ∘-mono F₂

  G₃ : (E≤ →mono-pw D≤) →mono 𝒫⊆
  G₃ = G₂ ∘-mono I₃

  F₃⊣G₃ : F₃ ⊣ G₃
  F₃⊣G₃ = F₂⊣G₂ ∘-galois H₃⊣I₃

  IsTilt : (R : Pred (D≈ ×-setoid E≈)) → (d : D) (e : E) (e₀ : E) (d₁ : D) → Set
  IsTilt R d e e₀ d₁ = e₀ E.≤ e × d D.≤ d₁ × (d₁ , e₀) ∈ R

  IsTiltConnecting : (R : Pred (D≈ ×-setoid E≈)) → Set
  IsTiltConnecting R = ∀ d e e₀ d₁ → IsTilt R d e e₀ d₁ → (d , e) ∈ R

  tilt→≤⨆ : (R : Pred (D≈ ×-setoid E≈)) → ∀ d e → (Σ e₀ ∶ E , Σ d₁ ∶ D , IsTilt R d e e₀ d₁) → d D.≤ D.⨆ ((↓! (D.⊤ , e) ∩ R) ∣₁) × e E.≤ E.⊤
  tilt→≤⨆ R d e (e₀ , d₁ , e₀≤e , d≤d₁ , d₁e₀∈R) =
    ( D.Po.trans d≤d₁ (D.⨆-ub ((↓! (D.⊤ , e) ∩ R) ∣₁) d₁ (e₀ , ((D.⊤-max d₁ , e₀≤e) , d₁e₀∈R)))
    , E.⊤-max e)

  module _ where
    open GaloisConnection
    preG₃F₃-explicit : (R : Pred (D≈ ×-setoid E≈))
      → (R ∈ preRL F₃⊣G₃)
      ↔ (((d , e) : D × E) → d D.≤ D.⨆ ((↓! (D.⊤ , e) ∩ R) ∣₁) × e E.≤ E.⊤ → (d , e) ∈ R)
    preG₃F₃-explicit R = (λ- , _$-)

    preG₃F₃-characterization : (R : Pred (D≈ ×-setoid E≈))
      → (R ∈ preRL F₃⊣G₃)
      ↔ (∀ d e e₀ d₁ → IsTilt R d e e₀ d₁ → (d , e) ∈ R) × (Is⨆Closed (D⨆ ×-slat E⨆) R)
    preG₃F₃-characterization R = (α , α⁻¹)
      where
      α₁ : (R ∈ preRL F₃⊣G₃) → (∀ d e e₀ d₁ → IsTilt R d e e₀ d₁ → (d , e) ∈ R)
      α₁ R∈preG₃F₃ d e e₀ d₁ tilt = R∈preG₃F₃ (tilt→≤⨆ R d e (e₀ , d₁ , tilt))

      α₂ : (R ∈ preRL F₃⊣G₃) → (Is⨆Closed (D⨆ ×-slat E⨆) R)
      α₂ = preGF-characterization R .proj₁ ∘ preRL-∘-⊆ F⊣G (H₀⊣I₀ ∘-galois H₁⊣I₁ ∘-galois H₂⊣I₂ ∘-galois H₃⊣I₃) {R}

      α : R ∈ preRL F₃⊣G₃ → (∀ d e e₀ d₁ → IsTilt R d e e₀ d₁ → (d , e) ∈ R) × (Is⨆Closed (D⨆ ×-slat E⨆) R)
      α = Product.< α₁ , α₂ >

      α⁻¹ : (∀ d e e₀ d₁ → IsTilt R d e e₀ d₁ → (d , e) ∈ R) × (Is⨆Closed (D⨆ ×-slat E⨆) R) → R ∈ preRL F₃⊣G₃
      α⁻¹ (tilt→R , ⨆closed) {(d , e)} (d≤⨆↓!⊤e∩R∣₁ , e≤⊤) =
        tilt→R d e
          (proj₂ (⨆ (↓! (D.⊤ , e) ∩ R))) (proj₁ (⨆ (↓! (D.⊤ , e) ∩ R)))
          (e≥⨆↓!⊤e∩R∣₂ , d≤⨆↓!⊤e∩R∣₁ , ⨆closed (↓! (D.⊤ , e) ∩ R) (∩-⊆-r (↓! (D.⊤ , e)) R))
        where
        e≥⨆↓!⊤e∩R∣₂ : E.⨆ ((↓! (D.⊤ , e) ∩ R) ∣₂) E.≤ e
        e≥⨆↓!⊤e∩R∣₂ = E.⨆-least ((↓! (D.⊤ , e) ∩ R) ∣₂) e (λ e₀ (d₁ , ((d₁≤⊤ , e₀≤e) , d₁e₀∈R)) → e₀≤e)

module _ {C D : Poset} (F : C →mono D) where
  -- Definition of monoidal properties for non-indexed binary operation on poset maps
  open PosetPoly D
  -- probably monoidal is not a right word for this property (it only refers to multiplication and not to unit)

  IsLaxMonoidal : (_⊗C_ : Op₂ ∣ C ∣) (_⊗D_ : Op₂ ∣ D ∣) → Set
  IsLaxMonoidal _⊗C_ _⊗D_ = (a b : ∣ C ∣ ) → ⟦ F ⟧ a ⊗D ⟦ F ⟧ b ≤ ⟦ F ⟧ (a ⊗C b)

  IsOplaxMonoidal : (_⊗C_ : Op₂ ∣ C ∣) (_⊗D_ : Op₂ ∣ D ∣) → Set
  IsOplaxMonoidal _⊗C_ _⊗D_ = (a b : ∣ C ∣ ) → ⟦ F ⟧ (a ⊗C b) ≤ ⟦ F ⟧ a ⊗D ⟦ F ⟧ b

  IsMonoidal : (_⊗C_ : Op₂ ∣ C ∣) (_⊗D_ : Op₂ ∣ D ∣) → Set
  IsMonoidal _⊗C_ _⊗D_ = (a b : ∣ C ∣ ) → ⟦ F ⟧ (a ⊗C b) ≈ ⟦ F ⟧ a ⊗D ⟦ F ⟧ b

  lax∧oplax→monoidal : (_⊗C_ : Op₂ ∣ C ∣) (_⊗D_ : Op₂ ∣ D ∣)
    → IsLaxMonoidal _⊗C_ _⊗D_
    → IsOplaxMonoidal _⊗C_ _⊗D_
    → IsMonoidal _⊗C_ _⊗D_
  lax∧oplax→monoidal _⊗C_ _⊗D_ lax oplax a b = antisym (oplax a b) (lax a b)


module _ {C D : Poset}  {L : C →mono D} {R : D →mono C} where
  -- Definition of lifting of (non-indexed) binary operation on a poset along with an adjunction
  liftOpAlong⊣ : (L⊣R : L ⊣ R) (_⊗C_ : Op₂ ∣ C ∣) → Op₂ ∣ D ∣
  liftOpAlong⊣ L⊣R _⊗C_ a b = ⟦ L ⟧ (⟦ R ⟧ a ⊗C ⟦ R ⟧ b)


module _
  (C≈ : Setoid) where
  -- General results about ∩ and its lift along with any ⊣

  private
    𝒫⊆ = Pred⊆-poset C≈

  module _ {D≤ : Poset} {L : 𝒫⊆ →mono D≤} {R : D≤ →mono 𝒫⊆} (L⊣R : L ⊣ R) where
    private
      open PosetPoly D≤
      D≈ = PosetPoly.Eq.setoid D≤
      D = ∣ D≤ ∣
      _[∩]_ : Op₂ ∣ D≤ ∣
      _[∩]_ = liftOpAlong⊣ L⊣R _∩_
      open GaloisConnection L⊣R

    -- Any right adjoint functor to 𝒫⊆ is lax monoidal wrt [∩]
    [∩]-∩-right-adjoint-lax-monoidal : IsLaxMonoidal R _[∩]_ _∩_
    [∩]-∩-right-adjoint-lax-monoidal a b = η (⟦ R ⟧ a ∩ ⟦ R ⟧ b)

    -- Any left adjoint functor from 𝒫⊆ is oplax monoidal wrt ∩
    ∩-[∩]-left-adjoint-oplax-monoidal : IsOplaxMonoidal L _∩_ _[∩]_
    ∩-[∩]-left-adjoint-oplax-monoidal S S' = L .Mono.mono ((∩-mono S (⟦ R ⟧ (⟦ L ⟧ S)) S' (⟦ R ⟧ (⟦ L ⟧ S')) (η S) (η S')))

    -- If a set of fixed points of an adjunction is closed under ∩ then so is the image of the right adjoint
    preRL-∩closed→∩∈imageR : ((S S' : Pred C≈) → S ∈ preRL → S' ∈ preRL → (S ∩ S') ∈ preRL) → ((a b : D) → Σ c ∶ D , (⟦ R ⟧ c ≐ (⟦ R ⟧ a ∩ ⟦ R ⟧ b)))
    preRL-∩closed→∩∈imageR preRL-∩closed a b =
      let
      Ra∩Rb∈preRL : (⟦ R ⟧ a ∩ ⟦ R ⟧ b) ∈ preRL
      Ra∩Rb∈preRL = preRL-∩closed (⟦ R ⟧ a) (⟦ R ⟧ b) (R∈preRL a) (R∈preRL b)
      in
      preRL⊆imageR Ra∩Rb∈preRL

    -- If an image of a right adjoint is closed under ∩ then the right adjoint is oplax monoidal wrt [∩] and ∩
    ∩∈imageR→[∩]-∩-right-adjoint-oplax-monoidal :
      ((a b : D) → Σ c ∶ D , (⟦ R ⟧ c ≐ (⟦ R ⟧ a ∩ ⟦ R ⟧ b))) → IsOplaxMonoidal R _[∩]_ _∩_
    ∩∈imageR→[∩]-∩-right-adjoint-oplax-monoidal ∩∈imageR a b =
      let
      (c , Rc≐Ra∩Rb) = ∩∈imageR a b -- we have c such that ⟦ R ⟧ c ≐ ⟦ R ⟧ a ∩ ⟦ R ⟧ b
      open PosetReasoning (Pred⊆-poset C≈)
      in
      begin
      ⟦ R ⟧ (a [∩] b)                      ≡⟨⟩
      ⟦ R ∘-mono L ⟧ (⟦ R ⟧ a ∩ ⟦ R ⟧ b)   ≈˘⟨ (R ∘-mono L) .Mono.cong Rc≐Ra∩Rb ⟩
      ⟦ R ∘-mono L ⟧ (⟦ R ⟧ c)             ≈⟨ RLR≈R c  ⟩
      ⟦ R ⟧ c                              ≈⟨ Rc≐Ra∩Rb ⟩
      ⟦ R ⟧ a ∩ ⟦ R ⟧ b                    ∎

    preRL-∩closed→[∩]-∩-right-adjoint-oplax-monoidal :
      ((S S' : Pred C≈) → S ∈ preRL → S' ∈ preRL → (S ∩ S') ∈ preRL)
      → IsOplaxMonoidal R _[∩]_ _∩_
    preRL-∩closed→[∩]-∩-right-adjoint-oplax-monoidal
      = ∩∈imageR→[∩]-∩-right-adjoint-oplax-monoidal
      ∘ preRL-∩closed→∩∈imageR

    [∩]-∩-right-adjoint-oplax-monoidal→monoidal :
      IsOplaxMonoidal R _[∩]_ _∩_
      → IsMonoidal R _[∩]_ _∩_
    [∩]-∩-right-adjoint-oplax-monoidal→monoidal oplax =
      lax∧oplax→monoidal R _[∩]_ _∩_ [∩]-∩-right-adjoint-lax-monoidal oplax


module _
  (Index : Set) where
  -- Definitions for indexed binary operations

  module _
    (P Q : Index → Index → Poset)
    (F : (C D : Index) → P C D →mono Q C D)
    where
    -- Monoidal properties between indexed posets

    module _
      (C D E : Index)
      (_⊗P_ : ∣ P C D ∣ → ∣ P D E ∣ → ∣ P C E ∣)
      (_⊗Q_ : ∣ Q C D ∣ → ∣ Q D E ∣ → ∣ Q C E ∣)
      where

      open PosetPoly (Q C E)
      IsIndexedLaxMonoidal : Set
      IsIndexedLaxMonoidal = (a : ∣ P C D ∣) → (b : ∣ P D E ∣) → ⟦ F C D ⟧ a ⊗Q ⟦ F D E ⟧ b ≤ ⟦ F C E ⟧ (a ⊗P b)

      IsIndexedOplaxMonoidal : Set
      IsIndexedOplaxMonoidal = (a : ∣ P C D ∣) → (b : ∣ P D E ∣) → ⟦ F C E ⟧ (a ⊗P b) ≤ ⟦ F C D ⟧ a ⊗Q ⟦ F D E ⟧ b

      IsIndexedMonoidal : Set
      IsIndexedMonoidal = (a : ∣ P C D ∣) → (b : ∣ P D E ∣) → ⟦ F C E ⟧ (a ⊗P b) ≈ ⟦ F C D ⟧ a ⊗Q ⟦ F D E ⟧ b

  module _ (P Q : Index → Index → Poset) where
    -- Definition of lifting of an indexed binary operation on a poset along with an adjunction
    module _ {L : (C D : Index) → P C D →mono Q C D} {R : (C D : Index) → Q C D →mono P C D} (L⊣R : (C D : Index) → L C D ⊣ R C D) where
      indexedLiftOpAlong⊣ : (C D E : Index) → (∣ P C D ∣ → ∣ P D E ∣ → ∣ P C E ∣) → (∣ Q C D ∣ → ∣ Q D E ∣ → ∣ Q C E ∣)
      indexedLiftOpAlong⊣ C D E _⊗P_ a b = ⟦ L C E ⟧ (⟦ R C D ⟧ a ⊗P ⟦ R D E ⟧ b)

  module _ (∣_∣Ix : Index → Setoid) where
    -- general results about ⋈ and ⊣
    private
      𝒫⊆ : Index → Index → Poset
      𝒫⊆ C D = Pred⊆-poset (∣ C ∣Ix ×-setoid ∣ D ∣Ix)


    module _ (P≤ : Index → Index → Poset)
      {L : (C D : Index) → 𝒫⊆ C D →mono P≤ C D}
      {R : (C D : Index) → P≤ C D →mono 𝒫⊆ C D}
      (L⊣R : (C D : Index) → L C D ⊣ R C D) where

      private module _ (C D : Index) where
        open GaloisConnection (L⊣R C D) public

      private module _ {C D E : Index} where
          _[⋈]_ : ∣ P≤ C D ∣ → ∣ P≤ D E ∣ → ∣ P≤ C E ∣
          _[⋈]_ = indexedLiftOpAlong⊣ 𝒫⊆ P≤ L⊣R C D E _⋈_

      module _ (C D E : Index) where
        private
          C≈ = ∣ C ∣Ix
          D≈ = ∣ D ∣Ix
          E≈ = ∣ E ∣Ix

        [⋈]-⋈-right-adjoint-lax-monoidal : IsIndexedLaxMonoidal P≤ 𝒫⊆ R C D E _[⋈]_ _⋈_
        [⋈]-⋈-right-adjoint-lax-monoidal a b = η C E (⟦ R C D ⟧ a ⋈ ⟦ R D E ⟧ b)

        ⋈-[⋈]-left-adjoint-oplax-monoidal : IsIndexedOplaxMonoidal 𝒫⊆ P≤  L C D E _⋈_ _[⋈]_
        ⋈-[⋈]-left-adjoint-oplax-monoidal S S' = L C E .Mono.mono (⋈-mono S (⟦ R C D ∘-mono L C D ⟧ S) S' (⟦ (R D E ∘-mono L D E) ⟧ S') (η C D S) (η D E S'))

        PreRL⋈Closed = ((S : Pred (C≈ ×-setoid D≈)) (S' : Pred (D≈ ×-setoid E≈)) → S ∈ preRL C D → S' ∈ preRL D E → (S ⋈ S') ∈ preRL C E)
        ⋈∈ImageR = ((a : ∣ P≤ C D ∣) (b : ∣ P≤ D E ∣) → Σ c ∶ ∣ P≤ C E ∣ , (⟦ R C E ⟧ c ≐ (⟦ R C D ⟧ a ⋈ ⟦ R D E ⟧ b)))

        preRL-⋈closed→⋈∈imageR : PreRL⋈Closed → ⋈∈ImageR
        preRL-⋈closed→⋈∈imageR preRL-⋈closed a b =
          let
          Ra⋈Rb∈preRL : (⟦ R C D ⟧ a ⋈ ⟦ R D E ⟧ b) ∈ preRL C E
          Ra⋈Rb∈preRL = preRL-⋈closed (⟦ R C D ⟧ a) (⟦ R D E ⟧ b) (R∈preRL _ _ a) (R∈preRL _ _ b)
          in
          preRL⊆imageR _ _ Ra⋈Rb∈preRL

        ⋈∈imageR→[⋈]-⋈-right-adjoint-oplax-monoidal : ⋈∈ImageR → IsIndexedOplaxMonoidal P≤ 𝒫⊆  R C D E _[⋈]_ _⋈_
        ⋈∈imageR→[⋈]-⋈-right-adjoint-oplax-monoidal ⋈∈imageR a b =
            let
            (c , Rc≐Ra⋈Rb) = ⋈∈imageR a b
            _ : typeOf Rc≐Ra⋈Rb ≡ (⟦ R C E ⟧ c ≐ (⟦ R C D ⟧ a ⋈ ⟦ R D E ⟧ b)) -- debug
            _ = ≡.refl
            open PosetReasoning (Pred⊆-poset (∣ C ∣Ix ×-setoid ∣ E ∣Ix))
            in
            begin
            ⟦ R C E ⟧ (a [⋈] b)                                  ≡⟨⟩
            ⟦ R C E ∘-mono L C E ⟧ (⟦ R C D ⟧ a ⋈ ⟦ R D E ⟧ b)   ≈˘⟨ (R _ _ ∘-mono L _ _) .Mono.cong Rc≐Ra⋈Rb ⟩
            ⟦ R C E ∘-mono L C E ⟧ (⟦ R C E ⟧ c)                  ≈⟨ RLR≈R _ _ c  ⟩
            ⟦ R C E ⟧ c                                           ≈⟨ Rc≐Ra⋈Rb ⟩
            ⟦ R C D ⟧ a ⋈ ⟦ R D E ⟧ b                            ∎

        preRL-⋈closed→[⋈]-⋈-right-adjoint-oplax-monoidal : PreRL⋈Closed → IsIndexedOplaxMonoidal P≤ 𝒫⊆  R C D E _[⋈]_ _⋈_
        preRL-⋈closed→[⋈]-⋈-right-adjoint-oplax-monoidal
          = ⋈∈imageR→[⋈]-⋈-right-adjoint-oplax-monoidal
          ∘ preRL-⋈closed→⋈∈imageR

module CheckOplaxMonoidalityForIntersection where
  -- Here we check the oplax-monoidality of G G₀ G₁ G₂ G₃, wrt ∩ and [∩], ⋈ and [⋈]

  module F⊣G (C⨆ : SLat) where
    private
      module C = SLat C⨆
      C≤ = SLat.poset C⨆
      C≈ = SLat.Eq.setoid C⨆
      C = ∣ C⨆ ∣
      open SLat C⨆
      open 𝒫⊆-and-Endo C⨆
      open GaloisConnection F⊣G
      -- naive operation for nondeterministic choice
      _[∩]_ : Op₂ ∣ Endo ∣
      _[∩]_ = liftOpAlong⊣ F⊣G _∩_

      h : ∣ Endo ∣ → ∣ Endo ∣ → C → C≈ →cong C≈
      Cong.⟦ h f g p₀ ⟧ p = p₀ ⊓ (⟦ f ⟧ p ⊓ ⟦ g ⟧ p)
      h f g p₀ .Cong.isCongruent .IsCong.cong {p} {p'} p≈p' =
        ⊓-cong p₀ (⟦ f ⟧ p ⊓ ⟦ g ⟧ p) p₀ (⟦ f ⟧ p' ⊓ ⟦ g ⟧ p')
          C.Eq.refl
          (⊓-cong (⟦ f ⟧ p) (⟦ g ⟧ p) (⟦ f ⟧ p') (⟦ g ⟧ p')
                  (f .Mono.cong p≈p') (g .Mono.cong p≈p'))

    -- [∩] can be written by ν
    [∩]-ν-representation : ∀ f g p₀ → ⟦ f [∩] g ⟧ p₀ ≈ ν (h f g p₀)
    [∩]-ν-representation f g p₀ =
      ⨆-cong (↓! p₀ ∩ (⟦ G ⟧ f ∩ ⟦ G ⟧ g)) (post poset (h f g p₀))
        (∀↔→≐ {X≈ = C≈} {↓! p₀ ∩ (⟦ G ⟧ f ∩ ⟦ G ⟧ g)} {post poset (h f g p₀)} φ)
      where
      lhs = λ p → p ≤ p₀ × (p ≤ ⟦ f ⟧ p) × (p ≤ ⟦ g ⟧ p)
      rhs = λ p → p ≤ (p₀ ⊓ (⟦ f ⟧ p ⊓ ⟦ g ⟧ p))
      φ : ∀ p → lhs p ↔ rhs p
      φ p =
        let open SetoidReasoning Prop↔-setoid in
        begin
        (p ≤ p₀ × ((p ≤ ⟦ f ⟧ p) × (p ≤ ⟦ g ⟧ p))) ≈˘⟨ ( (id , id) ×-↔ ≤⊓↔≤× _ _ _) ⟩
        (p ≤ p₀ × (p ≤ (⟦ f ⟧ p ⊓ ⟦ g ⟧ p))) ≈˘⟨ ≤⊓↔≤× _ _ _ ⟩
        (p ≤ (p₀ ⊓ (⟦ f ⟧ p ⊓ ⟦ g ⟧ p))) ∎



    ∩-⨆closed : (R R' : Pred C≈) → Is⨆Closed C⨆ R → Is⨆Closed C⨆ R' → Is⨆Closed C⨆ (R ∩ R')
    ∩-⨆closed R R' R-⨆closed R'-⨆closed S S⊆R∩R' = (R-⨆closed S (proj₁ ∘ S⊆R∩R') , R'-⨆closed S (proj₂ ∘ S⊆R∩R'))

    ∩-preRL-closed : (R R' : Pred C≈) → R ∈ preRL → R' ∈ preRL → (R ∩ R') ∈ preRL
    ∩-preRL-closed R R' R∈preRL R'∈preRL =
      preGF-characterization (R ∩ R') .proj₂
        (∩-⨆closed R R'
          (preGF-characterization R .proj₁ R∈preRL)
          (preGF-characterization R' .proj₁ R'∈preRL))

    [∩]-∩-oplax-monoidal : IsOplaxMonoidal G _[∩]_ _∩_
    [∩]-∩-oplax-monoidal = preRL-∩closed→[∩]-∩-right-adjoint-oplax-monoidal C≈ F⊣G ∩-preRL-closed

    [∩]-∩-lax-monoidal : IsLaxMonoidal G _[∩]_ _∩_
    [∩]-∩-lax-monoidal = [∩]-∩-right-adjoint-lax-monoidal C≈ F⊣G

    [∩]-∩-monoidal : IsMonoidal G _[∩]_ _∩_
    [∩]-∩-monoidal = [∩]-∩-right-adjoint-oplax-monoidal→monoidal (C≈) F⊣G [∩]-∩-oplax-monoidal

    -- show exsistance of cheaper (efficient) version of operation that is also oplax-monoidal
    private
      _[⊓]_ : Op₂ ∣ Endo ∣ -- The pointwise meet (_⊓_)
      Mono.⟦ f [⊓] g ⟧ c = ⟦ f ⟧ c ⊓ ⟦ g ⟧ c
      (f [⊓] g) .Mono.isMonotone .IsMono.mono c≤c' = ⊓-mono _ _ _ _ (f .Mono.mono c≤c') (g .Mono.mono c≤c')
      (f [⊓] g) .Mono.isMonotone .IsMono.cong c≈c' = Po.antisym ((f [⊓] g) .Mono.isMonotone .IsMono.mono (Po.reflexive c≈c')) (((f [⊓] g) .Mono.isMonotone .IsMono.mono (Po.reflexive (Eq.sym c≈c'))))

      [∩]≤[⊓] : (f g : ∣ Endo ∣) → (c : C) → ⟦ f [∩] g ⟧ c ≤ ⟦ f [⊓] g ⟧ c
      [∩]≤[⊓] f g c = ⨆-mono (↓! c ∩ (⟦ G ⟧ f ∩ ⟦ G ⟧ g)) (lowerbounds poset (｛ ⟦ f ⟧ c ｝ ∪ ｛ ⟦ g ⟧ c ｝)) ⊆
        where
        open PosetReasoning C≤
        ⊆ : (↓! c ∩ (⟦ G ⟧ f ∩ ⟦ G ⟧ g)) ⊆ (lowerbounds poset (｛ ⟦ f ⟧ c ｝ ∪ ｛ ⟦ g ⟧ c ｝))
        ⊆ {x} (x≤c , x≤fx , x≤gx) x' (inj₁ fc≈x') = begin x ≤⟨ x≤fx ⟩ ⟦ f ⟧ x ≤⟨ f .Mono.mono x≤c ⟩ ⟦ f ⟧ c ≈⟨ fc≈x' ⟩ x' ∎
        ⊆ {x} (x≤c , x≤fx , x≤gx) x' (inj₂ gc≈x') = begin x ≤⟨ x≤gx ⟩ ⟦ g ⟧ x ≤⟨ g .Mono.mono x≤c ⟩ ⟦ g ⟧ c ≈⟨ gc≈x' ⟩ x' ∎

      [⊓]-∩-oplax-monoidal : IsOplaxMonoidal G _[⊓]_ _∩_
      [⊓]-∩-oplax-monoidal f g =
        let open PosetReasoning 𝒫⊆ in
        begin
        ⟦ G ⟧ (f [⊓] g) ≤⟨ (λ {x} → φ x) ⟩
        (⟦ G ⟧ f ∩ ⟦ G ⟧ g ) ∎
        where
        f⊓g : Endo .PosetPoly.Carrier
        Mono.⟦ f⊓g ⟧ c = ⟦ f ⟧ c ⊓ ⟦ g ⟧ c
        f⊓g .Mono.isMonotone .IsMono.mono {c} {c'} c≤c' = ⊓-mono (⟦ f ⟧ c) (⟦ g ⟧ c) (⟦ f ⟧ c') (⟦ g ⟧ c') (f .Mono.mono c≤c') (g .Mono.mono c≤c')
        f⊓g .Mono.isMonotone .IsMono.cong c≈c' = Po.antisym
          (f⊓g .Mono.isMonotone .IsMono.mono (Po.reflexive c≈c'))
          (f⊓g .Mono.isMonotone .IsMono.mono (Po.reflexive (Eq.sym c≈c')))

        φ : ∀ x → x ∈ (⟦ G ⟧ (f [⊓] g)) → x ∈ (⟦ G ⟧ f ∩ ⟦ G ⟧ g)
        φ x x∈G[f⊓g] =
          ( G .Mono.mono {f⊓g} {f} (λ c → ⊓-lb-l (⟦ f ⟧ c) (⟦ g ⟧ c)) x∈G[f⊓g]
          , G .Mono.mono {f⊓g} {g} (λ c → ⊓-lb-r (⟦ f ⟧ c) (⟦ g ⟧ c)) x∈G[f⊓g])

      [⊓]-∩-lax-monoidal : IsLaxMonoidal G _[⊓]_ _∩_
      [⊓]-∩-lax-monoidal f g =
        let open PosetReasoning 𝒫⊆ in
        begin
        (⟦ G ⟧ f ∩ ⟦ G ⟧ g) ≈˘⟨ [∩]-∩-monoidal f g  ⟩
        ⟦ G ⟧ (f [∩] g) ≤⟨ G .Mono.mono {f[∩]g} {f⊓g} ([∩]≤[⊓] f g) ⟩
        ⟦ G ⟧ (f [⊓] g) ∎
        where
        f[∩]g : ∣ Endo ∣
        Mono.⟦ f[∩]g ⟧ c = ⟦ f [∩] g ⟧ c
        f[∩]g .Mono.isMonotone .IsMono.mono {c} {c'} c≤c' = ⨆-mono (↓! c ∩ (⟦ G ⟧ f ∩ ⟦ G ⟧ g)) (↓! c' ∩ (⟦ G ⟧ f ∩ ⟦ G ⟧ g)) λ {x} (x≤c , P) → (Po.trans x≤c c≤c' , P)
        f[∩]g .Mono.isMonotone .IsMono.cong {c} {c'} c≈c' = Po.antisym
          (f[∩]g .Mono.isMonotone .IsMono.mono (Po.reflexive c≈c'))
          (f[∩]g .Mono.isMonotone .IsMono.mono (Po.reflexive (Eq.sym c≈c')))

        f⊓g : ∣ Endo ∣
        Mono.⟦ f⊓g ⟧ c = ⟦ f ⟧ c ⊓ ⟦ g ⟧ c
        f⊓g .Mono.isMonotone .IsMono.mono {c} {c'} c≤c' = ⊓-mono (⟦ f ⟧ c) (⟦ g ⟧ c) (⟦ f ⟧ c') (⟦ g ⟧ c') (f .Mono.mono c≤c') (g .Mono.mono c≤c')
        f⊓g .Mono.isMonotone .IsMono.cong c≈c' = Po.antisym
          (f⊓g .Mono.isMonotone .IsMono.mono (Po.reflexive c≈c'))
          (f⊓g .Mono.isMonotone .IsMono.mono (Po.reflexive (Eq.sym c≈c')))


      [⊓]-∩-monoidal : IsMonoidal G _[⊓]_ _∩_
      [⊓]-∩-monoidal = lax∧oplax→monoidal G _[⊓]_ _∩_ [⊓]-∩-lax-monoidal [⊓]-∩-oplax-monoidal


  module _ (D⨆ E⨆ : SLat) where
    private
      D≤ = SLat.poset D⨆
      D≈ = SLat.Eq.setoid D⨆
      D = ∣ D⨆ ∣
      module D = SLat D⨆

      E≤ = SLat.poset E⨆
      E≈ = SLat.Eq.setoid E⨆
      E = ∣ E⨆ ∣
      module E = SLat E⨆

      open 𝒫⊆-and-Endo (D⨆ ×-slat E⨆)

    module F₀⊣G₀ where
      private
        _[∩]_ = liftOpAlong⊣ (F₀⊣G₀ D⨆ E⨆) _∩_
        open GaloisConnection (F₀⊣G₀ D⨆ E⨆)
      ∩-tiltbowtieclosed : (R R' : Pred (D≈ ×-setoid E≈))
        → IsTiltBowTieConnecting D⨆ E⨆ R → IsTiltBowTieConnecting D⨆ E⨆ R' → IsTiltBowTieConnecting D⨆ E⨆ (R ∩ R')
      ∩-tiltbowtieclosed R R' R-closed R'-closed d e d₀ e₀ e₁ (d₀≤d , e₀≤e , e≤e₁ , (d₀e₁∈R , d₀e₁∈R') , (de₀∈R , de₀∈R'))
        = (R-closed d e d₀ e₀ e₁ (d₀≤d , e₀≤e , e≤e₁ , d₀e₁∈R , de₀∈R)) , R'-closed d e d₀ e₀ e₁ (d₀≤d , e₀≤e , e≤e₁ , d₀e₁∈R' , de₀∈R')

      ∩-preRL-closed : (R R' : Pred (D≈ ×-setoid E≈)) → R ∈ preRL → R' ∈ preRL → (R ∩ R') ∈ preRL
      ∩-preRL-closed R R' R∈preRL R'∈preRL =
        preG₀F₀-characterization D⨆ E⨆ (R ∩ R') .proj₂
          ( ∩-tiltbowtieclosed R R'
            (preG₀F₀-characterization D⨆ E⨆ R .proj₁ R∈preRL .proj₁)
            (preG₀F₀-characterization D⨆ E⨆ R' .proj₁ R'∈preRL .proj₁)
          , F⊣G.∩-⨆closed (D⨆ ×-slat E⨆) R R'
            (preG₀F₀-characterization D⨆ E⨆ R .proj₁ R∈preRL .proj₂)
            (preG₀F₀-characterization D⨆ E⨆ R' .proj₁ R'∈preRL .proj₂))

      [∩]-∩-oplax-monoidal : IsOplaxMonoidal (G₀ D⨆ E⨆) _[∩]_ _∩_
      [∩]-∩-oplax-monoidal = preRL-∩closed→[∩]-∩-right-adjoint-oplax-monoidal (D≈ ×-setoid E≈) (F₀⊣G₀ D⨆ E⨆) ∩-preRL-closed


    module F₁⊣G₁ where
      private
        _[∩]_ = liftOpAlong⊣ (F₁⊣G₁ D⨆ E⨆) _∩_
        open GaloisConnection (F₁⊣G₁ D⨆ E⨆)
      ∩-bowtieclosed : (R R' : Pred (D≈ ×-setoid E≈))
        → IsBowTieConnecting D⨆ E⨆ R → IsBowTieConnecting D⨆ E⨆ R' → IsBowTieConnecting D⨆ E⨆ (R ∩ R')
      ∩-bowtieclosed R R' R-closed R'-closed d e d₀ e₀ d₁ e₁ (d₀≤d , e₀≤e , d≤d₁ , e≤e₁ , (d₀e₁∈R , d₀e₁∈R') , (d₁e₀∈R , d₁e₀∈R'))
        = (R-closed d e d₀ e₀ d₁ e₁ (d₀≤d , e₀≤e , d≤d₁ , e≤e₁ , d₀e₁∈R , d₁e₀∈R)) , R'-closed d e d₀ e₀ d₁ e₁ (d₀≤d , e₀≤e , d≤d₁ , e≤e₁ , d₀e₁∈R' , d₁e₀∈R')

      ∩-preRL-closed : (R R' : Pred (D≈ ×-setoid E≈)) → R ∈ preRL → R' ∈ preRL → (R ∩ R') ∈ preRL
      ∩-preRL-closed R R' R∈preRL R'∈preRL =
        preG₁F₁-characterization D⨆ E⨆ (R ∩ R') .proj₂
          ( ∩-bowtieclosed R R'
            (preG₁F₁-characterization D⨆ E⨆ R .proj₁ R∈preRL .proj₁)
            (preG₁F₁-characterization D⨆ E⨆ R' .proj₁ R'∈preRL .proj₁)
          , F⊣G.∩-⨆closed (D⨆ ×-slat E⨆) R R'
            (preG₁F₁-characterization D⨆ E⨆ R .proj₁ R∈preRL .proj₂)
            (preG₁F₁-characterization D⨆ E⨆ R' .proj₁ R'∈preRL .proj₂))

      [∩]-∩-oplax-monoidal : IsOplaxMonoidal (G₁ D⨆ E⨆) _[∩]_ _∩_
      [∩]-∩-oplax-monoidal = preRL-∩closed→[∩]-∩-right-adjoint-oplax-monoidal (D≈ ×-setoid E≈) (F₁⊣G₁ D⨆ E⨆) ∩-preRL-closed

    -- TODO: show [∩]-∩-oplax-monoidal for F₂⊣G₂ and F₃⊣G₃ (this must be as easy as F₀⊣G₀ and F₁⊣F₂)
    --
module CheckOplaxMonoidalityForComposition where
  private
    module _ (C⨆ D⨆ : SLat) where
      open 𝒫⊆-and-Endo (C⨆ ×-slat D⨆) public

  module F⊣G where
    private
      module _ (C⨆ D⨆ : SLat) where
        open GaloisConnection (F⊣G C⨆ D⨆) public

    module _ (C⨆ D⨆ E⨆ : SLat) where
      private
        _[⋈]_ : ∣ Endo C⨆ D⨆ ∣ → ∣ Endo D⨆ E⨆ ∣ → ∣ Endo C⨆ E⨆ ∣
        _[⋈]_ = indexedLiftOpAlong⊣ SLat 𝒫⊆ Endo F⊣G C⨆ D⨆ E⨆ _⋈_
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

      ⋈-⨆closed : (R : Pred (C≈ ×-setoid D≈)) (R' : Pred (D≈ ×-setoid E≈)) → Is⨆Closed (C⨆ ×-slat D⨆) R → Is⨆Closed (D⨆ ×-slat E⨆) R' → Is⨆Closed (C⨆ ×-slat E⨆) (R ⋈ R')
      ⋈-⨆closed R R' R-⨆closed R'-⨆closed S S⊆R⋈R' = (⨆T₂ , [⨆S₁,⨆T₂]∈R , [⨆T₂,⨆S₂]∈R')
        where

        -- We define a subset T ⊆ C × D × E where eath tuple (c , d , e) ∈ T ,  (c,e) ∈ S and d mediates c and d , i.e, (c,d) ∈ R (d,e) ∈ R'.
        -- Note: Sinse S ⊆ R ⋈ R', (c,e)∈S already implies existence of the mediator d n D.
        T : Pred (C≈ ×-setoid (D≈ ×-setoid E≈))
        Pred.⟦ T ⟧ (c , d , e) = (c , e) ∈ S × (c , d) ∈ R × (d , e) ∈ R'
        T .Pred.isWellDefined (c≈c' , d≈d' , e≈e') (ce∈S , cd∈R , de∈R') = (S .Pred.isWellDefined (c≈c' , e≈e') ce∈S , R .Pred.isWellDefined (c≈c' , d≈d') cd∈R , R' .Pred.isWellDefined (d≈d' , e≈e') de∈R')

        -- A bunch of equalities between projections of T and S
        T₁ = T ∣₁
        T₂ = (T ∣₂) ∣₁
        T₃ = (T ∣₂) ∣₂

        S₁ = S ∣₁
        S₂ = S ∣₂

        S₁≐T₁ : S₁ ≐ T₁
        S₁≐T₁ .proj₁ (e , ce∈S) =
          let
          (d , cde∈T) = S⊆R⋈R' ce∈S
          in
          ((d , e) , (ce∈S , cde∈T))
        S₁≐T₁ .proj₂ ((d , e) , (ce∈S , cde∈T)) = (e , ce∈S)

        S₂≐T₃ : S₂ ≐ T₃
        S₂≐T₃ .proj₁ (c , ce∈S) =
          let
          (d , cde∈T) = S⊆R⋈R' ce∈S
          in
          (d , c , ce∈S , cde∈T)
        S₂≐T₃ .proj₂ (d , c , ce∈S , cde∈T) = (c , ce∈S)

        T₁₂ : Pred (C≈ ×-setoid D≈)
        T₁₂ = (Pred-assoc-rl T) ∣₁

        T₂₃ : Pred (D≈ ×-setoid E≈)
        T₂₃ = T ∣₂

        [T₁₂]₁≐T₁ : (T₁₂ ∣₁) ≐ T₁
        [T₁₂]₁≐T₁ .proj₁ (d , e , cde∈T) = ((d , e) , cde∈T)
        [T₁₂]₁≐T₁ .proj₂ ((d , e) , cde∈T) = (d , e , cde∈T)

        [T₁₂]₂≐T₂ : (T₁₂ ∣₂) ≐ T₂
        [T₁₂]₂≐T₂ .proj₁ (c , e , cde∈T) = (e , c , cde∈T)
        [T₁₂]₂≐T₂ .proj₂ (e , c , cde∈T) = (c , e , cde∈T)

        -- One can easily check T₁₂ ⊆ R and T₂₃ ⊆ R'.
        -- Then, we get
        -- (1) ⨆ S₁ , ⨆ T₂ ≈ ⨆ T₁₂ ∈ R by S₁ ≐ T₁ and join closeness of R
        -- (2) ⨆ T₂ , ⨆ S₂ ≈ ⨆ T₂₃ ∈ R' by S₂ ≐ T₃ and join closeness of R'
        -- ⨆ S ∈ R ⋈ R' is witnessed by the intermediate element ⨆ T₂
        T₁₂⊆R : T₁₂ ⊆ R
        T₁₂⊆R (e , ce∈S , cd∈R , de∈R') = cd∈R

        T₂₃⊆R' : T₂₃ ⊆ R'
        T₂₃⊆R' (c , ce∈S , cd∈R , de∈R') = de∈R'

        module _ where
          open SLat (C⨆ ×-slat (D⨆ ×-slat E⨆))
          ⨆T : C × D × E
          ⨆T = ⨆ T

          ⨆T₁ = let (c , _ , _) = ⨆T in c
          ⨆T₂ = let (_ , d , _) = ⨆T in d
          ⨆T₃ = let (_ , _ , e) = ⨆T in e

        module _ where
          open SLat (C⨆ ×-slat E⨆)
          ⨆S = ⨆ S
          ⨆S₁ = let (c , _) = ⨆S in c
          ⨆S₂ = let (_ , e) = ⨆S in e

        ⨆S₁≈⨆T₁ : ⨆S₁ C.≈ ⨆T₁
        ⨆S₁≈⨆T₁ = C.⨆-cong S₁ T₁ S₁≐T₁

        ⨆S₂≈⨆T₃ : ⨆S₂ E.≈ ⨆T₃
        ⨆S₂≈⨆T₃ = E.⨆-cong S₂ T₃ S₂≐T₃

        module _ where
          open SLat (C⨆ ×-slat D⨆)
          ⨆T₁₂∈R : ⨆ T₁₂ ∈ R
          ⨆T₁₂∈R = R-⨆closed T₁₂ T₁₂⊆R

          ⨆T₁₂≈[⨆T₁,⨆T₂] : ⨆ T₁₂ ≈ (⨆T₁ , ⨆T₂)
          ⨆T₁₂≈[⨆T₁,⨆T₂] =
            ( C.⨆-cong (T₁₂ ∣₁) T₁ [T₁₂]₁≐T₁
            , D.⨆-cong (T₁₂ ∣₂) T₂ [T₁₂]₂≐T₂)

          [⨆T₁,⨆T₂]∈R : (⨆T₁ , ⨆T₂) ∈ R
          [⨆T₁,⨆T₂]∈R = R .Pred.isWellDefined ⨆T₁₂≈[⨆T₁,⨆T₂] ⨆T₁₂∈R

          [⨆S₁,⨆T₂]∈R : (⨆S₁ , ⨆T₂) ∈ R
          [⨆S₁,⨆T₂]∈R = R .Pred.isWellDefined (C.Eq.sym ⨆S₁≈⨆T₁ , D.Eq.refl) [⨆T₁,⨆T₂]∈R

        module _ where
          open SLat (D⨆ ×-slat E⨆)
          [⨆T₂,⨆T₃]∈R' : (⨆T₂ , ⨆T₃) ∈ R'
          [⨆T₂,⨆T₃]∈R' = R'-⨆closed T₂₃ T₂₃⊆R'

          [⨆T₂,⨆S₂]∈R' : (⨆T₂ , ⨆S₂) ∈ R'
          [⨆T₂,⨆S₂]∈R' = R' .Pred.isWellDefined (D.Eq.refl , E.Eq.sym ⨆S₂≈⨆T₃) [⨆T₂,⨆T₃]∈R'

      ⋈-preRL-closed : (R : Pred (C≈ ×-setoid D≈)) (R' : Pred (D≈ ×-setoid E≈)) → R ∈ preRL C⨆ D⨆ → R' ∈ preRL D⨆ E⨆ → (R ⋈ R') ∈ preRL C⨆ E⨆
      ⋈-preRL-closed R R' R∈preGF R'∈preGF =
        preGF-characterization C⨆ E⨆ (R ⋈ R') .proj₂
          (⋈-⨆closed R R'
            (preGF-characterization C⨆ D⨆ R .proj₁ R∈preGF)
            (preGF-characterization D⨆ E⨆ R' .proj₁ R'∈preGF))

      [⋈]-⋈-oplax-monoidal :  IsIndexedOplaxMonoidal SLat Endo 𝒫⊆ G C⨆ D⨆ E⨆ _[⋈]_ _⋈_
      [⋈]-⋈-oplax-monoidal =  preRL-⋈closed→[⋈]-⋈-right-adjoint-oplax-monoidal SLat SLat.Eq.setoid Endo F⊣G C⨆ D⨆ E⨆ ⋈-preRL-closed

      -- TODO: show cheaper (efficient) version of oplax-monoidal operation
      private
        h : ∣ Endo C⨆ D⨆ ∣ → ∣ Endo D⨆ E⨆ ∣ → (C × E) → D≈ →cong D≈
        Cong.⟦ h f g (c₀ , e₀) ⟧  d = (⟦ f ⟧ (c₀ , d) .proj₂) D.⊓ (⟦ g ⟧ (d , e₀) .proj₁)
        h f g (c₀ , e₀) .Cong.isCongruent .IsCong.cong {d} {d'} d≈d' =
          D.⊓-cong (⟦ f ⟧ (c₀ , d) .proj₂) (⟦ g ⟧ (d , e₀) .proj₁) (⟦ f ⟧ (c₀ , d') .proj₂) (⟦ g ⟧ (d' , e₀) .proj₁)
            (proj₂-mono C≤ D≤ .IsMono.cong (f .Mono.cong (C.Eq.refl , d≈d')))
            (proj₁-mono D≤ E≤ .IsMono.cong (g .Mono.cong (d≈d' , E.Eq.refl)))

        _⊠_ : ∣ Endo C⨆ D⨆ ∣ → ∣ Endo D⨆ E⨆ ∣ → ∣ Endo C⨆ E⨆ ∣
        Mono.⟦ f ⊠ g ⟧ (c₀ , e₀) = (⟦ f ⟧ (c₀ , d₀ (c₀ , e₀)) .proj₁ , ⟦ g ⟧ (d₀ (c₀ , e₀) , e₀) .proj₂)
          where
          d₀ : C × E → D
          d₀ (c₀ , e₀) = D.ν (h f g (c₀ , e₀))

        (f ⊠ g) .Mono.isMonotone .IsMono.mono {(c , e)} {(c' , e')} (c≤c' , e≤e')
          = proj₁-mono C≤ D≤ .IsMono.mono (f .Mono.mono
            ( c≤c'
            , D.ν-mono (h f g (c , e)) (h f g (c' , e'))
                       (λ d →
                         D.⊓-mono (⟦ f ⟧ (c , d) .proj₂) (⟦ g ⟧ (d , e) .proj₁) (⟦ f ⟧ (c' , d) .proj₂) (⟦ g ⟧ (d , e') .proj₁)
                                  (proj₂-mono C≤ D≤ .IsMono.mono (f .Mono.mono (c≤c' , D.Po.refl)))
                                  (proj₁-mono D≤ E≤ .IsMono.mono (g .Mono.mono (D.Po.refl , e≤e'))))))
          , proj₂-mono D≤ E≤ .IsMono.mono (g .Mono.mono
            ( D.ν-mono (h f g (c , e)) (h f g (c' , e'))
                       (λ d →
                         D.⊓-mono (⟦ f ⟧ (c , d) .proj₂) (⟦ g ⟧ (d , e) .proj₁) (⟦ f ⟧ (c' , d) .proj₂) (⟦ g ⟧ (d , e') .proj₁)
                                  (proj₂-mono C≤ D≤ .IsMono.mono (f .Mono.mono (c≤c' , D.Po.refl)))
                                  (proj₁-mono D≤ E≤ .IsMono.mono (g .Mono.mono (D.Po.refl , e≤e'))))
            , e≤e'))
        (f ⊠ g) .Mono.isMonotone .IsMono.cong ce≈ce' = PosetPoly.antisym (C≤ ×-poset E≤)
          ((f ⊠ g) .Mono.isMonotone .IsMono.mono (PosetPoly.reflexive (C≤ ×-poset E≤) ce≈ce'))
          ((f ⊠ g) .Mono.isMonotone .IsMono.mono (PosetPoly.reflexive (C≤ ×-poset E≤) (PosetPoly.Eq.sym (C≤ ×-poset E≤) ce≈ce')))

  module F₂⊣G₂ where
    private
      module _ (C⨆ D⨆ : SLat) where
        open GaloisConnection (F₂⊣G₂ C⨆ D⨆) public
    module _ (C⨆ D⨆ E⨆ : SLat) where
      private
        _[⋈]_ = indexedLiftOpAlong⊣ SLat 𝒫⊆ _ F₂⊣G₂ C⨆ D⨆ E⨆ _⋈_
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

      ⋈-⨆closed×loosebowtieconnecting : (R : Pred (C≈ ×-setoid D≈)) (R' : Pred (D≈ ×-setoid E≈))
        → IsLooseBowTieConnecting C⨆ D⨆ R × Is⨆Closed (C⨆ ×-slat D⨆) R
        → IsLooseBowTieConnecting D⨆ E⨆ R' × Is⨆Closed (D⨆ ×-slat E⨆) R'
        → IsLooseBowTieConnecting C⨆ E⨆ (R ⋈ R') × Is⨆Closed (C⨆ ×-slat E⨆) (R ⋈ R')
      ⋈-⨆closed×loosebowtieconnecting R R' (R-loosebowtieconnecting , R-⨆closed) (R'-loosebowtieconnecting , R'-⨆closed) = R⋈R'-loosebowtieconnecting , R⋈R'-⨆closed
        where
        R⋈R'-⨆closed = F⊣G.⋈-⨆closed C⨆ D⨆ E⨆ R R' R-⨆closed R'-⨆closed

        R-fanoutconnecting = ⨆closed→loosebowtieconnecting↔fanoutconnecting×lowerinconnecting C⨆ D⨆ R R-⨆closed .proj₁ R-loosebowtieconnecting .proj₁
        R-lowerinconnecting = ⨆closed→loosebowtieconnecting↔fanoutconnecting×lowerinconnecting C⨆ D⨆ R R-⨆closed .proj₁ R-loosebowtieconnecting .proj₂

        R'-fanoutconnecting = ⨆closed→loosebowtieconnecting↔fanoutconnecting×lowerinconnecting D⨆ E⨆ R' R'-⨆closed .proj₁ R'-loosebowtieconnecting .proj₁
        R'-lowerinconnecting = ⨆closed→loosebowtieconnecting↔fanoutconnecting×lowerinconnecting D⨆ E⨆ R' R'-⨆closed .proj₁ R'-loosebowtieconnecting .proj₂

        R⋈R'-lowerinconnecting : IsLowerInConnecting C⨆ E⨆ (R ⋈ R')
        R⋈R'-lowerinconnecting c e c₁ (c≤c₁ , c₁e∈R⋈R' @ (d , c₁d∈R , de∈R')) = d , R-lowerinconnecting c d c₁ (c≤c₁ , c₁d∈R) , de∈R'

        R⋈R'-fanoutconnecting : IsFanOutConnecting C⨆ E⨆ (R ⋈ R')
        R⋈R'-fanoutconnecting c e e₀ e₁ (e₀≤e , e≤e₁ , (ce₁∈R⋈R' @ (d₁ , cd₁∈R , d₁e₁∈R')) , (ce₀∈R⋈R' @ (d₀ , cd₀∈R , d₀e₀∈R'))) = ce∈R⋈R'
          where
          d' = d₀ D.⊔ d₁

          private module _ where
            open SLat (D⨆ ×-slat E⨆)

            R'-⊔closed : Is⊔Closed (D⨆ ×-slat E⨆) R'
            R'-⊔closed = ⨆closed→⊔closed (D⨆ ×-slat E⨆) R' R'-⨆closed

            d₀e₀⊔d₁e₀∈R' : ((d₀ , e₀) ⊔ (d₁ , e₁)) ∈ R'
            d₀e₀⊔d₁e₀∈R' = R'-⊔closed  (d₀ , e₀)  (d₁ , e₁) d₀e₀∈R' d₁e₁∈R'

            d₀e₀⊔d₁e₁≈d'e₁ : ((d₀ , e₀) ⊔ (d₁ , e₁)) ≈ (d' , e₁)
            d₀e₀⊔d₁e₁≈d'e₁ = Eq.trans
              (⊔-componentwise D⨆ E⨆ d₀ e₀ d₁ e₁)
              (D.Eq.refl , E.≤→⊔-≈ e₀ e₁ (E.Po.trans e₀≤e e≤e₁))

            d'e₁∈R' : (d' , e₁) ∈ R'
            d'e₁∈R' = R' .Pred.isWellDefined d₀e₀⊔d₁e₁≈d'e₁ d₀e₀⊔d₁e₀∈R'

          d₀≤d' : d₀ D.≤ d'
          d₀≤d' = D.⊔-ub-l d₀ d₁

          d₀e₁∈R' : (d₀ , e₁) ∈ R'
          d₀e₁∈R' = R'-lowerinconnecting d₀ e₁ d' (d₀≤d' , d'e₁∈R')

          d₀e∈R' : (d₀ , e) ∈ R'
          d₀e∈R' = R'-fanoutconnecting d₀ e e₀ e₁ (e₀≤e , e≤e₁ , d₀e₁∈R' , d₀e₀∈R')

          ce∈R⋈R' : (c , e) ∈ (R ⋈ R')
          ce∈R⋈R' = d₀ , cd₀∈R , d₀e∈R'

        R⋈R'-loosebowtieconnecting = ⨆closed→loosebowtieconnecting↔fanoutconnecting×lowerinconnecting C⨆ E⨆ (R ⋈ R') R⋈R'-⨆closed .proj₂ (R⋈R'-fanoutconnecting , R⋈R'-lowerinconnecting)

      ⋈-preRL-closed : (R : Pred (C≈ ×-setoid D≈)) (R' : Pred (D≈ ×-setoid E≈)) → R ∈ preRL C⨆ D⨆ → R' ∈ preRL D⨆ E⨆ → (R ⋈ R') ∈ preRL C⨆ E⨆
      ⋈-preRL-closed R R' R∈preRL R'∈preRL =
        preG₂F₂-characterization C⨆ E⨆ (R ⋈ R') .proj₂
          (⋈-⨆closed×loosebowtieconnecting R R'
            (preG₂F₂-characterization C⨆ D⨆ R .proj₁ R∈preRL)
            (preG₂F₂-characterization D⨆ E⨆ R' .proj₁ R'∈preRL))

      [⋈]-⋈-oplax-monoidal :  IsIndexedOplaxMonoidal SLat _ 𝒫⊆ G₂ C⨆ D⨆ E⨆ _[⋈]_ _⋈_
      [⋈]-⋈-oplax-monoidal = preRL-⋈closed→[⋈]-⋈-right-adjoint-oplax-monoidal SLat SLat.Eq.setoid _ F₂⊣G₂ C⨆ D⨆ E⨆ ⋈-preRL-closed

  module F₃⊣G₃ where
    private
      module _ (C⨆ D⨆ : SLat) where
        open GaloisConnection (F₃⊣G₃ C⨆ D⨆) public
    module _ (C⨆ D⨆ E⨆ : SLat) where
      private
        _[⋈]_ = indexedLiftOpAlong⊣ SLat 𝒫⊆ _ F₃⊣G₃ C⨆ D⨆ E⨆ _⋈_
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

      ⋈-tiltclosed : (R : Pred (C≈ ×-setoid D≈)) (R' : Pred (D≈ ×-setoid E≈)) → IsTiltConnecting C⨆ D⨆ R → IsTiltConnecting D⨆ E⨆ R' → IsTiltConnecting C⨆ E⨆ (R ⋈ R')
      ⋈-tiltclosed R R' R-tiltclosed  R'-tiltclosed c e e₀ c₁ (e₀≤e , c≤c₁ , (d , c₁d∈R , de₀∈R)) =
        (d , R-tiltclosed c d d c₁ (D.Po.refl , c≤c₁ , c₁d∈R) , R'-tiltclosed d e e₀ d (e₀≤e , D.Po.refl , de₀∈R))

      ⋈-preRL-closed : (R : Pred (C≈ ×-setoid D≈)) (R' : Pred (D≈ ×-setoid E≈)) → R ∈ preRL C⨆ D⨆ → R' ∈ preRL D⨆ E⨆ → (R ⋈ R') ∈ preRL C⨆ E⨆
      ⋈-preRL-closed R R' R∈preRL R'∈preRL =
        preG₃F₃-characterization C⨆ E⨆ (R ⋈ R') .proj₂
          ( ⋈-tiltclosed R R'
            (preG₃F₃-characterization C⨆ D⨆ R .proj₁ R∈preRL .proj₁)
            (preG₃F₃-characterization D⨆ E⨆ R' .proj₁ R'∈preRL .proj₁)
          , F⊣G.⋈-⨆closed C⨆ D⨆ E⨆ R R'
            (preG₃F₃-characterization C⨆ D⨆ R .proj₁ R∈preRL .proj₂)
            (preG₃F₃-characterization D⨆ E⨆ R' .proj₁ R'∈preRL .proj₂))

      [⋈]-⋈-oplax-monoidal :  IsIndexedOplaxMonoidal SLat _ 𝒫⊆ G₃ C⨆ D⨆ E⨆ _[⋈]_ _⋈_
      [⋈]-⋈-oplax-monoidal = preRL-⋈closed→[⋈]-⋈-right-adjoint-oplax-monoidal SLat SLat.Eq.setoid _ F₃⊣G₃ C⨆ D⨆ E⨆ ⋈-preRL-closed
