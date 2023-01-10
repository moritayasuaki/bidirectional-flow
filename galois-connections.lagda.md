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
open import complete-lattice
open import function-pair

```

-->

2-poset
-------

https://ncatlab.org/nlab/show/2-poset

- Category of relations:
  - objects: complete lattices, D , E , ...
  - morphisms: relations between objects, r , r' , r'' , ... (𝒫(D × E))
  - compositions: relation composition, r ⨝ r'
  - 2-morphisms: inclusion r ⊆ r'

- Category of monotone endofunctions on products
  - objects: complete lattices, D , E , ...
  - morphisms: monotone endofunctions on product lattice (D × E → D × E)
  - compositions: f ∙ f' := (c , e) ↦ ⋀ { (c' , d , e') |  (c', d') = f (c , d) ∧ (d' , e') = f' (d , e) }
  - 2-morphisms: pointwise ordering

- Category of bidirectional monotone functions
  - objects: complete lattices, D , E , ...
  - morphisms: pairs of forward and backward monotone functions, (f , b) , (f' , b') , ... (D → E × E → D)
  - compositions: composition of forward and backward monotone functions, (f , b) ∙ (f' , b') = (f ∘ f' , b' ∘ b)
  - 2-morphisms: pointwise ordering, (f , b) ≤ (f' , b') := (∀ d, f d ≤ f' d) ∧ (∀ e , b e ≤ b' e)

- Category of monotone functions
  - objects: complete lattices, D , E , ...
  - morphisms: monotone functions f , f' : D → E
  - compositions: function composition f ∘ f'
  - 2-morphisms: pointwise ordering, f ≤ f' := ∀ d, f d ≤ f' d

Those 2-morphisms above are all partial order, i.e Hom categories are thin categories.

There are a number of adjunctions.

```txt
                      r ⊆ pair2rel fb
rel2pair ⊣ pair2rel   ===============
                      rel2pair r ≥ fb
```

```txt
                      r ⊆ endo2rel e
rel2endo ⊣ endo2rel   ===============
                      rel2endo r ≥ e
```

```txt
                      r ⊆ mono2rel f
rel2mono ⊣ mono2rel   ===============
                      rel2mono r ≥ f
```


In homogeneous setting, composition of 2-morphisms is a tensor product in monoidal category
- (D , D) ⊗ (D , D) → (D , D)

```txt
                       rel2pair
                      ---->
            (𝒫(D×E),⊆) ⊥   (D⇒E × E⇒D , ≤) + monotone
                 |    <----    |
                 |     pair2rel     |
                 |             |
            (𝒫(D×E),⊆) ==== (D⇒E × E⇒D , ≤)
            + something       monotone + something
```

The bottom two categories in the diagram are fixed point of adjunction.
Their tensor product does different thing (e.g. adding pair of retation) from the top two.

- rel2pair ∘ pair2rel adds pairs on the relation for butterfly shape relation

```txt
    d     e
    |\   /|
    | \ / |
    d₀ x  e₀  ===> d₀---e₀
    | / \ |
    |/   \|
    d'    e'
```



```agda

module galois-connections where

module transfer-function-pair
  (D-cmlat E-cmlat : complete-meet-semilattice)
  (let D-pre = cmlat→pre D-cmlat)
  (let E-pre = cmlat→pre E-cmlat)
  (let (cmlat D _≤D_ ⋀D D-is-cmlat) = D-cmlat)
  (let (cmlat E _≤E_ ⋀E E-is-cmlat) = E-cmlat)
  where

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

  open _×rel_ _≤D_ _≤E_ renaming (_≈₁_ to _≈D_ ; _≈₂_ to _≈E_)

  _≤fun_ : rel (fun D E) (fun D E)
  f ≤fun f' = ∀ d → f d ≤E f' d

  _≤mfun_ : rel (monotone-func D-pre E-pre) (monotone-func D-pre E-pre)
  mf ≤mfun mf' = mf .func ≤fun mf' .func
    where open monotone-func

  _≤pair_ : rel (func-pair D E) (func-pair D E)
  (f , b) ≤pair (f' , b') = (∀ d → f d ≤E f' d) × (∀ e → b e ≤D b' e)

  _≤mpair_ : rel (monotone-func-pair D-pre E-pre) (monotone-func-pair D-pre E-pre)
  mfb ≤mpair mfb' = mfb .pair ≤pair mfb' .pair
    where open monotone-func-pair

  ≈×≈→≈ : ∀ {d d' e e'} → d ≈D d' → e ≈E e' → (d , e) ≈ (d' , e')
  forward (≈×≈→≈ ≈D ≈E) = forward ≈D , forward ≈E
  backward (≈×≈→≈ ≈D ≈E) = backward ≈D , backward ≈E


  ≅×≅→≅ : ∀ {X Y} {S S' : subset X} {T T' : subset Y} → S ≅ S' → T ≅ T' → ((S ∘ fst) ∩ (T ∘ snd)) ≅ ((S' ∘ fst) ∩ (T' ∘ snd))
  forward (≅×≅→≅ S=S' T=T') (d , e) = (forward S=S' d) , (forward T=T' e)
  backward (≅×≅→≅ S=S' T=T') (d , e) = (backward S=S' d) , (backward T=T' e)

  _≈pair_ = iso-pair _≤pair_
  _≈mpair_ = iso-pair _≤mpair_

  module _ where
    open is-preorder

    ≤fun-is-preorder : is-preorder _≤fun_
    rel-is-reflexive ≤fun-is-preorder f d = E.≤-refl (f d)
    rel-is-transitive ≤fun-is-preorder f≤f' f'≤f'' d = E.≤-trans (f≤f' d) (f'≤f'' d)

    ≤mfun-is-preorder : is-preorder _≤mfun_
    rel-is-reflexive ≤mfun-is-preorder (mono f _) d = E.≤-refl _
    rel-is-transitive ≤mfun-is-preorder f≤f' f'≤f'' d = E.≤-trans (f≤f' d) (f'≤f'' d)

    ≤pair-is-preorder : is-preorder _≤pair_
    fst (rel-is-reflexive ≤pair-is-preorder (f , b)) d = E.≤-refl (f d)
    snd (rel-is-reflexive ≤pair-is-preorder (f , b)) e = D.≤-refl (b e)
    fst (rel-is-transitive ≤pair-is-preorder fb≤fb' fb'≤fb'') d = E.≤-trans (fst fb≤fb' d) (fst fb'≤fb'' d)
    snd (rel-is-transitive ≤pair-is-preorder fb≤fb' fb'≤fb'') e = D.≤-trans (snd fb≤fb' e) (snd fb'≤fb'' e)

    ≤mpair-is-preorder : is-preorder _≤mpair_
    fst (rel-is-reflexive ≤mpair-is-preorder (mfp' (f , b) _)) d = E.≤-refl (f d)
    snd (rel-is-reflexive ≤mpair-is-preorder (mfp' (f , b) _)) e = D.≤-refl (b e)
    fst (rel-is-transitive ≤mpair-is-preorder fb≤fb' fb'≤fb'') d = E.≤-trans (fst fb≤fb' d) (fst fb'≤fb'' d)
    snd (rel-is-transitive ≤mpair-is-preorder fb≤fb' fb'≤fb'') e = D.≤-trans (snd fb≤fb' e) (snd fb'≤fb'' e)

  module _ {R : subset (D × E)}
    (R-welldefined : is-welldefined-subset ≤-pre R)
    (R-meet-closed : is-meet-closed-subset D×E-is-cmlat R) where
    R-subst : ∀{p q} → (iso : p ≈ q) → R p → R q
    R-subst iso = transport ≤-pre →-is-preorder R-welldefined iso

    fst-meet-closed : is-meet-closed-subset D-is-cmlat (fst-subset R)
    fst-meet-closed S₁ S₁⊆R₁ = ⋀E S₂ , ⋀S₁⋀S₂∈R
      where

      counterpart : ∀ {d} → d ∈ S₁ → E
      counterpart d∈S₁ = fst (S₁⊆R₁ d∈S₁)

      pairing-in-R : ∀ {d} → (d∈S₁ : d ∈ S₁) → (d , counterpart (d∈S₁)) ∈ R
      pairing-in-R d∈S₁ = snd (S₁⊆R₁ d∈S₁)

      S : subset (D × E)
      S (d , e) = Σ (d ∈ S₁) \ d∈S₁ → counterpart d∈S₁ ≈E e

      S₂ : subset E
      S₂ = snd-subset S

      fstS=S₁ : fst-subset S ≅ S₁
      backward fstS=S₁ d∈S₁                      = (counterpart d∈S₁ , d∈S₁ , iso-refl E.≤-refl _)
      forward  fstS=S₁ (d∈fstS @ (_ , d∈S₁ , _)) = d∈S₁

      S=S₁×S₂ : ((fst-subset S ∘ fst) ∩ (snd-subset S ∘ snd)) ≅ ((S₁ ∘ fst) ∩ (S₂ ∘ snd))
      S=S₁×S₂ =  ≅×≅→≅ fstS=S₁ (is-preorder.iso-reflexive ⊆-is-preorder S₂)

      ⋀fstS≈D⋀S₁ : ⋀D (fst-subset S) ≈D ⋀D S₁
      ⋀fstS≈D⋀S₁ = D.bigmeet-welldefined (! fstS=S₁)

      S⊆R : S ⊆ R
      S⊆R (d∈S' , counterpart-d=e) = R-subst (≈×≈→≈ (D.iso-reflexive _) counterpart-d=e) (pairing-in-R d∈S')

      ⋀S∈R : ⋀ S ∈ R
      ⋀S∈R = R-meet-closed S S⊆R

      ⋀S₁⋀S₂∈R : (⋀D S₁ , ⋀E S₂) ∈ R
      ⋀S₁⋀S₂∈R = R-subst (≈×≈→≈ ⋀fstS≈D⋀S₁ (E.iso-reflexive _)) ⋀S∈R

    snd-meet-closed : is-meet-closed-subset E-is-cmlat (snd-subset R)
    snd-meet-closed S₂ S₂⊆R₂ = ⋀D S₁ , ⋀S₁⋀S₂∈R
      where

      counterpart : ∀ {e} → e ∈ S₂ → D
      counterpart e∈S₂ = fst (S₂⊆R₂ e∈S₂)

      pairing-in-R : ∀ {e} → (e∈S₂ : e ∈ S₂) → (counterpart (e∈S₂), e) ∈ R
      pairing-in-R e∈S₂ = snd (S₂⊆R₂ e∈S₂)

      S : subset (D × E)
      S (d , e) = Σ (e ∈ S₂) \ e∈S₂ → counterpart e∈S₂ ≈D d

      S₁ : subset D
      S₁ = fst-subset S

      sndS=S₂ : snd-subset S ≅ S₂
      backward sndS=S₂ e∈S₂                      = (counterpart e∈S₂ , e∈S₂ , iso-refl D.≤-refl _)
      forward  sndS=S₂ (e∈sndS @ (_ , e∈S₂ , _)) = e∈S₂

      S=S₁×S₂ : ((fst-subset S ∘ fst) ∩ (snd-subset S ∘ snd)) ≅ ((S₁ ∘ fst) ∩ (S₂ ∘ snd))
      S=S₁×S₂ =  ≅×≅→≅ (is-preorder.iso-reflexive ⊆-is-preorder S₁) sndS=S₂

      ⋀sndS≈E⋀S₂ : ⋀E (snd-subset S) ≈E ⋀E S₂
      ⋀sndS≈E⋀S₂ = E.bigmeet-welldefined (! sndS=S₂)

      S⊆R : S ⊆ R
      S⊆R (e∈S' , counterpart-e=d) = R-subst (≈×≈→≈ counterpart-e=d (E.iso-reflexive _)) (pairing-in-R e∈S')

      ⋀S∈R : ⋀ S ∈ R
      ⋀S∈R = R-meet-closed S S⊆R

      ⋀S₁⋀S₂∈R : (⋀D S₁ , ⋀E S₂) ∈ R
      ⋀S₁⋀S₂∈R = R-subst (≈×≈→≈ (D.iso-reflexive _) ⋀sndS≈E⋀S₂) ⋀S∈R


  -- Left adjoin
  rel2pair : subset (D × E) → func-pair D E
  fst (rel2pair R) d₀ = ⋀E ｛ e ∣ Σ[ d ∈ D ] (d₀ ≤D d × (d , e) ∈ R) ｝
  snd (rel2pair R) e₀ = ⋀D ｛ d ∣ Σ[ e ∈ E ] (e₀ ≤E e × (d , e) ∈ R) ｝

  -- Right adjoint
  pair2rel : func-pair D E → subset (D × E)
  pair2rel (f , b) (d , e) = f d ≤E e × b e ≤D d


  module _ {f : D → E} {b : E → D}
    (f-is-mono : is-monotone D.≤-pre E.≤-pre f) (b-is-mono : is-monotone E.≤-pre D.≤-pre b) where
    pair2rel-mono-join-closed : is-meet-closed-subset D×E-is-cmlat (pair2rel (f , b))
    fst (pair2rel-mono-join-closed S' S'⊆) =
      begin-≤
      f (fst (⋀ S')) ≡⟨⟩
      f (⋀D ｛ d ∣ Σ[ e ∈ E ] ((d , e) ∈ S')｝) ≤⟨ mono-meet≤meet-mono {D-cmlat} {E-cmlat} f-is-mono ｛ d ∣ Σ[ e ∈ E ] ((d , e) ∈ S')｝ ⟩
      ⋀E (fimage f ｛ d ∣ Σ[ e ∈ E ] ((d , e) ∈ S')｝) ≡⟨⟩
      ⋀E ｛ e ∣ Σ[ d ∈ D ] ((Σ[ e' ∈ E ](S' (d , e'))) × f d ≡ e)｝ ≈⟨ E.bigmeet-≡-≤ f _ ⟩
      ⋀E ｛ e ∣ Σ[ d ∈ D ] ((Σ[ e' ∈ E ](S' (d , e'))) × f d ≤E e)｝ ≤⟨ E.bigmeet-monotone (\ { {e} (d , de∈S') → d , ((e , de∈S') , fst (S'⊆ de∈S')) }) ⟩
      ⋀E ｛ e ∣ Σ[ d ∈ D ] ((d , e) ∈ S')｝ ≡⟨⟩
      snd (⋀ S') ∎
      where open ≤E-reasoning
    snd (pair2rel-mono-join-closed S' S'⊆) =
      begin-≤
      b (snd (⋀ S')) ≡⟨⟩
      b (⋀E ｛ e ∣ Σ[ d ∈ D ] ((d , e) ∈ S')｝) ≤⟨ mono-meet≤meet-mono {E-cmlat} {D-cmlat} b-is-mono ｛ e ∣ Σ[ d ∈ D ] ((d , e) ∈ S')｝ ⟩
      ⋀D (fimage b ｛ e ∣ Σ[ d ∈ D ] ((d , e) ∈ S')｝) ≡⟨⟩
      ⋀D ｛ d ∣ Σ[ e ∈ E ] ((Σ[ d' ∈ D ](S' (d' , e))) × b e ≡ d)｝ ≈⟨ D.bigmeet-≡-≤ b _ ⟩
      ⋀D ｛ d ∣ Σ[ e ∈ E ] ((Σ[ d' ∈ D ](S' (d' , e))) × b e ≤D d)｝ ≤⟨ D.bigmeet-monotone (\ { {d} (e , de∈S') → e , ((d , de∈S') , snd (S'⊆ de∈S')) }) ⟩
      ⋀D ｛ d ∣ Σ[ e ∈ E ] ((d , e) ∈ S')｝ ≡⟨⟩
      fst (⋀ S') ∎
      where open ≤D-reasoning


  module _ (R : subset (D × E)) where
    rel2pair-R-is-monotone-pair : is-monotone-pair D-pre E-pre (rel2pair R)
    fst rel2pair-R-is-monotone-pair {d} {d'} d≤d' =
      begin-≤
      fst (rel2pair R) d ≤⟨ E.bigmeet-monotone (\ { {e} (d'' , d'≤d'' , Rd''e) → d'' , (d≤d' ⟨ D.≤-trans ⟩ d'≤d'') , Rd''e }) ⟩
      fst (rel2pair R) d' ∎
      where open ≤E-reasoning
    snd rel2pair-R-is-monotone-pair {e} {e'} e≤e' =
      begin-≤
      snd (rel2pair R) e ≤⟨ D.bigmeet-monotone (\ { {d} (e'' , e'≤e'' , Rde'') → e'' , (e≤e' ⟨ E.≤-trans ⟩ e'≤e'') , Rde'' }) ⟩
      snd (rel2pair R) e' ∎
      where open ≤D-reasoning

  rel2pair-is-antitone : is-antitone ⊆-is-preorder ≤pair-is-preorder rel2pair
  fst (rel2pair-is-antitone {r} {r'} r⊆r') de = E.bigmeet-monotone \{ (d , d≤d , dre) → d , d≤d , r⊆r' dre}
  snd (rel2pair-is-antitone {r} {r'} r⊆r') de = D.bigmeet-monotone \{ (e , e≤e , dre) → e , e≤e , r⊆r' dre}

  pair2rel-is-antitone : is-antitone ≤pair-is-preorder ⊆-is-preorder pair2rel
  pair2rel-is-antitone (f'≤endo , b'≤b) {d , e} (fd≤e , be≤d) = (f'≤endo d ⟨ E.≤-trans ⟩ fd≤e) , (b'≤b e ⟨ D.≤-trans ⟩ be≤d)

  pre-fun = pre (fun D E) _≤fun_ ≤fun-is-preorder
  pre-mfun : preordered-set
  pre-mfun = pre (monotone-func D-pre E-pre) _≤mfun_ ≤mfun-is-preorder

  pre-pair = pre (func-pair D E) _≤pair_ ≤pair-is-preorder

  pre-mpair : preordered-set
  pre-mpair = pre (monotone-func-pair D-pre E-pre) _≤mpair_ ≤mpair-is-preorder


  pre-rel : preordered-set
  pre-rel = pre (subset (D × E)) _⊆_ ⊆-is-preorder

  pair2rel-anti : antitone-func pre-mpair pre-rel
  monotone-func.func pair2rel-anti (mfp' pair pair-is-monotone) = pair2rel pair
  monotone-func.property pair2rel-anti = pair2rel-is-antitone

  rel2pair-anti : antitone-func pre-rel pre-mpair
  monotone-func.func rel2pair-anti r = mfp' (rel2pair r) (rel2pair-R-is-monotone-pair r)
  monotone-func.property rel2pair-anti = rel2pair-is-antitone

  pair2rel-rel2pair-mono = pre-comp-anti pair2rel-anti rel2pair-anti
  open monotone-func pair2rel-rel2pair-mono renaming (property to pair2rel-rel2pair-is-monotone)
  rel2pair-pair2rel-mono = pre-comp-anti rel2pair-anti pair2rel-anti
  open monotone-func rel2pair-pair2rel-mono renaming (property to rel2pair-pair2rel-is-monotone)

  module _
    {R : subset (D × E)}
    (R-meet-closed : is-meet-closed-subset D×E-is-cmlat R)
    (R-welldefined : is-welldefined-subset ≤-pre R)
    where
    fst-boundedmeet→butterfly : ∀ d₀ e₀ → (⋀D \ d → ∃ \ e → e₀ ≤E e × R (d , e)) ≤D d₀ → (∃ \ d' → ∃ \ e → d' ≤D d₀ × e₀ ≤E e × R (d' , e))
    fst-boundedmeet→butterfly d₀ e₀ ≤d₀ =
      (⋀D (\ d → ∃ \ e → e₀ ≤E e × R (d , e))) , (( ⋀E (λ e → ∃ (\ d → (e₀ ≤E e) × R (d , e)))  ) , (≤d₀ , ((E.bigmeet-greatest _ _ (λ{ e'' (d'' , e₀≤ , r)  → e₀≤})) , R-meet-closed ( (\{(d , e) → (e₀ ≤E e) × R (d , e)}))  \{ (_ , dRe) → dRe})))

    snd-boundedmeet→butterfly : ∀ d₀ e₀ → (⋀E \ e → ∃ \ d → d₀ ≤D d × R (d , e)) ≤E e₀ → (∃ \ e' → ∃ \ d → e' ≤E e₀ × d₀ ≤D d × R (d , e'))
    snd-boundedmeet→butterfly d₀ e₀ ≤e₀ =
      ((⋀E \ e → ∃ \ d → d₀ ≤D d × R (d , e))) , (( ⋀D (λ d → ∃ (λ e → (d₀ ≤D d) × R (d , e)))  ) , (≤e₀ , ((D.bigmeet-greatest _ _ (λ{ d'' (e'' , d₀≤ , r)  → d₀≤})) , R-meet-closed ( (\{(d , e) → (d₀ ≤D d) × R (d , e)}))  \{ (_ , dRe) → dRe})))

  module _
    (R : subset (D × E))
    (f : D → E) (b : E → D) where

    right-transpose : (f , b) ≤pair rel2pair R → R ⊆ pair2rel (f , b)
    fst (right-transpose (f≤ , b≤) {d , e} dRe) =
      begin-≤
      f d ≤⟨ f≤ d ⟩
      fst (rel2pair R) d ≤⟨ E.bigmeet-lowerbound _ _ (d , D.≤-refl d , dRe) ⟩
      e ∎
        where open ≤E-reasoning
    snd (right-transpose (f≤ , b≤) {d , e} dRe) =
      begin-≤
      b e ≤⟨ b≤ e ⟩
      snd (rel2pair R) e ≤⟨ D.bigmeet-lowerbound _ _ (e , E.≤-refl e , dRe) ⟩
      d ∎
        where open ≤D-reasoning
    module _
      (f-is-mono : is-monotone D.≤-pre E.≤-pre f) (b-is-mono : is-monotone E.≤-pre D.≤-pre b) where

      f-is-wd : f ∈ is-welldefined D.≤-pre E.≤-pre
      f-is-wd = monotone2welldefined D.≤-pre E.≤-pre f-is-mono
      b-is-wd : b ∈ is-welldefined E.≤-pre D.≤-pre
      b-is-wd = monotone2welldefined E.≤-pre D.≤-pre b-is-mono

      left-transpose : R ⊆ pair2rel (f , b) → (f , b) ≤pair rel2pair R
      fst (left-transpose R⊆pair2rel[fb]) d₀ =
        begin-≤
        f d₀                                         ≈⟨ f-is-wd (D.bigmeet-up-iso d₀) ⟩
        f (⋀D (D.↑ d₀))                              ≤⟨ mono-meet≤meet-mono {D-cmlat} {E-cmlat} f-is-mono (D.↑ d₀) ⟩
        ⋀E (fimage f (D.↑ d₀))                       ≈⟨ E.bigmeet-≡-≤ f _ ⟩
        ⋀E ｛ e ∣ Σ[ d ∈ D ] (d₀ ≤D d × f d ≤E e) ｝  ≤⟨ E.bigmeet-monotone (\ { (e' , e₀≤e' , d'Re') → e' , e₀≤e' , fst (R⊆pair2rel[fb] d'Re')}) ⟩
        ⋀E ｛ e ∣ Σ[ d ∈ D ] (d₀ ≤D d × (d , e) ∈ R) ｝  ≡⟨⟩
        fst (rel2pair R) d₀ ∎
          where open ≤E-reasoning
      snd (left-transpose R⊆pair2rel[fb]) e₀ =
        begin-≤
        b e₀                                         ≈⟨ b-is-wd (E.bigmeet-up-iso e₀) ⟩
        b (⋀E (E.↑ e₀))                              ≤⟨ mono-meet≤meet-mono {E-cmlat} {D-cmlat} b-is-mono (E.↑ e₀) ⟩
        ⋀D (fimage b (E.↑ e₀))                       ≈⟨ D.bigmeet-≡-≤ b _ ⟩
        ⋀D ｛ d ∣ Σ[ e ∈ E ] (e₀ ≤E e × b e ≤D d) ｝  ≤⟨ D.bigmeet-monotone (\ { (e' , e₀≤e' , d'Re') → e' , e₀≤e' , snd (R⊆pair2rel[fb] d'Re')}) ⟩
        ⋀D ｛ d ∣ Σ[ e ∈ E ] (e₀ ≤E e × (d , e) ∈ R) ｝ ≡⟨⟩
        snd (rel2pair R) e₀ ∎
          where open ≤D-reasoning



      -- R ⊆ pair2rel (f , b) ↔ (f , b) ≤pair rel2pair R
      -- forward galois-connection = left-transpose
      -- backward galois-connection = right-transpose

      unit : ((f , b) ≤pair rel2pair R) → (f , b) ≤pair rel2pair R
      unit = left-transpose ∘ right-transpose

      counit : R ⊆ pair2rel (f , b) → R ⊆ pair2rel (f , b)
      counit = right-transpose ∘ left-transpose

  module unit (R : subset (D × E)) where
    pair2rel-rel2pair-increasing : R ⊆ pair2rel (rel2pair R)
    fst (pair2rel-rel2pair-increasing {d₀ , e₀} d₀Re₀) =
      begin-≤
      fst (rel2pair R) d₀                                     ≡⟨⟩
      ⋀E ｛ e ∣ Σ[ d ∈ D ] (d₀ ≤D d × (d , e) ∈ R) ｝     ≤⟨ E.bigmeet-monotone (\ { (d , (d₀≤d , e₀≤e) , dRe) → d , d₀≤d , dRe }) ⟩
      snd (⋀ (↑ (d₀ , e₀) ∩ ｛ de ∣ de ∈ R ｝)) ≤⟨ snd (backward (bigmeet-up-intersection-iso (d₀ , e₀) (\de → de ∈ R) d₀Re₀)) ⟩
      e₀ ∎
      where open ≤E-reasoning
    snd (pair2rel-rel2pair-increasing {d₀ , e₀} d₀Re₀) =
      begin-≤
      snd (rel2pair R) e₀                                    ≡⟨⟩
      ⋀D ｛ d ∣ Σ[ e ∈ E ] (e₀ ≤E e × (d , e) ∈ R) ｝     ≤⟨ D.bigmeet-monotone (\ { (e , (d₀≤d , e₀≤e) , dRe) → e , e₀≤e , dRe }) ⟩
      fst (⋀ (↑ (d₀ , e₀) ∩ ｛ de ∣ de ∈ R ｝)) ≤⟨ fst (backward (bigmeet-up-intersection-iso (d₀ , e₀) (\de → de ∈ R) d₀Re₀)) ⟩
      d₀ ∎
      where open ≤D-reasoning

    is-butterfly : pred (subset (D × E))
    is-butterfly R = ∀ d₀ e₀ {d e d' e'}
      → d' ≤D d₀ → d₀ ≤D d
      → e' ≤E e₀ → e₀ ≤E e
      → (d' , e) ∈ R → (d , e') ∈ R → (d₀ , e₀) ∈ R

    pair2rel-rel2pair-butterfly : pair2rel (rel2pair R) ⊆ R → is-butterfly R
    pair2rel-rel2pair-butterfly r2rR⊆R d₀ e₀ {d} {e} {d'} {e'} d'≤d₀ d₀≤d e'≤e₀ e₀≤e d'Re dRe' =  r2rR⊆R (⋀E≤e₀ , ⋀D≤d₀)
      where
      ⋀E≤e₀ : fst (rel2pair R) d₀ ≤E e₀
      ⋀E≤e₀ =
        begin-≤
        fst (rel2pair R) d₀ ≡⟨⟩
        ⋀E ｛ e ∣ Σ[ d ∈ D ] (d₀ ≤D d × (d , e) ∈ R) ｝ ≤⟨ E.bigmeet-lowerbound _ _ (d , d₀≤d , dRe') ⟩
        e' ≤⟨ e'≤e₀ ⟩
        e₀ ∎
        where open ≤E-reasoning
      ⋀D≤d₀ : snd (rel2pair R) e₀ ≤D d₀
      ⋀D≤d₀ =
        begin-≤
        snd (rel2pair R) e₀ ≡⟨⟩
        ⋀D ｛ d ∣ Σ[ e ∈ E ] (e₀ ≤E e × (d , e) ∈ R) ｝ ≤⟨  D.bigmeet-lowerbound _ _ (e , e₀≤e , d'Re) ⟩
        d' ≤⟨ d'≤d₀ ⟩
        d₀ ∎
        where open ≤D-reasoning

    module _ where
      R' = pair2rel (rel2pair R)
      R'-meet-closed : is-meet-closed-subset D×E-is-cmlat (pair2rel (rel2pair R))
      R'-meet-closed = pair2rel-mono-join-closed (fst (rel2pair-R-is-monotone-pair R)) (snd (rel2pair-R-is-monotone-pair R))

    module _ (R-meet-closed : is-meet-closed-subset D×E-is-cmlat R) where

      butterfly-pair2rel-rel2pair : is-butterfly R → pair2rel (rel2pair R) ⊆ R
      butterfly-pair2rel-rel2pair R-butterfly {(d₀ , e₀)} d₀R'e₀ =
        R-butterfly d₀ e₀
          {d =  ⋀D (λ d → ∃ (λ e → (d₀ ≤D d) × (d , e) ∈ R))}
          {e =  ⋀E (λ e → ∃ (λ d → (e₀ ≤E e) × (d , e) ∈ R))}
          {d' = ⋀D ｛ d ∣ ∃ (\ e → e₀ ≤E e × (d , e) ∈ R) ｝ }
          {e' = ⋀E ｛ e ∣ ∃ (\ d → d₀ ≤D d × (d , e) ∈ R) ｝ }
          (snd d₀R'e₀) (D.bigmeet-greatest _ _ \ _ → fst ∘ snd)
          (fst d₀R'e₀) (E.bigmeet-greatest _ _ \ _ → fst ∘ snd)
          (R-meet-closed _ snd)
          (R-meet-closed _ snd)

  module counit (f : D → E) (b : E → D)
    (f-mono : is-monotone D.≤-pre E.≤-pre f)
    (b-mono : is-monotone E.≤-pre D.≤-pre b) where

    rel2pair-pair2rel-increasing : (f , b) ≤pair rel2pair (pair2rel (f , b))
    rel2pair-pair2rel-increasing = left-transpose (pair2rel (f , b)) f b f-mono b-mono id

    private
      fb = f , b
      fb' = rel2pair (pair2rel fb)

      a : D → D
      a d₀ = ⋀D ｛ d ∣ Σ _ (\ e → d₀ ≤D d × f d ≤E e × b e ≤D d) ｝

      p : E → E
      p e₀ = ⋀E ｛ e ∣ Σ _ (\ d → e₀ ≤E e × f d ≤E e × b e ≤D d) ｝

      id≤a : ∀ d₀ → d₀ ≤D a d₀
      id≤a d₀ = D.bigmeet-greatest _ _ (\ { d (e , d₀≤d , fd≤e , be≤d) → d₀≤d})

      id≤p : ∀ e₀ → e₀ ≤E p e₀
      id≤p e₀ = E.bigmeet-greatest _ _ (\ { e (d , e₀≤e , fd≤e , be≤d) → e₀≤e})

      bf≤a : ∀ d₀ →  b (f d₀) ≤D a d₀
      bf≤a d₀ =
        begin-≤
        b (f d₀) ≤⟨ D.bigmeet-greatest _ _ (\{ d (e , d₀≤d , fd≤e , be≤d) → b-mono (f-mono d₀≤d) ⟨ D.≤-trans ⟩ b-mono fd≤e ⟨ D.≤-trans ⟩ be≤d }) ⟩
        ⋀D (\ d → ∃ \ e → d₀ ≤D d × f d ≤E e × b e ≤D d) ≡⟨⟩
        a d₀ ∎
        where open ≤D-reasoning

      fb≤p : ∀ e₀ →  f (b e₀) ≤E p e₀
      fb≤p e₀ =
        begin-≤
        f (b e₀) ≤⟨ E.bigmeet-greatest _ _ (\{ e (d , e₀≤e , fd≤e , be≤d) → f-mono (b-mono e₀≤e) ⟨ E.≤-trans ⟩ f-mono be≤d ⟨ E.≤-trans ⟩ fd≤e }) ⟩
        ⋀E (\ e → ∃ \ d → e₀ ≤E e × f d ≤E e × b e ≤D d) ≡⟨⟩
        p e₀ ∎
        where open ≤E-reasoning



    private
      f* : D → E
      f* d = f (b (f d) ∨D d)
      b* : E → D
      b* e = b (f (b e) ∨E e)

      fb* : (D → E) × (E → D)
      fb* = f* , b*

    rel2pair-pair2rel→fix : fb' ≤pair fb → fb* ≤pair fb
    rel2pair-pair2rel→fix ≤endob = fb*≤ ⟨ ≤pair-trans ⟩ ≤endob
      where
        open is-preorder ≤pair-is-preorder renaming (rel-is-transitive to ≤pair-trans)
        fb*≤ : fb* ≤pair fb'
        fst fb*≤ d =
          begin-≤
          fst fb* d ≤⟨ mono-meet≤meet-mono {D-cmlat} {E-cmlat} f-mono _ ⟩
          ⋀E ((fimage f) (is-upperbound _≤D_ ｛ b (f d) , d ｝₂ )) ≡⟨⟩
          ⋀E  (\ e → Σ D (\ d' → (d' ∈ is-upperbound _≤D_ ｛ b (f d) , d ｝₂) × (f d' ≡ e))) ≈⟨ E.bigmeet-≡-≤ f _ ⟩
          ⋀E  (\ e → Σ D (\ d' → (d' ∈ is-upperbound _≤D_ ｛ b (f d) , d ｝₂) × (f d' ≤E e))) ≤⟨ E.bigmeet-monotone (\ {(d' , d≤d' , fd'≤e , be≤d' ) → d' , bin-upperbound→subset-upperbound _≤D_ ((b-mono (f-mono d≤d') ⟨ D.≤-trans ⟩ b-mono fd'≤e ⟨ D.≤-trans ⟩ be≤d') , d≤d') , fd'≤e }) ⟩
          ⋀E (\ e → Σ D (\ d' → d ≤D d' × f d' ≤E e × b e ≤D d')) ≡⟨⟩
          fst fb' d ∎
          where
            open ≤E-reasoning
        snd fb*≤ e =
          begin-≤
          snd fb* e ≤⟨ mono-meet≤meet-mono {E-cmlat} {D-cmlat} b-mono _ ⟩
          ⋀D ((fimage b) (is-upperbound _≤E_ ｛ f (b e) , e ｝₂ )) ≡⟨⟩
          ⋀D  (\ d → Σ E (\ e' → (e' ∈ is-upperbound _≤E_ ｛ f (b e) , e ｝₂) × (b e' ≡ d))) ≈⟨ D.bigmeet-≡-≤ b _ ⟩
          ⋀D  (\ d → Σ E (\ e' → (e' ∈ is-upperbound _≤E_ ｛ f (b e) , e ｝₂) × (b e' ≤D d))) ≤⟨ D.bigmeet-monotone (\ {(e' , e≤e' , fd≤e' , be'≤d) → e' , bin-upperbound→subset-upperbound _≤E_ ((f-mono (b-mono e≤e') ⟨ E.≤-trans ⟩ f-mono be'≤d ⟨ E.≤-trans ⟩ fd≤e') , e≤e') , be'≤d }) ⟩
          ⋀D (\ d → Σ E (\ e' → e ≤E e' × f d ≤E e' × b e' ≤D d)) ≡⟨⟩
          snd fb' e ∎
          where
            open ≤D-reasoning

    fix→rel2pair-pair2rel : fb* ≤pair fb → fb' ≤pair fb
    fst (fix→rel2pair-pair2rel fb*≤endob) d =
      begin-≤
      fst fb' d ≡⟨⟩
      ⋀E ｛ e ∣ Σ[ d' ∈ D ] (d ≤D d' × f d' ≤E e × b e ≤D d') ｝  ≤⟨ E.bigmeet-lowerbound _ _ ((b (f d) ∨D d) , (D⋁.bigjoin-upperbound _ _ (right ≡.refl) , fst fb*≤endob d , D⋁.bigjoin-upperbound _ _ (left ≡.refl))) ⟩
      f d ≡⟨⟩
      fst fb d ∎
      where open ≤E-reasoning
            module D⋁ = is-complete-join-semilattice D-is-cjlat

    snd (fix→rel2pair-pair2rel fb*≤endob) e =
      begin-≤
      snd fb' e ≡⟨⟩
      ⋀D ｛ d ∣ Σ[ e' ∈ E ] (e ≤E e' × f d ≤E e' × b e' ≤D d) ｝  ≤⟨ D.bigmeet-lowerbound _ _ ((f (b e) ∨E e) , (E⋁.bigjoin-upperbound _ _ (right ≡.refl) , E⋁.bigjoin-upperbound _ _ (left ≡.refl) , snd fb*≤endob e)) ⟩
      b e ≡⟨⟩
      snd fb e ∎
      where open ≤D-reasoning
            module E⋁ = is-complete-join-semilattice E-is-cjlat

```

- Category of subsets on complete lattice X:
  - objects: subsets of X, s∈𝓟X, s'∈𝓟X, ...
  - morphisms: inclusion s ⊆ s' fp

- Category of endo functions on complete lattice X
  - objects: endo monotone fucntions e, e', e'' : X → X
  - morphisms: pointwise order relation e ≤ e'



```txt
            s ⊆ endo2rel f
            =========
            rel2endo s ≥ f
```

```agda
module _ (X : Set) where
  endo = X → X

module _ (X : preordered-set) where
  monotone-endo = monotone-func X X

module endo-function (X-cmlat : complete-meet-semilattice)
  (let (cmlat X _≤X_ ⋀X X-is-cmlat) = X-cmlat)
  (let X-pre = cmlat→pre X-cmlat) where

  private
    module X = is-complete-meet-semilattice X-is-cmlat
      renaming (rel-is-preorder to ≤-pre ; op-is-bigmeet to ⋀-bigmeet ; rel-is-reflexive to ≤-refl ; rel-is-transitive to ≤-trans)

  X-cjlat = cmlat→cjlat X-cmlat
  open complete-join-semilattice X-cjlat
    renaming (operation to ⋁X ; property to X-is-cjlat)

  ⊤X = ⋀X ∅

  ⊥X = ⋁X ∅

  _∨X_ = \ x y → ⋁X ｛ x , y ｝₂

  rel2endo : subset X → (X → X)
  rel2endo s x₀ = ⋀X ｛ x ∣ x₀ ≤X x × x ∈ s ｝

  rel2endo-s-is-monotone : ∀ s → is-monotone X.≤-pre X.≤-pre (rel2endo s)
  rel2endo-s-is-monotone s x≤x' = X.bigmeet-monotone \ { (x'≤x'' , x''∈s) → X.≤-trans x≤x' x'≤x'' , x''∈s }

  endo2rel : endo X → subset X
  endo2rel f x = f x ≤X x

  _≤endo_ : rel (endo X) (endo X)
  f ≤endo f' = ∀ x → f x ≤X f' x

  module _ where
    open monotone-func
    open preordered-set
    _≤mendo_ : rel (monotone-endo X-pre) (monotone-endo X-pre)
    f ≤mendo f' = func f ≤endo func f'

    open is-preorder
    ≤endo-is-preorder : is-preorder _≤endo_
    (rel-is-reflexive ≤endo-is-preorder f) d = X.≤-refl (f d)
    (rel-is-transitive ≤endo-is-preorder f≤f' f'≤f'') d = X.≤-trans (f≤f' d) (f'≤f'' d)

    ≤mendo-is-preorder : is-preorder _≤mendo_
    rel-is-reflexive ≤mendo-is-preorder d = (rel-is-reflexive ≤endo-is-preorder (func d))
    rel-is-transitive ≤mendo-is-preorder f≤f' f'≤f'' = rel-is-transitive ≤endo-is-preorder f≤f' f'≤f''

    _≈endo_ : rel (X → X) (X → X)
    _≈endo_ = iso-pair _≤endo_

    _≈mendo_ : rel (monotone-endo X-pre) (monotone-endo X-pre)
    _≈mendo_ = iso-pair _≤mendo_

    pre-subset = pre (subset X) _⊆_ ⊆-is-preorder
    pre-mendo = pre (monotone-endo X-pre) _≤mendo_ ≤mendo-is-preorder

    rel2endo-antitone : antitone-func pre-subset pre-mendo
    func rel2endo-antitone s = mono (rel2endo s) (rel2endo-s-is-monotone s)
    property rel2endo-antitone {s} {s'} s⊆s' x₀ = X.bigmeet-monotone \{ (x₀≤x , x∈s) → x₀≤x , s⊆s' x∈s}

    endo2rel-antitone : antitone-func pre-mendo pre-subset
    func endo2rel-antitone f = endo2rel (func f)
    property endo2rel-antitone {f} {f'} f≤endo' {x} x∈endo2relf' = X.≤-trans (f≤endo' x) x∈endo2relf'


  module _ where
    endo2rel-rel2endo-antitone-galois-connection : is-antitone-galois-connection endo2rel-antitone rel2endo-antitone
    endo2rel-rel2endo-antitone-galois-connection s f-mono =
      begin-≈
      flip _⊆_ (endo2relm f-mono) s ≡⟨⟩
      (∀ {x : X} → s x → f x ≤X x) ≈⟨ hidden↔explicit _ ⟩
      (∀ x₀ → x₀ ∈ s → f x₀ ≤X x₀) ≈⟨ X.bigmeet-mono-equivalence s (f-is-mono)  ⟩
      (∀ x₀ → f x₀ ≤X ⋀X (\ x → x₀ ≤X x × x ∈ s)) ≡⟨⟩
      f ≤endo rel2endo s ∎
      where open reasoning _ (→-is-preorder)
            open monotone-func endo2rel-antitone renaming (func to endo2relm ; property to endo2relm-is-antitone)
            open monotone-func f-mono renaming (func to f ; property to f-is-mono)

```

```
module _ (D-cmlat E-cmlat : complete-meet-semilattice) (let D-pre = cmlat→pre D-cmlat) (let E-pre = cmlat→pre E-cmlat) where

  open transfer-function-pair D-cmlat E-cmlat
  module D-cmlat = complete-meet-semilattice D-cmlat
  module E-cmlat = complete-meet-semilattice E-cmlat

  D-is-pre = is-complete-meet-semilattice.rel-is-preorder D-cmlat.property
  E-is-pre = is-complete-meet-semilattice.rel-is-preorder E-cmlat.property

  pair2rel-rel2pair-antitone-galois-connection : is-antitone-galois-connection pair2rel-anti rel2pair-anti
  forward (pair2rel-rel2pair-antitone-galois-connection r (mfp' (f , b) (f-mono , b-mono))) = left-transpose r f b f-mono b-mono
  backward (pair2rel-rel2pair-antitone-galois-connection r (mfp' (f , b) _)) = right-transpose r f b

  rel-mpair-connected : antitone-galois-connection pre-rel pre-mpair
  galois-connection.left-adjoint rel-mpair-connected = pair2rel-anti
  galois-connection.right-adjoint rel-mpair-connected = monotone-func.dual rel2pair-anti
  galois-connection.left-right-is-galois-connection rel-mpair-connected = pair2rel-rel2pair-antitone-galois-connection

  module D×E-cmlat = complete-meet-semilattice (D-cmlat ×-cmlat E-cmlat)
  D×E-is-pre = is-complete-meet-semilattice.rel-is-preorder D×E-cmlat.property
  open endo-function (D-cmlat ×-cmlat E-cmlat)

  rel-mendo-connected : antitone-galois-connection pre-rel pre-mendo
  galois-connection.left-adjoint rel-mendo-connected = endo2rel-antitone
  galois-connection.right-adjoint rel-mendo-connected = monotone-func.dual rel2endo-antitone
  galois-connection.left-right-is-galois-connection rel-mendo-connected = endo2rel-rel2endo-antitone-galois-connection

  endo2pair : endo (D-cmlat.carrier × E-cmlat.carrier) → func-pair (D-cmlat.carrier) (E-cmlat.carrier)
  fst (endo2pair f) d = snd (f (d , E-cmlat.operation U))
  snd (endo2pair f) e = fst (f (D-cmlat.operation U , e))


  mendo2mpair : monotone-endo (cmlat→pre (D-cmlat ×-cmlat E-cmlat)) → monotone-func-pair D-pre E-pre
  fst (monotone-func-pair.pair (mendo2mpair (mono h h-is-mono))) = fst (endo2pair h)
  snd (monotone-func-pair.pair (mendo2mpair (mono h h-is-mono))) = snd (endo2pair h)
  fst (monotone-func-pair.pair-is-monotone (mendo2mpair (mono h h-is-mono))) d≤d' = snd (h-is-mono (d≤d' , is-preorder.rel-is-reflexive E-is-pre _))
  snd (monotone-func-pair.pair-is-monotone (mendo2mpair (mono h h-is-mono))) e≤e' = fst (h-is-mono (is-preorder.rel-is-reflexive D-is-pre _ , e≤e'))

  pair2endo : func-pair (D-cmlat.carrier) (E-cmlat.carrier) → endo (D-cmlat.carrier × E-cmlat.carrier)
  pair2endo (f , b) (d , e) = (b e , f d)

  mpair2mendo : monotone-func-pair D-pre E-pre → monotone-endo (cmlat→pre (D-cmlat ×-cmlat E-cmlat))
  monotone-func.func (mpair2mendo (mfp' (f , b) (f-mono , b-mono))) (d , e) = pair2endo (f , b) (d , e)
  monotone-func.property (mpair2mendo (mfp' (f , b) (f-mono , b-mono))) (d≤d' , e≤e') = b-mono e≤e' , f-mono d≤d'


  mendo-mpair-connected : galois-connection pre-mendo pre-mpair
  galois-connection.left-adjoint mendo-mpair-connected = mono mpair2mendo (\{ (f-mono , b-mono) (d , e) → b-mono e , f-mono d})
  galois-connection.right-adjoint mendo-mpair-connected = mono mendo2mpair (\ f≤f' → (\ d → snd (f≤f' (d , E-cmlat.operation U))) , (\ e → fst (f≤f' (D-cmlat.operation U , e))))
  forward (galois-connection.left-right-is-galois-connection mendo-mpair-connected (mono h h-mono) (mfp' (f , b) (f-mono , b-mono))) mpair2mendo[fb]≤h
    = f≤snd[h[id,⊥]] , b≤endost[h[⊥,id]]
    where
    f≤snd[h[id,⊥]] : ∀ d → E-cmlat.relation (f d) (snd (h (d , _)))
    f≤snd[h[id,⊥]] d = snd (mpair2mendo[fb]≤h (d , E-cmlat.operation U))
    b≤endost[h[⊥,id]] : ∀ e → D-cmlat.relation (b e) (fst (h (_ , e)))
    b≤endost[h[⊥,id]] e = fst (mpair2mendo[fb]≤h (D-cmlat.operation U , e))

  backward (galois-connection.left-right-is-galois-connection mendo-mpair-connected (mono h h-mono) (mfp' (f , b) (f-mono , b-mono))) (f≤snd[mendo2mpair[h]] , b≤endost[mendo2mpair[h]])
    = pair2endo[f,b]≤h
    where
    pair2endo[f,b]≤h : ∀ p → D×E-cmlat.relation (pair2endo (f , b) p) (h p)
    fst (pair2endo[f,b]≤h p) = begin-≤ fst (pair2endo (f , b) p) ≤⟨  b≤endost[mendo2mpair[h]] (snd p) ⟩ fst (h (D-cmlat.operation U , snd p)) ≤⟨ fst (h-mono ((is-complete-meet-semilattice.bigmeet-lowerbound D-cmlat.property _ _ _ ) , (is-preorder.rel-is-reflexive E-is-pre _))) ⟩ fst (h p) ∎
      where
      open reasoning _ D-is-pre
    snd (pair2endo[f,b]≤h p) = begin-≤ snd (pair2endo (f , b) p) ≤⟨  f≤snd[mendo2mpair[h]] (fst p) ⟩ snd (h (fst p , E-cmlat.operation U)) ≤⟨ snd (h-mono ((is-preorder.rel-is-reflexive D-is-pre _) , (is-complete-meet-semilattice.bigmeet-lowerbound E-cmlat.property _ _ _ ))) ⟩ snd (h p) ∎
      where
      open reasoning _ E-is-pre

  rel-mpair-connected' : antitone-galois-connection pre-rel pre-mpair
  rel-mpair-connected' = comp-galois-connection rel-mendo-connected mendo-mpair-connected

  test : (let (gal-conn l' r' _) = rel-mpair-connected') (let (gal-conn l r _) = rel-mpair-connected) →
    ∀ pair →  monotone-func.func l pair ≅ monotone-func.func l' pair
  forward (test (mfp' fp fp-is-monotone)) {p} x = (snd x , fst x)
  backward (test (mfp' fp fp-is-monotone)) {p} x = (snd x , fst x)

  pair2fun : func-pair D-cmlat.carrier E-cmlat.carrier → fun D-cmlat.carrier E-cmlat.carrier
  pair2fun (f , b) = f

  mpair2mfun : monotone-func-pair D-pre E-pre → monotone-func D-pre E-pre
  monotone-func.func (mpair2mfun (mfp' pair pair-is-monotone)) = fst pair
  monotone-func.property (mpair2mfun (mfp' pair pair-is-monotone)) = fst pair-is-monotone

  -- mpair2mfun : monotone-func-pair D-is-pre E-is-pre → monotone-func D-is-pre E-is-pre
  -- mpair2mfun = ?
  fun2pair : fun D-cmlat.carrier E-cmlat.carrier → func-pair (D-cmlat.carrier) (E-cmlat.carrier)
  fun2pair f = f , \ _ → ⊥D

  mfun2mpair : monotone-func D-pre E-pre → monotone-func-pair D-pre E-pre
  monotone-func-pair.pair (mfun2mpair (mono func property)) = fun2pair func
  fst (monotone-func-pair.pair-is-monotone (mfun2mpair (mono func property))) = property
  snd (monotone-func-pair.pair-is-monotone (mfun2mpair (mono func property))) {d} {d'} _ = is-complete-meet-semilattice.bigmeet-monotone D-cmlat.property (\ x → x)

  mpair-mfun-connected : galois-connection pre-mpair pre-mfun
  galois-connection.left-adjoint mpair-mfun-connected = mono mfun2mpair (\ f≤f' → (\ d → f≤f' d) , (\ e → is-complete-meet-semilattice.bigmeet-monotone D-cmlat.property (\ x → x)))
  galois-connection.right-adjoint mpair-mfun-connected = mono mpair2mfun (\ fb≤fb' d → fst fb≤fb' d)
  forward (galois-connection.left-right-is-galois-connection mpair-mfun-connected mfp mf) Lmf≤mfp d = fst Lmf≤mfp d
  backward (galois-connection.left-right-is-galois-connection mpair-mfun-connected mfp mf) mf≤Rmfp = (\ d → mf≤Rmfp d) , (\ e → is-complete-meet-semilattice.bigmeet-lowerbound D-cmlat.property _ _ (\ _ → ⊥-elim))
    where open import Data.Empty

  mendo-mfun-connected : galois-connection pre-mendo pre-mfun
  mendo-mfun-connected = comp-galois-connection mendo-mpair-connected mpair-mfun-connected

  rel-mfun-connected : antitone-galois-connection pre-rel pre-mfun
  rel-mfun-connected = comp-galois-connection rel-mendo-connected mendo-mfun-connected


```
* fixed-points of galois-connection

Let X is a poset,

```txt

                         L
                      ------->
            (𝒫(C),⊆)    ⊥       X
                      <-------
               | ↑       R      | ↑
               | |              | |
               |⊣|              |⊢|
               ↓ J        α     ↓ J
                      ------->
        (𝒫(C),⊆)_fix     ≅     X_fix
                      <-------


                         L
                      ------->            ---------->             ------------------------------>
            (𝒫(A × B),⊆)    ⊥   A×B→A×B                 A→B × B→A                                 A→B
                      <-------            <-----------            <------------------------------
               | ↑       R      | ↑                      | |
               | |              | |                      | |
               |⊣|              |⊢|                      | |
               ↓ J        α     ↓ J                      | |
                      ------->                           | |
        (𝒫(A×B),⊆)_fix   ≅    A×B→A×B_fix               | |
              | |     <-------                           | |
              | |                                        | |
              | |                                        | |
              | |                                        | |
              | |                                        | |
              | |       ------------------------------   | |
        (𝒫(A×B),⊆)_fix₂               ≅                  A→B × B→A (f (id ∧ b ⊥) ≥ f
                        ------------------------------

```

If we have a pair of adjoints L, R on the top then we have
a full sub category (𝒫(C),⊆)_fix of (𝒫(C),⊆) whose objects are c with an isomorphism c ≃ηc RL(c)
and a full sub category X_fix of X whose objects are x with an isomorphism LR(x) ≃εx x
https://ncatlab.org/nlab/show/fixed+point+of+an+adjunction

X → Y → Z

p2f (f2p f ⋈ f2p g) = f ⊗ g = p2f (f2p (f * g))
p2f (f2p (f * (g * h))) = f ⊗ g ⊗ h

```agda
module fixed-points-of-galois-connection {C D : preordered-set} (C-D-connected : galois-connection C D) where
  open galois-connection C-D-connected
  open is-preorder
  open monotone-func renaming (property to monotonicity)
  private
    module C = preordered-set C renaming (relation to _≤_ ; property to is-pre ; equiv to _≅_)
    module D = preordered-set D renaming (relation to _≤_ ; property to is-pre ; equiv to _≅_)

  C*-carrier = Σ _ \ c → c C.≤ lr c
  C*-is-pre : is-preorder {C*-carrier} (map-rel fst fst C._≤_)
  rel-is-reflexive C*-is-pre _ = rel-is-reflexive C.is-pre _
  rel-is-transitive C*-is-pre =  rel-is-transitive C.is-pre

  C* : preordered-set
  C* = pre C*-carrier (map-rel fst fst C._≤_) C*-is-pre

  D*-carrier = Σ _ \ d → rl d D.≤ d
  D*-is-pre : is-preorder {D*-carrier} (map-rel fst fst D._≤_)
  rel-is-reflexive D*-is-pre _ = rel-is-reflexive D.is-pre _
  rel-is-transitive D*-is-pre =  rel-is-transitive D.is-pre

  D* : preordered-set
  D* = pre D*-carrier (map-rel fst fst D._≤_) D*-is-pre

  {-

    D ←L C
    ↓L   ↑L
    D* ≅ C*
  -}

  -- inclusion C* → C
  C*2C : monotone-func C* C
  func C*2C = fst
  monotonicity C*2C = id

  C2C* : monotone-func C C*
  func C2C* c = lr c , backward (lr-idempotent (func right-adjoint c))
  monotonicity C2C* c≤c' = lr-mono c≤c'

  D*2D : monotone-func D* D
  func D*2D = fst
  monotonicity D*2D = id

  D2D* : monotone-func D D*
  func D2D* d = rl d , forward (rl-idempotent (func left-adjoint d))
  monotonicity D2D* d≤d' = rl-mono d≤d'

  C*2C-C2C*-is-galois-connection : is-galois-connection C*2C C2C*
  forward (C*2C-C2C*-is-galois-connection c (c* , c*≤lrc*)) c*≤c =
    begin-≤
    c* ≤⟨ c*≤lrc* ⟩
    lr c* ≤⟨ lr-mono c*≤c ⟩
    lr c ∎
    where
      open reasoning _ C.is-pre
  backward (C*2C-C2C*-is-galois-connection c (c* , c*≤lrc*)) c*≤lrc =
    begin-≤
    c* ≤⟨ c*≤lrc ⟩
    lr c ≤⟨ lr-decreasing c ⟩
    c ∎
    where
      open reasoning _ C.is-pre

  C-C*-connected : galois-connection C C*
  C-C*-connected = gal-conn C*2C C2C* C*2C-C2C*-is-galois-connection

  D2D*-D*2D-is-galois-connection : is-galois-connection D2D* D*2D
  forward (D2D*-D*2D-is-galois-connection (d* , rld*≤d*) d) rld≤d* =
    begin-≤
    d ≤⟨ rl-increasing d ⟩
    rl d ≤⟨ rld≤d* ⟩
    d* ∎
    where
      open reasoning _ D.is-pre

  backward (D2D*-D*2D-is-galois-connection (d* , rld*≤d*) d) d≤d* =
    begin-≤
    rl d ≤⟨ rl-mono d≤d* ⟩
    rl d* ≤⟨ rld*≤d* ⟩
    d* ∎
    where
      open reasoning _ D.is-pre

  C*2D* : monotone-func C* D*
  func C*2D* c* = (func D2D* ∘ func right-adjoint ∘ func C*2C) c*
  monotonicity C*2D* c*≤c*' = (monotonicity D2D* ∘ monotonicity right-adjoint) c*≤c*' -- c*≤c*' is defined by relation on projecion (snd c* is irrelevant) applying monotonicity C*2C is valid but make it ambiguous

  D*2C* : monotone-func D* C*
  func D*2C* d* = (func C2C* ∘ func left-adjoint ∘ func D*2D) d*
  monotonicity D*2C* d*≤d*' = (monotonicity C2C* ∘ monotonicity left-adjoint) d*≤d*'

  private
    rl-welldefined : is-welldefined D.is-pre D.is-pre rl
    rl-welldefined = monotone2welldefined D.is-pre D.is-pre rl-mono
    rld≤d→rld≅d : ∀ {d} → rl d D.≤ d → rl d D.≅ d
    forward (rld≤d→rld≅d ≤) = ≤
    backward (rld≤d→rld≅d ≤) = rl-increasing _
    rld≤d→rlrlrld≅d : ∀ {d} → rl d D.≤ d → rl (rl (rl d)) D.≅ d
    rld≤d→rlrlrld≅d {d} rld≤d = begin-≈
      rl (rl (rl d)) ≈⟨ rl-welldefined (rl-welldefined rld≅d) ⟩
      rl (rl d) ≈⟨ rl-welldefined rld≅d ⟩
      rl d ≈⟨ rld≅d ⟩
      d ∎
      where
      open reasoning _ D.is-pre
      rld≅d : rl d D.≅ d
      rld≅d = rld≤d→rld≅d rld≤d

    lr-welldefined : is-welldefined C.is-pre C.is-pre lr
    lr-welldefined = monotone2welldefined C.is-pre C.is-pre lr-mono
    c≤lrc→c≅lrc : ∀ {c} → c C.≤ lr c → c C.≅ lr c
    forward (c≤lrc→c≅lrc ≤) = ≤
    backward (c≤lrc→c≅lrc ≤) = lr-decreasing _
    c≤lrc→c≅lrlrlrc : ∀ {c} → c C.≤ lr c → c C.≅ lr (lr (lr c))
    c≤lrc→c≅lrlrlrc {c} c≤lrc = begin-≈
      c ≈⟨ c≅lrc ⟩
      lr c ≈⟨ lr-welldefined c≅lrc ⟩
      lr (lr c) ≈⟨  lr-welldefined (lr-welldefined c≅lrc) ⟩
      lr (lr (lr c)) ∎
      where
      open reasoning _ C.is-pre
      c≅lrc : c C.≅ lr c
      c≅lrc = c≤lrc→c≅lrc c≤lrc

  C*2D*-D*2C*-is-order-isomorphism : is-order-isomorphism C*2D* D*2C*
  forward (fst C*2D*-D*2C*-is-order-isomorphism (d , rld≤d)) = forward (rld≤d→rlrlrld≅d rld≤d)
  backward (fst C*2D*-D*2C*-is-order-isomorphism (d , rld≤d)) = backward (rld≤d→rlrlrld≅d rld≤d)
  forward (snd C*2D*-D*2C*-is-order-isomorphism (c , c≤lrc)) =  backward (c≤lrc→c≅lrlrlrc c≤lrc)
  backward (snd C*2D*-D*2C*-is-order-isomorphism (c , c≤lrc)) = forward (c≤lrc→c≅lrlrlrc c≤lrc)

```


