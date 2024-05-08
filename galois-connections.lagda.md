```agda
{-# OPTIONS --type-in-type --exact-split #-}
open import Agda.Primitive hiding (_⊔_)
open import Level renaming (_⊔_ to _l⊔_)
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum renaming (inj₁ to left; inj₂ to right)
import Relation.Binary.PropositionalEquality as ≡
open ≡ using (_≡_ ; _≗_)
open import Relation.Binary renaming (_⇔_ to _⇔₂_)
open import Relation.Nullary
open import Relation.Unary
open import Relation.Binary.Lattice
open import Function renaming (_⇔_ to _⇔fun_; _↔_ to _↔fun_)
open import Data.Nat using (ℕ; suc; zero)

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
```

```agda
module _ (X : Set) where
  endo = X → X

module _ (X : preordered-set) where
  monotone-endo = monotone-func X X

module endo-function (X-cmlat : complete-meet-semilattice)
  (let (cmlat X _≤X_ ⋀X X-is-cmlat) = X-cmlat)
  (let X-pre = cmlat→pre X-cmlat)
  (open is-complete-meet-semilattice X-is-cmlat
      renaming (rel-is-preorder to ≤-pre ; op-is-bigmeet to ⋀-bigmeet ; rel-is-reflexive to ≤-refl ; rel-is-transitive to ≤-trans))
  where

  rel2endo : subset X → (X → X)
  rel2endo s x₀ = ⋀X ｛ x ∣ x₀ ≤X x × x ∈ s ｝

  rel2endo-is-pointwisely-monotone : ∀ s → is-monotone ≤-pre ≤-pre (rel2endo s)
  rel2endo-is-pointwisely-monotone s x≤x' = bigmeet-monotone \ { (x'≤x'' , x''∈s) → ≤-trans x≤x' x'≤x'' , x''∈s }

  endo2rel : endo X → subset X
  endo2rel f x = f x ≤X x


  mendo2rel : monotone-endo X-pre → subset X
  mendo2rel (mono f _) x = f x ≤X x


  _≤endo_ : rel (endo X) (endo X)
  f ≤endo f' = ∀ x → f x ≤X f' x

  module _ where
    open monotone-func
    open preordered-set
    _≤mendo_ : rel (monotone-endo X-pre) (monotone-endo X-pre)
    f ≤mendo f' = func f ≤endo func f'

    open is-preorder
    ≤endo-is-preorder : is-preorder _≤endo_
    (rel-is-reflexive ≤endo-is-preorder f) d = ≤-refl (f d)
    (rel-is-transitive ≤endo-is-preorder f≤f' f'≤f'') d = ≤-trans (f≤f' d) (f'≤f'' d)

    ≤mendo-is-preorder : is-preorder _≤mendo_
    rel-is-reflexive ≤mendo-is-preorder d = (rel-is-reflexive ≤endo-is-preorder (func d))
    rel-is-transitive ≤mendo-is-preorder f≤f' f'≤f'' = rel-is-transitive ≤endo-is-preorder f≤f' f'≤f''

    _≈endo_ : rel (X → X) (X → X)
    _≈endo_ = iso-pair _≤endo_

    _≈mendo_ : rel (monotone-endo X-pre) (monotone-endo X-pre)
    _≈mendo_ = iso-pair _≤mendo_

    pre-subset = pre (subset X) _⊆_ ⊆-is-preorder
    pre-endo = pre (endo X) _≤endo_ ≤endo-is-preorder
    pre-mendo = pre (monotone-endo X-pre) _≤mendo_ ≤mendo-is-preorder

    rel2mendo : subset X → monotone-endo X-pre
    func (rel2mendo s) = rel2endo s
    property (rel2mendo s) x≤x' = rel2endo-is-pointwisely-monotone s x≤x'

    rel2mendo-is-antitone : is-antitone ⊆-is-preorder ≤mendo-is-preorder rel2mendo
    rel2mendo-is-antitone {s} {s'} s⊆s' x = bigmeet-monotone \{ {x'} (x≤x' , x'∈s) → x≤x' , s⊆s' x'∈s }

    mendo2rel-is-antitone : is-antitone ≤mendo-is-preorder ⊆-is-preorder mendo2rel
    mendo2rel-is-antitone f≤f' {x} x∈endo2relf' = ≤-trans (f≤f' x) x∈endo2relf'

    img-mendo2rel-meetclosed : ∀ e → is-meet-closed-subset X-is-cmlat (mendo2rel e)
    img-mendo2rel-meetclosed (mono f f-mono) s s⊆ =
      ≤-trans (mono-meet≤meet-mono {X-cmlat} {X-cmlat} f-mono s)
        (≤-trans (bigmeet-≡-≤ f s .forward)
                 (bigmeet-monotone \ {x} x∈s → x , x∈s , s⊆ x∈s))

    anti-rel2mendo : antitone-func pre-subset pre-mendo
    func anti-rel2mendo s = mono (rel2endo s) (rel2endo-is-pointwisely-monotone s)
    property anti-rel2mendo {s} {s'} = rel2mendo-is-antitone {s} {s'}

    anti-mendo2rel : antitone-func pre-mendo pre-subset
    func anti-mendo2rel f = mendo2rel f
    property anti-mendo2rel {s} {s'} = mendo2rel-is-antitone {s} {s'}

    module fixedpoint (f : monotone-endo X-pre) (let X-cjlat = cmlat→cjlat X-cmlat) (let (cjlat _ _ ⋁X X-is-cjlat) = X-cjlat) (let _∨X_ = \ x y → ⋁X ｛ x , y ｝₂)  where
      {-
        f' : monotone-endo X-pre
        f' = (rel2mendo ∘ mendo2rel) f
        f* : monotone-endo X-pre
        func f* d = func f (func f d) ∨X d
        property f* = {!!}

        test' : func f' ≡ \x₀ → ⋀X \x → x₀ ≤X x × func f x ≤X x
        test' = ≡.refl
        prop1 : ∀ x₀ → func f' x₀ ≤X x₀
        prop1 x₀ = {!P.bigmeet-greatest _ _ _!}
          where
          module M = complete-meet-semilattice X-cmlat
          module P = is-complete-meet-semilattice M.property
          -}

  module _ where
    endo2rel-rel2endo-antitone-galois-connection : is-antitone-galois-connection anti-mendo2rel anti-rel2mendo
    endo2rel-rel2endo-antitone-galois-connection s f-mono =
      begin-≈
      flip _⊆_ (endo2relm f-mono) s ≡⟨⟩
      (∀ {x : X} → s x → f x ≤X x) ≈⟨ hidden↔explicit _ ⟩
      (∀ x₀ → x₀ ∈ s → f x₀ ≤X x₀) ≈⟨ bigmeet-mono-equivalence s (f-is-mono)  ⟩
      (∀ x₀ → f x₀ ≤X ⋀X (\ x → x₀ ≤X x × x ∈ s)) ≡⟨⟩
      f ≤endo rel2endo s ∎
      where open reasoning _ (→-is-preorder)
            open monotone-func anti-mendo2rel renaming (func to endo2relm ; property to endo2relm-is-antitone)
            open monotone-func f-mono renaming (func to f ; property to f-is-mono)

```

```agda
module transfer-function-pair
  (D-cmlat E-cmlat : complete-meet-semilattice)
  (let D-pre = cmlat→pre D-cmlat)
  (let E-pre = cmlat→pre E-cmlat)
  (let (cmlat D _≤D_ ⋀D D-is-cmlat) = D-cmlat)
  (let (cmlat E _≤E_ ⋀E E-is-cmlat) = E-cmlat)
  (let D×E-cmlat = D-cmlat ×-cmlat E-cmlat)
  (let (cmlat D×E _≤_ ⋀ D×E-is-cmlat) = D×E-cmlat)
  (let D-cjlat = cmlat→cjlat D-cmlat)
  (let E-cjlat = cmlat→cjlat E-cmlat)
  (let D×E-cjlat = cmlat→cjlat D×E-cmlat)
  (let (cjlat _ _ ⋁D D-is-cjlat) = D-cjlat)
  (let (cjlat _ _ ⋁E E-is-cjlat) = E-cjlat)
  (let (cjlat _ _ ⋁ D×E-is-cjlat) = D×E-cjlat)
  (let _∨D_ = \ x y → ⋁D ｛ x , y ｝₂)
  (let _∨E_ = \ x y → ⋁E ｛ x , y ｝₂)
  (let _∨_ = \ x y → ⋁ ｛ x , y ｝₂)
  where

  private
    module D = is-complete-meet-semilattice D-is-cmlat
      renaming (rel-is-preorder to ≤-pre ; op-is-bigmeet to ⋀-bigmeet ; rel-is-reflexive to ≤-refl ; rel-is-transitive to ≤-trans)
    module E = is-complete-meet-semilattice E-is-cmlat
      renaming (rel-is-preorder to ≤-pre ; op-is-bigmeet to ⋀-bigmeet ; rel-is-reflexive to ≤-refl ; rel-is-transitive to ≤-trans)
    module ≤D-reasoning = reasoning _ D.≤-pre
    module ≤E-reasoning = reasoning _ E.≤-pre

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
    (R-welldefined : is-welldefined-subset (pre _ _ ≤-pre) R)
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

  rel2mpair : subset (D × E) → monotone-func-pair D-pre E-pre
  monotone-func-pair.pair (rel2mpair r) = rel2pair r
  fst (monotone-func-pair.pair-is-monotone (rel2mpair r)) d≤d' = E.bigmeet-monotone \ { {d''} (d' , d'≤d'' , [d',d'']∈r ) → d' , D.≤-trans d≤d' d'≤d'' , [d',d'']∈r }
  snd (monotone-func-pair.pair-is-monotone (rel2mpair r)) e≤e' = D.bigmeet-monotone \ { {e''} (e' , e'≤e'' , [e',e'']∈r ) → e' , E.≤-trans e≤e' e'≤e'' , [e',e'']∈r }

  -- Right adjoint
  pair2rel : func-pair D E → subset (D × E)
  pair2rel (f , b) (d , e) = f d ≤E e × b e ≤D d

  mpair2rel : monotone-func-pair D-pre E-pre → subset (D × E)
  mpair2rel (mfp' pair pair-is-monotone) = pair2rel pair
    

  module _ {f : D → E} {b : E → D}
    (f-is-mono : is-monotone D.≤-pre E.≤-pre f) (b-is-mono : is-monotone E.≤-pre D.≤-pre b) where
    pair2rel-mono-meet-closed : is-meet-closed-subset D×E-is-cmlat (pair2rel (f , b))
    fst (pair2rel-mono-meet-closed S' S'⊆) =
      begin-≤
      f (fst (⋀ S')) ≡⟨⟩
      f (⋀D ｛ d ∣ Σ[ e ∈ E ] ((d , e) ∈ S')｝) ≤⟨ mono-meet≤meet-mono {D-cmlat} {E-cmlat} f-is-mono ｛ d ∣ Σ[ e ∈ E ] ((d , e) ∈ S')｝ ⟩
      ⋀E (fimage f ｛ d ∣ Σ[ e ∈ E ] ((d , e) ∈ S')｝) ≡⟨⟩
      ⋀E ｛ e ∣ Σ[ d ∈ D ] ((Σ[ e' ∈ E ](S' (d , e'))) × f d ≡ e)｝ ≈⟨ E.bigmeet-≡-≤ f _ ⟩
      ⋀E ｛ e ∣ Σ[ d ∈ D ] ((Σ[ e' ∈ E ](S' (d , e'))) × f d ≤E e)｝ ≤⟨ E.bigmeet-monotone (\ { {e} (d , de∈S') → d , ((e , de∈S') , fst (S'⊆ de∈S')) }) ⟩
      ⋀E ｛ e ∣ Σ[ d ∈ D ] ((d , e) ∈ S')｝ ≡⟨⟩
      snd (⋀ S') ∎
      where open ≤E-reasoning
    snd (pair2rel-mono-meet-closed S' S'⊆) =
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

  pair2rel-anti : antitone-func pre-pair pre-rel
  monotone-func.func pair2rel-anti pair = pair2rel pair
  monotone-func.property pair2rel-anti = pair2rel-is-antitone

  rel2pair-anti : antitone-func pre-rel pre-pair
  monotone-func.func rel2pair-anti r = rel2pair r
  monotone-func.property rel2pair-anti = rel2pair-is-antitone

  mpair2rel-anti : antitone-func pre-mpair pre-rel
  monotone-func.func mpair2rel-anti = mpair2rel
  monotone-func.property mpair2rel-anti = pair2rel-is-antitone

  rel2mpair-anti : antitone-func pre-rel pre-mpair
  monotone-func.func rel2mpair-anti r = mfp' (rel2pair r) (rel2pair-R-is-monotone-pair r)
  monotone-func.property rel2mpair-anti = rel2pair-is-antitone

  pair2rel-rel2pair-mono = pre-comp-anti mpair2rel-anti rel2mpair-anti
  open monotone-func pair2rel-rel2pair-mono renaming (property to pair2rel-rel2pair-is-monotone)
  rel2pair-pair2rel-mono = pre-comp-anti rel2mpair-anti mpair2rel-anti
  open monotone-func rel2pair-pair2rel-mono renaming (property to rel2pair-pair2rel-is-monotone)

  module _
    {R : subset (D × E)}
    (R-meet-closed : is-meet-closed-subset D×E-is-cmlat R)
    (R-welldefined : is-welldefined-subset (pre _ _ ≤-pre) R)
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
      R'-meet-closed = pair2rel-mono-meet-closed (fst (rel2pair-R-is-monotone-pair R)) (snd (rel2pair-R-is-monotone-pair R))

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


```
module _ (D-cmlat E-cmlat : complete-meet-semilattice) (let D-pre = cmlat→pre D-cmlat) (let E-pre = cmlat→pre E-cmlat) where

  open transfer-function-pair D-cmlat E-cmlat
  module D-cmlat = complete-meet-semilattice D-cmlat
  module E-cmlat = complete-meet-semilattice E-cmlat

  D-is-pre = is-complete-meet-semilattice.rel-is-preorder D-cmlat.property
  E-is-pre = is-complete-meet-semilattice.rel-is-preorder E-cmlat.property

  mpair2rel-rel2mpair-antitone-galois-connection : is-antitone-galois-connection mpair2rel-anti rel2mpair-anti
  forward (mpair2rel-rel2mpair-antitone-galois-connection r (mfp' (f , b) (f-mono , b-mono))) = left-transpose r f b f-mono b-mono
  backward (mpair2rel-rel2mpair-antitone-galois-connection r (mfp' (f , b) _)) = right-transpose r f b


  {-
  pair2rel-rel2pair-antitone-galois-connection : is-antitone-galois-connection pair2rel-anti rel2pair-anti
  forward (pair2rel-rel2pair-antitone-galois-connection r (f , b)) x = \where
    .fst d → {!need monotonity of f!}
    .snd e → {!!}
      where
      f-wd : f ∈ is-welldefined D-is-pre E-is-pre
      f-wd x = {!!}
      b-wd : b ∈ is-welldefined E-is-pre D-is-pre
      b-wd x = {!!}
  backward (pair2rel-rel2pair-antitone-galois-connection r (f , b)) = right-transpose r f b
  -}


  rel-mpair-connected : antitone-galois-connection pre-rel pre-mpair
  galois-connection.left-adjoint rel-mpair-connected = mpair2rel-anti
  galois-connection.right-adjoint rel-mpair-connected = monotone-func.dual rel2mpair-anti
  galois-connection.left-right-is-galois-connection rel-mpair-connected = mpair2rel-rel2mpair-antitone-galois-connection


  private module D×E-cmlat = complete-meet-semilattice (D-cmlat ×-cmlat E-cmlat)
  D×E-is-pre = is-complete-meet-semilattice.rel-is-preorder D×E-cmlat.property
  open endo-function (D-cmlat ×-cmlat E-cmlat)

  rel-mendo-connected : antitone-galois-connection pre-rel pre-mendo
  galois-connection.left-adjoint rel-mendo-connected = anti-mendo2rel
  galois-connection.right-adjoint rel-mendo-connected = monotone-func.dual anti-rel2mendo
  galois-connection.left-right-is-galois-connection rel-mendo-connected = endo2rel-rel2endo-antitone-galois-connection

  endo2pair : endo (D-cmlat.carrier × E-cmlat.carrier) → func-pair (D-cmlat.carrier) (E-cmlat.carrier)
  fst (endo2pair f) d = snd (f (d , E-cmlat.operation U))
  snd (endo2pair f) e = fst (f (D-cmlat.operation U , e))

  endo2pair-is-monotone : is-monotone ≤endo-is-preorder ≤pair-is-preorder endo2pair
  fst (endo2pair-is-monotone e≤e') d = snd (e≤e' (d , E-cmlat.operation U))
  snd (endo2pair-is-monotone e≤e') e = fst (e≤e' (D-cmlat.operation U , e))


  mendo2mpair : monotone-endo (cmlat→pre (D-cmlat ×-cmlat E-cmlat)) → monotone-func-pair D-pre E-pre
  fst (monotone-func-pair.pair (mendo2mpair (mono h h-is-mono))) = fst (endo2pair h)
  snd (monotone-func-pair.pair (mendo2mpair (mono h h-is-mono))) = snd (endo2pair h)
  fst (monotone-func-pair.pair-is-monotone (mendo2mpair (mono h h-is-mono))) d≤d' = snd (h-is-mono (d≤d' , is-preorder.rel-is-reflexive E-is-pre _))
  snd (monotone-func-pair.pair-is-monotone (mendo2mpair (mono h h-is-mono))) e≤e' = fst (h-is-mono (is-preorder.rel-is-reflexive D-is-pre _ , e≤e'))

  mendo2mpair-is-monotone : is-monotone ≤mendo-is-preorder ≤mpair-is-preorder mendo2mpair
  fst (mendo2mpair-is-monotone e≤e') d = snd (e≤e' (d , E-cmlat.operation U))
  snd (mendo2mpair-is-monotone e≤e') e = fst (e≤e' (D-cmlat.operation U , e))

  mono-mendo2mpair : monotone-func pre-mendo pre-mpair
  monotone-func.func mono-mendo2mpair = mendo2mpair
  monotone-func.property mono-mendo2mpair {d} {d'} = mendo2mpair-is-monotone {d} {d'}


  pair2endo : func-pair (D-cmlat.carrier) (E-cmlat.carrier) → endo (D-cmlat.carrier × E-cmlat.carrier)
  pair2endo (f , b) (d , e) = (b e , f d)

  pair2endo-is-monotone : is-monotone ≤pair-is-preorder ≤endo-is-preorder pair2endo
  fst (pair2endo-is-monotone fb≤f'b' de) = snd fb≤f'b' (snd de)
  snd (pair2endo-is-monotone fb≤f'b' de) = fst fb≤f'b' (fst de)

  mpair2mendo : monotone-func-pair D-pre E-pre → monotone-endo (cmlat→pre (D-cmlat ×-cmlat E-cmlat))
  monotone-func.func (mpair2mendo (mfp' (f , b) (f-mono , b-mono))) (d , e) = pair2endo (f , b) (d , e)
  monotone-func.property (mpair2mendo (mfp' (f , b) (f-mono , b-mono))) (d≤d' , e≤e') = b-mono e≤e' , f-mono d≤d'

  mpair2mendo-is-monotone : is-monotone ≤mpair-is-preorder ≤mendo-is-preorder mpair2mendo
  mpair2mendo-is-monotone (f-mono , b-mono) (d , e) = b-mono e , f-mono d

  mono-mpair2mendo : monotone-func pre-mpair pre-mendo
  monotone-func.func mono-mpair2mendo = mpair2mendo
  monotone-func.property mono-mpair2mendo {d} {d'} = mpair2mendo-is-monotone {d} {d'}

  module _ where
    open galois-connection

  -- endo function needs to bemonotone
  mendo-mpair-connected : galois-connection pre-mendo pre-mpair
  galois-connection.left-adjoint mendo-mpair-connected = mono-mpair2mendo
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

  test2 : (let (gal-conn l' r' _) = rel-mpair-connected') (let (gal-conn l r _) = rel-mpair-connected) →
    ∀ pair →  monotone-func.func l pair ≅ monotone-func.func l' pair
  forward (test2 (mfp' fp fp-is-monotone)) {p} x = (snd x , fst x)
  backward (test2 (mfp' fp fp-is-monotone)) {p} x = (snd x , fst x)

  pair2fun : func-pair D-cmlat.carrier E-cmlat.carrier → fun D-cmlat.carrier E-cmlat.carrier
  pair2fun (f , b) = f

  pair2fun-is-monotone : is-monotone ≤pair-is-preorder ≤fun-is-preorder pair2fun
  pair2fun-is-monotone (f≤f' , b≤b') = f≤f'


  mpair2mfun : monotone-func-pair D-pre E-pre → monotone-func D-pre E-pre
  monotone-func.func (mpair2mfun (mfp' pair pair-is-monotone)) = pair2fun pair
  monotone-func.property (mpair2mfun (mfp' pair pair-is-monotone)) = fst pair-is-monotone

  mpair2mfun-mono : monotone-func pre-mpair pre-mfun
  mpair2mfun-mono = (mono mpair2mfun (\ fb≤fb' d → fst fb≤fb' d))

  fun2pair : fun D-cmlat.carrier E-cmlat.carrier → func-pair (D-cmlat.carrier) (E-cmlat.carrier)
  fun2pair f = f , \ _ → complete-meet-semilattice.operation D-cmlat U

  fun2pair-is-monotone : is-monotone ≤fun-is-preorder ≤pair-is-preorder fun2pair
  fst (fun2pair-is-monotone f≤f') d = f≤f' d
  snd (fun2pair-is-monotone _) _ = complete-meet-semilattice.property.bigmeet-monotone D-cmlat id

  mfun2mpair : monotone-func D-pre E-pre → monotone-func-pair D-pre E-pre
  monotone-func-pair.pair (mfun2mpair (mono func property)) = fun2pair func
  fst (monotone-func-pair.pair-is-monotone (mfun2mpair (mono func property))) = property
  snd (monotone-func-pair.pair-is-monotone (mfun2mpair (mono func property))) {d} {d'} _ = is-complete-meet-semilattice.bigmeet-monotone D-cmlat.property (\ x → x)

  mfun2mpair-is-monotone : is-monotone ≤mfun-is-preorder ≤mpair-is-preorder mfun2mpair
  mfun2mpair-is-monotone f≤f' .fst = \ d → f≤f' d
  mfun2mpair-is-monotone f≤f' .snd = \ e → is-complete-meet-semilattice.bigmeet-monotone D-cmlat.property (\ x → x)

  mono-mfun2mpair : monotone-func pre-mfun pre-mpair
  monotone-func.func mono-mfun2mpair = mfun2mpair
  monotone-func.property mono-mfun2mpair {d} {d'} = mfun2mpair-is-monotone {d} {d'}

  pair-fun-connected : galois-connection pre-pair pre-fun
  galois-connection.left-adjoint pair-fun-connected = mono fun2pair fun2pair-is-monotone
  galois-connection.right-adjoint pair-fun-connected = mono pair2fun pair2fun-is-monotone
  forward (galois-connection.left-right-is-galois-connection pair-fun-connected f fb) Lf≤fb d = fst Lf≤fb d
  backward (galois-connection.left-right-is-galois-connection pair-fun-connected f fb) f≤fb = \ where
    .fst d → f≤fb d
    .snd e → is-complete-meet-semilattice.bigmeet-lowerbound D-cmlat.property _ _ _

  mpair-mfun-connected : galois-connection pre-mpair pre-mfun
  galois-connection.left-adjoint mpair-mfun-connected = mono-mfun2mpair
  galois-connection.right-adjoint mpair-mfun-connected = mono mpair2mfun (\ fb≤fb' d → fst fb≤fb' d)
  forward (galois-connection.left-right-is-galois-connection mpair-mfun-connected mfp mf) Lmf≤mfp d = fst Lmf≤mfp d
  backward (galois-connection.left-right-is-galois-connection mpair-mfun-connected mfp mf) mf≤Rmfp = (\ d → mf≤Rmfp d) , (\ e → is-complete-meet-semilattice.bigmeet-lowerbound D-cmlat.property _ _ _)
  mendo-mfun-connected : galois-connection pre-mendo pre-mfun
  mendo-mfun-connected = comp-galois-connection mendo-mpair-connected mpair-mfun-connected

  rel2fun : subset (D-cmlat.carrier × E-cmlat.carrier) → fun D-cmlat.carrier E-cmlat.carrier
  rel2fun = pair2fun ∘ rel2pair

  rel2fun' : subset (D-cmlat.carrier × E-cmlat.carrier) → fun D-cmlat.carrier E-cmlat.carrier
  rel2fun' r d = ⋀E \ e → Σ _ \ d' → d ≤D d' × r (d' , e)
    where open E-cmlat renaming (operation to ⋀E)
          open D-cmlat renaming (relation to _≤D_)

  rel2mfun : subset (D-cmlat.carrier × E-cmlat.carrier) → monotone-func D-pre E-pre
  rel2mfun = mpair2mfun ∘ rel2mpair

  rel2mfun' : subset (D-cmlat.carrier × E-cmlat.carrier) → monotone-func D-pre E-pre
  rel2mfun' r = mono (rel2fun' r) \ d≤d' → bigmeet-monotone \where
    {e'} (d'' , d'≤d'' , d''e'∈r) → d'' , D-is-pre .is-preorder.rel-is-transitive d≤d' d'≤d'' , d''e'∈r
      where
      open E-cmlat renaming (carrier to E;property to E-is-cmlat)
      open is-complete-meet-semilattice E-is-cmlat
      open D-cmlat renaming (carrier to D;relation to _≤D_)

  fun2rel : fun D-cmlat.carrier E-cmlat.carrier → subset (D-cmlat.carrier × E-cmlat.carrier)
  fun2rel = pair2rel ∘ fun2pair

  fun2rel' : fun D-cmlat.carrier E-cmlat.carrier → subset (D-cmlat.carrier × E-cmlat.carrier)
  fun2rel' f (d , e) = f d ≤E e
    where open E-cmlat renaming (relation to _≤E_)

  mfun2rel' : monotone-func D-pre E-pre → subset (D-cmlat.carrier × E-cmlat.carrier)
  mfun2rel' (mono f f-mono) = fun2rel' f

  mfun2rel : monotone-func D-pre E-pre → subset (D-cmlat.carrier × E-cmlat.carrier)
  mfun2rel = fun2rel ∘ monotone-func.func
  -- (monotone-func.func mpair2rel-anti) ∘ (monotone-func.func mono-mfun2mpair)

  -- rel2mfun : (𝒫(C × D) , ⊆)^op ⇒ (C × D → C × D)
  rel2mfun-mono : antitone-func pre-rel pre-mfun
  rel2mfun-mono = pre-comp (monotone-func.dual mpair2mfun-mono) rel2mpair-anti
  -- mfun2rel : (𝒫(C × D) , ⊆)^op ⇒ EndoMonoFun (C × D)
  mfun2rel-mono : antitone-func pre-mfun pre-rel
  mfun2rel-mono = pre-comp mpair2rel-anti mono-mfun2mpair

  rel-mfun-connected : antitone-galois-connection pre-rel pre-mfun
  rel-mfun-connected = comp-galois-connection rel-mendo-connected mendo-mfun-connected



```

Order embeddings
```agda

  mfun2mpair-embedding : order-embedding pre-mfun pre-mpair
  order-embedding.func mfun2mpair-embedding = mfun2mpair
  is-order-embedding.func-is-monotone (order-embedding.property mfun2mpair-embedding) {d} {d'} = mfun2mpair-is-monotone {d} {d'}
  is-order-embedding.func-is-reflecting (order-embedding.property mfun2mpair-embedding) (Lf≤Lf' , Lb≤b') d = Lf≤Lf' d

  mpair2mendo-embedding : order-embedding pre-mpair pre-mendo
  order-embedding.func mpair2mendo-embedding = mpair2mendo
  is-order-embedding.func-is-monotone (order-embedding.property mpair2mendo-embedding) {d} {d'} = mpair2mendo-is-monotone {d} {d'}
  is-order-embedding.func-is-reflecting (order-embedding.property mpair2mendo-embedding) {fb} {fb'} Lfb≤Lfb' .fst d = snd (Lfb≤Lfb' (d , complete-meet-semilattice.operation E-cmlat ∅))
  is-order-embedding.func-is-reflecting (order-embedding.property mpair2mendo-embedding) {fb} {fb'} Lfb≤Lfb' .snd e = fst (Lfb≤Lfb' (complete-meet-semilattice.operation D-cmlat ∅ , e))

```

* fixed-points of galois-connection

Let X is a poset,

```txt

                         L
                      <------
            (𝒫(C),⊆)    ⊥       X
                      ------->
               | ↑       R      | ↑
               | |              | |
               |⊣|              |⊢|
               ↓ J        α     ↓ J
                      <-------
        (𝒫(C),⊆)_fix     ≅     X_fix
                      ------->

RL f = ~ f
                         L
                      <------            <----------             <-----------------------------
            (𝒫(A × B),⊆)  ⊤   A×B→A×B         ⊤       A→B × B→A                ⊤                A→B
                      ------->  monotone  ---------->  monotone  -----------------------------> monotone
               | ↑       R      | ↑                      | |                                      | |
               | |              | |                      | |                                      | |
               |⊣|              |⊢|                      | |                                      | |
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

(R ⋈ P) ⋈ Q ⊂ R ⋈ (P ⋈ Q) and
(R ⋈ P) ⋈ Q ⊂ R ⋈ (P ⋈ Q)


If we have a pair of adjoints L, R on the top then we have
a full sub category (𝒫(C),⊆)_fix of (𝒫(C),⊆) whose objects are c with an isomorphism c ≃ηc RL(c)
and a full sub category X_fix of X whose objects are x with an isomorphism LR(x) ≃εx x
https://ncatlab.org/nlab/show/fixed+point+of+an+adjunction

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

module derive-subset-galois
  {D : complete-meet-semilattice → complete-meet-semilattice → preordered-set}
  (⊆-D-gal : (X Y : complete-meet-semilattice) → antitone-galois-connection (pre (subset (complete-meet-semilattice.carrier X × complete-meet-semilattice.carrier Y)) _⊆_ ⊆-is-preorder) (D X Y))
  (imgL-welldefined : (X Y : complete-meet-semilattice) → ∀ r → complete-meet-semilattice.is-welldefined-subset' (X ×-cmlat Y) (galois-connection.left-adjoint (⊆-D-gal X Y) .monotone-func.func r))
  (imgL-meet-closed : (X Y : complete-meet-semilattice) → ∀ r → complete-meet-semilattice.is-meet-closed-subset' (X ×-cmlat Y) (galois-connection.left-adjoint (⊆-D-gal X Y) .monotone-func.func r))
  where
  private
    module G {a} {b} = galois-connection (⊆-D-gal a b)
    module ≤ X = preordered-set (cmlat→pre X) renaming (relation to _≤_; equiv to _≈_; property to preorder)
    Dobj = \ a b → preordered-set.carrier (D a b)
    module D {a} {b} = preordered-set (D a b) renaming (relation to _≤_; equiv to _≈_; property to ≤-preorder)
    module R {a} {b} = monotone-func (G.right-adjoint {a} {b})
    module L {a} {b} = monotone-func (G.left-adjoint {a} {b})
    open R renaming (func to R; property to R-mono)
    open L renaming (func to L; property to L-mono)
    ℛ = \ a b → subset (complete-meet-semilattice.carrier a × complete-meet-semilattice.carrier b)
    RL : ∀ a b → (d : Dobj a b) → Dobj a b
    RL a b d = R {a = a} {b = b} (L {a = a} {b = b} d)
    LR : ∀ a b → (d : ℛ a b) → ℛ a b
    LR a b d = L {a = a} {b = b} (R {a = a} {b = b} d)

  module _ {X : complete-meet-semilattice} where
    private
      module X = complete-meet-semilattice X renaming (operation to ⋀; relation to _≤_)
      open preordered-set (cmlat→pre X) renaming (equiv to _≈_)

    Δ : subset (X.carrier × X.carrier)
    Δ (x , x') = x ≈ x'

    δ : Dobj X X
    δ = R Δ

    RLδ≈δ : RL X X δ D.≈ δ
    RLδ≈δ = G.rl-idempotent Δ

  Lδ-monoidal-strength = ∀{X} → Δ {X} ≅ L (δ {X})

  module _ {X Y : complete-meet-semilattice} where
    private
      module X = complete-meet-semilattice X
      module Y = complete-meet-semilattice Y
      module X×Y = complete-meet-semilattice (X ×-cmlat Y)

    id⊆LR : (r : ℛ X Y) → r ⊆ LR X Y r
    id⊆LR r {x} x∈r = G.lr-decreasing r x∈r

    LRLR≅LR : (r : ℛ X Y) → L (R (LR X Y r)) ≅ LR _ _ r
    LRLR≅LR r .backward x = G.lr-idempotent (R r) .forward x
    LRLR≅LR r .forward x = G.lr-idempotent (R r) .backward x

    id≤RL : (d : Dobj X Y) → d D.≤ RL _ _ d
    id≤RL d = G.rl-increasing d

    top : Dobj X Y
    top = R ∅

    bot : Dobj X Y
    bot = R U

    _⊓_ : (x y : Dobj X Y) → Dobj X Y
    x ⊓ y = R (L x ∪ L y)

    _⊔_ : (x y : Dobj X Y) → Dobj X Y
    x ⊔ y = R (L x ∩ L y)

    ∪-monotone : {a a' : ℛ X Y} {b b' : ℛ X Y} → a ⊆ a' → b ⊆ b' → a ∪ b ⊆ a' ∪ b'
    ∪-monotone a⊆a' b⊆b' (left x∈a) = left (a⊆a' x∈a)
    ∪-monotone a⊆a' b⊆b' (right x∈b) = right (b⊆b' x∈b)

    ∩-monotone : {a a' : ℛ X Y} {b b' : ℛ X Y} → a ⊆ a' → b ⊆ b' → a ∩ b ⊆ a' ∩ b'
    ∩-monotone a⊆a' b⊆b' (fst , snd) = (a⊆a' fst , b⊆b' snd)

    RL∘⊓≈⊓ : (a : Dobj X Y) → (b : Dobj X Y) → (RL _ _ (a ⊓ b)) D.≈ (a ⊓ b)
    RL∘⊓≈⊓ a b = G.rl-idempotent (L a ∪ L b)

    ⊔∘RL≈⊔ : (a : Dobj X Y) → (b : Dobj X Y) → (RL _ _ a ⊓ RL _ _ b) D.≈ (a ⊓ b)
    ⊔∘RL≈⊔ a b .forward = R-mono Q
      where
      Q : L a ∪ L b ⊆ L (RL _ _ a) ∪ L (RL _ _ b)
      Q (left x∈La) = left (G.lr-idempotent a .forward x∈La)
      Q (right x∈Lb) = right (G.lr-idempotent b .forward x∈Lb)

    ⊔∘RL≈⊔ a b .backward = R-mono Q
      where
      Q : L (RL _ _ a) ∪ L (RL _ _ b) ⊆ L a ∪ L b
      Q (left x∈LRLa) = left (G.lr-idempotent a .backward x∈LRLa)
      Q (right x∈LRLb) = right (G.lr-idempotent b .backward x∈LRLb)

    ∪⊆LR∘∪ : (r : ℛ X Y) → (r' : ℛ X Y) → r ∪ r' ⊆ LR X Y (r ∪ r')
    ∪⊆LR∘∪ r r' = G.lr-decreasing _

    ∪⊆∪∘LR : (r : ℛ X Y) → (r' : ℛ X Y) → r ∪ r' ⊆ (LR X Y r ∪ LR X Y r')
    ∪⊆∪∘LR r r' = ∪-monotone {a = r} {b = r'} (G.lr-decreasing r) (G.lr-decreasing r')

    prop-∪-LR-commute = (r r' : ℛ X Y) → LR X Y (r ∪ r') ≅ LR X Y r ∪ LR X Y r'

  Ltop-monoidal-strength = ∀ {X Y} → (d : Dobj X Y) → ∅ ≅ L {a = X} {b = Y} top
  L⊓-monoidal-strength = ∀ {X Y} → (d : Dobj X Y) (d' : Dobj X Y) → L d ∪ L d' ≅ L (d ⊓ d')

  module _ {X Y : complete-meet-semilattice} where
    private
      module X = complete-meet-semilattice X
      module Y = complete-meet-semilattice Y
      module X×Y = complete-meet-semilattice (X ×-cmlat Y)

    ∅-lunit : (r : ℛ X Y) → ∅ ∪ r ≅ r
    forward (∅-lunit r) (right x∈r) = x∈r
    backward (∅-lunit r) x∈r = right x∈r

    top-lunit = (d : Dobj X Y) → (top ⊓ d) D.≈ d
    top-laxlunit = (d : Dobj X Y) → d D.≤ (top ⊓ d)
    top-oplaxlunit = (d : Dobj X Y) → (top ⊓ d) D.≤ d

    ∪-associative : (r r' r'' : ℛ X Y) → ((r ∪ r') ∪ r'') ≅ (r ∪ (r' ∪ r''))
    forward (∪-associative r r' r'') (left (left x)) = left x
    forward (∪-associative r r' r'') (left (right y)) = right (left y)
    forward (∪-associative r r' r'') (right y) = right (right y)
    backward (∪-associative r r' r'') (left x) = left (left x)
    backward (∪-associative r r' r'') (right (left x)) = left (right x)
    backward (∪-associative r r' r'') (right (right y)) = right y

    ⊓-associative = (d : Dobj X Y) (d' : Dobj X Y) (d'' : Dobj X Y) → ((d ⊓ d') ⊓ d'') D.≈ (d ⊓ (d' ⊓ d''))

    lemma-top-laxlunit : Ltop-monoidal-strength → top-laxlunit
    lemma-top-laxlunit ∅≅Ltop d = G.rl-increasing d ∙ (R-mono Q)
      where _∙_ = D.≤-preorder.rel-is-transitive
            Q : L top ∪ L d ⊆ L d
            Q (left x∈Ltop) = case ∅≅Ltop d .backward x∈Ltop of \()
            Q (right x∈Ld) = x∈Ld

    L-⊓-∪-assoc : L⊓-monoidal-strength → (d : Dobj X Y) (d' : Dobj X Y) (d'' : Dobj X Y) → L d ∪ L (d' ⊓ d'') ≅ L (d ⊓ d') ∪ L d''
    L-⊓-∪-assoc α d d' d'' .forward {x} x∈Ld∪L[d'⊓d''] = x∈L[d⊓d']∪Ld''
      where
      x∈Ld∪[Ld'∪Ld''] : x ∈ L d ∪ (L d' ∪ L d'')
      x∈Ld∪[Ld'∪Ld''] = ∪-monotone {X = X} {Y = Y} {a = L d} {b = L (d' ⊓ d'')} id (α d' d'' .backward) x∈Ld∪L[d'⊓d'']
      x∈[Ld∪Ld']∪Ld'' : x ∈ (L d ∪ L d') ∪ L d''
      x∈[Ld∪Ld']∪Ld'' = ∪-associative (L d) (L d') (L d'') .backward x∈Ld∪[Ld'∪Ld'']
      x∈L[d⊓d']∪Ld'' : x ∈ L (d ⊓ d') ∪ L d''
      x∈L[d⊓d']∪Ld'' = ∪-monotone {X = X} {Y = Y} {a = L d ∪ L d'} {b = L d''} (α d d' .forward) id x∈[Ld∪Ld']∪Ld''

    L-⊓-∪-assoc α d d' d'' .backward {x} x∈[Ld⊓Ld']∪Ld'' = x∈Ld∪L[d'⊓d'']
      where
      x∈[Ld∪Ld']∪Ld'' : x ∈ (L d ∪ L d') ∪ L d''
      x∈[Ld∪Ld']∪Ld'' = ∪-monotone {X = X} {Y = Y} {a = L (d ⊓ d')} {b = L d''} (α d d' .backward) id x∈[Ld⊓Ld']∪Ld''
      x∈Ld∪[Ld'∪Ld''] : x ∈ L d ∪ (L d' ∪ L d'')
      x∈Ld∪[Ld'∪Ld''] =  ∪-associative (L d) (L d') (L d'') .forward x∈[Ld∪Ld']∪Ld''
      x∈Ld∪L[d'⊓d''] : x ∈ L d ∪ L (d' ⊓ d'')
      x∈Ld∪L[d'⊓d''] = ∪-monotone {X = X} {Y = Y} {a = L d} {b = L d' ∪ L d''} id (α d' d'' .forward) x∈Ld∪[Ld'∪Ld'']

    lemma-⊓-assoc : L⊓-monoidal-strength → ⊓-associative
    lemma-⊓-assoc α d d' d'' .forward = R-mono (L-⊓-∪-assoc α d d' d'' .forward)
    lemma-⊓-assoc α d d' d'' .backward = R-mono (L-⊓-∪-assoc α d d' d'' .backward)

  module _ {X Y Z : complete-meet-semilattice} where
    private
      module X = complete-meet-semilattice X renaming (operation to ⋀; relation to _≤_)
      module Y = complete-meet-semilattice Y renaming (operation to ⋀; relation to _≤_)
      module Z = complete-meet-semilattice Z renaming (operation to ⋀; relation to _≤_)

    _⊗_ : (dxy : Dobj X Y) → (dyz : Dobj Y Z) → Dobj X Z
    dxy ⊗ dyz = R (L dxy ⋈ L dyz)

    ⋈-monotone : ∀ {X Y Z} {a a' : subset (X × Y)} {b b' : subset (Y × Z)} → a ⊆ a' → b ⊆ b' → a ⋈ b ⊆ a' ⋈ b'
    ⋈-monotone a⊆a' b⊆b' (y , ∈a , ∈b) = y , (a⊆a' ∈a) , (b⊆b' ∈b)

    RL∘⊗≈⊗ : (dxy : Dobj X Y) → (dyz : Dobj Y Z) → (RL X Z (dxy ⊗ dyz)) D.≈ (dxy ⊗ dyz)
    RL∘⊗≈⊗ dxy dyz = G.rl-idempotent (L dxy ⋈ L dyz)

    ⊗∘RL≈⊗ : (dxy : Dobj X Y) → (dyz : Dobj Y Z) → (RL X Y dxy ⊗ RL Y Z dyz) D.≈ (dxy ⊗ dyz)
    ⊗∘RL≈⊗ dxy dyz .forward = R-mono Q
      where
      Q : L dxy ⋈ L dyz ⊆ L (RL X Y dxy) ⋈ L (RL Y Z dyz)
      Q (y , xy∈Ldxy , yz∈Ldyz) = y , G.lr-idempotent _ .forward xy∈Ldxy , G.lr-idempotent _ .forward yz∈Ldyz
    ⊗∘RL≈⊗ dxy dyz .backward = R-mono Q
      where
      Q : L (RL X Y dxy) ⋈ L (RL Y Z dyz) ⊆ L dxy ⋈ L dyz
      Q (y , xy∈LRLdxy , yz∈LRLdyz) = y , G.lr-idempotent _ .backward xy∈LRLdxy , G.lr-idempotent _ .backward yz∈LRLdyz

    ⊗∘RL≈RL∘⊗ : (dxy : Dobj X Y) → (dyz : Dobj Y Z) → (RL X Y dxy ⊗ RL Y Z dyz) D.≈ (RL X Z (dxy ⊗ dyz))
    ⊗∘RL≈RL∘⊗ dxy dyz .forward = trans (⊗∘RL≈⊗ dxy dyz .forward) (! (RL∘⊗≈⊗ dxy dyz) .forward)
      where trans = D.≤-preorder.rel-is-transitive
    ⊗∘RL≈RL∘⊗ dxy dyz .backward = trans (! (RL∘⊗≈⊗ dxy dyz) .backward) (⊗∘RL≈⊗ dxy dyz .backward)
      where trans = D.≤-preorder.rel-is-transitive

    ⋈⊆LR∘⋈ : (rxy : ℛ X Y) → (ryz : ℛ Y Z) → rxy ⋈ ryz ⊆ LR X Z (rxy ⋈ ryz)
    ⋈⊆LR∘⋈ rxy ryz = G.lr-decreasing  (rxy ⋈ ryz)

    ⋈⊆⋈∘LR : (rxy : ℛ X Y) → (ryz : ℛ Y Z) → rxy ⋈ ryz ⊆ LR X Y rxy ⋈ LR Y Z ryz
    ⋈⊆⋈∘LR rxy ryz  = ⋈-monotone {a = rxy} {b = ryz} (G.lr-decreasing rxy) (G.lr-decreasing ryz)

    prop-⋈-LR-commute = (rxy : ℛ X Y) → (ryz : ℛ Y Z) → LR X Z (rxy ⋈ ryz) ≅ LR X Y rxy ⋈ LR Y Z ryz
    -- this condition makes ⊗ associative (but is this necessary condition?)

  L⊗-monoidal-strength = ∀ {X Y Z} → (dxy : Dobj X Y) (dyz : Dobj Y Z) → L dxy ⋈ L dyz ≅ L (dxy ⊗ dyz)

  module _ (X Y : complete-meet-semilattice)  where
    private
      module X = complete-meet-semilattice X
      module Y = complete-meet-semilattice Y

    Δ-lunit : (r : ℛ X Y) (r-is-wd : is-welldefined-subset (cmlat→pre X ×-pre cmlat→pre Y) r) → Δ {X} ⋈ r ≅ r
    Δ-lunit r r-is-wd .forward {x , y} (x' , xx'∈Δ , x'y∈r) = r-is-wd (record { forward = (xx'∈Δ .backward) , (≤.preorder.rel-is-reflexive Y _) ; backward = (xx'∈Δ .forward) , (≤.preorder.rel-is-reflexive Y _) }) .forward x'y∈r
    Δ-lunit r r-is-wd .backward {x , y} xy∈r = x , refl-iso (≤.preorder.rel-is-reflexive X _) ≡.refl , xy∈r

    δ-lunit = (dxy : Dobj X Y) → (δ ⊗ dxy) D.≈ dxy
    -- a morphism in D is a relation d ≥ d' so δ ⊗ d ≥ d' is lax condition
    -- you can check terminology on lax monoidal category (such as lax-, oplax, biased, unbiased and skew)
    -- https://ncatlab.org/nlab/show/lax+monoidal+category
    δ-laxlunit = (dxy : Dobj X Y) → dxy D.≤ (δ ⊗ dxy)
    -- RΔ ⊗ dxy = R(LRΔ ⋈ Ldxy) = R(Δ ⋈ Ldxy) = RLdxy ≥ dxy

    lemma-δ-laxlunit : Lδ-monoidal-strength → δ-laxlunit
    lemma-δ-laxlunit Δ≅Lδ dxy = G.rl-increasing dxy ∙ (R-mono Q)
      where _∙_ = D.≤-preorder.rel-is-transitive
            Q : L δ ⋈ L dxy ⊆ L dxy
            Q {x , y} (x' , xLRΔx' , x'yLdxy) = let
              xΔx' = Δ≅Lδ .backward xLRΔx'
              in Δ-lunit (L dxy) wd .forward (x' , xΔx' , x'yLdxy)
              where wd : is-welldefined-subset (cmlat→pre X ×-pre cmlat→pre Y) (L dxy)
                    wd = imgL-welldefined X Y dxy

  module _ {X Y Z W : complete-meet-semilattice} where
    private
      module X = complete-meet-semilattice X renaming (operation to ⋀; relation to _≤_)
      module Y = complete-meet-semilattice Y renaming (operation to ⋀; relation to _≤_)
      module Z = complete-meet-semilattice Z renaming (operation to ⋀; relation to _≤_)

    ⋈-associative : (rxy : ℛ X Y) (ryz : ℛ Y Z) (rzw : ℛ Z W) → (rxy ⋈ ryz) ⋈ rzw ≅ rxy ⋈ (ryz ⋈ rzw)
    ⋈-associative rxy ryz rzw .forward {x , w} (z , (y , xy∈rxy , yz∈ryz) , zw∈rzw) = (y , xy∈rxy , z , yz∈ryz , zw∈rzw)
    ⋈-associative rxy ryz rzw .backward {x , w} (y , xy∈rxy , z , yz∈ryz , zw∈rzw) = (z , (y , xy∈rxy , yz∈ryz) , zw∈rzw)

    ⊗-associative = (dxy : Dobj X Y) (dyz : Dobj Y Z) (dzw : Dobj Z W) → ((dxy ⊗ dyz) ⊗ dzw) D.≈ (dxy ⊗ (dyz ⊗ dzw))

    L-⊗-⋈-assoc : L⊗-monoidal-strength → (dxy : Dobj X Y) (dyz : Dobj Y Z) (dzw : Dobj Z W) → L dxy ⋈ L (dyz ⊗ dzw) ≅ L (dxy ⊗ dyz) ⋈ L dzw
    L-⊗-⋈-assoc α dxy dyz dzw .forward {x , w} (y , xy∈Ldxy , yw∈L[dyz⊗dzw]) =
      let
        (z , yz∈Ldyz , zw∈Ldzw) = α dyz dzw .backward yw∈L[dyz⊗dzw]
        xz∈L[dxy⊗dyz] = α dxy dyz .forward (y , xy∈Ldxy , yz∈Ldyz)
      in (z , xz∈L[dxy⊗dyz] , zw∈Ldzw)

    L-⊗-⋈-assoc α dxy dyz dzw .backward {x , w} (z , xz∈L[dxy⊗dyz] , zw∈Ldzw) =
      let
        (y , xy∈Ldxy , yz∈Ldyz) = α dxy dyz .backward xz∈L[dxy⊗dyz]
        yw∈L[dyz⊗dzw] = α dyz dzw .forward (z , yz∈Ldyz , zw∈Ldzw)
      in y , xy∈Ldxy , yw∈L[dyz⊗dzw]

    lemma-⊗-assoc : L⊗-monoidal-strength → ⊗-associative
    lemma-⊗-assoc α dxy dyz dzw .forward = R-mono (L-⊗-⋈-assoc α dxy dyz dzw .forward)
    lemma-⊗-assoc α dxy dyz dzw .backward = R-mono (L-⊗-⋈-assoc α dxy dyz dzw .backward)

    ⊗₃ : (dxy : Dobj X Y) → (dyz : Dobj Y Z) → (dzw : Dobj Z W) → Dobj X W
    ⊗₃ dxy dyz dzw = R ((L dxy ⋈ L dyz) ⋈ L dzw)

{-
    ⊗⊗≤⊗₃ : (dxy : Dobj X Y) → (dyz : Dobj Y Z) → (dzw : Dobj Z W) → ((dxy ⊗ dyz) ⊗ dzw) D.≤ ⊗₃ dxy dyz dzw
    ⊗⊗≤⊗₃ dxy dyz dzw = R-mono \{ x → {!!} , {!!} }
-}
{-
    -- So far, I have not used the complete-meet-semilattice condition at all
  P = derive-subset-galois.L-⊗-⋈-assoc rel-mfun-connected wd cl \ f g → (\where
    .forward {xz} (y , xy∈Lf , yz∈Lg) → \where
      .fst → rel-is-transitive _ {!!} (derive-subset-galois.Δ-lunit rel-mfun-connected wd)
      .snd → rel-is-transitive _ {!!} (derive-subset-galois.Δ-lunit rel-mfun-connected wd)
    .backward → {!!})
    where
      module rf-con X Y = galois-connection (rel-mfun-connected X Y)
      open rf-con
      module ×-cmlat X Y = complete-meet-semilattice (X ×-cmlat Y)
      open ×-cmlat
      module cmlat-pre X = preordered-set (cmlat→pre X)
      module tmp X = is-preorder (cmlat-pre.property X)
      open tmp
      wd : (X Y : complete-meet-semilattice)
             (r : transfer-function-pair.pre-mfun X Y .preordered-set.carrier) →
               is-welldefined-subset' X Y (left-adjoint X Y .monotone-func.func r)
      wd X Y (mono f f-mono) {d = xy} {d' = xy'} xy≈xy' .forward  xy∈Lf
        = left-adjoint X Y .monotone-func.property (\ _ → f-mono (xy≈xy' .backward .fst)) ({!!} , {!!})
      wd X Y (mono f f-mono) xy≈xy' .backward = {!!}
      cl : (X Y : complete-meet-semilattice)
             (r : transfer-function-pair.pre-mfun X Y .preordered-set.carrier) →
             {!!}
      cl = {!!}
-}
```

