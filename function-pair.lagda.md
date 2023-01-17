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

module function-pair where
module _ (D E : Set) where
  func-pair : Set
  func-pair = (D → E) × (E → D)

  pair-app : func-pair → D × E → E × D
  pair-app fb de = fst fb (fst de) , snd fb (snd de)

module _ (D E : preordered-set)
  (let (pre D-carrier _≤D_ ≤D-pre) = D)
  (let (pre E-carrier _≤E_ ≤E-pre) = E) where
  is-monotone-pair : pred (func-pair D-carrier E-carrier)
  is-monotone-pair fb = is-monotone ≤D-pre ≤E-pre (fst fb) × is-monotone ≤E-pre ≤D-pre (snd fb)

  record monotone-func-pair : Set where
    constructor mfp'
    field
      pair : func-pair D-carrier E-carrier
      pair-is-monotone : is-monotone-pair pair

module _ {D-cmlat E-cmlat : complete-meet-semilattice}
  (let (cmlat D _≤D_ ⋀D D-is-cmlat) = D-cmlat)
  (let (cmlat E _≤E_ ⋀E E-is-cmlat) = E-cmlat)
  (let D-pre = cmlat→pre D-cmlat)
  (let E-pre = cmlat→pre E-cmlat)
  (let D×E-cmlat = D-cmlat ×-cmlat E-cmlat)
  (let D×E-is-cmlat = complete-meet-semilattice.property D×E-cmlat)
  where

  private
    module D = is-complete-meet-semilattice D-is-cmlat renaming (rel-is-preorder to ≤-pre ; rel-is-reflexive to ≤-refl ; rel-is-transitive to ≤-trans)
    module E = is-complete-meet-semilattice E-is-cmlat renaming (rel-is-preorder to ≤-pre ; rel-is-reflexive to ≤-refl ; rel-is-transitive to ≤-trans)

  open complete-meet-semilattice D×E-cmlat renaming (operation to ⋀ ; relation to _≤_)
  open is-complete-meet-semilattice D×E-is-cmlat renaming (rel-is-preorder to ≤-pre ; rel-is-reflexive to ≤-refl ; rel-is-transitive to ≤-trans)

  open _×rel_ _≤D_ _≤E_ renaming (_≈₁_ to _≈D_ ; _≈₂_ to _≈E_)

  -- d₀≤d → fd≤e → fd₀≤e
  mono-≤ : {f : D → E} (f-mono : is-monotone D.≤-pre E.≤-pre f) → ∀ {d e d₀} → d₀ ≤D d → f d ≤E e → f d₀ ≤E e
  mono-≤ {f} f-mono {d} {e} {d₀} d≤d₀ fd≤e =
    begin-≤
    f d₀ ≤⟨ f-mono d≤d₀ ⟩
    f d ≤⟨ fd≤e ⟩
    e ∎
    where
      open reasoning _  E.≤-pre

  -- f (⋀S) ≤ ⋀ (f S)
  mono-meet≤meet-mono : {f : D → E} (f-mono : is-monotone D.≤-pre E.≤-pre f) → (S : subset D) → f (⋀D S) ≤E ⋀E (fimage f S)
  mono-meet≤meet-mono {f} f-mono S =
    begin-≤
    f (⋀D S) ≤⟨ E.bigmeet-greatest _ _ (\ {e (d , d∈S , fd≡e) →  ≡.subst (f (⋀D S) ≤E_) fd≡e (f-mono (D.bigmeet-lowerbound S d d∈S)) }) ⟩
    ⋀E (fimage f S) ∎
    where
      open reasoning _  E.≤-pre

  module _ (f : D → E) (b : E → D) where

    -- f d ≤ e × b e ≤ d ↔ b (f d) ≤ d
    mono-pair-backforward : (b-mono : is-monotone E.≤-pre D.≤-pre b) → ∀ d → (Σ[ e ∈ E ] (f d ≤E e) × (b e ≤D d)) ↔ (b (f d) ≤D d)
    forward (mono-pair-backforward b-mono d) (e , fd≤e , be≤d) =
      begin-≤
      b (f d) ≤⟨ b-mono fd≤e ⟩
      b e ≤⟨ be≤d ⟩
      d ∎
      where
        open reasoning _ D.≤-pre
    backward (mono-pair-backforward _ d) bfd≤d = f d , E.≤-refl (f d) , bfd≤d

    -- f d ≤ e × b e ≤ d ↔ f (b e) ≤ e
    mono-pair-forwardback : (f-mono : is-monotone D.≤-pre E.≤-pre f) → ∀ e → (Σ[ d ∈ D ] (f d ≤E e) × (b e ≤D d)) ↔ (f (b e) ≤E e)
    forward (mono-pair-forwardback f-mono e) (d , fd≤e , be≤d) =
      begin-≤
      f (b e) ≤⟨ f-mono be≤d ⟩
      f d ≤⟨ fd≤e ⟩
      e ∎
      where
        open reasoning _ E.≤-pre
    backward (mono-pair-forwardback _ e) fbe≤e = b e , fbe≤e , D.≤-refl (b e)

```
