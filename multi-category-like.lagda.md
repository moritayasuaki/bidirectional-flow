```agda
{-# OPTIONS --type-in-type --exact-split #-}
open import Level
open import Data.Product renaming (proj₁ to fst; proj₂ to snd)
open import Data.Sum renaming (inj₁ to left; inj₂ to right)
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.List
open import Data.Vec
open import Data.Unit

module multi-category-like where


-- operad structure
module operad (C : Set) where
  -- domain of operad
  nary-prod : ℕ → Set
  nary-prod zero = ⊤
  nary-prod (suc n) = C × nary-prod n

  nary-hom : ℕ → Set
  nary-hom n = nary-prod n → C

  fsum : ∀{n : ℕ} → Vec ℕ n → ℕ
  fsum [] = ℕ.zero
  fsum (x ∷ k) = x + fsum k

  nary-comp : (n : ℕ) → Vec ℕ n → Set
  nary-comp n k = ((i : Fin n) → nary-hom (Data.Vec.lookup k i)) → nary-hom n → nary-hom (fsum k)

  data catalan : ℕ → Set where
    zero' : catalan 0
    one : catalan 1
    _∙_ : ∀ {n m} → catalan (ℕ.suc n) → catalan (ℕ.suc m) → catalan (ℕ.suc n + ℕ.suc m)

  nary-split : ∀ {n m} → nary-prod (n + m) → nary-prod n × nary-prod m
  nary-split {ℕ.zero} {m} x = tt , x
  nary-split {ℕ.suc n} {m} (c , cs) =
    let (cs' , cs'') = nary-split cs
    in (c , cs') , cs''

  module _ (I : C) (_⊗_ : C → C → C) where
    gen : (n : ℕ) → catalan n → nary-hom n
    gen ℕ.zero zero' tt = I
    gen (ℕ.suc .0) one (c , tt) = c
    gen .(ℕ.suc n + ℕ.suc m) (_∙_ {n} {m} t t') cs =
      let (cs' , cs'') = nary-split cs
      in (gen (ℕ.suc n) t cs') ⊗ (gen (ℕ.suc m) t' cs'')


-- hetro-operad
module hetero-operad (C : Set) where

  data complist (r : C) : C → Set where
    [] : complist r r
    _∷_ : (p : C × C) → complist r (snd p) → complist r (fst p)

  clist : C → C → Set
  clist l r = complist r l

  data compvec {r : C} (comp : C → C → Set) : {l : C} → clist l r → Set where
    [] : compvec comp []
    _∷_ : {ix-head : C × C} {ix-tail : clist (snd ix-head) r}
        → comp (fst ix-head) (snd ix-head) → compvec comp ix-tail → compvec comp (ix-head ∷ ix-tail)

  module _ (hom : C → C → Set) where
    nary-prod : ∀ {l r} → clist l r → Set
    nary-prod [] = ⊤
    nary-prod ((x , y) ∷ xs) = hom x y → nary-prod xs

    nary-hom : ∀ {l r} → clist l r → Set
    nary-hom {l} {r} ls = nary-prod ls → hom l r

open import predicate
open import preorder
open import complete-lattice
open import galois-connections

```
we have relation composition

⋈ : (𝓟(C × D),⊆) × (𝓟(D × E),⊆) → (𝓟(C × E),⊆)
which preserves meet-closed property but not butterfly condition.

We first think of n-ary relation composition operation indexed by lists of lattices Aᵢ.
big-⋈_{A₁A₂A₃...Aₙ} : 𝓟(A₁×A₂) → 𝓟(A₂×A₃) ... → 𝓟(Aₙ₋₁×Aₙ) → 𝒫(A×Z)
big-⋈_{A₁A₂A₃...Aₙ} r₁₂ r₂₃ ... rₙ₋₁ₙ = r₁₂ ⋈ r₂₃ ⋈ ... ⋈ rₙ₋₁ₙ


We derive corresponding n-ary composition operations on the following posets, from big-⋈ and adjunctions between the target poset and 𝒫(D × E):
- endofunctions ((D × E) → (D × E))
- bidirectional pairs of functions ((D → E) × (E → D))
- bidirectional pairs of functions with fb* ≤pair fb
- butterfly relations
- unidirectional functions (D → E)

big-⊗_{A₁A₂A₃...Aₙ} x₁₂ x₂₃ ... xₙ₋₁ₙ = G₁ₙ ((F₁₂ x₁₂) ⋈ (F₂₃ x₂₃) ⋈ ... ⋈ (Fₙ₋₁ₙ xₙ₋₁ₙ))
  where each pair (Gₙₘ , Fₙₘ) is the galois connection between 𝓟(Aₙ×Aₘ) and the target poset

```agda

module _
  (let lat = complete-meet-semilattice)
  (X : lat)
  (let X-pre = cmlat→pre X)
  (let X×X = X ×-cmlat X)
  (let (cmlat X-carrier _≤_ ⋀ X-is-cmlat) = X)
  (let (cmlat X×X-carrier _≤×_ ⋀× X×X-is-cmlat) = X×X)
  (let _≈_ = iso-pair _≤_)
  where

  open import compositions
  open operad
  open endo-function X×X
  open transfer-function-pair X X
  open import predicate
  open import preorder

  -- operad on binary relation
  ⋈ₙ-rel : ∀ {n} → nary-hom (preordered-set.carrier pre-rel) n
  ⋈ₙ-rel {ℕ.zero} _ (x , x') = x ≈ x' -- diagonal
  ⋈ₙ-rel {ℕ.suc n} (r , rs) = r ⋈ (⋈ₙ-rel rs) -- join

  module _ (P Q : preordered-set) (G : galois-connection P Q) (let (gal-conn l r lr-gal) = G) where
    nary-mapl : ∀{n} → nary-prod (preordered-set.carrier Q) n → nary-prod (preordered-set.carrier P) n
    nary-mapl {ℕ.zero} tt = tt
    nary-mapl {ℕ.suc n} (q , qs) = monotone-func.func l q , nary-mapl qs

    nary-mapr : ∀{n} → nary-prod (preordered-set.carrier P) n → nary-prod (preordered-set.carrier Q) n
    nary-mapr {ℕ.zero} tt = tt
    nary-mapr {ℕ.suc n} (p , ps) = monotone-func.func r p , nary-mapr ps

    nary-transposel : ∀{n} → nary-hom (preordered-set.carrier Q) n → nary-hom (preordered-set.carrier P) n
    nary-transposel f ps = monotone-func.func l (f (nary-mapr ps))

    nary-transposer : ∀{n} → nary-hom (preordered-set.carrier P) n → nary-hom (preordered-set.carrier Q) n
    nary-transposer g ps = monotone-func.func r (g (nary-mapl ps))

  ⋈ₙ-mendo : ∀ {n} → nary-hom (preordered-set.carrier pre-mendo) n
  ⋈ₙ-mendo {n} = nary-transposer _ _ (rel-mendo-connected X X) (⋈ₙ-rel {n})

  ⋈ₙ-mpair : ∀ {n} → nary-hom (preordered-set.carrier pre-mpair) n
  ⋈ₙ-mpair {n} = nary-transposer _ _ (rel-mpair-connected X X) (⋈ₙ-rel {n})

  ⋈ₙ-mfun : ∀ {n} → nary-hom (preordered-set.carrier pre-mfun) n
  ⋈ₙ-mfun {n} = nary-transposer _ _ (rel-mfun-connected X X) (⋈ₙ-rel {n})

  open import function-pair
  module _ (p q r : preordered-set.carrier pre-mpair)
    (let op2 = ⋈ₙ-mpair {2})
    (let op3 = ⋈ₙ-mpair {3})
    where

    thm2 = (op2 (p , op2 (q , r , _) , _)) ≤mpair (op3  (p , q , r , _))
    proof-thm2 : thm2
    fst proof-thm2 x0 = complete-meet-semilattice.property.bigmeet-monotone X (\ { {x'} (x , x0≤x , y , xy∈p , z , yz∈q , w , zw∈r , p) → x , x0≤x , y , xy∈p , z , (complete-meet-semilattice.property.bigmeet-lowerbound X _ _ (x , ({!!} , (z , ({!yz≤q!} , ({!!} , ({!!} , (record { forward = {!!} ; backward = {!!} }))))))) , {!!}) , record { forward = {!!} ; backward = {!!} } })
    snd proof-thm2 x0 = complete-meet-semilattice.property.bigmeet-monotone X (\ { {x'} (x , x0≤x , y , xy∈p , z , yz∈q , w , zw∈r , p) → x , x0≤x , y , xy∈p , z , ({!!} , {!!}) , {!!} })

{-
    test2 : Set
    test2 = ((op2 (p , op2 (q , r , _) , _)) ∩mpair ((op2 (op2 (p , q , _) , r , _)))) ≤mpair (op3 (p , q , r , _))
    test3 : test2
    test3 {x , y} (fx≤y , by≤x) = ({!fx≤y!} , {!!}) , ({!!} , {!!})
-}


```
