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
open import complete-lattice
open import preorder
open import galois-connections
open import function-pair

module compositions where

record preorder-enriched-cat : Set where
  field
    Ob : Set
    Hom : Ob → Ob → Set
    I : ∀{X} → Hom X X
    _⊗_ : ∀{X Y Z} → Hom X Y → Hom Y Z → Hom X Z
    _≤_ : ∀{X Y} → rel (Hom X Y) (Hom X Y)

  _≈_ : ∀{X Y} → rel (Hom X Y) (Hom X Y)
  _≈_ = iso-pair _≤_

  field
    Hom-is-preorder : ∀{X Y} → is-preorder (_≤_ {X} {Y})
    assoc : {X Y Z W : Ob} {a : Hom X Y} {b : Hom Y Z} {c : Hom Z W} → ((a ⊗ b) ⊗ c) ≈ (a ⊗ (b ⊗ c))
    lunit : {X Y : Ob} {a : Hom X Y} → (I ⊗ a) ≈ a
    runit : {X Y : Ob} {a : Hom X Y} → (a ⊗ I) ≈ a



module _ where
  open preorder-enriched-cat
  open monotone-func
  open complete-meet-semilattice
  open endo-function
  open transfer-function-pair

  module _ (X Y : complete-meet-semilattice)
    (let X-pre = cmlat→pre X)
    (let Y-pre = cmlat→pre Y)
    (let (cmlat X-carrier _≤X_ ⋀X X-prop) = X)
    (let (cmlat Y-carrier _≤Y_ ⋀Y Y-prop) = Y)
    (let X×Y = X ×-cmlat Y)
    (let (cmlat XY _≤XY_ ⋀XY XY-prop) = X×Y)
    (let XY-pre = cmlat→pre (X ×-cmlat Y))
    (let _≈XY_ = iso-pair _≤XY_)
    (let _≈X_ = iso-pair _≤X_)
    (let _≈Y_ = iso-pair _≤Y_)
    where

    ~pair : subset (X-carrier × Y-carrier) → subset (X-carrier × Y-carrier)
    ~pair r = pair2rel X Y (rel2pair X Y r)

    ~f : subset (X-carrier × Y-carrier) → subset (X-carrier × Y-carrier)
    ~f r = fun2rel X Y (rel2fun X Y r)

    _∨f_ : fun X-carrier Y-carrier → fun X-carrier Y-carrier → fun X-carrier Y-carrier
    f ∨f g = rel2fun X Y (fun2rel X Y f ∩ fun2rel X Y g)

    _∧f_ : fun X-carrier Y-carrier → fun X-carrier Y-carrier → fun X-carrier Y-carrier
    f ∧f g = rel2fun X Y (fun2rel X Y f ∪ fun2rel X Y g)

    _∨p_ : func-pair X-carrier Y-carrier → func-pair X-carrier Y-carrier → func-pair X-carrier Y-carrier
    f ∨p g = rel2pair X Y (pair2rel X Y f ∩ pair2rel X Y g)

    _∧p_ : func-pair X-carrier Y-carrier → func-pair X-carrier Y-carrier → func-pair X-carrier Y-carrier
    f ∧p g = rel2pair X Y (pair2rel X Y f ∪ pair2rel X Y g)

  module _ (X Y Z : complete-meet-semilattice)
    (let X-pre = cmlat→pre X)
    (let Y-pre = cmlat→pre Y)
    (let Z-pre = cmlat→pre Z)
    (let (cmlat X-carrier _≤X_ ⋀X X-prop) = X)
    (let (cmlat Y-carrier _≤Y_ ⋀Y Y-prop) = Y)
    (let (cmlat Z-carrier _≤Z_ ⋀Z Z-prop) = Z)
    (let X×Z = X ×-cmlat Z)
    (let X×Y = X ×-cmlat Y)
    (let Y×Z = Y ×-cmlat Z)
    (let X×Y×Z = X ×-cmlat (Y ×-cmlat Z))
    (let (cmlat XYZ _≤XYZ_ ⋀XYZ XYZ-prop) = X×Y×Z)
    (let (cmlat XZ _≤XZ_ ⋀XZ XZ-prop) = X×Z)
    (let (cmlat XY _≤XY_ ⋀XY XY-prop) = X×Y)
    (let (cmlat YZ _≤YZ_ ⋀YZ YZ-prop) = Y×Z)
    (let XZ-pre = cmlat→pre (X ×-cmlat Z))
    (let XY-pre = cmlat→pre (X ×-cmlat Y))
    (let YZ-pre = cmlat→pre (Y ×-cmlat Z))
    (let _≈XZ_ = iso-pair _≤XZ_)
    (let _≈XY_ = iso-pair _≤XY_)
    (let _≈YZ_ = iso-pair _≤YZ_)
    (let _≈X_ = iso-pair _≤X_)
    (let _≈Y_ = iso-pair _≤Y_)
    (let _≈Z_ = iso-pair _≤Z_)
    where

    module latprop (C : complete-meet-semilattice) where
      open complete-meet-semilattice.property C public

    module preprop (P : preordered-set) where
      open preordered-set.property P public


    mendo-comp : monotone-func XY-pre XY-pre → monotone-func YZ-pre YZ-pre → monotone-func XZ-pre XZ-pre
    func (mendo-comp f g) (x , z) = ⋀XZ \{ (x' , z') → (x , z) ≤XZ (x' , z') × ∃ \ y' → f .func (x' , y') ≤XY (x' , y') × g .func (y' , z') ≤YZ (y' , z')  }
    property (mendo-comp f g) {xz} {x'z'} (xz≤x'z') = latprop.bigmeet-monotone X×Z \{ {(x''z'')} ((x'z'≤x''z'') , Ey') → XZ-trans xz≤x'z' x'z'≤x''z'' , Ey'}
      where XZ-trans = preprop.rel-is-transitive XZ-pre
            XY-trans = preprop.rel-is-transitive XY-pre
            YZ-trans = preprop.rel-is-transitive YZ-pre

    rel2mendo∘⋈∘mendo2rel≈mendo-comp : (f : monotone-func XY-pre XY-pre) → (g : monotone-func YZ-pre YZ-pre)
      → ∀ xz → func (rel2mendo X×Z ((mendo2rel X×Y f) ⋈ (mendo2rel Y×Z g))) xz ≈XZ func (mendo-comp f g) xz
    forward (rel2mendo∘⋈∘mendo2rel≈mendo-comp f g (x , z)) = latprop.bigmeet-monotone X×Z id
    backward (rel2mendo∘⋈∘mendo2rel≈mendo-comp f g (x , z)) = latprop.bigmeet-monotone X×Z id

    _⋈p_ : subset (X-carrier × Y-carrier) → subset (Y-carrier × Z-carrier) → subset (X-carrier × Z-carrier)
    r ⋈p r' = pair2rel X Z (rel2pair X Z (r ⋈ r'))

    _⊗p_ : func-pair X-carrier Y-carrier → func-pair Y-carrier Z-carrier → func-pair X-carrier Z-carrier
    f ⊗p g = rel2pair X Z (pair2rel X Y f ⋈ pair2rel Y Z g)

    _⊗p'_ : func-pair X-carrier Y-carrier → func-pair Y-carrier Z-carrier → func-pair X-carrier Z-carrier
    (f , b) ⊗p' (f' , b') = \where
      .fst x → ⋀Z \{ z → ∃ \ x' → x ≤X x' × ∃ \ y → (f x' ≤Y y × b y ≤X x') × (f' y ≤Z z × b' z ≤Y y) }
      .snd z → ⋀X \{ x → ∃ \ z' → z ≤Z z' × ∃ \ y → (f x ≤Y y × b y ≤X x) × (f' y ≤Z z' × b' z' ≤Y y) }

    ⊗p≈⊗p' : (f : func-pair X-carrier Y-carrier) → (g : func-pair Y-carrier Z-carrier)
      → (∀ x → fst (f ⊗p' g) x ≈Z fst (f ⊗p g) x)
      → (∀ z → snd (f ⊗p' g) z ≈X snd (f ⊗p g) z)
    forward (⊗p≈⊗p' f g x z) = latprop.bigmeet-monotone X id
    backward (⊗p≈⊗p' f g x z) = latprop.bigmeet-monotone X id

    _⊗mp_ : monotone-func-pair X-pre Y-pre → monotone-func-pair Y-pre Z-pre → monotone-func-pair X-pre Z-pre
    monotone-func-pair.pair (mfp' fb fb-mono ⊗mp mfp' fb' fb'-mono) = fb ⊗p' fb'
    fst (monotone-func-pair.pair-is-monotone (mfp' fb fb-mono ⊗mp mfp' fb' fb'-mono)) {x} {x'} x≤x' = latprop.bigmeet-monotone Z \{ (_ , x'≤x'' , P) → (_ , trans X-pre x≤x' x'≤x'' , P)}
        where trans = preprop.rel-is-transitive
    snd (monotone-func-pair.pair-is-monotone (mfp' fb fb-mono ⊗mp mfp' fb' fb'-mono)) {z} {z'} z≤z' = latprop.bigmeet-monotone X \{ (_ , z'≤z'' , P) → (_ , trans Z-pre z≤z' z'≤z'' , P) }
        where trans = preprop.rel-is-transitive

    pair2rel-⊗-monoidal-strength-⊇ : ∀ f g → mpair2rel X Y f ⋈ mpair2rel Y Z g ⊆ (mpair2rel X Z (f ⊗mp g))
    pair2rel-⊗-monoidal-strength-⊇ (mfp' (f , b) (f-mono , b-mono)) (mfp' (f' , b') (f'-mono , b'-mono)) {x , z} (y , xy∈p2r[f] , yz∈p2r[g]) .fst
      = latprop.bigmeet-lowerbound Z _ _ (x , refl X-pre _ , y , xy∈p2r[f] , yz∈p2r[g])
        where refl = preprop.rel-is-reflexive
    pair2rel-⊗-monoidal-strength-⊇ (mfp' (f , b) (f-mono , b-mono)) (mfp' (f' , b') (f'-mono , b'-mono)) {x , z} (y , xy∈p2r[f] , yz∈p2r[g]) .snd
      = latprop.bigmeet-lowerbound X _ _ (z , refl Z-pre _ , y , xy∈p2r[f] , yz∈p2r[g])
        where refl = preprop.rel-is-reflexive

    pair2rel-⊗-monoidal-strength-⊆ : ∀ f g → mpair2rel X Z (f ⊗mp g) ⊆ mpair2rel X Y f ⋈ mpair2rel Y Z g
    pair2rel-⊗-monoidal-strength-⊆ (mfp' (f , b) (f-mono , b-mono)) (mfp' (f' , b') (f'-mono , b'-mono)) {x , z} (fst⊗≤z , snd⊗≤x)
      = ⋀Y s , \where
        .fst .fst → latprop.bigmeet-greatest Y _ _ (\{ y (fx≤y , b'z≤y , _) → fx≤y})
        .fst .snd → trans X-pre {y = ⋀X (fimage b s)} (mono-meet≤meet-mono b-mono s)
          (trans X-pre
            (latprop.bigmeet-monotone X (\{ {x'} (z' , z≤z' , y , (fx'≤y , by≤x') , (f'y≤z' , b'z'≤y)) → (⋀Y \y' → f x ≤Y y' × b' z ≤Y y') , ((latprop.bigmeet-greatest Y  _ _ (\ _ → fst) , latprop.bigmeet-greatest Y _ _ (\ y' → (\{(fx≤y' , b'z≤y') → trans Y-pre (b'-mono z≤z') (trans Y-pre {!!}  b'z≤y')})) , {!!}) , {!!})}))
            snd⊗≤x)
-- (trans X-pre {y = ⋀X (fimage b s)} (mono-meet≤meet-mono b-mono s) (latprop.bigmeet-monotone X (\ { {x'} (_ , _ , z≤z' , P)  → f x' , ({!!} , ({!!} , {!!})) , {!!}})))
        .snd → ({!!} , {!!})
      where refl = preprop.rel-is-reflexive
            trans = preprop.rel-is-transitive
            py : pred Y-carrier
            py = {!!}
            s = \ y → f x ≤Y y × b' z ≤Y y × py y

    _⊗p-fix_ : func-pair X-carrier Y-carrier → func-pair Y-carrier Z-carrier → func-pair X-carrier Z-carrier
    (f , b) ⊗p-fix (f' , b') = \where
       .fst x₀ →  (⋀XYZ \ xyz → xyz ≤XYZ (h x₀ ⊥Z) xyz) .snd .snd
       .snd z₀ → (⋀XYZ \ xyz → xyz ≤XYZ (h ⊥X z₀) xyz) .fst
      where
        open derive-∧⋁∨⊤⊥ _≤X_ ⋀X renaming (_∨_ to _∨X_; ⊥ to ⊥X)
        open derive-∧⋁∨⊤⊥ _≤Y_ ⋀Y renaming (_∨_ to _∨Y_; ⊥ to ⊥Y)
        open derive-∧⋁∨⊤⊥ _≤Z_ ⋀Z renaming (_∨_ to _∨Z_; ⊥ to ⊥Z)

        h : X-carrier → Z-carrier → X-carrier × Y-carrier × Z-carrier → X-carrier × Y-carrier × Z-carrier
        h x₀ z₀ (x , y , z) = (x₀ ∨X b y , f x ∨Y b' z , z₀ ∨Z f' y)

    _⊗f_ : fun X-carrier Y-carrier → fun Y-carrier Z-carrier → fun X-carrier Z-carrier
    f ⊗f g = rel2fun X Z (fun2rel X Y f ⋈ fun2rel Y Z g)

    _⊗f'_ : fun X-carrier Y-carrier → fun Y-carrier Z-carrier → fun X-carrier Z-carrier
    (f ⊗f' g) x = ⋀Z (\z → ∃ \ x' → x ≤X x' × ∃ \y → (f x' ≤Y y) × (g y ≤Z z))


    _⊗f-fix_ : fun X-carrier Y-carrier → fun Y-carrier Z-carrier → fun X-carrier Z-carrier
    (f ⊗f-fix g) x = (⋀XYZ (\xyz → xyz ≤XYZ h x xyz)) .snd .snd
      where
        open derive-∧⋁∨⊤⊥ _≤X_ ⋀X renaming (_∨_ to _∨X_; ⊥ to ⊥X)
        open derive-∧⋁∨⊤⊥ _≤Y_ ⋀Y renaming (_∨_ to _∨Y_; ⊥ to ⊥Y)
        open derive-∧⋁∨⊤⊥ _≤Z_ ⋀Z renaming (_∨_ to _∨Z_; ⊥ to ⊥Z)
        h : X-carrier → X-carrier × Y-carrier × Z-carrier → X-carrier × Y-carrier × Z-carrier
        h x₀ (x , y , z) = (x₀ , f x , g y)

    ⊗f-fix≈⊗f : (f : fun X-carrier Y-carrier) → (g : fun Y-carrier Z-carrier) → ∀ x → (f ⊗f-fix g) x ≈Z (f ⊗f' g) x
    ⊗f-fix≈⊗f f g x .forward = {!!}
    ⊗f-fix≈⊗f f g x .backward = {!!}

    ⊗f≈⊗f' : (f : fun X-carrier Y-carrier) → (g : fun Y-carrier Z-carrier) → ∀ x → (f ⊗f g) x ≈Z (f ⊗f' g) x
    forward (⊗f≈⊗f' f g x) = latprop.bigmeet-monotone Z \where
      (x' , x≤x' , y , fx'≤y , gy≤z) → x' , x≤x' , y , (fx'≤y , (latprop.bigmeet-lowerbound X _ _ _)) , gy≤z , (latprop.bigmeet-lowerbound Y _ _ _)
    backward (⊗f≈⊗f' f g x) = latprop.bigmeet-monotone Z \where
      (x' , x≤x' , y , (fx'≤y , _) , (gy≤z , _)) → x' , x≤x' , y , fx'≤y , gy≤z

    -- (⋀XY (λ y → relation Y (f x) y × relation Z (g y) z))
    _⊗mf'_ : monotone-func X-pre Y-pre → monotone-func Y-pre Z-pre → monotone-func X-pre Z-pre
    mono f f-mono ⊗mf' mono g g-mono = mono (f ⊗f' g) \ {x} {x'} x≤x' → latprop.bigmeet-monotone Z \{ {z} (x'' , x'≤x'' , y , fx''≤y , gy≤z) → x'' , (preprop.rel-is-transitive X-pre x≤x' x'≤x'' , y , (fx''≤y , gy≤z))}

    mfun2rel-⊗-monoidal-strength : ∀ f g → (mfun2rel' X Z (f ⊗mf' g)) ≅ mfun2rel' X Y f ⋈ mfun2rel' Y Z g
    forward (mfun2rel-⊗-monoidal-strength (mono f f-mono) (mono g g-mono)) {x , z} xz∈f2r[f⊗g] = (⋀Y \ y → f x ≤Y y × g y ≤Z z) ,
      latprop.bigmeet-greatest Y _ _ (\ y (fx≤y , gy≤z) → fx≤y) , (_∙_ {y = ⋀Z (fimage g (\{ y → f x ≤Y y × g y ≤Z z}))} (mono-meet≤meet-mono {D-cmlat = Y} {E-cmlat = Z} {f = g} g-mono (\{ y → f x ≤Y y × g y ≤Z z})) (latprop.bigmeet-≡-≤ Z _ _ .forward ∙ latprop.bigmeet-lowerbound Z _ _ ((f x) , (((preprop.rel-is-reflexive Y-pre _) , gfx≤z ) , gfx≤z))))
      -- (mono-meet≤meet-mono f-mono (\{ y → f x ≤Y y × g y ≤Z z}) ∙ {!!})
      where _∙_ = preprop.rel-is-transitive Z-pre
            gfx≤z : g (f x) ≤Z z
            gfx≤z = latprop.bigmeet-greatest Z _ _ (\{ z' (x' , x≤x' , y' , fx'≤y' , gy≤z') → g-mono (f-mono x≤x') ∙ (g-mono fx'≤y' ∙ gy≤z')})  ∙ xz∈f2r[f⊗g]
    backward (mfun2rel-⊗-monoidal-strength f g) {x , z} (y , xy∈Lf , yz∈Lg) = latprop.bigmeet-lowerbound Z _ _ (x , ((preprop.rel-is-reflexive X-pre _) , (y , (xy∈Lf , yz∈Lg))))

    module _ (mf : monotone-func X-pre Y-pre) (mg : monotone-func Y-pre Z-pre)
      (let (mono f f-mono) = mf) (let (mono g g-mono) = mg)
      (let _∙_ = preprop.rel-is-transitive Z-pre)
      (let refl = preprop.rel-is-reflexive)
      where
      ∘-⋀ : ∀ x → ⋀Z (\ z → g (f x) ≤Z z) ≈Z g (f x)
      forward (∘-⋀ x) = latprop.bigmeet-lowerbound Z _ _ (refl Z-pre _)
      backward (∘-⋀ x) = latprop.bigmeet-greatest Z _ _ \where
        z z∈gfx → z∈gfx

      -- ⊗fun is the same as ordinal function composition
      ⊗f'≈∘ : ∀ x → (f ⊗f' g) x ≈Z g (f x)
      forward (⊗f'≈∘ x) =  latprop.bigmeet-lowerbound Z _ _
        (x , preprop.rel-is-reflexive X-pre _ , f x , refl Y-pre _ , refl Z-pre _)
      backward (⊗f'≈∘ x) = latprop.bigmeet-greatest Z _ _ \where

        z (x' , x≤x' , y , fx≤y , gy≤z) → g-mono (f-mono x≤x') ∙ (g-mono fx≤y ∙ gy≤z)

      ⊗f≈∘ : ∀ x → (f ⊗f g) x ≈Z (g ∘ f) x
      forward (⊗f≈∘ x) = forward (⊗f≈⊗f' f g x) ∙ forward (⊗f'≈∘ x)
      backward (⊗f≈∘ x) = backward (⊗f'≈∘ x) ∙ backward (⊗f≈⊗f' f g x)

    module _
      (let refl = preprop.rel-is-reflexive)
      (let _∙_ = preprop.rel-is-transitive X-pre)
      (r : subset (X-carrier × Y-carrier))
      (r' : subset (Y-carrier × Z-carrier))
      (r-meetclosed : complete-lattice.is-meet-closed-subset XY-prop r)
      (r'-meetclosed : complete-lattice.is-meet-closed-subset YZ-prop r')
      where

      ~f-⋈-commute : (~f X Y r ⋈ ~f Y Z r') ≅ ~f X Z (r ⋈ r')
      forward ~f-⋈-commute {x , z} (y , xy∈~r , yz∈~r' ) = \where
        .fst → latprop.bigmeet-lowerbound Z _ _ (x , refl X-pre _ , ((⋀Y \y → r (x , y) × r' (y , z))) , {!!} , {!!})
        .snd → latprop.bigmeet-lowerbound X _ _ _
      backward ~f-⋈-commute {x , z} (≤z , ≤x) = (⋀Y \y → r (x , y) × r' (y , z)) , \where
        .fst .fst → latprop.bigmeet-greatest Y _ _ \ y y∈xrr'z → latprop.bigmeet-lowerbound Y _ _ (x , (refl X-pre _ , y∈xrr'z .fst))
        .fst .snd → latprop.bigmeet-lowerbound X _ _ _
        .snd .fst → latprop.bigmeet-lowerbound Z _ _ ((⋀XYZ \{ (x , y , z) → (x , y) ∈ r × (y , z) ∈ r'}) .snd .fst , {!!} , {!!})
        .snd .snd → latprop.bigmeet-greatest Y _ _ \ y y∈xrr'z → latprop.bigmeet-lowerbound Y _ _ _

  module _ (X Y : complete-meet-semilattice)
    (let X-pre = cmlat→pre X)
    (let Y-pre = cmlat→pre Y)
    (let (cmlat X-carrier _≤X_ ⋀X X-prop) = X)
    (let (cmlat Y-carrier _≤Y_ ⋀Y Y-prop) = Y)
    (let _≈X_ = iso-pair _≤X_)
    (let _≈Y_ = iso-pair _≤Y_)
    (mf : monotone-func X-pre Y-pre)
    (let (mono f f-mono) = mf)
    (let _∙_ = preprop.rel-is-transitive Y)
    (let refl = preprop.rel-is-reflexive) where
    ⊗fun-unitl : ∀ x → ( _⊗f_ X X Y id f) x ≈Y f x
    ⊗fun-unitl x = ⊗f≈∘ X X Y (mono id id) mf x

    ⊗fun-unitr : ∀ x → ( _⊗f_ X Y Y f id) x ≈Y f x
    ⊗fun-unitr x = ⊗f≈∘ X Y Y mf (mono id id) x

  module _ (X : complete-meet-semilattice)
    (let X-pre = cmlat→pre X)
    (let (cmlat X-carrier _≤X_ ⋀X X-prop) = X)
    (let X×X = X ×-cmlat X)
    (let X×[X×X] = X ×-cmlat X×X)
    (let [X×X]×X = X×X ×-cmlat X)
    (let XX-pre = cmlat→pre X×X)
    (let [X×X]×X-pre = cmlat→pre [X×X]×X)
    (let X×[X×X]-pre = cmlat→pre X×[X×X])
    (let _≈X_ = iso-pair _≤X_)
    where


  module _
    (pre-hom : (X Y : complete-meet-semilattice) → preordered-set)
    (gal : (X Y : complete-meet-semilattice) → antitone-galois-connection (pre-subset (X ×-cmlat Y)) (pre-hom X Y))
    (let L∘R = \(X Y : complete-meet-semilattice) → galois-connection.comonad-functor (gal X Y))
    where

    module _
      (X Y Z : complete-meet-semilattice)
      (let X-pre = cmlat→pre X)
      (let Y-pre = cmlat→pre Y)
      (let Z-pre = cmlat→pre Z)
      (let (cmlat X-carrier _≤X_ ⋀X X-prop) = X)
      (let (cmlat Y-carrier _≤Y_ ⋀Y Y-prop) = Y)
      (let (cmlat Z-carrier _≤Z_ ⋀Z Z-prop) = Z)
      (let X×Z = X ×-cmlat Z)
      (let X×Y = X ×-cmlat Y)
      (let Y×Z = Y ×-cmlat Z)
      (let (cmlat XZ _≤XZ_ ⋀XZ XZ-prop) = X×Z)
      (let (cmlat XY _≤XY_ ⋀XY XY-prop) = X×Y)
      (let (cmlat YZ _≤YZ_ ⋀YZ YZ-prop) = Y×Z)
      (let XZ-pre = cmlat→pre (X ×-cmlat Z))
      (let XY-pre = cmlat→pre (X ×-cmlat Y))
      (let YZ-pre = cmlat→pre (Y ×-cmlat Z))
      (let _≈XZ_ = iso-pair _≤XZ_)
      (let _≈XY_ = iso-pair _≤XY_)
      (let _≈YZ_ = iso-pair _≤YZ_)
      (let _≈X_ = iso-pair _≤X_)
      (let _≈Y_ = iso-pair _≤Y_)
      (let _≈Z_ = iso-pair _≤Z_)
      where

      -- some references: https://ncatlab.org/nlab/show/adjoint+monad
      --  General adjoint algebras and coalgebras in End(A)
      -- https://ncatlab.org/nlab/show/lax+monoidal+category
      -- this must be obtained by galois connectionh
      -- lax monoidal functor does not mean functor on lax monoidal category
      -- multi functor lax monoidal category
      -- unbiased oplax monoidal category
      -- We have unbiased version
      functor-on-unbiased-oplax-monoidal-categories = ∀ r r' → monotone-func.func (L∘R X Z) (r ⋈ r') ⊆ monotone-func.func (L∘R X Y) r ⋈ monotone-func.func (L∘R Y Z) r'
      {-
      proof-⋈-unbiased-oplax-monoidal-category-preserving : ⋈-unbiased-oplax-monoidal-category-preserving
      proof-⋈-unbiased-oplax-monoidal-category-preserving r r' {x , z} join-first = ⋀Y (\y → r (x , y) × r' (y , z)) , \where
        .fst → {!!}
        .snd → {!!}
      -}

      functor-on-unbiased-normal-monoidal-categories = ∀ r r' → monotone-func.func (L∘R X Y) r ⋈ monotone-func.func (L∘R Y Z) r' ≅ monotone-func.func (L∘R X Z) (r ⋈ r')


      -- we still have other operations on relations, intersection and union.
      -- ⊗(⊗(x , y) , z) ≤ ⊗(x , y , z)
      -- ⊗(x , ⊗(y , z)) ≤ ⊗(x , y , z)
      -- ((x ⋈ y) ⋈ z) ∩ (x ⋈ (y ⋈ z)) ??


  cat-rel : preorder-enriched-cat
  Ob cat-rel = complete-meet-semilattice
  Hom cat-rel D E = preordered-set.carrier (pre-rel D E)
  I cat-rel {X} (x , x') = x ≡ x' -- maybe we should do x ≈ x' and relation to be well-defined
    where _~_ = iso-pair (complete-meet-semilattice.relation X)
  _⊗_ cat-rel = _⋈_
  _≤_ cat-rel = _⊆_
  Hom-is-preorder cat-rel = ⊆-is-preorder
  forward (assoc cat-rel) (z , (y , p , q) , r) = y , p , z , q , r
  backward (assoc cat-rel) (y , p , z , q , r) = z , (y , p , q) , r
  iso-pair.forward (lunit cat-rel) (x , ≡.refl , y) = y
  backward (lunit cat-rel) x =  _ , ≡.refl , x
  forward (runit cat-rel) (x , y , ≡.refl) = y
  backward (runit cat-rel) x = _ , x , ≡.refl

  cat-mfun : preorder-enriched-cat
  Ob cat-mfun = complete-meet-semilattice
  Hom cat-mfun D E = preordered-set.carrier (pre-mfun D E)
  I cat-mfun {X} = mono id id
  _⊗_ cat-mfun f g = pre-comp g f
  _≤_ cat-mfun {X} {Y} f g = _≤mfun_ X Y f g
  Hom-is-preorder cat-mfun {X} {Y} = ≤mfun-is-preorder X Y
  forward (assoc cat-mfun {W = W} {a} {b} {c}) x = W .property.rel-is-reflexive (c .func (b .func (a .func x)))
  backward (assoc cat-mfun {W = W} {a} {b} {c}) x = W .property.rel-is-reflexive (c .func (b .func (a .func x)))
  forward (lunit cat-mfun {Y = Y} {a}) x = Y .property.rel-is-reflexive (a .func x)
  backward (lunit cat-mfun {Y = Y} {a}) x = Y .property.rel-is-reflexive (a .func x)
  forward (runit cat-mfun {Y = Y} {a}) x = Y .property.rel-is-reflexive (a .func x)
  backward (runit cat-mfun {Y = Y} {a}) x = Y .property.rel-is-reflexive (a .func x)


{-
  cat-mendo : preorder-enriched-cat
  Ob cat-mendo = complete-meet-semilattice
  Hom cat-mendo D E = preordered-set.carrier (pre-mendo (D ×-cmlat E))
  I cat-mendo = mono id id
  _⊗_ cat-mendo {X} {Y} {Z} f g = mendo-comp X Y Z f g
  _≤_ cat-mendo {X} {Y} f g = _≤mfun_ (X ×-cmlat Y) (X ×-cmlat Y) f g
  Hom-is-preorder cat-mendo {X} {Y} = ≤mfun-is-preorder (X ×-cmlat Y) (X ×-cmlat Y)
  cat-mendo .assoc = {!!}
  cat-mendo .lunit = {!!}
  cat-mendo .runit = {!!}
-}
```
P = derive-subset-galois.L-⊗-⋈-assoc {! !} {!!} {!!} {!!}
