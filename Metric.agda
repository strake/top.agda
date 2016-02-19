module Metric where

open import Agda.Primitive
open import Algebra.FunctionProperties.Core
open import Algebra.Structures
open import Data.Empty
open import Data.Product as Π
open import Data.Sum
open import Function using (_∘_; flip; id)
open import Relation.Binary
open import Relation.Unary

open import Top

record IsOrdMonoid {a ℓ} {A : Set a} (≈ ≤ : Rel A ℓ) (∙ : Op₂ A) (ε : A) : Set (a ⊔ ℓ) where
    field isMonoid      : IsMonoid ≈ ∙ ε
          isTotalOrder  : IsTotalOrder ≈ ≤
          ∙-preserves-≤ : ∙ Preserves₂ ≤ ⟶ ≤ ⟶ ≤

record OrdMonoid c ℓ : Set (lsuc (c ⊔ ℓ)) where
    infixl 7 _∙_
    infixl 4 _≤_
    infixl 4 _≈_
    field Carrier     : Set c
          _≈_         : Rel Carrier ℓ
          _≤_         : Rel Carrier ℓ
          _∙_         : Op₂ Carrier
          ε           : Carrier
          isOrdMonoid : IsOrdMonoid _≈_ _≤_ _∙_ ε

    open IsOrdMonoid isOrdMonoid public

record IsPseudometric {a m ℓ} {A : Set a} (M : OrdMonoid m ℓ) (d : A → A → OrdMonoid.Carrier M) : Set (a ⊔ m ⊔ ℓ) where
    open OrdMonoid M
    field nonNeg : {x y   : A} → ε ≤ d x y
          ident  : {x     : A} → ε ≈ d x x
          symm   : {x y   : A} → d x y ≈ d y x
          △      : {x y z : A} → d x z ≤ d x y ∙ d y z

record Pseudometric c m ℓ : Set (lsuc (c ⊔ m ⊔ ℓ)) where
    field Carrier : Set c
          Meter   : OrdMonoid m ℓ
          d       : Carrier → Carrier → OrdMonoid.Carrier Meter
          isPseudometric : IsPseudometric Meter d

    open IsPseudometric isPseudometric public
    open OrdMonoid Meter public hiding (Carrier)

data Extended {ℓ} (A : Set ℓ) : Set ℓ where
    ∞   : Extended A
    fin : A → Extended A

pseudometricTop :
    {c m ℓ : _} → (M : Pseudometric c m ℓ) →
    let open Pseudometric M
        Δ = OrdMonoid.Carrier Meter
    in (Σ (Op₂ Δ) λ min → {x y : Δ} → (min x y ≤ ε → x ≤ ε ⊎ y ≤ ε) × min x y ≤ x × min x y ≤ y) →
       Top Carrier
pseudometricTop {_} {m} {ℓ} M (min , minProp) = record
    { opens = λ u → {x : A} → x ∈ u → ∃ λ δ → (ε < δ) × (λ y → d x y < δ) ⊆ u;
      empty = ∅ , ∅-Empty     , ⊥-elim;
      full  = U , U-Universal , λ { tt → ∞ , δ<∞ , λ _ → tt };
      intersection = λ { u v u∈o v∈o (x∈u , x∈v) →
                             let δ = min' (proj₁ (u∈o x∈u)) (proj₁ (v∈o x∈v))
                             in δ , proj₁ minProp' ((proj₁ ∘ proj₂) (u∈o x∈u)) ((proj₁ ∘ proj₂) (v∈o x∈v)) ,
                                let a⊆u = (proj₂ ∘ proj₂) (u∈o x∈u)
                                    b⊆v = (proj₂ ∘ proj₂) (v∈o x∈v)
                                in λ dxy<δ → Π.map (a⊆u ∘ <-≤' dxy<δ) (b⊆v ∘ <-≤' dxy<δ) (proj₂ minProp') };
      union = λ { I a (i , x∈ai) → let δ' = proj₂ (a i) x∈ai
                                   in proj₁ δ' , (proj₁ ∘ proj₂) δ' , _,_ i ∘ (proj₂ ∘ proj₂) δ' } }
  where open Pseudometric M renaming (Carrier to A)
        open OrdMonoid Meter using () renaming (Carrier to Δ)

        transitive = IsTotalOrder.trans (OrdMonoid.isTotalOrder Meter)
        reflexive  = IsTotalOrder.refl  (OrdMonoid.isTotalOrder Meter)

        min' : Op₂ (Extended Δ)
        min' ∞ y = y
        min' x ∞ = x
        min' (fin x) (fin y) = fin (min x y)

        data _≤'_ : REL (Extended Δ) (Extended Δ) (m ⊔ ℓ) where
            ∞≤∞ : ∞ ≤' ∞
            f≤∞ : {x : Δ} → fin x ≤' ∞
            f≤f : {x y : Δ} → x ≤ y → fin x ≤' fin y

        data _<_ : REL Δ (Extended Δ) (m ⊔ ℓ) where
            δ<∞ : {x : _} → x < ∞
            δ<f : {x y : _} → (y ≤ x → ⊥) → x < fin y

        <-≤' : {x : _} {y' z' : _} → x < y' → y' ≤' z' → x < z'
        <-≤' δ<∞ ∞≤∞ = δ<∞
        <-≤' (δ<f _) f≤∞ = δ<∞
        <-≤' (δ<f y≤x→⊥) (f≤f y≤z) = δ<f (y≤x→⊥ ∘ transitive y≤z)

        minProp' : {x y : Extended Δ} → (ε < x → ε < y → ε < min' x y) × min' x y ≤' x × min' x y ≤' y
        minProp' {x'} {y'} with x' | y'
        ... | ∞ | ∞ = (λ _ _ → δ<∞) , ∞≤∞ , ∞≤∞
        ... | ∞ | fin y = (λ _ ε<y → ε<y) , f≤∞ , f≤f reflexive
        ... | fin x | ∞ = (λ ε<x _ → ε<x) , f≤f reflexive , f≤∞
        ... | fin x | fin y = (λ { (δ<f x≤ε→⊥) (δ<f y≤ε→⊥) → δ<f ([ x≤ε→⊥ , y≤ε→⊥ ] ∘ proj₁ minProp) }) , Π.map f≤f f≤f (proj₂ minProp)
