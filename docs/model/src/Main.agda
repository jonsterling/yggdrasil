module Main where

open import Agda.Primitive
open import Prelude.Bool
open import Prelude.Decidable
open import Prelude.Inspect
open import Prelude.Maybe
open import Prelude.Monoidal
  renaming (_⊗_ to _×_)
open import Prelude.Natural
open import Prelude.Path
open import Prelude.Size
open import Prelude.String

infix 2 _⊸_
infix 0 _▸_⊩_⇒_
infix 0 _▸_⊩_⇐_⟖_
infix 0 _▸_⊢_⇒_
infixl 5 _⊛_
infixl 5 _⊗_

data List (A : Set) : Set where
  ε : List A
  _⊗_ : (xs : List A) (x : A) → List A

_⊛_
  : {A : Set}
  → List A
  → List A
  → List A
xs ⊛ ε = xs
xs ⊛ (ys ⊗ y) = (xs ⊛ ys) ⊗ y

list-eq
  : {A : Set}
  → (δ : (a a′ : A) → Decidable (a ≡ a′))
  → (xs₀ xs₁ : List A)
  → Decidable (xs₀ ≡ xs₁)
list-eq _≟_ ε ε = ⊕.inr refl
list-eq _≟_ ε (_ ⊗ _) = ⊕.inl λ()
list-eq _≟_ (xs₀ ⊗ x₀) ε = ⊕.inl λ()
list-eq _≟_ (xs₀ ⊗ x₀) (xs₁ ⊗ x₁) with x₀ ≟ x₁
… | ⊕.inl κ₀ = ⊕.inl λ { refl → κ₀ refl }
… | ⊕.inr refl with list-eq _≟_ xs₀ xs₁
… | ⊕.inl κ₁ = ⊕.inl λ { refl → κ₁ refl }
… | ⊕.inr refl = ⊕.inr refl

OName = String
TName = Nat

mutual
  Canopy : Set
  Canopy = List Frame

  Cluster : Set
  Cluster = List Face

  Gallery : Set
  Gallery = List Visage

  data Mesh : Set where
    nil : Mesh
    cons : (ϕ : Face) (ω : Mesh) → Mesh
    -- cut⇕ : (ω₀ : Mesh) (ω₁ : Mesh) → Mesh
    -- cut⊗ : (ω₁ : Mesh) (ω₀ : Mesh) → Mesh

  data Face : Set where
    cut : (ϕ : Face) (ω : Mesh) → Face
    abs : (Ϡ : Canopy) (ϕ : Face) → Face
    ovar : (ϑ : OName) → Face
    tvar : (x : TName) → Face

  record Frame : Set where
    no-eta-equality
    inductive
    constructor _⊸_
    field
      dom : Canopy
      cod : Cluster

  record Visage : Set where
    no-eta-equality
    inductive
    constructor ▸δ
    field
      ϑ : OName
      ψ : Frame

module Context where
  Context : Set
  Context = List Frame

  look : (Γ : Context) (x : TName) → Maybe Frame
  look ε x = no
  look (Γ ⊗ ψ) ze = so ψ
  look (Γ ⊗ ψ) (su x) = look Γ x
open Context
  using (Context)

module Signature where
  Signature : Set
  Signature = Gallery

  look : (𝔏 : Signature) (ϑ : OName) → Maybe Frame
  look ε ϑ = no
  look (𝔏 ⊗ ▸δ ϑ? ψ) ϑ with String.⟦ ϑ? ≟ ϑ ⟧
  … | ff = look 𝔏 ϑ
  … | tt = so ψ
open Signature
  using (Signature)

module Computad where
  Computad : Set
  Computad = List Signature

  look : (Θ : Computad) (ϑ : OName) → Maybe Frame
  look ε ϑ = no
  look (Θ ⊗ 𝔏) ϑ with Signature.look 𝔏 ϑ
  … | no = look Θ ϑ
  … | ψ = ψ
open Computad
  using (Computad)

data Drop- : (ϡ₀ ϡ₁ ϡ₂ : Canopy) → Set where
  nil
    : ∀ {ϡ₀}
    → Drop- ϡ₀ ε ϡ₀
  cons
    : ∀ {ϡ₀ ϡ₁ ψ ρ}
    → Drop- ϡ₀ ϡ₁ ρ
    → Drop- (ϡ₀ ⊗ ψ) (ϡ₁ ⊗ ψ) ρ

data Drop+ : (ϰ₀ ϰ₁ : Cluster) (ϡ : Canopy) → Set where
  nil
    : Drop+ ε ε ε
  ext
    : ∀ {ϰ ϕ ϡ}
    → Drop+ ε ϰ ϡ
    → Drop+ ε (ϰ ⊗ ϕ) (ϡ ⊗ (ε ⊸ ε ⊗ ϕ))
  cons
    : ∀ {ϰ₀ ϰ₁ ϕ ρ}
    → Drop+ ϰ₀ ϰ₁ ρ
    → Drop+ (ϰ₀ ⊗ ϕ) (ϰ₁ ⊗ ϕ) ρ

data Diminish : (ψ₀ ψ₁ : Frame) (ϡ : Canopy) → Set where
  dim
    : ∀ {ϡ₀ ϡ₁ ϡ⁻ ϡ⁺ ϰ₀ ϰ₁}
    → Drop- ϡ₀ ϡ₁ ϡ⁻
    → Drop+ ϰ₀ ϰ₁ ϡ⁺
    → Diminish (ϡ₀ ⊸ ϰ₀) (ϡ₁ ⊸ ϰ₁) (ϡ⁻ ⊛ ϡ⁺)

data Reframe : (ϡ : Canopy) (ψ : Frame) → Set where
  nil
    : Reframe ε (ε ⊸ ε)
  cons
    : ∀ {ϡ Γ γ Δ δ}
    → Reframe ϡ (Γ ⊸ γ)
    → Reframe (ϡ ⊗ (Δ ⊸ δ)) (Γ ⊛ Δ ⊸ γ ⊛ δ)

mutual
  data _▸_⊩_⇐_⟖_ (Θ : Computad) (Γ : Context) (ω : Mesh) (ξ : Canopy) (ϡ : Canopy) : Set where
    check
      : ∀ {ψ₀ ψ₁}
      → Θ ▸ Γ ⊩ ω ⇒ ψ₀
      → Reframe ξ ψ₁
      → Diminish ψ₀ ψ₁ ϡ
      → Θ ▸ Γ ⊩ ω ⇐ ξ ⟖ ϡ

  data _▸_⊩_⇒_ (Θ : Computad) (Γ : Context) : (ω : Mesh) (ψ : Frame) → Set where
    nil
      : Θ ▸ Γ ⊩ nil ⇒ ε ⊸ ε
    cons
      : ∀ {ϕ ω ϡ₀ ϡ₁ ϰ₀ ϰ₁}
      → Θ ▸ Γ ⊢ ϕ ⇒ ϡ₀ ⊸ ϰ₀
      → Θ ▸ Γ ⊩ ω ⇒ ϡ₁ ⊸ ϰ₁
      → Θ ▸ Γ ⊩ cons ϕ ω ⇒ (ϡ₀ ⊛ ϡ₁) ⊸ (ϰ₀ ⊛ ϰ₁)

  data _▸_⊢_⇒_ (Θ : Computad) (Γ : Context) : (ϕ : Face) (ψ : Frame) → Set where
    cut
      : ∀ {ϕ ω ξ ϡ ϰ}
      → Θ ▸ Γ ⊢ ϕ ⇒ ξ ⊸ ϰ
      → Θ ▸ Γ ⊩ ω ⇐ ξ ⟖ ϡ
      → Θ ▸ Γ ⊢ cut ϕ ω ⇒ ϡ ⊸ ϰ
    ovar
      : ∀ {ϑ ψ}
      → Computad.look Θ ϑ ≡ so ψ
      → Θ ▸ Γ ⊢ ovar ϑ ⇒ ψ
    abs
      : ∀ {Ϡ ϕ ϡ ϰ}
      → Θ ▸ Γ ⊛ Ϡ ⊢ ϕ ⇒ ϡ ⊸ ϰ
      → Θ ▸ Γ ⊢ abs Ϡ ϕ ⇒ Ϡ ⊛ ϡ ⊸ ϰ
    tvar
      : ∀ {x ψ}
      → Context.look Γ x ≡ so ψ
      → Θ ▸ Γ ⊢ tvar x ⇒ ψ

frame-inj
  : ∀ {ϡ₀ ϡ₁ ϰ₀ ϰ₁}
  → (ϡ₀ ⊸ ϰ₀) ≡ (ϡ₁ ⊸ ϰ₁)
  → ϡ₀ ≡ ϡ₁ × ϰ₀ ≡ ϰ₁
frame-inj refl = refl , refl

mutual
  {-# TERMINATING #-}
  frame-eq : (ψ₀ ψ₁ : Frame) → Decidable (ψ₀ ≡ ψ₁)
  frame-eq (ϡ₀ ⊸ ϰ₀) (ϡ₁ ⊸ ϰ₁) with list-eq face-eq ϰ₀ ϰ₁ -- FIXME: list-eq needs sized types
  … | ⊕.inl κ₀ = ⊕.inl λ { refl → κ₀ refl }
  … | ⊕.inr refl with list-eq frame-eq ϡ₀ ϡ₁
  … | ⊕.inl κ₁ = ⊕.inl λ { refl → κ₁ refl }
  … | ⊕.inr refl = ⊕.inr refl

  mesh-eq : (ω₀ ω₁ : Mesh) → Decidable (ω₀ ≡ ω₁)
  mesh-eq nil nil = ⊕.inr refl
  mesh-eq nil (cons _ _) = ⊕.inl λ()
  mesh-eq (cons _ _) nil = ⊕.inl λ()
  mesh-eq (cons ϕ₀ ω₀) (cons ϕ₁ ω₁) with face-eq ϕ₀ ϕ₁
  … | ⊕.inl κ₀ = ⊕.inl λ { refl → κ₀ refl }
  … | ⊕.inr refl with mesh-eq ω₀ ω₁
  … | ⊕.inl κ₁ = ⊕.inl λ { refl → κ₁ refl }
  … | ⊕.inr refl = ⊕.inr refl

  face-eq : (ϕ₀ ϕ₁ : Face) → Decidable (ϕ₀ ≡ ϕ₁)
  face-eq (cut ϕ₀ ω₀) (cut ϕ₁ ω₁) with face-eq ϕ₀ ϕ₁
  … | ⊕.inl κ₀ = ⊕.inl λ { refl → κ₀ refl }
  … | ⊕.inr refl with mesh-eq ω₀ ω₁
  … | ⊕.inl κ₁ = ⊕.inl λ { refl → κ₁ refl }
  … | ⊕.inr refl = ⊕.inr refl
  face-eq (cut _ _) (abs _ _) = ⊕.inl λ()
  face-eq (cut _ _) (ovar _) = ⊕.inl λ()
  face-eq (cut _ _) (tvar _) = ⊕.inl λ()
  face-eq (abs _ _) (cut _ _) = ⊕.inl λ()
  face-eq (abs Ϡ₀ ϕ₀) (abs Ϡ₁ ϕ₁) with list-eq frame-eq Ϡ₀ Ϡ₁
  … | ⊕.inl κ₀ = ⊕.inl λ { refl → κ₀ refl }
  … | ⊕.inr refl with face-eq ϕ₀ ϕ₁
  … | ⊕.inl κ₁ = ⊕.inl λ { refl → κ₁ refl }
  … | ⊕.inr refl = ⊕.inr refl
  face-eq (abs _ _) (ovar _) = ⊕.inl λ()
  face-eq (abs _ _) (tvar _) = ⊕.inl λ()
  face-eq (ovar _) (cut _ _) = ⊕.inl λ()
  face-eq (ovar _) (abs _ _) = ⊕.inl λ()
  face-eq (ovar ϑ₀) (ovar ϑ₁) with ϑ₀ String.≟ ϑ₁
  … | ⊕.inl κ = ⊕.inl λ { refl → κ refl }
  … | ⊕.inr refl = ⊕.inr refl
  face-eq (ovar _) (tvar _) = ⊕.inl λ()
  face-eq (tvar _) (cut _ _) = ⊕.inl λ()
  face-eq (tvar _) (abs _ _) = ⊕.inl λ()
  face-eq (tvar _) (ovar _) = ⊕.inl λ()
  face-eq (tvar x₀) (tvar x₁) with x₀ Nat.≟ x₁
  … | ⊕.inl κ = ⊕.inl λ { refl → κ refl }
  … | ⊕.inr refl = ⊕.inr refl

unique-drop-
  : ∀ {ϡ₀ ϡ₁ ϡ₂₀ ϡ₂₁}
  → Drop- ϡ₀ ϡ₁ ϡ₂₀
  → Drop- ϡ₀ ϡ₁ ϡ₂₁
  → ϡ₂₀ ≡ ϡ₂₁
unique-drop- nil nil = refl
unique-drop- (cons φ₀) (cons φ₁) with unique-drop- φ₀ φ₁
unique-drop- (cons φ₀) (cons φ₁) | refl = refl

unique-drop+
  : ∀ {ϰ₀ ϰ₁ ϡ₂₀ ϡ₂₁}
  → Drop+ ϰ₀ ϰ₁ ϡ₂₀
  → Drop+ ϰ₀ ϰ₁ ϡ₂₁
  → ϡ₂₀ ≡ ϡ₂₁
unique-drop+ nil nil = refl
unique-drop+ (ext φ₀) (ext φ₁) with unique-drop+ φ₀ φ₁
unique-drop+ (ext φ₀) (ext φ₁) | refl = refl
unique-drop+ (cons φ₀) (cons φ₁) with unique-drop+ φ₀ φ₁
unique-drop+ (cons φ₀) (cons φ₁) | refl = refl

unique-diminish
  : ∀ {ψ₀ ψ₁ ϡ₀ ϡ₁}
  → Diminish ψ₀ ψ₁ ϡ₀
  → Diminish ψ₀ ψ₁ ϡ₁
  → ϡ₀ ≡ ϡ₁
unique-diminish (dim φ₀⁻ φ₀⁺) (dim φ₁⁻ φ₁⁺) with unique-drop- φ₀⁻ φ₁⁻ | unique-drop+ φ₀⁺ φ₁⁺
unique-diminish (dim φ₀⁻ φ₀⁺) (dim φ₁⁻ φ₁⁺) | refl | refl = refl

unique-reframe
  : ∀ {ξ ψ₀ ψ₁}
  → Reframe ξ ψ₀
  → Reframe ξ ψ₁
  → ψ₀ ≡ ψ₁
unique-reframe nil nil = refl
unique-reframe (cons φ₀) (cons φ₁) with unique-reframe φ₀ φ₁
unique-reframe (cons φ₀) (cons φ₁) | refl = refl

mutual
  unique-check-mesh
    : ∀ {Θ Γ ω ξ ϡ₀ ϡ₁}
    → Θ ▸ Γ ⊩ ω ⇐ ξ ⟖ ϡ₀
    → Θ ▸ Γ ⊩ ω ⇐ ξ ⟖ ϡ₁
    → ϡ₀ ≡ ϡ₁
  unique-check-mesh (check ⊢ω₀ ⊢ref₀ ⊢dim₀) (check ⊢ω₁ ⊢ref₁ ⊢dim₁) with unique-infer-mesh ⊢ω₀ ⊢ω₁ | unique-reframe ⊢ref₀ ⊢ref₁
  … | refl | refl with unique-diminish ⊢dim₀ ⊢dim₁
  unique-check-mesh (check ⊢ω₀ ⊢ref₀ ⊢dim₀) (check ⊢ω₁ ⊢ref₁ ⊢dim₁) | refl | refl | refl = refl

  unique-infer-mesh
    : ∀ {Θ Γ ω ψ₀ ψ₁}
    → Θ ▸ Γ ⊩ ω ⇒ ψ₀
    → Θ ▸ Γ ⊩ ω ⇒ ψ₁
    → ψ₀ ≡ ψ₁
  unique-infer-mesh nil nil = refl
  unique-infer-mesh (cons ⊢ϕ₀ ⊢ω₀) (cons ⊢ϕ₁ ⊢ω₁) with unique-infer-face ⊢ϕ₀ ⊢ϕ₁ | unique-infer-mesh ⊢ω₀ ⊢ω₁
  unique-infer-mesh (cons ⊢ϕ₀ ⊢ω₀) (cons ⊢ϕ₁ ⊢ω₁) | refl | refl = refl

  unique-infer-face
    : ∀ {Θ Γ ϕ ψ₀ ψ₁}
    → Θ ▸ Γ ⊢ ϕ ⇒ ψ₀
    → Θ ▸ Γ ⊢ ϕ ⇒ ψ₁
    → ψ₀ ≡ ψ₁
  unique-infer-face (cut ⊢ϕ₀ ⊢ω₀) (cut ⊢ϕ₁ ⊢ω₁) with unique-infer-face ⊢ϕ₀ ⊢ϕ₁
  unique-infer-face (cut ⊢ϕ₀ ⊢ω₀) (cut ⊢ϕ₁ ⊢ω₁) | refl with unique-check-mesh ⊢ω₀ ⊢ω₁
  unique-infer-face (cut ⊢ϕ₀ ⊢ω₀) (cut ⊢ϕ₁ ⊢ω₁) | refl | refl = refl
  unique-infer-face (ovar ⊢ϑ₀) (ovar ⊢ϑ₁) = Maybe.⊢.so-inj (≡.seq (≡.inv ⊢ϑ₀ , ⊢ϑ₁))
  unique-infer-face (abs ⊢ϕ₀) (abs ⊢ϕ₁) with unique-infer-face ⊢ϕ₀ ⊢ϕ₁
  unique-infer-face (abs ⊢ϕ₀) (abs ⊢ϕ₁) | refl = refl
  unique-infer-face (tvar ⊢x₀) (tvar ⊢x₁) = Maybe.⊢.so-inj (≡.seq (≡.inv ⊢x₀ , ⊢x₁))

reframe : (ϡ : Canopy) → Σ Frame (Reframe ϡ)
reframe ε = _ ▸ nil
reframe (ϡ ⊗ (Δ ⊸ δ)) with reframe ϡ
… | (Γ ⊸ γ) ▸ φ = (Γ ⊛ Δ ⊸ γ ⊛ δ) ▸ cons φ

drop- : (ϡ₀ ϡ₁ : Canopy) → Decidable (Σ Canopy (Drop- ϡ₀ ϡ₁))
drop- ϡ₀ ε = ⊕.inr (_ ▸ nil)
drop- ε (ϡ₁ ⊗ ψ₁) = ⊕.inl λ { (_ ▸ ()) }
drop- (ϡ₀ ⊗ ψ₀) (ϡ₁ ⊗ ψ₁) with frame-eq ψ₀ ψ₁
… | ⊕.inl κ₀ = ⊕.inl λ { (_ ▸ cons _) → κ₀ refl }
… | ⊕.inr refl with drop- ϡ₀ ϡ₁
… | ⊕.inl κ₁ = ⊕.inl λ { (_ ▸ cons ρ) → κ₁ (_ ▸ ρ) }
… | ⊕.inr (_ ▸ ρ) = ⊕.inr (_ ▸ cons ρ)

drop+ : (ϰ₀ ϰ₁ : Cluster) → Decidable (Σ Canopy (Drop+ ϰ₀ ϰ₁))
drop+ ε ε = ⊕.inr (_ ▸ nil)
drop+ ε (ϰ₁ ⊗ ϕ₁) with drop+ ε ϰ₁
… | ⊕.inl κ = ⊕.inl λ { (_ ▸ ext φ) → κ (_ ▸ φ) }
… | ⊕.inr (_ ▸ φ) = ⊕.inr (_ ▸ ext φ)
drop+ (ϰ₀ ⊗ ϕ₀) ε = ⊕.inl λ { (_ ▸ ()) }
drop+ (ϰ₀ ⊗ ϕ₀) (ϰ₁ ⊗ ϕ₁) with face-eq ϕ₀ ϕ₁
… | ⊕.inl κ₀ = ⊕.inl λ { (_ ▸ cons _) → κ₀ refl }
… | ⊕.inr refl with drop+ ϰ₀ ϰ₁
… | ⊕.inl κ₁ = ⊕.inl λ { (_ ▸ cons φ₁) → κ₁ (_ ▸ φ₁) }
… | ⊕.inr (_ ▸ φ₁) = ⊕.inr (_ ▸ cons φ₁)

diminish : (ψ₀ ψ₁ : Frame) → Decidable (Σ Canopy (Diminish ψ₀ ψ₁))
diminish (ϡ₀ ⊸ ϰ₀) (ϡ₁ ⊸ ϰ₁) with drop- ϡ₀ ϡ₁
… | ⊕.inl κ₀ = ⊕.inl λ { (_ ▸ dim φ₀ φ₁) → κ₀ (_ ▸ φ₀) }
… | ⊕.inr (_ ▸ φ₀) with drop+ ϰ₀ ϰ₁
… | ⊕.inl κ₁ = ⊕.inl λ { (_ ▸ dim _ φ₁) → κ₁ (_ ▸ φ₁) }
… | ⊕.inr (_ ▸ φ₁) = ⊕.inr (_ ▸ dim φ₀ φ₁)

mutual
  ⊢check-mesh
    : ∀ Θ Γ ω ξ
    → Decidable (Σ (List Frame) λ ϡ → Θ ▸ Γ ⊩ ω ⇐ ξ ⟖ ϡ)
  ⊢check-mesh Θ Γ ω ξ with ⊢infer-mesh Θ Γ ω
  ⊢check-mesh Θ Γ ω ξ | ⊕.inl κ₀ = ⊕.inl λ { (_ ▸ check φ₀ _ _) → κ₀ (_ ▸ φ₀) }
  ⊢check-mesh Θ Γ ω ξ | ⊕.inr (ψ₀ ▸ φ₀) with reframe ξ
  ⊢check-mesh Θ Γ ω ξ | ⊕.inr (ψ₀ ▸ φ₀) | ψ₁ ▸ φ₁ with diminish ψ₀ ψ₁
  ⊢check-mesh Θ Γ ω ξ | ⊕.inr (ψ₀ ▸ φ₀) | ψ₁ ▸ φ₁ | ⊕.inl κ₂ =
      ⊕.inl λ { (_ ▸ check φ₀′ φ₁′ φ₂) → κ₂ (_ ▸ ≡.coe* (λ X → Diminish X _ _) (unique-infer-mesh φ₀′ φ₀) (≡.coe* (λ Y → Diminish _ Y _) (unique-reframe φ₁′ φ₁) φ₂)) }
  ⊢check-mesh Θ Γ ω ξ | ⊕.inr (ψ₀ ▸ φ₀) | ψ₁ ▸ φ₁ | ⊕.inr (_ ▸ φ₂) = ⊕.inr (_ ▸ check φ₀ φ₁ φ₂)

  ⊢infer-mesh
    : ∀ Θ Γ ω
    → Decidable (Σ Frame λ ψ → Θ ▸ Γ ⊩ ω ⇒ ψ)
  ⊢infer-mesh Θ Γ nil = ⊕.inr (_ ▸ nil)
  ⊢infer-mesh Θ Γ (cons ϕ ω) with ⊢infer-face Θ Γ ϕ
  ⊢infer-mesh Θ Γ (cons ϕ ω) | ⊕.inl κ₀ = ⊕.inl λ { (_ ▸ cons φ₀ φ₁) → κ₀ (_ ▸ φ₀) }
  ⊢infer-mesh Θ Γ (cons ϕ ω) | ⊕.inr φ₀ with ⊢infer-mesh Θ Γ ω
  ⊢infer-mesh Θ Γ (cons ϕ ω) | ⊕.inr φ₀ | ⊕.inl κ₁ = ⊕.inl λ { (_ ▸ cons _ φ₁) → κ₁ (_ ▸ φ₁) }
  ⊢infer-mesh Θ Γ (cons ϕ ω) | ⊕.inr (_ ⊸ _ ▸ φ₀) | ⊕.inr (_ ⊸ _ ▸ φ₁) = ⊕.inr (_ ▸ cons φ₀ φ₁)

  ⊢infer-face
    : ∀ Θ Γ ϕ
    → Decidable (Σ Frame λ ψ → Θ ▸ Γ ⊢ ϕ ⇒ ψ)
  ⊢infer-face Θ Γ (cut ϕ ω) with ⊢infer-face Θ Γ ϕ
  … | ⊕.inl κ₀ = ⊕.inl λ { (_ ▸ cut φ₀ _) → κ₀ (_ ▸ φ₀) }
  … | ⊕.inr (ξ ⊸ _ ▸ φ₀) with ⊢check-mesh Θ Γ ω ξ
  … | ⊕.inl κ₁ = ⊕.inl λ { (_ ▸ cut φ₀′ φ₁) → κ₁ (_ ▸ ≡.coe* (λ X → _ ▸ _ ⊩ _ ⇐ X ⟖ _) (⊗.fst (frame-inj (unique-infer-face φ₀′ φ₀))) φ₁) }
  … | ⊕.inr (_ ▸ φ₁) = ⊕.inr (_ ▸ cut φ₀ φ₁)
  ⊢infer-face Θ Γ (abs Ϡ ϕ) with ⊢infer-face Θ (Γ ⊛ Ϡ) ϕ
  … | ⊕.inl κ = ⊕.inl λ { (_ ▸ abs φ) → κ (_ ▸ φ) }
  … | ⊕.inr (_ ⊸ _ ▸ φ) = ⊕.inr (_ ▸ abs φ)
  ⊢infer-face Θ Γ (ovar ϑ) with Computad.look Θ ϑ | inspect (Computad.look Θ) ϑ
  ⊢infer-face Θ Γ (ovar ϑ) | no   | [ φ ] = ⊕.inl λ { (_ ▸ ovar φ′) → Maybe.⊢.no≢so (≡.seq (≡.inv φ , φ′)) }
  ⊢infer-face Θ Γ (ovar ϑ) | so ψ | [ φ ] = ⊕.inr (_ ▸ ovar φ)
  ⊢infer-face Θ Γ (tvar x) with Context.look Γ x | inspect (Context.look Γ) x
  ⊢infer-face Θ Γ (tvar x) | no   | [ φ ] = ⊕.inl λ { (_ ▸ tvar φ′) → Maybe.⊢.no≢so (≡.seq (≡.inv φ , φ′)) }
  ⊢infer-face Θ Γ (tvar x) | so ψ | [ φ ] = ⊕.inr (_ ▸ tvar φ)

infer-mesh : Computad → Context → Mesh → Maybe Frame
infer-mesh Θ Γ ω with ⊢infer-mesh Θ Γ ω
… | ⊕.inl _ = no
… | ⊕.inr (ψ ▸ _) = so ψ

infer-face : Computad → Context → Face → Maybe Frame
infer-face Θ Γ ϕ with ⊢infer-face Θ Γ ϕ
… | ⊕.inl _ = no
… | ⊕.inr (ψ ▸ _) = so ψ

module Test where
  𝔏₀ : Signature
  𝔏₀ =
    let Δ = ε in
    let Δ = Δ ⊗ ▸δ "bool" (ε ⊸ ε) in
    Δ

  𝔏₁ : Signature
  𝔏₁ =
    let Δ = ε in
    let Δ = Δ ⊗ ▸δ "ff" (ε ⊸ ε ⊗ ovar "bool") in
    let Δ = Δ ⊗ ▸δ "tt" (ε ⊸ ε ⊗ ovar "bool") in
    let Δ = Δ ⊗ ▸δ "not" (ε ⊗ (ε ⊸ ε ⊗ ovar "bool") ⊸ ε ⊗ ovar "bool") in
    let Δ = Δ ⊗ ▸δ "and" (ε ⊗ (ε ⊸ ε ⊗ ovar "bool") ⊗ (ε ⊸ ε ⊗ ovar "bool") ⊸ (ε ⊗ ovar "bool")) in
    Δ

  Θ : Computad
  Θ = ε ⊗ 𝔏₀ ⊗ 𝔏₁

  term₀ : Face
  term₀ = cut (ovar "and") (cons (ovar "ff") (cons (ovar "not") nil))

  term₁ : Face
  term₁ = cut (ovar "and") (cons (ovar "ff") (cons (abs (ε ⊗ (ε ⊸ ε ⊗ ovar "bool")) (cut (ovar "not") (cons (tvar 0) nil))) nil))

  test : infer-face Θ ε term₀ ≡ infer-face Θ ε term₁
  test = refl
