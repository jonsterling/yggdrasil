module Main where

open import Agda.Primitive
open import Prelude.Bool
open import Prelude.Decidable
open import Prelude.Inspect
open import Prelude.List
open import Prelude.Maybe
open import Prelude.Monoidal
  hiding (_⇒_)
open import Prelude.Path
open import Prelude.Size
open import Prelude.String

infix 1 _⇒_
infix 0 _⊩_∈_
infix 0 _⊢_∈_

open List
  using (_++_)

Name : Set
Name = String

Operator : Set
Operator = Name

mutual
  data Complex : Set where
    stop : (Γ : List Face) → Complex
    step : (𝔣 : Face) (ω : Complex) → Complex
    cmp⇔ : (ω₀ : Complex) (ω₁ : Complex) → Complex
    cmp⇕ : (ω₁ : Complex) (ω₀ : Complex) → Complex

  data Face : Set where
    idn : (Γ : List Face) → Face
    cut : (𝔣 : Face) (ω : Complex) → Face
    var : (ϑ : Operator) → Face

record Arity : Set where
  no-eta-equality
  constructor _⇒_
  field
    dom : List Face
    cod : List Face
open Arity

module Decl where
  record Decl : Set where
    no-eta-equality
    constructor ▸δ
    field
      ϑ : Operator
      α : Arity
  open Decl public

  ∂- : Decl → List Face
  ∂- (▸δ ϑ (σ ⇒ τ)) = σ

  ∂+ : Decl → List Face
  ∂+ (▸δ ϑ (σ ⇒ τ)) = τ
open Decl public
  hiding (module Decl)
  using (Decl)
  using (▸δ)

module Sig where
  Sig : Set
  Sig = List Decl

  look : (𝔏 : Sig) (ϑ : Operator) → Maybe Arity
  look [] ϑ = no
  look (▸δ ϑ? (σ ⇒ τ) ∷ 𝔏) ϑ with String.⟦ ϑ? ≟ ϑ ⟧
  … | ff = look 𝔏 ϑ
  … | tt = so (σ ⇒ τ)
open Sig public
  using (Sig)

module Ctx where
  Ctx : Set
  Ctx = List Sig

  look : (Γ : Ctx) (ϑ : Operator) → Maybe Arity
  look [] ϑ = no
  look (𝔏 ∷ Γ) ϑ with Sig.look 𝔏 ϑ
  … | no = look Γ ϑ
  … | α = α
open Ctx public
  using (Ctx)

mutual
  data _⊩_∈_ (𝔉 : Ctx) : (ω : Complex) (α : Arity) → Set where
    stop
      : ∀ {Γ}
      → 𝔉 ⊩ stop Γ ∈ Γ ⇒ Γ
    step
      : ∀ {𝔣 ω Γ₀ Γ₁ Δ₀ Δ₁}
      → 𝔉 ⊢ 𝔣 ∈ Γ₀ ⇒ Δ₀
      → 𝔉 ⊩ ω ∈ Γ₁ ⇒ Δ₁
      → 𝔉 ⊩ step 𝔣 ω ∈ Γ₀ ++ Γ₁ ⇒ Δ₀ ++ Δ₁
    cmp⇔
      : ∀ {ω₀ ω₁ Γ₀ Γ₁ Δ₀ Δ₁}
      → 𝔉 ⊩ ω₀ ∈ Γ₀ ⇒ Γ₁
      → 𝔉 ⊩ ω₁ ∈ Δ₀ ⇒ Δ₁
      → 𝔉 ⊩ cmp⇔ ω₀ ω₁ ∈ Γ₀ ++ Δ₀ ⇒ Γ₁ ++ Δ₁
    cmp⇕
      : ∀ {ω₀ ω₁ Γ Δ Θ}
      → 𝔉 ⊩ ω₁ ∈ Δ ⇒ Θ
      → 𝔉 ⊩ ω₀ ∈ Γ ⇒ Δ
      → 𝔉 ⊩ cmp⇕ ω₁ ω₀ ∈ Γ ⇒ Θ

  data _⊢_∈_ (𝔉 : Ctx) : (𝔣 : Face) (α : Arity) → Set where
    var
      : ∀ {ϑ α}
      → Ctx.look 𝔉 ϑ ≡ so α
      → 𝔉 ⊢ var ϑ ∈ α
    idn
      : (Γ : List Face)
      → 𝔉 ⊢ idn Γ ∈ Γ ⇒ Γ
    cut
      : ∀ {𝔣 ω Γ Δ Ξ}
      → 𝔉 ⊢ 𝔣 ∈ Ξ ⇒ Δ
      → 𝔉 ⊩ ω ∈ Γ ⇒ Ξ
      → 𝔉 ⊢ cut 𝔣 ω ∈ Γ ⇒ Δ

{-# TERMINATING #-}
mutual
  complex-eq : (ω₀ ω₁ : Complex) → Decidable (ω₀ ≡ ω₁)
  complex-eq (stop Γ) (stop Γ′) with List._⊢_≟_ face-eq Γ Γ′
  complex-eq (stop Γ) (stop Γ′) | ⊕.inl κ = ⊕.inl λ { refl → κ refl }
  complex-eq (stop Γ) (stop Γ′) | ⊕.inr refl = ⊕.inr refl
  complex-eq (stop _) (step _ _) = ⊕.inl λ()
  complex-eq (stop _) (cmp⇔ _ _) = ⊕.inl λ()
  complex-eq (stop _) (cmp⇕ _ _) = ⊕.inl λ()
  complex-eq (step _ _) (stop _) = ⊕.inl λ()
  complex-eq (step 𝔣 ω) (step 𝔣′ ω′) with face-eq 𝔣 𝔣′
  complex-eq (step 𝔣 ω) (step 𝔣′ ω′) | ⊕.inl κ₀ = ⊕.inl λ { refl → κ₀ refl }
  complex-eq (step 𝔣 ω) (step 𝔣′ ω′) | ⊕.inr φ₀ with complex-eq ω ω′
  complex-eq (step 𝔣 ω) (step 𝔣′ ω′) | ⊕.inr φ₀ | ⊕.inl κ₁ = ⊕.inl λ { refl → κ₁ refl }
  complex-eq (step 𝔣 ω) (step 𝔣′ ω′) | ⊕.inr refl | ⊕.inr refl = ⊕.inr refl
  complex-eq (step _ _) (cmp⇔ _ _) = ⊕.inl λ()
  complex-eq (step _ _) (cmp⇕ _ _) = ⊕.inl λ()
  complex-eq (cmp⇔ _ _) (stop _) = ⊕.inl λ()
  complex-eq (cmp⇔ _ _) (step _ _) = ⊕.inl λ()
  complex-eq (cmp⇔ ω₀ ω₁) (cmp⇔ ω₀′ ω₁′) with complex-eq ω₀ ω₀′
  complex-eq (cmp⇔ ω₀ ω₁) (cmp⇔ ω₀′ ω₁′) | ⊕.inl κ₀ = ⊕.inl λ { refl → κ₀ refl}
  complex-eq (cmp⇔ ω₀ ω₁) (cmp⇔ ω₀′ ω₁′) | ⊕.inr φ₀ with complex-eq ω₁ ω₁′
  complex-eq (cmp⇔ ω₀ ω₁) (cmp⇔ ω₀′ ω₁′) | ⊕.inr φ₀ | ⊕.inl κ₁ = ⊕.inl λ { refl → κ₁ refl}
  complex-eq (cmp⇔ ω₀ ω₁) (cmp⇔ ω₀′ ω₁′) | ⊕.inr refl | ⊕.inr refl = ⊕.inr refl
  complex-eq (cmp⇔ _ _) (cmp⇕ _ _) = ⊕.inl λ()
  complex-eq (cmp⇕ _ _) (stop _) = ⊕.inl λ()
  complex-eq (cmp⇕ _ _) (step _ _) = ⊕.inl λ()
  complex-eq (cmp⇕ _ _) (cmp⇔ _ _) = ⊕.inl λ()
  complex-eq (cmp⇕ ω₁ ω₀) (cmp⇕ ω₁′ ω₀′) with complex-eq ω₁ ω₁′
  complex-eq (cmp⇕ ω₁ ω₀) (cmp⇕ ω₁′ ω₀′) | ⊕.inl κ₀ = ⊕.inl λ { refl → κ₀ refl}
  complex-eq (cmp⇕ ω₁ ω₀) (cmp⇕ ω₁′ ω₀′) | ⊕.inr φ₀ with complex-eq ω₀ ω₀′
  complex-eq (cmp⇕ ω₁ ω₀) (cmp⇕ ω₁′ ω₀′) | ⊕.inr φ₀ | ⊕.inl κ₁ = ⊕.inl λ { refl → κ₁ refl}
  complex-eq (cmp⇕ ω₁ ω₀) (cmp⇕ ω₁′ ω₀′) | ⊕.inr refl | ⊕.inr refl = ⊕.inr refl

  face-eq : (𝔣₀ 𝔣₁ : Face) → Decidable (𝔣₀ ≡ 𝔣₁)
  face-eq (idn Γ) (idn Γ′) with List._⊢_≟_ face-eq Γ Γ′
  face-eq (idn Γ) (idn Γ′) | ⊕.inl κ = ⊕.inl λ { refl → κ refl }
  face-eq (idn Γ) (idn Γ′) | ⊕.inr refl = ⊕.inr refl
  face-eq (idn _) (cut _ _) = ⊕.inl λ()
  face-eq (idn _) (var _) = ⊕.inl λ()
  face-eq (cut _ _) (idn _) = ⊕.inl λ()
  face-eq (cut 𝔣 ω) (cut 𝔣′ ω′) with face-eq 𝔣 𝔣′
  face-eq (cut 𝔣 ω) (cut 𝔣′ ω′) | ⊕.inl κ₀ = ⊕.inl λ { refl → κ₀ refl }
  face-eq (cut 𝔣 ω) (cut 𝔣′ ω′) | ⊕.inr φ₀ with complex-eq ω ω′
  face-eq (cut 𝔣 ω) (cut 𝔣′ ω′) | ⊕.inr φ₀ | ⊕.inl κ₁ = ⊕.inl λ { refl → κ₁ refl }
  face-eq (cut 𝔣 ω) (cut 𝔣′ ω′) | ⊕.inr refl | ⊕.inr refl = ⊕.inr refl
  face-eq (cut _ _) (var _) = ⊕.inl λ()
  face-eq (var _) (idn _) = ⊕.inl λ()
  face-eq (var _) (cut _ _) = ⊕.inl λ()
  face-eq (var ϑ) (var ϑ′) with ϑ String.≟ ϑ′
  face-eq (var ϑ) (var ϑ′) | ⊕.inl κ = ⊕.inl λ { refl → κ refl }
  face-eq (var ϑ) (var ϑ′) | ⊕.inr refl = ⊕.inr refl

mutual
  face-unique
    : ∀ {𝔉 𝔣 Γ₀ Γ₁ Δ₀ Δ₁}
    → 𝔉 ⊢ 𝔣 ∈ Γ₀ ⇒ Δ₀
    → 𝔉 ⊢ 𝔣 ∈ Γ₁ ⇒ Δ₁
    → Γ₀ ≡ Γ₁ ⊗ Δ₀ ≡ Δ₁
  face-unique {Γ₀ = Γ₀} {Γ₁} {Δ₀} {Δ₁} (var ϑ) (var ϑ′) = φ (≡.seq (≡.inv ϑ , ϑ′))
    where
      φ : so (Γ₀ ⇒ Δ₀) ≡ so (Γ₁ ⇒ Δ₁) → Γ₀ ≡ Γ₁ ⊗ Δ₀ ≡ Δ₁
      φ refl = refl , refl
  face-unique (idn Γ) (idn .Γ) = refl , refl
  face-unique (cut 𝔣 ω) (cut 𝔣′ ω′) with face-unique 𝔣 𝔣′ | complex-unique ω ω′
  face-unique (cut 𝔣 ω) (cut 𝔣′ ω′) | refl , refl | refl , refl = refl , refl

  complex-unique
    : ∀ {𝔉 ω Γ₀ Γ₁ Δ₀ Δ₁}
    → 𝔉 ⊩ ω ∈ Γ₀ ⇒ Δ₀
    → 𝔉 ⊩ ω ∈ Γ₁ ⇒ Δ₁
    → Γ₀ ≡ Γ₁ ⊗ Δ₀ ≡ Δ₁
  complex-unique stop stop = refl , refl
  complex-unique (step 𝔣 ω) (step 𝔣′ ω′) with face-unique 𝔣 𝔣′ | complex-unique ω ω′
  complex-unique (step 𝔣 ω) (step 𝔣′ ω′) | refl , refl | refl , refl = refl , refl
  complex-unique (cmp⇔ ω₀ ω₁) (cmp⇔ ω₀′ ω₁′) with complex-unique ω₀ ω₀′ | complex-unique ω₁ ω₁′
  complex-unique (cmp⇔ ω₀ ω₁) (cmp⇔ ω₀′ ω₁′) | refl , refl | refl , refl = refl , refl
  complex-unique (cmp⇕ ω₁ ω₀) (cmp⇕ ω₁′ ω₀′) with complex-unique ω₁ ω₁′ | complex-unique ω₀ ω₀′
  complex-unique (cmp⇕ ω₁ ω₀) (cmp⇕ ω₁′ ω₀′) | refl , refl | refl , refl = refl , refl

mutual
  face-inf-chk
    : (𝔉 : Ctx)
    → (Δ : List Face)
    → (𝔣 : Face)
    → Decidable (Σ (List Face) λ Γ → 𝔉 ⊢ 𝔣 ∈ Γ ⇒ Δ)
  face-inf-chk 𝔉 Δ 𝔣 with face-inf-inf 𝔉 𝔣
  face-inf-chk 𝔉 Δ 𝔣 | ⊕.inl κ₀ = ⊕.inl λ { (Γ ▸ ⊢𝔣) → κ₀ (Γ ▸ Δ ▸ ⊢𝔣) }
  face-inf-chk 𝔉 Δ 𝔣 | ⊕.inr (Γ ▸ Δ′ ▸ ⊢𝔣) with face-eq List.⊢ Δ ≟ Δ′
  face-inf-chk 𝔉 Δ 𝔣 | ⊕.inr (Γ ▸ Δ′ ▸ ⊢𝔣) | ⊕.inl κ₁ = ⊕.inl λ { (_ ▸ ⊢𝔣′) → κ₁ (⊗.snd (face-unique ⊢𝔣′ ⊢𝔣)) }
  face-inf-chk 𝔉 .Δ′ 𝔣 | ⊕.inr (Γ ▸ Δ′ ▸ ⊢𝔣) | ⊕.inr refl = ⊕.inr (Γ ▸ ⊢𝔣)

  face-inf-inf
    : (𝔉 : Ctx)
    → (𝔣 : Face)
    → Decidable (Σ (List Face) λ Γ → Σ (List Face) λ Δ → 𝔉 ⊢ 𝔣 ∈ Γ ⇒ Δ)
  face-inf-inf 𝔉 (idn Γ) = ⊕.inr (Γ ▸ Γ ▸ idn Γ)
  face-inf-inf 𝔉 (cut 𝔣 ω) with face-inf-inf 𝔉 𝔣
  face-inf-inf 𝔉 (cut 𝔣 ω) | ⊕.inl κ₀ =
    ⊕.inl λ { (_ ▸ _ ▸ cut ⊢𝔣 ⊢ω) → κ₀ (_ ▸ _ ▸ ⊢𝔣) }
  face-inf-inf 𝔉 (cut 𝔣 ω) | ⊕.inr (Ξ ▸ Δ ▸ ⊢𝔣) with complex-inf-chk 𝔉 Ξ ω
  face-inf-inf 𝔉 (cut 𝔣 ω) | ⊕.inr (Ξ ▸ Δ ▸ ⊢𝔣) | ⊕.inl κ₁ =
    ⊕.inl λ { (_ ▸ _ ▸ cut ⊢𝔣′ ⊢ω) → κ₁ (_ ▸ ≡.coe* (λ X → _ ⊩ _ ∈ _ ⇒ X) (⊗.fst (face-unique ⊢𝔣′ ⊢𝔣)) ⊢ω) }
  face-inf-inf 𝔉 (cut 𝔣 ω) | ⊕.inr (_ ▸ _ ▸ ⊢𝔣) | ⊕.inr (_ ▸ ⊢ω) =
    ⊕.inr (_ ▸ _ ▸ cut ⊢𝔣 ⊢ω)
  face-inf-inf 𝔉 (var ϑ) with Ctx.look 𝔉 ϑ | inspect (Ctx.look 𝔉) ϑ
  face-inf-inf 𝔉 (var ϑ) | no | [ ⊬ϑ ] =
    ⊕.inl λ { (_ ▸ _ ▸ var ⊢ϑ) → Maybe.⊢.no≢so (≡.seq (≡.inv ⊬ϑ , ⊢ϑ)) }
  face-inf-inf 𝔉 (var ϑ) | so (_ ⇒ _) | [ ⊢ϑ ] =
    ⊕.inr (_ ▸ _ ▸ var ⊢ϑ)

  complex-inf-chk
    : (𝔉 : Ctx)
    → (Δ : List Face)
    → (ω : Complex)
    → Decidable (Σ (List Face) λ Γ → 𝔉 ⊩ ω ∈ Γ ⇒ Δ)
  complex-inf-chk 𝔉 Δ (stop Γ) with face-eq List.⊢ Γ ≟ Δ
  complex-inf-chk 𝔉 Δ (stop Γ) | ⊕.inl κ = ⊕.inl λ { (_ ▸ stop) → κ refl }
  complex-inf-chk 𝔉 Δ (stop Γ) | ⊕.inr refl = ⊕.inr (Δ ▸ stop)
  complex-inf-chk 𝔉 Δ (step 𝔣 ω) with complex-inf-inf 𝔉 (step 𝔣 ω)
  complex-inf-chk 𝔉 Δ (step 𝔣 ω) | ⊕.inl κ =
    ⊕.inl λ { (_ ▸ step ⊢𝔣 ⊢ω) → κ (_ ▸ _ ▸ step ⊢𝔣 ⊢ω) }
  complex-inf-chk 𝔉 Δ (step 𝔣 ω) | ⊕.inr (_ ▸ Δ′ ▸ step ⊢𝔣 ⊢ω) with face-eq List.⊢ Δ′ ≟ Δ
  complex-inf-chk 𝔉 Δ (step 𝔣 ω) | ⊕.inr (_ ▸ Δ′ ▸ step ⊢𝔣 ⊢ω) | ⊕.inl κ₁ =
    ⊕.inl λ { (_ ▸ step ⊢𝔣′ ⊢ω′) → κ₁ (≡.ap² (λ { (xs , ys) → xs ++ ys}) (⊗.snd (face-unique ⊢𝔣 ⊢𝔣′) , ⊗.snd (complex-unique ⊢ω ⊢ω′))) }
  complex-inf-chk 𝔉 Δ (step 𝔣 ω) | ⊕.inr (_ ▸ _ ▸ step ⊢𝔣 ⊢ω) | ⊕.inr refl =
    ⊕.inr (_ ▸ step ⊢𝔣 ⊢ω)
  complex-inf-chk 𝔉 Δ (cmp⇔ ω₀ ω₁) with complex-inf-inf 𝔉 ω₀
  complex-inf-chk 𝔉 Δ (cmp⇔ ω₀ ω₁) | ⊕.inl κ₀ =
    ⊕.inl λ { (_ ▸ cmp⇔ ⊢ω₀ _) → κ₀ (_ ▸ _ ▸ ⊢ω₀) }
  complex-inf-chk 𝔉 Δ (cmp⇔ ω₀ ω₁) | ⊕.inr (_ ▸ _ ▸ ⊢ω₀) with complex-inf-inf 𝔉 ω₁
  complex-inf-chk 𝔉 Δ (cmp⇔ ω₀ ω₁) | ⊕.inr (_ ▸ _ ▸ ⊢ω₀) | ⊕.inl κ₁ =
    ⊕.inl λ { (_ ▸ cmp⇔ _ ⊢ω₁) → κ₁ (_ ▸ _ ▸ ⊢ω₁) }
  complex-inf-chk 𝔉 Δ (cmp⇔ ω₀ ω₁) | ⊕.inr (Γ₀ ▸ Γ₁ ▸ ⊢ω₀) | ⊕.inr (Δ₀ ▸ Δ₁ ▸ ⊢ω₁) with face-eq List.⊢ Γ₁ ++ Δ₁ ≟ Δ
  complex-inf-chk 𝔉 Δ (cmp⇔ ω₀ ω₁) | ⊕.inr (Γ₀ ▸ Γ₁ ▸ ⊢ω₀) | ⊕.inr (Δ₀ ▸ Δ₁ ▸ ⊢ω₁) | ⊕.inl κ₂ =
    ⊕.inl λ { (_ ▸ cmp⇔ ⊢ω₀′ ⊢ω₁′) → κ₂ (≡.ap² (λ { (xs , ys) → xs ++ ys }) (⊗.snd (complex-unique ⊢ω₀ ⊢ω₀′) , ⊗.snd (complex-unique ⊢ω₁ ⊢ω₁′))) }
  complex-inf-chk 𝔉 .(Γ₁ ++ Δ₁) (cmp⇔ ω₀ ω₁) | ⊕.inr (Γ₀ ▸ Γ₁ ▸ ⊢ω₀) | (⊕.inr (Δ₀ ▸ Δ₁ ▸ ⊢ω₁)) | ⊕.inr refl =
    ⊕.inr (_ ▸ cmp⇔ ⊢ω₀ ⊢ω₁)
  complex-inf-chk 𝔉 Δ (cmp⇕ ω₁ ω₀) with complex-inf-chk 𝔉 Δ ω₁
  complex-inf-chk 𝔉 Δ (cmp⇕ ω₁ ω₀) | ⊕.inl κ₀ =
    ⊕.inl λ { (_ ▸ cmp⇕ ⊢ω₁ _) → κ₀ (_ ▸ ⊢ω₁) }
  complex-inf-chk 𝔉 Δ (cmp⇕ ω₁ ω₀) | ⊕.inr (Ξ ▸ ⊢ω₁) with complex-inf-chk 𝔉 Ξ ω₀
  complex-inf-chk 𝔉 Δ (cmp⇕ ω₁ ω₀) | ⊕.inr (Ξ ▸ ⊢ω₁) | ⊕.inl κ₁ =
    ⊕.inl λ { (_ ▸ cmp⇕ ⊢ω₁′ ⊢ω₀) → κ₁ (_ ▸ ≡.coe* (λ X → _ ⊩ _ ∈ _ ⇒ X) (⊗.fst (complex-unique ⊢ω₁′ ⊢ω₁)) ⊢ω₀) }
  complex-inf-chk 𝔉 Δ (cmp⇕ ω₁ ω₀) | ⊕.inr (_ ▸ ⊢ω₁) | ⊕.inr (_ ▸ ⊢ω₀) =
    ⊕.inr (_ ▸ cmp⇕ ⊢ω₁ ⊢ω₀)

  complex-inf-inf
    : (𝔉 : Ctx)
    → (ω : Complex)
    → Decidable (Σ (List Face) λ Γ → Σ (List Face) λ Δ → 𝔉 ⊩ ω ∈ Γ ⇒ Δ)
  complex-inf-inf 𝔉 (stop Γ) = ⊕.inr (_ ▸ _ ▸ stop)
  complex-inf-inf 𝔉 (step 𝔣 ω) with face-inf-inf 𝔉 𝔣
  complex-inf-inf 𝔉 (step 𝔣 ω) | ⊕.inl κ₀ =
    ⊕.inl λ { (_ ▸ _ ▸ step ⊢𝔣 ⊢ω) → κ₀ (_ ▸ _ ▸ ⊢𝔣) }
  complex-inf-inf 𝔉 (step 𝔣 ω) | ⊕.inr (Γ₀ ▸ Δ₀ ▸ ⊢𝔣) with complex-inf-inf 𝔉 ω
  complex-inf-inf 𝔉 (step 𝔣 ω) | ⊕.inr (Γ₀ ▸ Δ₀ ▸ ⊢𝔣) | ⊕.inl κ₁ =
    ⊕.inl λ { (_ ▸ _ ▸ step ⊢𝔣′ ⊢ω) → κ₁ (_ ▸ _ ▸ ⊢ω) }
  complex-inf-inf 𝔉 (step 𝔣 ω) | ⊕.inr (Γ₀ ▸ Δ₀ ▸ ⊢𝔣) | ⊕.inr (Γ₁ ▸ Δ₁ ▸ ⊢ω) =
    ⊕.inr (_ ▸ _ ▸ step ⊢𝔣 ⊢ω)
  complex-inf-inf 𝔉 (cmp⇔ ω₀ ω₁) with complex-inf-inf 𝔉 ω₀
  complex-inf-inf 𝔉 (cmp⇔ ω₀ ω₁) | ⊕.inl κ₀ =
    ⊕.inl λ { (_ ▸ _ ▸ cmp⇔ ⊢ω₀ ⊢ω₁) → κ₀ (_ ▸ _ ▸ ⊢ω₀) }
  complex-inf-inf 𝔉 (cmp⇔ ω₀ ω₁) | ⊕.inr (_ ▸ _ ▸ ⊢ω₀) with complex-inf-inf 𝔉 ω₁
  complex-inf-inf 𝔉 (cmp⇔ ω₀ ω₁) | ⊕.inr (_ ▸ _ ▸ ⊢ω₀) | ⊕.inl κ₁ =
    ⊕.inl λ { (_ ▸ _ ▸ cmp⇔ ⊢ω₀′ ⊢ω₁) → κ₁ (_ ▸ _ ▸ ⊢ω₁) }
  complex-inf-inf 𝔉 (cmp⇔ ω₀ ω₁) | ⊕.inr (_ ▸ _ ▸ ⊢ω₀) | ⊕.inr (_ ▸ _ ▸ ⊢ω₁) =
    ⊕.inr (_ ▸ _ ▸ cmp⇔ ⊢ω₀ ⊢ω₁)
  complex-inf-inf 𝔉 (cmp⇕ ω₁ ω₀) with complex-inf-inf 𝔉 ω₁
  complex-inf-inf 𝔉 (cmp⇕ ω₁ ω₀) | ⊕.inl κ₀ =
    ⊕.inl λ { (_ ▸ _ ▸ cmp⇕ ⊢ω₁ ⊢ω₀) → κ₀ (_ ▸ _ ▸ ⊢ω₁) }
  complex-inf-inf 𝔉 (cmp⇕ ω₁ ω₀) | ⊕.inr (Ξ ▸ Δ ▸ ⊢ω₁) with complex-inf-chk 𝔉 Ξ ω₀
  complex-inf-inf 𝔉 (cmp⇕ ω₁ ω₀) | ⊕.inr (Ξ ▸ Δ ▸ ⊢ω₁) | ⊕.inl κ₁ =
    ⊕.inl λ { (_ ▸ _ ▸ cmp⇕ ⊢ω₁′ ⊢ω₀) → κ₁ (_ ▸ ≡.coe* (λ X → _ ⊩ _ ∈ _ ⇒ X) (⊗.fst (complex-unique ⊢ω₁′ ⊢ω₁)) ⊢ω₀) }
  complex-inf-inf 𝔉 (cmp⇕ ω₁ ω₀) | ⊕.inr (_ ▸ _ ▸ ⊢ω₁) | ⊕.inr (_ ▸ ⊢ω₀) =
    ⊕.inr (_ ▸ _ ▸ cmp⇕ ⊢ω₁ ⊢ω₀)

face-inf : Ctx → Face → Maybe Arity
face-inf 𝔉 𝔣 with face-inf-inf 𝔉 𝔣
face-inf 𝔉 𝔣 | ⊕.inl _ = no
face-inf 𝔉 𝔣 | ⊕.inr (Γ ▸ Δ ▸ _) = so (Γ ⇒ Δ)

module Test where
  𝔏₀ : Sig
  𝔏₀ =
    let Δ = [] in
    let Δ = ▸δ "bool" ([] ⇒ []) ∷ Δ in
    Δ

  𝔏₁ : Sig
  𝔏₁ =
    let Δ = [] in
    let Δ = ▸δ "ff" ([] ⇒ var "bool" ∷ []) ∷ Δ in
    let Δ = ▸δ "tt" ([] ⇒ var "bool" ∷ []) ∷ Δ in
    let Δ = ▸δ "and" (var "bool" ∷ var "bool" ∷ [] ⇒ var "bool" ∷ []) ∷ Δ in
    Δ

  𝔏₂ : Sig
  𝔏₂ =
    let Δ = [] in
    let Δ = ▸δ "and/ff/ff" (cut (var "and") (step (var "ff") (step (var "ff") (stop []))) ∷ [] ⇒ var "bool" ∷ []) ∷ Δ in
    Δ

  𝔉 : Ctx
  𝔉 = 𝔏₂ ∷ 𝔏₁ ∷ 𝔏₀ ∷ []

  test₀ : _
  test₀ = face-inf 𝔉 (var "bool")

  test₁ : _
  test₁ = face-inf 𝔉 (cut (var "and") (step (var "ff") (step (var "ff") (stop []))))
