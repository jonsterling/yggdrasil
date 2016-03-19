{-# OPTIONS --experimental-irrelevance --type-in-type #-}
module Main where

open import Prelude.Bool
open import Prelude.Decidable
open import Prelude.Inspect
open import Prelude.List
open import Prelude.Monoidal
open import Prelude.Path
open import Prelude.String

open List
  using (_++_)

data Maybe (A : Set) : Set where
  no : Maybe A
  so : (a : A) → Maybe A

no≢so : {A : Set}{a : A} (φ : no ≡ so a) → 𝟘
no≢so ()

Name : Set
Name = String

record Tp : Set where
  no-eta-equality
  constructor ▸tp
  field
    ● : Name

record Op : Set where
  no-eta-equality
  constructor ▸op
  field
    ϑ : Name

mutual
  data Forest : Set where
    ▸ε : (ψ* : List Tree) → Forest
    ▸φ : (ψ : Tree) (ω : Forest) → Forest

  data Tree : Set where
    ▸ε : (● : Tp) → Tree
    ▸ψ : (ϑ : Op) (ω : Forest) → Tree

postulate
  forest-≟ : (ω₀ ω₁ : Forest) → Decidable (ω₀ ≡ ω₁)
  tree-≟ : (ψ₀ ψ₁ : Tree) → Decidable (ψ₀ ≡ ψ₁)
  tree*-≟ : (ψ₀* ψ₁* : List Tree) → Decidable (ψ₀* ≡ ψ₁*)

record Arity : Set where
  no-eta-equality
  constructor ▸ar
  field
    src : List Tree
    tgt : Tree
open Arity public

record Decl : Set where
  no-eta-equality
  constructor ▸δ#
  field
    ϑ : Op
    α : Arity
pattern ▸δ ϑ σ τ = ▸δ# (▸op ϑ) (▸ar σ τ)

module Sig where
  Sig : Set
  Sig = List Decl

  look : (𝔏 : Sig) (ϑ : Op) → Maybe Arity
  look [] ϑ = no
  look (▸δ ϑ? σ τ ∷ 𝔏) (▸op ϑ) with String.⟦ ϑ? ≟ ϑ ⟧
  … | ff = look 𝔏 (▸op ϑ)
  … | tt = so (▸ar σ τ)
open Sig public
  using (Sig)

module Ctx where
  Ctx : Set
  Ctx = List Sig

  look : (Γ : Ctx) (ϑ : Op) → Maybe Arity
  look [] ϑ = no
  look (𝔏 ∷ Γ) ϑ with Sig.look 𝔏 ϑ
  … | no = look Γ ϑ
  … | α = α
open Ctx public
  using (Ctx)

infix 0 _⊩_∈_⇉_
infix 0 _⊢_∈_⇒_
mutual
  data _⊩_∈_⇉_ (Γ : Ctx) : (ω : Forest) (σ* τ : List Tree) → Set where
    ▸ε
      : (ω : List Tree)
      → Γ ⊩ ▸ε ω ∈ ω ⇉ ω -- FIXME: proper partial application
    ▸φ
      : {ψ : Tree}{ω : Forest}{σ*λ σ*ρ τ* : List Tree}{τ : Tree}
      → Γ ⊢ ψ ∈ σ*λ ⇒ τ
      → Γ ⊩ ω ∈ σ*ρ ⇉ τ*
      → Γ ⊩ ▸φ ψ ω ∈ (σ*λ ++ σ*ρ) ⇉ (τ ∷ τ*)

  data _⊢_∈_⇒_ (Γ : Ctx) : (t : Tree) (σ* : List Tree) (τ : Tree) → Set where
    ▸ε
      : (τ : Tp)
      → Γ ⊢ ▸ε τ ∈ (▸ε τ ∷ []) ⇒ (▸ε τ)
    ▸ψ
      : {ϑ : Op}{ω : Forest}{σ* τ* : List Tree}{τ : Tree}
      → Ctx.look Γ ϑ ≡ so (▸ar τ* τ)
      → Γ ⊩ ω ∈ σ* ⇉ τ*
      → Γ ⊢ (▸ψ ϑ ω) ∈ σ* ⇒ τ
pattern ▸ψ≡ ϑ ω = ▸ψ {ϑ = ▸op ϑ} refl ω

mutual
  tree-inf-chk
    : (Γ : Ctx)
    → (τ : Tree)
    → (ψ : Tree)
    → Decidable (Σ[ List Tree ∋ σ* ] (Γ ⊢ ψ ∈ σ* ⇒ τ))
  tree-inf-chk Γ τ ψ with tree-inf-inf Γ ψ
  tree-inf-chk Γ τ ψ | ⊕.inl κ =
    ⊕.inl λ { (σ* ▸ ⊢ψ) → κ (σ* ▸ τ ▸ ⊢ψ) }
  tree-inf-chk Γ τ ψ | ⊕.inr (σ* ▸ τ′ ▸ ⊢ψ) with tree-≟ τ τ′
  tree-inf-chk Γ τ ψ | ⊕.inr (σ* ▸ τ′ ▸ ⊢ψ) | ⊕.inl κ =
    ⊕.inl λ { (_ ▸ ⊢ψ) → {!!} } -- determinacy
  tree-inf-chk Γ τ ψ | ⊕.inr (σ* ▸ .τ ▸ ⊢ψ) | ⊕.inr refl =
    ⊕.inr (σ* ▸ ⊢ψ)

  tree-inf-inf
    : (Γ : Ctx)
    → (ψ : Tree)
    → Decidable (Σ[ List Tree ∋ σ* ] Σ[ Tree ∋ τ ] (Γ ⊢ ψ ∈ σ* ⇒ τ))
  tree-inf-inf Γ (▸ε ●) =
    ⊕.inr ((▸ε ● ∷ []) ▸ (▸ε ●) ▸ ▸ε ●)
  tree-inf-inf Γ (▸ψ ϑ ω) with Ctx.look Γ ϑ | inspect (Ctx.look Γ) ϑ
  tree-inf-inf Γ (▸ψ ϑ ω) | no | [ φ ] =
    ⊕.inl λ { (σ ▸ τ ▸ ▸ψ ϑ∈Γ ⊢ω) → no≢so (φ ≡.⁻¹ ≡.⟓ ϑ∈Γ) }
  tree-inf-inf Γ (▸ψ ϑ ω) | so (▸ar τ* τ) | [ φ ] with forest-inf-chk Γ τ* ω
  tree-inf-inf Γ (▸ψ ϑ ω) | so (▸ar τ* τ) | [ φ ] | ⊕.inl κ =
    ⊕.inl λ { (σ* ▸ τ′ ▸ ▸ψ {τ* = τ*′} ϑ∈Γ ⊢ω) → κ (σ* ▸ {!!}) } -- injective
  tree-inf-inf Γ (▸ψ ϑ ω) | so (▸ar τ* τ) | [ φ ] | ⊕.inr (σ* ▸ ⊢ω) =
    ⊕.inr (σ* ▸ τ ▸ ▸ψ φ ⊢ω)

  forest-inf-chk
    : (Γ : List Sig)
    → (τ* : List Tree)
    → (ω : Forest)
    → Decidable (Σ[ List Tree ∋ σ* ] (Γ ⊩ ω ∈ σ* ⇉ τ*))
  forest-inf-chk Γ τ* (▸ε ψ*) with tree*-≟ ψ* τ*
  forest-inf-chk Γ τ* (▸ε ψ*) | ⊕.inl κ =
    ⊕.inl λ { (ψ′* ▸ ⊢ω) → κ {!!} } -- determinacy via ▸ε
  forest-inf-chk Γ τ* (▸ε .τ*) | ⊕.inr refl =
    ⊕.inr (τ* ▸ ▸ε τ*)
  forest-inf-chk Γ [] (▸φ ψ ω) =
    ⊕.inl λ { (_ ▸ ()) }
  forest-inf-chk Γ (τ ∷ τ*) (▸φ ψ ω) with tree-inf-chk Γ τ ψ
  forest-inf-chk Γ (τ ∷ τ*) (▸φ ψ ω) | ⊕.inl κ =
    ⊕.inl {!!}
  forest-inf-chk Γ (τ ∷ τ*) (▸φ ψ ω) | ⊕.inr ⊢ψ with forest-inf-chk Γ τ* ω
  forest-inf-chk Γ (τ ∷ τ*) (▸φ ψ ω) | ⊕.inr ⊢ψ | ⊕.inl ⊢ω =
    ⊕.inl {!!}
  forest-inf-chk Γ (τ ∷ τ*) (▸φ ψ ω) | ⊕.inr (σ*λ ▸ ⊢ψ) | ⊕.inr (σ*ρ ▸ ⊢ω) =
    ⊕.inr (σ*λ ++ σ*ρ ▸ ▸φ ⊢ψ ⊢ω)

module Test where
  𝔏₀ : Sig
  𝔏₀ =
    let Δ = [] in
    let Δ = ▸δ "bool" [] (▸ψ (▸op "*") (▸ε [])) ∷ Δ in
    Δ

  𝔏₁ : Sig
  𝔏₁ =
    let Δ = [] in
    let Δ = ▸δ "ff" [] (▸ψ (▸op "bool") (▸ε [])) ∷ Δ in
    let Δ = ▸δ "tt" [] (▸ψ (▸op "bool") (▸ε [])) ∷ Δ in
    let Δ = ▸δ "and"
            (▸ψ (▸op "bool") (▸ε []) ∷
             ▸ψ (▸op "bool") (▸ε []) ∷
             [])
            (▸ψ (▸op "bool") (▸ε [])) ∷ Δ in
    Δ

  𝔏₂ : Sig
  𝔏₂ =
    let Δ = [] in
    let Δ = ▸δ "and-ff-ff"
            (▸ψ (▸op "and")
               (▸φ (▸ψ (▸op "ff") (▸ε []))
               (▸φ (▸ψ (▸op "ff") (▸ε []))
               (▸ε []))) ∷
             [])
            (▸ψ (▸op "ff") (▸ε [])) ∷ Δ in
    let Δ = ▸δ "and-ff-tt"
            (▸ψ (▸op "and")
               (▸φ (▸ψ (▸op "ff") (▸ε []))
               (▸φ (▸ψ (▸op "tt") (▸ε []))
               (▸ε []))) ∷
             [])
            (▸ψ (▸op "ff") (▸ε [])) ∷ Δ in
    let Δ = ▸δ "and-tt-ff"
            (▸ψ (▸op "and")
               (▸φ (▸ψ (▸op "tt") (▸ε []))
               (▸φ (▸ψ (▸op "ff") (▸ε []))
               (▸ε []))) ∷
             [])
            (▸ψ (▸op "ff") (▸ε [])) ∷ Δ in
    let Δ = ▸δ "and-tt-tt"
            (▸ψ (▸op "and")
               (▸φ (▸ψ (▸op "tt") (▸ε []))
               (▸φ (▸ψ (▸op "tt") (▸ε []))
               (▸ε []))) ∷
             [])
            (▸ψ (▸op "tt") (▸ε [])) ∷ Δ in
    let Δ = ▸δ "and-tt-tt-idn" -- FIXME: free structure?
            []
            (▸ψ
              (▸op "and")
              (▸φ (▸ψ (▸op "tt") (▸ε []))
              (▸φ (▸ψ (▸op "tt") (▸ε []))
              (▸ε [])))) ∷ Δ in
    Δ

  Γ : Ctx
  Γ = 𝔏₂ ∷ 𝔏₁ ∷ 𝔏₀ ∷ []

  test₀
    : Ctx.look Γ (▸op "and")
    ≡ so
        (▸ar
          (▸ψ (▸op "bool") (▸ε []) ∷ ▸ψ (▸op "bool") (▸ε []) ∷ [])
          (▸ψ (▸op "bool") (▸ε [])))
  test₀ = refl

  test₁
    : Γ ⊢ ▸ψ (▸op "ff") (▸ε [])
        ∈ []
        ⇒ ▸ψ (▸op "bool") (▸ε [])
  test₁ = ▸ψ≡ "ff" (▸ε [])

  test₂
    : Γ ⊢ ▸ψ (▸op "and")
            (▸φ (▸ψ (▸op "ff") (▸ε []))
            (▸φ (▸ψ (▸op "ff") (▸ε []))
             (▸ε [])))
        ∈ []
        ⇒ ▸ψ (▸op "bool") (▸ε [])
  test₂ = ▸ψ≡ "and" (▸φ (▸ψ≡ "ff" (▸ε [])) (▸φ (▸ψ≡ "ff" (▸ε [])) (▸ε [])))

  test₃
    : Γ ⊢ ▸ψ (▸op "and") (▸φ (▸ψ (▸op "ff") (▸ε [])) (▸ε _))
        ∈ ▸ψ (▸op "bool") (▸ε []) ∷ []
        ⇒ ▸ψ (▸op "bool") (▸ε [])
  test₃ = ▸ψ≡ "and" (▸φ (▸ψ≡ "ff" (▸ε [])) (▸ε _))

  test₄
    : Γ ⊢ ▸ψ (▸op "and-tt-tt") (▸φ (▸ψ (▸op "and-tt-tt-idn") (▸ε [])) (▸ε []))
        ∈ []
        ⇒ ▸ψ (▸op "tt") (▸ε [])
  test₄ = ▸ψ≡ "and-tt-tt" (▸φ (▸ψ≡ "and-tt-tt-idn" (▸ε [])) (▸ε []))

  test₅
    : Γ ⊢ ▸ψ (▸op "and-tt-tt") (▸ε _)
        ∈ ▸ψ (▸op "and") (▸φ (▸ψ (▸op "tt") (▸ε [])) (▸φ (▸ψ (▸op "tt") (▸ε [])) (▸ε []))) ∷ []
        ⇒ ▸ψ (▸op "tt") (▸ε [])
  test₅ = ▸ψ≡ "and-tt-tt" (▸ε _)
