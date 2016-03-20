{-# OPTIONS --experimental-irrelevance --type-in-type #-}
module Main where

open import Agda.Primitive
open import Prelude.Bool
open import Prelude.Decidable
open import Prelude.Inspect
open import Prelude.List
open import Prelude.Maybe
open import Prelude.Monoidal
open import Prelude.Path
open import Prelude.Size
open import Prelude.String

open List
  using (_++_)

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
    ▸ε : Forest
    ▸φ : (ψ : Tree) (ω : Forest) → Forest

  data Tree : Set where
    ▸ε : (τ : Tp) → Tree
    ▸ψ : (ϑ : Op) (ω : Forest) → Tree

record Arity : Set where
  no-eta-equality
  constructor ▸ar
  field
    src : List Tree
    tgt : Tree
open Arity public

module Decl where
  record Decl : Set where
    no-eta-equality
    constructor ▸δ#
    field
      ϑ : Op
      α : Arity
  open Decl public
  pattern ▸δ ϑ σ τ = ▸δ# (▸op ϑ) (▸ar σ τ)

  ∂- : Decl → List Tree
  ∂- (▸δ ϑ σ τ) = σ

  ∂+ : Decl → Tree
  ∂+ (▸δ ϑ σ τ) = τ
open Decl public
  hiding (module Decl)
  using (Decl)
  using (▸δ#)
  using (▸δ)

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
      : Γ ⊩ ▸ε ∈ [] ⇉ []
    ▸φ
      : {ψ : Tree}{ω : Forest}{σ*λ σ*ρ τ* : List Tree}{τ : Tree}
      → Γ ⊢ ψ ∈ σ*λ ⇒ τ
      → Γ ⊩ ω ∈ σ*ρ ⇉ τ*
      → Γ ⊩ ▸φ ψ ω ∈ σ*λ ++ σ*ρ ⇉ τ ∷ τ*

  data _⊢_∈_⇒_ (Γ : Ctx) : (ψ : Tree) (σ* : List Tree) (τ : Tree) → Set where
    ▸ε
      : (τ : Tp)
      → Γ ⊢ ▸ε τ ∈ ▸ε τ ∷ [] ⇒ ▸ε τ
    ▸ψ
      : {ϑ : Op}{ω : Forest}{σ* τ* : List Tree}{τ : Tree}
      → Ctx.look Γ ϑ ≡ so (▸ar τ* τ)
      → Γ ⊩ ω ∈ σ* ⇉ τ*
      → Γ ⊢ ▸ψ ϑ ω ∈ σ* ⇒ τ
pattern ▸ψ≡ ϑ ω = ▸ψ {ϑ = ▸op ϑ} refl ω

forest-▸φ-inj
  : {ψ₀ ψ₁ : Tree}{ω₀ ω₁ : Forest}
  → _≡_ {A = Forest} (▸φ ψ₀ ω₀) (▸φ ψ₁ ω₁)
  → (ψ₀ ≡ ψ₁) ⊗ (ω₀ ≡ ω₁)
forest-▸φ-inj refl = refl , refl

tree-▸ε-inj
  : {τ₀ τ₁ : Tp}
  → _≡_ {A = Tree} (▸ε τ₀) (▸ε τ₁)
  → τ₀ ≡ τ₁
tree-▸ε-inj refl = refl

tree-▸ψ-inj
  : {ϑ₀ ϑ₁ : Op}{ω₀ ω₁ : Forest}
  → _≡_ {A = Tree} (▸ψ ϑ₀ ω₀) (▸ψ ϑ₁ ω₁)
  → (ϑ₀ ≡ ϑ₁) ⊗ (ω₀ ≡ ω₁)
tree-▸ψ-inj refl = refl , refl

▸ar-inj
  : {σ₀* σ₁* : List Tree}{τ₀ τ₁ : Tree}
  → ▸ar σ₀* τ₀ ≡ ▸ar σ₁* τ₁
  → (σ₀* ≡ σ₁*) ⊗ (τ₀ ≡ τ₁)
▸ar-inj refl = refl , refl

▸tp-inj
  : {τ₀ τ₁ : Name}
  → ▸tp τ₀ ≡ ▸tp τ₁
  → τ₀ ≡ τ₁
▸tp-inj refl = refl

▸op-inj
  : {ϑ₀ ϑ₁ : Name}
  → ▸op ϑ₀ ≡ ▸op ϑ₁
  → ϑ₀ ≡ ϑ₁
▸op-inj refl = refl

tp-eq
  : (τ₀ τ₁ : Tp)
  → Decidable (τ₀ ≡ τ₁)
tp-eq (▸tp τ₀) (▸tp τ₁) with τ₀ String.≟ τ₁
tp-eq (▸tp τ₀) (▸tp τ₁) | ⊕.inl κ =
  ⊕.inl λ π → κ (▸tp-inj π)
tp-eq (▸tp τ₀) (▸tp τ₁) | ⊕.inr π =
  ⊕.inr (≡.ap¹ ▸tp π)

op-eq
  : (ϑ₀ ϑ₁ : Op)
  → Decidable (ϑ₀ ≡ ϑ₁)
op-eq (▸op ϑ₀) (▸op ϑ₁) with ϑ₀ String.≟ ϑ₁
op-eq (▸op ϑ₀) (▸op ϑ₁) | ⊕.inl κ =
  ⊕.inl λ π → κ (▸op-inj π)
op-eq (▸op ϑ₀) (▸op ϑ₁) | ⊕.inr π =
  ⊕.inr (≡.ap¹ ▸op π)

{-# TERMINATING #-}
-- FIXME: could fix this by defining list locally but probably not worth it
mutual
  forest-eq : (ω₀ ω₁ : Forest) → Decidable (ω₀ ≡ ω₁)
  forest-eq ▸ε ▸ε =
    ⊕.inr refl
  forest-eq ▸ε (▸φ ψ₁ ω₁) =
    ⊕.inl λ()
  forest-eq (▸φ ψ₀ ω₀) ▸ε =
    ⊕.inl λ()
  forest-eq (▸φ ψ₀ ω₀) (▸φ ψ₁ ω₁) with tree-eq ψ₀ ψ₁
  forest-eq (▸φ ψ₀ ω₀) (▸φ ψ₁ ω₁) | ⊕.inl κ₀ =
    ⊕.inl λ π₀ → κ₀ (⊗.fst (forest-▸φ-inj π₀))
  forest-eq (▸φ ψ₀ ω₀) (▸φ ψ₁ ω₁) | ⊕.inr π₀ with forest-eq ω₀ ω₁
  forest-eq (▸φ ψ₀ ω₀) (▸φ ψ₁ ω₁) | ⊕.inr π₀ | ⊕.inl κ₁ =
    ⊕.inl λ π₁ → κ₁ (⊗.snd (forest-▸φ-inj π₁))
  forest-eq (▸φ ψ₀ ω₀) (▸φ ψ₁ ω₁) | ⊕.inr π₀ | ⊕.inr π₁ =
    ⊕.inr (≡.ap¹ (λ x → ▸φ x _) π₀ ≡.⟓ ≡.ap¹ (▸φ _) π₁)

  tree-eq : (ψ₀ ψ₁ : Tree) → Decidable (ψ₀ ≡ ψ₁)
  tree-eq (▸ε τ₀) (▸ε τ₁) with tp-eq τ₀ τ₁
  tree-eq (▸ε τ₀) (▸ε τ₁) | ⊕.inl κ =
    ⊕.inl λ π → κ (tree-▸ε-inj π)
  tree-eq (▸ε τ₀) (▸ε τ₁) | ⊕.inr π =
    ⊕.inr (≡.ap¹ ▸ε π)
  tree-eq (▸ε τ₀) (▸ψ ϑ₁ ω₁) =
    ⊕.inl λ()
  tree-eq (▸ψ ϑ₀ ω₀) (▸ε τ₁) =
    ⊕.inl λ()
  tree-eq (▸ψ ϑ₀ ω₀) (▸ψ ϑ₁ ω₁) with op-eq ϑ₀ ϑ₁
  tree-eq (▸ψ ϑ₀ ω₀) (▸ψ ϑ₁ ω₁) | ⊕.inl κ₀ =
    ⊕.inl λ π → κ₀ (⊗.fst (tree-▸ψ-inj π))
  tree-eq (▸ψ ϑ₀ ω₀) (▸ψ ϑ₁ ω₁) | ⊕.inr π₀ with forest-eq ω₀ ω₁
  tree-eq (▸ψ ϑ₀ ω₀) (▸ψ ϑ₁ ω₁) | ⊕.inr π₀ | ⊕.inl κ₁ =
    ⊕.inl λ π₁ → κ₁ (⊗.snd (tree-▸ψ-inj π₁))
  tree-eq (▸ψ ϑ₀ ω₀) (▸ψ ϑ₁ ω₁) | ⊕.inr π₀ | ⊕.inr π₁ =
    ⊕.inr (≡.ap¹ (λ x → ▸ψ x _) π₀ ≡.⟓ ≡.ap¹ (▸ψ _) π₁)

mutual
  ⊢tree-unique
    : {Γ : Ctx}{ψ : Tree}{σ₀* σ₁* : List Tree}{τ₀ τ₁ : Tree}
    → Γ ⊢ ψ ∈ σ₀* ⇒ τ₀
    → Γ ⊢ ψ ∈ σ₁* ⇒ τ₁
    → (σ₀* ≡ σ₁*) ⊗ (τ₀ ≡ τ₁)
  ⊢tree-unique (▸ε τ) (▸ε .τ) =
    refl , refl
  ⊢tree-unique (▸ψ ⊢ϑ₀ ⊢ω₀) (▸ψ ⊢ϑ₁ ⊢ω₁) with ⊢forest-unique ⊢ω₀ ⊢ω₁
  ⊢tree-unique (▸ψ ⊢ϑ₀ ⊢ω₀) (▸ψ ⊢ϑ₁ ⊢ω₁) | refl , refl =
    refl , (⊗.snd (▸ar-inj (Maybe.⊢.so-inj (⊢ϑ₀ ≡.⁻¹ ≡.⟓ ⊢ϑ₁))))

  ⊢forest-unique
    : {Γ : Ctx}{ω : Forest}{σ₀* σ₁* τ₀* τ₁* : List Tree}
    → Γ ⊩ ω ∈ σ₀* ⇉ τ₀*
    → Γ ⊩ ω ∈ σ₁* ⇉ τ₁*
    → (σ₀* ≡ σ₁*) ⊗ (τ₀* ≡ τ₁*)
  ⊢forest-unique ▸ε ▸ε =
    refl , refl
  ⊢forest-unique
    (▸φ {σ*λ = σ*λ₀}{σ*ρ₀}{τ₀*}{τ₀} ⊢ψ₀ ⊢ω₀)
    (▸φ {σ*λ = σ*λ₁}{σ*ρ₁}{τ₁*}{τ₁} ⊢ψ₁ ⊢ω₁)
    with ⊢tree-unique ⊢ψ₀ ⊢ψ₁ | ⊢forest-unique ⊢ω₀ ⊢ω₁
  ... | (π₀₀ , π₀₁) | (π₁₀ , π₁₁)
    = ≡.ap¹ (_++ σ*ρ₀) π₀₀ ≡.⟓ ≡.ap¹ (σ*λ₁ ++_) π₁₀
    , ≡.ap¹ (_∷ τ₀*) π₀₁ ≡.⟓ ≡.ap¹ (τ₁ ∷_) π₁₁

mutual
  tree-inf-chk
    : (Γ : Ctx)
    → (τ : Tree)
    → (ψ : Tree)
    → Decidable (Σ[ List Tree ∋ σ* ] (Γ ⊢ ψ ∈ σ* ⇒ τ))
  tree-inf-chk Γ τ ψ with tree-inf-inf Γ ψ
  tree-inf-chk Γ τ ψ | ⊕.inl κ =
    ⊕.inl λ { (σ* ▸ ⊢ψ) → κ (σ* ▸ τ ▸ ⊢ψ) }
  tree-inf-chk Γ τ ψ | ⊕.inr (σ* ▸ τ′ ▸ ⊢ψ) with tree-eq τ τ′
  tree-inf-chk Γ τ ψ | ⊕.inr (σ* ▸ τ′ ▸ ⊢ψ) | ⊕.inl κ =
    ⊕.inl λ { (_ ▸ ⊢ψ′) → κ (⊗.snd (⊢tree-unique ⊢ψ′ ⊢ψ)) }
  tree-inf-chk Γ τ ψ | ⊕.inr (σ* ▸ .τ ▸ ⊢ψ) | ⊕.inr refl =
    ⊕.inr (σ* ▸ ⊢ψ)

  tree-inf-inf
    : (Γ : Ctx)
    → (ψ : Tree)
    → Decidable (Σ[ List Tree ∋ σ* ] Σ[ Tree ∋ τ ] (Γ ⊢ ψ ∈ σ* ⇒ τ))
  tree-inf-inf Γ (▸ε ●) =
    ⊕.inr ((▸ε ● ∷ []) ▸ (▸ε ●) ▸ ▸ε ●)
  tree-inf-inf Γ (▸ψ ϑ ω) with Ctx.look Γ ϑ | inspect (Ctx.look Γ) ϑ
  tree-inf-inf Γ (▸ψ ϑ ω) | no | [ ⊢ϑ ] =
    ⊕.inl λ { (σ ▸ τ ▸ ▸ψ ⊢ϑ′ ⊢ω) → Maybe.⊢.no≢so (⊢ϑ ≡.⁻¹ ≡.⟓ ⊢ϑ′) }
  tree-inf-inf Γ (▸ψ ϑ ω) | so (▸ar τ* τ) | [ ⊢ϑ ] with forest-inf-chk Γ τ* ω
  tree-inf-inf Γ (▸ψ ϑ ω) | so (▸ar τ* τ) | [ ⊢ϑ ] | ⊕.inl κ =
    ⊕.inl λ
      { (σ* ▸ τ′ ▸ ▸ψ {τ* = τ*′} ⊢ϑ′ ⊢ω) → κ
          (σ* ▸
            ≡.coe*
              (λ X → Γ ⊩ ω ∈ σ* ⇉ X)
              (⊗.fst (▸ar-inj (Maybe.⊢.so-inj (⊢ϑ′ ≡.⁻¹ ≡.⟓ ⊢ϑ))))
              ⊢ω)
      }
  tree-inf-inf Γ (▸ψ ϑ ω) | so (▸ar τ* τ) | [ φ ] | ⊕.inr (σ* ▸ ⊢ω) =
    ⊕.inr (σ* ▸ τ ▸ ▸ψ φ ⊢ω)

  forest-inf-chk
    : (Γ : List Sig)
    → (τ* : List Tree)
    → (ω : Forest)
    → Decidable (Σ[ List Tree ∋ σ* ] (Γ ⊩ ω ∈ σ* ⇉ τ*))
  forest-inf-chk Γ [] ▸ε =
    ⊕.inr (_ ▸ ▸ε)
  forest-inf-chk Γ (τ ∷ τ*) ▸ε =
    ⊕.inl λ { (_ ▸ ()) }
  forest-inf-chk Γ [] (▸φ ψ ω) =
    ⊕.inl λ { (_ ▸ ()) }
  forest-inf-chk Γ (τ ∷ τ*) (▸φ ψ ω) with tree-inf-chk Γ τ ψ
  forest-inf-chk Γ (τ ∷ τ*) (▸φ ψ ω) | ⊕.inl κ₀ =
    ⊕.inl λ { (_ ▸ ▸φ ⊢ψ ⊢ω) → κ₀ (_ ▸ ⊢ψ) }
  forest-inf-chk Γ (τ ∷ τ*) (▸φ ψ ω) | ⊕.inr ⊢ψ with forest-inf-chk Γ τ* ω
  forest-inf-chk Γ (τ ∷ τ*) (▸φ ψ ω) | ⊕.inr ⊢ψ | ⊕.inl κ₁ =
    ⊕.inl λ { (_ ▸ ▸φ ⊢ψ ⊢ω) → κ₁ (_ ▸ ⊢ω) }
  forest-inf-chk Γ (τ ∷ τ*) (▸φ ψ ω) | ⊕.inr (σ*λ ▸ ⊢ψ) | ⊕.inr (σ*ρ ▸ ⊢ω) =
    ⊕.inr (σ*λ ++ σ*ρ ▸ ▸φ ⊢ψ ⊢ω)

module Test where
  𝔏₀ : Sig
  𝔏₀ =
    let Δ = [] in
    let Δ = ▸δ "bool" [] (▸ψ (▸op "*") ▸ε) ∷ Δ in
    Δ

  𝔏₁ : Sig
  𝔏₁ =
    let Δ = [] in
    let Δ = ▸δ "ff" [] (▸ψ (▸op "bool") ▸ε) ∷ Δ in
    let Δ = ▸δ "tt" [] (▸ψ (▸op "bool") ▸ε) ∷ Δ in
    let Δ = ▸δ "and"
            (▸ψ (▸op "bool") ▸ε ∷
             ▸ψ (▸op "bool") ▸ε ∷
             [])
            (▸ψ (▸op "bool") ▸ε) ∷ Δ in
    Δ

  𝔏₂ : Sig
  𝔏₂ =
    let Δ = [] in
    let Δ = ▸δ "and-ff-ff"
            (▸ψ (▸op "and")
               (▸φ (▸ψ (▸op "ff") ▸ε)
               (▸φ (▸ψ (▸op "ff") ▸ε)
               (▸ε))) ∷
             [])
            (▸ψ (▸op "ff") ▸ε) ∷ Δ in
    let Δ = ▸δ "and-ff-tt"
            (▸ψ (▸op "and")
               (▸φ (▸ψ (▸op "ff") ▸ε)
               (▸φ (▸ψ (▸op "tt") ▸ε)
               (▸ε))) ∷
             [])
            (▸ψ (▸op "ff") ▸ε) ∷ Δ in
    let Δ = ▸δ "and-tt-ff"
            (▸ψ (▸op "and")
               (▸φ (▸ψ (▸op "tt") ▸ε)
               (▸φ (▸ψ (▸op "ff") ▸ε)
               (▸ε))) ∷
             [])
            (▸ψ (▸op "ff") ▸ε) ∷ Δ in
    let Δ = ▸δ "and-tt-tt"
            (▸ψ (▸op "and")
               (▸φ (▸ψ (▸op "tt") ▸ε)
               (▸φ (▸ψ (▸op "tt") ▸ε)
               (▸ε))) ∷
             [])
            (▸ψ (▸op "tt") ▸ε) ∷ Δ in
    let Δ = ▸δ "and-tt-tt-idn" -- FIXME: free structure?
            []
            (▸ψ
              (▸op "and")
              (▸φ (▸ψ (▸op "tt") ▸ε)
              (▸φ (▸ψ (▸op "tt") ▸ε)
              (▸ε)))) ∷ Δ in
    Δ

  Γ : Ctx
  Γ = 𝔏₂ ∷ 𝔏₁ ∷ 𝔏₀ ∷ []

  test₀
    : Ctx.look Γ (▸op "and")
    ≡ so
        (▸ar
          (▸ψ (▸op "bool") ▸ε ∷ ▸ψ (▸op "bool") ▸ε ∷ [])
          (▸ψ (▸op "bool") ▸ε))
  test₀ = refl

  test₁
    : Γ ⊢ ▸ψ (▸op "ff") ▸ε
        ∈ []
        ⇒ ▸ψ (▸op "bool") ▸ε
  test₁ = ▸ψ≡ "ff" ▸ε

  test₂
    : Γ ⊢ ▸ψ (▸op "and")
            (▸φ (▸ψ (▸op "ff") ▸ε)
            (▸φ (▸ψ (▸op "ff") ▸ε)
            (▸ε)))
        ∈ []
        ⇒ ▸ψ (▸op "bool") ▸ε
  test₂ = ▸ψ≡ "and" (▸φ (▸ψ≡ "ff" ▸ε) (▸φ (▸ψ≡ "ff" ▸ε) ▸ε))

  test₃
    : Γ ⊢ ▸ψ (▸op "and-tt-tt") (▸φ (▸ψ (▸op "and-tt-tt-idn") ▸ε) ▸ε)
        ∈ []
        ⇒ ▸ψ (▸op "tt") ▸ε
  test₃ = ▸ψ≡ "and-tt-tt" (▸φ (▸ψ≡ "and-tt-tt-idn" ▸ε) ▸ε)

  test₄
    : _≡_
      (tree-inf-inf Γ
        (▸ψ (▸op "and")
          (▸φ (▸ψ (▸op "ff") ▸ε)
          (▸φ (▸ψ (▸op "ff") ▸ε)
          (▸ε)))))
      (⊕.inr
        ( []
        ▸ ▸ψ (▸op "bool") ▸ε
        ▸ ▸ψ≡ "and" (▸φ (▸ψ≡ "ff" ▸ε) (▸φ (▸ψ≡ "ff" ▸ε) ▸ε))))
  test₄ = refl
