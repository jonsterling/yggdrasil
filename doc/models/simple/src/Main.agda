{-# OPTIONS --experimental-irrelevance --type-in-type #-}
module Main where

open import Prelude.Bool
open import Prelude.List
open import Prelude.Path
open import Prelude.String

open List
  using (_++_)

pattern · = []

data Maybe (A : Set) : Set where
  no : Maybe A
  so : (a : A) → Maybe A

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
    ε : Forest
    φ : (t : Tree) (ω : Forest) → Forest

  data Tree : Set where
    ε : (● : Tp) → Tree
    ψ : (ϑ : Op) (ω : Forest) → Tree

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

  look : Ctx → Op → Maybe Arity
  look [] ϑ = no
  look (𝔏 ∷ Γ) ϑ with Sig.look 𝔏 ϑ
  … | no = look Γ ϑ
  … | α = α
open Ctx public
  using (Ctx)

module Test where
  𝔏₀ : Sig
  𝔏₀ =
    let Δ = · in
    let Δ = ▸δ "bool" · (ψ (▸op "*") ε) ∷ Δ in
    Δ

  𝔏₁ : Sig
  𝔏₁ =
    let Δ = · in
    let Δ = ▸δ "ff" · (ψ (▸op "bool") ε) ∷ Δ in
    let Δ = ▸δ "tt" · (ψ (▸op "bool") ε) ∷ Δ in
    let Δ = ▸δ "and"
            (ψ (▸op "bool") ε ∷
             ψ (▸op "bool") ε ∷
             ·)
            (ψ (▸op "bool") ε) ∷ Δ in
    Δ

  𝔏₂ : Sig
  𝔏₂ =
    let Δ = · in
    let Δ = ▸δ "and-ff-ff"
            (ψ (▸op "and")
               (φ (ψ (▸op "ff") ε)
               (φ (ψ (▸op "ff") ε)
               (ε))) ∷
             ·)
            (ψ (▸op "ff") ε) ∷ Δ in
    let Δ = ▸δ "and-ff-tt"
            (ψ (▸op "and")
               (φ (ψ (▸op "ff") ε)
               (φ (ψ (▸op "tt") ε)
               (ε))) ∷
             ·)
            (ψ (▸op "ff") ε) ∷ Δ in
    let Δ = ▸δ "and-tt-ff"
            (ψ (▸op "and")
               (φ (ψ (▸op "tt") ε)
               (φ (ψ (▸op "ff") ε)
               (ε))) ∷
             ·)
            (ψ (▸op "ff") ε) ∷ Δ in
    let Δ = ▸δ "and-tt-tt"
            (ψ (▸op "and")
               (φ (ψ (▸op "tt") ε)
               (φ (ψ (▸op "tt") ε)
               (ε))) ∷
             ·)
            (ψ (▸op "tt") ε) ∷ Δ in
    Δ

  Γ : Ctx
  Γ = 𝔏₂ ∷ 𝔏₁ ∷ 𝔏₀ ∷ []

  test
    : Ctx.look Γ (▸op "and")
    ≡ so
        (▸ar
          (ψ (▸op "bool") ε ∷ ψ (▸op "bool") ε ∷ [])
          (ψ (▸op "bool") ε))
  test = refl
