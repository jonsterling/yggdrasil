{-# OPTIONS --experimental-irrelevance --type-in-type #-}
module Main where

open import Prelude.List
open import Prelude.String

open List
  using (_++_)

pattern · = []

Name : Set
Name = String

record Op : Set where
  no-eta-equality
  constructor ▸o
  field
    ϑ : Name

record Cell : Set where
  no-eta-equality
  constructor ▸c
  field
    f : Name

mutual
  data Forest : Set where
    ε : Forest
    φ : (f : Tree) (ω : Forest) → Forest

  data Tree : Set where
    ε : (ϑ : Op) → Tree
    ψ : (f : Cell) (ω : Forest) → Tree

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
    op : Name
    ar : Arity
open Decl public
pattern ▸δ ϑ σ τ = ▸δ# ϑ (▸ar σ τ)

Sig : Set
Sig = List Decl

Ctx : Set
Ctx = List Sig

module Test where
  𝔏₀ : Sig
  𝔏₀ =
    let Δ = · in
    let Δ = ▸δ "bool" · (ψ (▸c "*") ε) ∷ Δ in
    Δ

  𝔏₁ : Sig
  𝔏₁ =
    let Δ = · in
    let Δ = ▸δ "ff" · (ψ (▸c "bool") ε) ∷ Δ in
    let Δ = ▸δ "tt" · (ψ (▸c "bool") ε) ∷ Δ in
    let Δ = ▸δ "and"
            (ψ (▸c "bool") ε ∷
             ψ (▸c "bool") ε ∷
             ·)
            (ψ (▸c "bool") ε) ∷ Δ in
    Δ

  𝔏₂ : Sig
  𝔏₂ =
    let Δ = · in
    let Δ = ▸δ "and-ff-ff"
            (ψ (▸c "and")
               (φ (ψ (▸c "ff") ε)
               (φ (ψ (▸c "ff") ε)
               (ε))) ∷
             ·)
            (ψ (▸c "ff") ε) ∷ Δ in
    let Δ = ▸δ "and-ff-tt"
            (ψ (▸c "and")
               (φ (ψ (▸c "ff") ε)
               (φ (ψ (▸c "tt") ε)
               (ε))) ∷
             ·)
            (ψ (▸c "ff") ε) ∷ Δ in
    let Δ = ▸δ "and-tt-ff"
            (ψ (▸c "and")
               (φ (ψ (▸c "tt") ε)
               (φ (ψ (▸c "ff") ε)
               (ε))) ∷
             ·)
            (ψ (▸c "ff") ε) ∷ Δ in
    let Δ = ▸δ "and-tt-tt"
            (ψ (▸c "and")
               (φ (ψ (▸c "tt") ε)
               (φ (ψ (▸c "tt") ε)
               (ε))) ∷
             ·)
            (ψ (▸c "tt") ε) ∷ Δ in
    Δ
