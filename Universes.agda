{-# OPTIONS --without-K --exact-split --safe #-}

module Universes where

open import Agda.Primitive public renaming
  ( Level to Universe
  ; lzero to U₀
  ; lsuc  to _⁺
  ; Setω  to Uω
  )
  using (_⊔_)

Type = λ ℓ → Set ℓ

El : (U : Universe) → Type (U ⁺)
El U = Type U


U₁ = U₀ ⁺
U₂ = U₁ ⁺
U₃ = U₂ ⁺

_⁺⁺ : Universe → Universe
U ⁺⁺ = U ⁺ ⁺

universe-of : {U : Universe} (X : El U) → Universe
universe-of {U} X = U
