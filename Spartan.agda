{-# OPTIONS --without-K --exact-split --safe #-}

module Spartan where

open import Universes public

variable
  U V W T : Universe

data One : El U₀  where
  ⋆ : One

one-ind : (P : One → El U) → P ⋆ → ((x : One) -> P x)
one-ind P a ⋆ = a

one-rec : (B : El U) → B → (One → B)
one-rec B b x = one-ind (λ _ → B) b x

!one : {X : El U} → X → One
!one _ = ⋆

data Zero : El U₀ where

zero-ind : (P : Zero → El U) → ((x : Zero) → P x)
zero-ind P ()


zero-rec : (A : El U) → Zero -> A
zero-rec A z = zero-ind (λ _ → A) z

!zero : (A : El U) → Zero -> A
!zero = zero-rec

is-empty : El U → El U
is-empty X = X → Zero


¬ : El U → El U
¬ = is-empty


