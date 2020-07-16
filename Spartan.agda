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
one-rec B b _ = b

!one : {X : El U} → X → One
!one _ = ⋆






