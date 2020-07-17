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

data ℕ : El U₀ where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

ℕ-ind : (P : ℕ → El U) → P 0 → ((n : ℕ) → P n → P (succ n)) → ((n : ℕ) → P n)
ℕ-ind P z s zero = z
ℕ-ind P z s (succ n) = s n (ℕ-ind P z s n)


ℕ-rec : (X : El U) → X → (ℕ → X → X) → (ℕ → X)
ℕ-rec X x sx n = ℕ-ind (λ _ → X) x sx n

ℕ-iter : (X : El U) → X → (X → X) → ℕ → X
ℕ-iter X x sx n = ℕ-rec X x (λ _ → sx) n

module Arithmetic where
  _+_ _×_ : ℕ → ℕ → ℕ

  x + y = ℕ-iter ℕ x succ y
  x × y = ℕ-iter ℕ 0 (x +_) y

  infixl 20 _+_
  infixl 21 _×_

module ℕ-order where
  _≤_ _≥_ : ℕ → ℕ → El U₀
  _≤_ = ℕ-iter
          (ℕ → El U₀)
          (λ _ → One)
          λ n≤ sm → ℕ-rec (El U₀) Zero (λ m _ → n≤ m) sm


  x ≥ y = y ≤ x
  infix 10 _≤_
  infix 10 _≥_

-- exercise
-- x ≤ y if and only if Σ z ꞉ ℕ , x + z ≡ y.
-- (x ≤ y) ≡ Σ z ꞉ ℕ , x + z ≡ y.

data _+_ {U V} (X : El U) (Y : El V) : El (U ⊔ V) where
  inl : X → X + Y
  inr : Y → X + Y

+-ind 
  : {X : El U} {Y : El V} (P : X + Y → El W)
  → ((x : X) → P (inl x))
  → ((y : Y) → P (inr y))
  → ((z : X + Y) → P z)
+-ind P inlP inrP (inl x) = inlP x
+-ind P inlP inrP (inr x) = inrP x

+-rec
  : {X : El U} {Y : El V} (Z : El W)
  → ((x : X) → Z)
  → ((y : Y) → Z)
  → ((z : X + Y) → Z)
+-rec Z inlZ inrZ z = +-ind (λ _ → Z) inlZ inrZ z

bool : El U₀
bool = One + One

pattern tt = inl ⋆
pattern ff = inr ⋆

bool-ind : (P : bool → El U) → P tt → P ff → ((b : bool) → P b)
bool-ind P then else = 
  +-ind 
    P 
    (one-ind (λ x → P (inl x)) then) 
    (one-ind (λ x → P (inr x)) else)


