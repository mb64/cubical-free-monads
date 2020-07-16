{-# OPTIONS --cubical --safe #-}

module Util where

-- Various utility functions
-- They're probably in the stdlib, but IDK Agda well enough to know what to import

-- agda-mode Unicode Cheat Sheet
-- Char Emacs       Compose key
--  →   \r          ->
--  λ   \lambda     ll
--  ≡   \==         =_
--  ₁   \_1         _1
--  ₂   \_2         _2
--  ∘   \o
--  ∀   \forall     FA

open import Cubical.Core.Everything public

private
  variable
    l l' l'' : Level

compPath : ∀ {l} {A : Set l} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
compPath {x = x} p q i = hcomp (λ j → λ { (i = i0) → x
                                        ; (i = i1) → q j })
                               (p i)

_∘_ : {A : Set l} {B : Set l'} {C : Set l''} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

infixr 9 _∘_

_$_ : {A : Set l} {B : Set l'} → (A → B) → A → B
f $ x = f x

infixr 0 _$_

id : {A : Set l} → A → A
id x = x
