{-# OPTIONS --cubical --safe #-}

module Class where

open import Util

private
  variable
    A B C : Set

record Functor (F : (Set → Set₁)) : Set₂ where
  field
    fmap : (A → B) → F A → F B
    fmap-id-legit : (m : F A) → fmap id m ≡ m
    fmap-compose-legit
      : (m : F A)
      → (f : B → C)
      → (g : A → B)
      → fmap (f ∘ g) m ≡ fmap f (fmap g m)
  _<$>_ : (A → B) → F A → F B
  f <$> x = fmap f x

open Functor

record Applicative (F : (Set → Set₁)) : Set₂ where
  infixl 4 _<*>_

  field
    functor : Functor F
    pure : A → F A
    _<*>_ : F (A → B) → F A → F B
    app-identity : (v : F A) → (pure id <*> v) ≡ v
    app-compose
      : (u : F (B → C))
      → (v : F (A → B))
      → (w : F A)
      → (pure _∘_ <*> u <*> v <*> w) ≡ (u <*> (v <*> w))
    app-homo
      : (f : A → B)
      → (x : A)
      → (pure f <*> pure x) ≡ pure (f x)
    app-intchg
      : (u : F (A → B))
      → (y : A)
      → (u <*> pure y) ≡ (pure (_$ y) <*> u)

  open Functor functor public
