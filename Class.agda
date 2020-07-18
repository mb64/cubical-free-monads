{-# OPTIONS --cubical --safe #-}

module Class where

open import Cubical.Core.Everything
open import Function.Base using (id; _$_)

private
  variable
    A B C : Set
    ℓ ℓ′ ℓ″ : Level

-- Custom non-dependent definition, since the one in the prelude is too general
_∘_ : {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

infixr 9 _∘_

record Functor (F : Set → Set₁) : Set₂ where
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

record Applicative (F : Set → Set₁) : Set₂ where
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

record Monad (M : Set → Set₁) : Set₂ where
  infixl 1 _>>=_

  field
    applicative : Applicative M
    _>>=_ : M A → (A → M B) → M B

  open Applicative applicative public

  return : A → M A
  return = pure

  field
    monad-left-id
      : (a : A)
      → (f : A → M B)
      → (return a >>= f) ≡ f a
    monad-right-id
      : (m : M A)
      → (m >>= return) ≡ m
    monad-assoc
      : (m : M A)
      → (f : A → M B)
      → (g : B → M C)
      → (m >>= f >>= g) ≡ (m >>= (λ x → f x >>= g))
