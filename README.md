# Verified (cubical) free monads

An experiment in Cubical Agda.

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

## Free monads are not legit monads

Free monads aren't real monads according to the [monad
laws](https://wiki.haskell.org/Monad_laws).  For example, for all monads
`m >>= return` should equal `m`.  However, in free monads, the data structure
`Bind m Return` is clearly not equal to `m`.

In a sense, free monads are simply deferring the responsibility of satisfying
the monad laws to the interpreter that actually runs `Bind`.

## They can be in Cubical Agda

This is where Cubical Agda and Higher Inductive Types come in.  With HITs, you
can define you own equalities, and functions that pattern match on them have to
prove that they respect that equality.

`FreeReader`, in `FreeReader.agda`, defines all of the monad laws as higher
inductive paths:

```agda
-- The Reader monad, as a free monad
data FreeReader (R : Set) : Set → Set₁ where
  Pure : A → FreeReader R A
  Bind : FreeReader R A → (A → FreeReader R B) → FreeReader R B
  Ask : FreeReader R R

  -- Monad laws
  LeftId : ∀ {A B}
    → (a : A)
    → (f : A → FreeReader R B)
    → Bind (Pure a) f ≡ f a
  RightId : ∀ {A}
    → (m : FreeReader R A)
    → Bind m Pure ≡ m
  Assoc : ∀ {A B C}
    → (m : FreeReader R A)
    → (f : A → FreeReader R B)
    → (g : B → FreeReader R C)
    → Bind (Bind m f) g ≡ Bind m (λ x → Bind (f x) g)
```

Then, it can be proven to follow the functor, applicative functor, and monad
laws.

(This is a lot better than without cubical type theory: usually, it's
impossible to even prove the *normal* Reader monad is a functor, since that
requires function extensionality.)

## File layout

 * `Class.agda` has the `Funtor`, `Applicative`, and `Monad` classes, including
   all their laws
 * `FreeReader.agda` has `FreeReader R`'s instances, including all the proofs
   that they're legit
 * `Interpreter.agda` has the `runFree` function, which runs `FreeReader`, and
   proves that it respects the monad laws

## Non-ASCII Unicode used

```
Char   Emacs
 →      \r
 λ      \lambda
 ≡      \==
 ₁      \_1
 ₂      \_2
 ∘      \o
 ∀      \forall
 ∙      \.
 ⟨      \<
 ⟩      \>
 ℓ      \ell
 ′      \'1
 ″      \'2
```
