{-# OPTIONS --cubical --safe #-}

module test where

open import Cubical.Core.Everything

compPath : ∀ {ℓ} {A : Set ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
compPath {x = x} p q i = hcomp (λ j → λ { (i = i0) → x
                                        ; (i = i1) → q j })
                               (p i)

sym : ∀ {l} {A : Set l} {x y : A} → x ≡ y → y ≡ x
sym f i = f (~ i)

variable
  l l' l'' : Level
  A B C : Set

_∘_ : {A : Set l} {B : Set l'} {C : Set l''} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

infixr 9 _∘_

_$_ : {A : Set l} {B : Set l'} → (A → B) → A → B
f $ x = f x

infixr 0 _$_

id : {A : Set l} → A → A
id x = x

data FreeM : Set → Set₁ where
  Pure : A → FreeM A
  Bind : FreeM A → (A → FreeM B) → FreeM B
  LeftId : ∀ {A B}
    → (a : A)
    → (f : A → FreeM B)
    → Bind (Pure a) f ≡ f a
  RightId : ∀ {A}
    → (m : FreeM A)
    → Bind m Pure ≡ m
  Assoc : ∀ {A B C}
    → (m : FreeM A)
    → (f : A → FreeM B)
    → (g : B → FreeM C)
    → Bind (Bind m f) g ≡ Bind m (λ x → Bind (f x) g)

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

freem-functor : Functor FreeM
freem-functor .fmap f m = Bind m (Pure ∘ f)
freem-functor .fmap-id-legit m i = RightId m i
freem-functor .fmap-compose-legit m f g i
  = hcomp (λ j → λ { (i = i0) → Bind m (Pure ∘ f ∘ g)
                   ; (i = i1) → Assoc m (Pure ∘ g) (Pure ∘ f) (~ j)
                   })
          (Bind m (λ x → LeftId (g x) (Pure ∘ f) (~ i)))

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
    -- app-intchg
    --   : (u : F (A → B))
    --   → (y : A)
    --   → (u <*> pure y) ≡ (pure (_$ y) <*> u)

  open Functor functor public

freem-ap : Applicative FreeM
freem-ap .Applicative.functor = freem-functor
freem-ap .Applicative.pure = Pure
freem-ap .Applicative._<*>_ mf m = Bind mf (λ f → Bind m (Pure ∘ f))
freem-ap .Applicative.app-identity v i
  = hcomp (λ j → λ { (i = i0) → LeftId id (λ f → Bind v (Pure ∘ f)) (~ j)
                   ; (i = i1) → v
                   })
          (RightId v i)
freem-ap .Applicative.app-compose u v w
  -- For some reason, Agda doesn't like wildcards in cubical proofs. Oh well.
  -- Start: Pure _∘_ <*> u <*> v <*> w
  = compPath {y = Bind u (λ u' → Pure (u' ∘_)) <*> v <*> w}
           (λ i → LeftId _∘_ (λ f → Bind u (Pure ∘ f)) i <*> v <*> w)
  $ compPath {y = Bind u (λ u' → Bind (Pure (u' ∘_)) (λ c → Bind v (Pure ∘ c))) <*> w}
           (λ i → Assoc u (λ u' → Pure (u' ∘_)) (λ f → Bind v (Pure ∘ f)) i <*> w)
  $ compPath {y = Bind u (λ u' → Bind v (λ v' → Pure (u' ∘ v'))) <*> w}
           (λ i → Bind u (λ u' → LeftId (u' ∘_) (λ c → Bind v (Pure ∘ c)) i) <*> w)
  $ compPath {y = Bind u (λ u' → Bind (Bind v (λ v' → Pure (u' ∘ v'))) (λ f → Bind w (Pure ∘ f)))}
           (λ i → Assoc u (λ u' → Bind v (λ v' → Pure (u' ∘ v'))) (λ f → Bind w (Pure ∘ f)) i)
  $ compPath {y = Bind u (λ u' → Bind v (λ v' → Bind (Pure (u' ∘ v')) (λ f → Bind w (Pure ∘ f))))}
           (λ i → Bind u (λ u' → Assoc v (λ v' → Pure (u' ∘ v')) (λ f → Bind w (Pure ∘ f)) i))
  $ compPath {y = Bind u (λ u' → Bind v (λ v' → Bind w (Pure ∘ u' ∘ v')))}
           (λ i → Bind u (λ u' → Bind v (λ v' → LeftId (u' ∘ v') (λ f → Bind w (Pure ∘ f)) i)))
  $ compPath {y = Bind u (λ u' → Bind v (λ v' → Bind w (λ w' → Bind (Pure (v' w')) (Pure ∘ u'))))}
           (λ i → Bind u (λ u' → Bind v (λ v' → Bind w (λ w' → LeftId (v' w') (Pure ∘ u') (~ i)))))
  $ compPath {y = Bind u (λ u' → Bind v (λ v' → Bind (Bind w (Pure ∘ v')) (Pure ∘ u')))}
           (λ i → Bind u (λ u' → Bind v (λ v' → Assoc w (Pure ∘ v') (Pure ∘ u') (~ i))))
           (λ i → Bind u (λ u' → Assoc v (λ f → Bind w (Pure ∘ f)) (Pure ∘ u') (~ i)))
  -- End: Bind u (λ u' → Bind (Bind v (λ v' → Bind w (Pure ∘ v')) (Pure ∘ u'))
  where open Applicative freem-ap
freem-ap .Applicative.app-homo f x
  = compPath (LeftId f (λ f' → Bind (Pure x) (λ x' → Pure (f' x'))))
             (LeftId x (λ x' → Pure (f x')))
