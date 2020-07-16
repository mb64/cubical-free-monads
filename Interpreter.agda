{-# OPTIONS --cubical --safe #-}

module Interpreter where

open import Util
open import FreeReader

-- Runs it in the reader monad
runFree : ∀ {R A} → R → FreeReader R A → A
runFree r (Pure x) = x
runFree r (Bind x f) = runFree r $ f $ runFree r x
runFree r Ask = r
-- Since it's so simple, all these compute nicely
runFree r (LeftId a f i) = runFree r $ f a
runFree r (RightId x i) = runFree r x
runFree r (Assoc x f g i) = runFree r $ g $ runFree r $ f $ runFree r x
