{-# OPTIONS --cubical --safe #-}

module Interpreter where

open import Util
open import FreeM

-- Runs it in the identity monad
runFreeM : FreeM A → A
runFreeM (Pure x) = x
runFreeM (Bind x f) = runFreeM $ f $ runFreeM x
-- Since it's so simple, all these compute nicely
runFreeM (LeftId a f i) = runFreeM $ f a
runFreeM (RightId x i) = runFreeM x
runFreeM (Assoc x f g i) = runFreeM $ g $ runFreeM $ f $ runFreeM x
