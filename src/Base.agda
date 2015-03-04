------------------------------------------------------------------------------
-- First-order logic base
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Base where

infix  3 ¬_
infixr 1 _∨_

------------------------------------------------------------------------------
-- The empty type.
data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

------------------------------------------------------------------------------
-- Negation.
--
-- The underscore allows to write for example `¬ ¬ A` instead of `¬ (¬ A)`.
¬_ : Set → Set
¬ A = A → ⊥

-----------------------------------------------------------------------------
-- The disjunction data type.

data _∨_ (A B : Set) : Set where
  inj₁ : A → A ∨ B
  inj₂ : B → A ∨ B

case : ∀ {A B} → {C : Set} → (A → C) → (B → C) → A ∨ B → C
case f g (inj₁ a) = f a
case f g (inj₂ b) = g b

------------------------------------------------------------------------------
-- The principle of the excluded middle.

-- Since ATPs work in classical logic, we postulate the principle of
-- the exclude middle for working with this logic.

postulate pem : ∀ {A} → A ∨ ¬ A
