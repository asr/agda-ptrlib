------------------------------------------------------------------------------
-- FOL theorems
------------------------------------------------------------------------------

{-# OPTIONS --exact-split              #-}
{-# OPTIONS --no-sized-types           #-}
{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Properties where

open import Base

------------------------------------------------------------------------------
-- The principle of indirect proof (proof by contradiction).
¬-elim : {A : Set} → (¬ A → ⊥) → A
¬-elim h = case (λ a → a) (λ ¬a → ⊥-elim (h ¬a)) pem

-- The propositional principle of identity `p → p`.
ppi : {A : Set} → A → A
ppi a = a

-- The propositional principle of identity `p → p` by contradiction.
ppi→← : {A : Set} → A → A
ppi→← {A} = ¬-elim helper
  where helper : ¬ (A → A) → ⊥
        helper h = h (λ a → a)
