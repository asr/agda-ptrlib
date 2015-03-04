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
pip : {A : Set} → (¬ A → ⊥) → A
pip h = case (λ a → a) (λ ¬a → ⊥-elim (h ¬a)) pem

-- The propositional principle of identity `p → p` [da Costa and de
-- Ronde 2014].
ppi : {A : Set} → A → A
ppi a = a

-- The propositional principle of identity `p → p` [da Costa and de
-- Ronde 2014] by contradiction.
ppi→← : {A : Set} → A → A
ppi→← {A} = pip helper
  where helper : ¬ (A → A) → ⊥
        helper h = h (λ a → a)

-- The propositional principle of identity `p → p` [da Costa and de
-- Ronde 2014] by contradiction (simplified proof).
ppi→←' : {A : Set} → A → A
ppi→←' = pip (λ h → h (λ a → a))

-- Modus pones.
mp : {A B : Set} → A → (A → B) → B
mp a a→b = a→b a

-- Modus pones by contradiction.
mp→← : {A B : Set} → A → (A → B) → B
mp→← {B = B} a a→b = pip helper
  where helper : ¬ B → ⊥
        helper h = h (a→b a)

-- Modus pones by contradiction (simplified proof).
mp→←' : {A B : Set} → A → (A → B) → B
mp→←' {B = B} a a→b = pip (λ h → h (a→b a))

------------------------------------------------------------------------------
-- References

-- da Costa, N.C.A. and de Ronde, C. (2014). Non-reflexive Logical
-- Foundation for Quantum Mechanics. Foundations of Physics 44.12,
-- pp. 1369–1380.
