module vektorji where

open import naravna

data Vec : Set → ℕ → Set where
    [] : {A : Set} → Vec A O
    _∷_ : {A : Set} {n : ℕ} → A → Vec A n → Vec A (S n)

_++_ : {A : Set} {m n : ℕ} → Vec A m → Vec A n → Vec A (m + n)
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ ({!   !} ++ ys)

map : {A B : Set} {m : ℕ} → (A → B) → Vec A m → Vec B m
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs