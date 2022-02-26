module fin where

open import naravna using (ℕ; S; O; _+_)

data Fin : ℕ -> Set where
    Fo : {n : ℕ} -> Fin (S n)
    Fs : {n : ℕ} -> Fin n -> Fin (S n)

toℕ : {n : ℕ} → Fin n → ℕ
toℕ Fo = O
toℕ (Fs f) = S (toℕ f)

fromℕ : (n : ℕ) → Fin (S n)
fromℕ O = Fo
fromℕ (S n) = Fs (fromℕ n)

_↑_ : {m : ℕ} → Fin m → ∀ (n : ℕ) → Fin (m + n)
Fo ↑ n = Fo
Fs m ↑ n = Fs (m ↑ n)
