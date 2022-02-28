module fin where

open import naravna using (Nat; suc; zero; _+_)

data Fin : Nat -> Set where
    Fo : {n : Nat} -> Fin (suc n)
    Fs : {n : Nat} -> Fin n -> Fin (suc n)

toNat : {n : Nat} → Fin n → Nat
toNat Fo = zero
toNat (Fs f) = suc (toNat f)

fromNat : (n : Nat) → Fin (suc n)
fromNat zero = Fo
fromNat (suc n) = Fs (fromNat n)

_↑_ : {m : Nat} → Fin m → ∀ (n : Nat) → Fin (m + n)
Fo ↑ n = Fo
Fs m ↑ n = Fs (m ↑ n)
