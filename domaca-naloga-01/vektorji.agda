module vektorji where

open import naravna
open import fin

data Vec : Set → Nat → Set where
    [] : {A : Set} → Vec A zero
    _::_ : {A : Set} {n : Nat} → A → Vec A n → Vec A (suc n)

_++_ : {A : Set} {m n : Nat} → Vec A m → Vec A n → Vec A (m + n)
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

map : {A B : Set} {m : Nat} → (A → B) → Vec A m → Vec B m
map f [] = []
map f (x :: xs) = f x :: map f xs

hd : {A : Set} {m : Nat} → Vec A (suc m) → A
hd (x :: _) = x

_[_] : {A : Set} {n : Nat} -> Vec A n -> Fin n -> A
[] [ () ]
(x :: v) [ Fo ] = x
(x :: v) [ Fs ind ] = v [ ind ]

_[_]←_ : {A : Set} {n : Nat} -> Vec A n -> Fin n → A -> Vec A n
_[_]←_ [] ()
_[_]←_ (x :: xs) Fo v = v :: xs
_[_]←_ (x :: xs) (Fs i) v = x :: (xs [ i ]← v)
