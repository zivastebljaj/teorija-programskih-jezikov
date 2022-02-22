module naravna where

-- naravna števila bi lahko v Agdi definirali na sledeči način

data Nat : Set where
    -- za razliko od OCamla moramo vedno povedati tudi kodomeno konstruktorja,
    -- saj se bo lahko spreminjala
    O : Nat
    S : Nat -> Nat 

-- vsako definicijo najprej začnemo z deklaracijo tipa

plus : Nat -> Nat -> Nat
plus O n = n
plus (S m) n = S (plus m n)

-- če ime definicije vsebuje podčrtaje, lahko uporabljamo miksfiksni zapis,
-- v katerem argumente damo na mesta podčrtajev

sestej_ter_invrnirezultat : Nat -> Nat -> Nat
sestej O ter n invrnirezultat = n
sestej (S m) ter n invrnirezultat = S (sestej m ter n invrnirezultat)

-- Agda podpira (in spodbuja) vnos v UTF8, zato je bolj naravna definicija
-- naravnih števil takšna

data ℕ : Set where
    O : ℕ
    S : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
O + n = n
(S m) + n = S (m + n)
