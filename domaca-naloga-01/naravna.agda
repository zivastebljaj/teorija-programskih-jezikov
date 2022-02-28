module naravna where
open import boole using(true; false; Bool)

-- naravna števila bi lahko v Agdi definirali na sledeči način

data Nat : Set where
    -- za razliko od OCamla moramo vedno povedati tudi kodomeno konstruktorja,
    -- saj se bo lahko spreminjala
    zero : Nat
    suc : Nat -> Nat 

-- vsako definicijo najprej začnemo z deklaracijo tipa

plus : Nat -> Nat -> Nat
plus zero n = n
plus (suc m) n = suc (plus m n)

-- če ime definicije vsebuje podčrtaje, lahko uporabljamo miksfiksni zapis,
-- v katerem argumente damo na mesta podčrtajev

sestej_ter_invrnirezultat : Nat -> Nat -> Nat
sestej zero ter n invrnirezultat = n
sestej (suc m) ter n invrnirezultat = suc (sestej m ter n invrnirezultat)


_+_ : Nat → Nat → Nat
zero + n = n
(suc m) + n = suc (m + n)
