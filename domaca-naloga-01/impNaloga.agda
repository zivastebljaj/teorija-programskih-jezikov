module impNaloga where

import naravna
open naravna using (Nat; zero; suc)
open import vektorji using(Vec; _[_]; _[_]←_; []; _::_ )
open import seznami using(List)
open import fin using (Fin; _↑_; toNat; fromNat; Fo; Fs)
open import boole
open import pari

-- Namesto suc (suc zero) lahko napišemo kar 2
{-# BUILTIN NATURAL Nat #-}

infixr 3 _；_ 
infix 4 _:=_
infix 5 IF_THEN_ELSE_END
infix 6 WHILE_DO_DONE
infix 6 SKIP

infix 10 _≡_
infix 10 _>_
infix 10 _<_

infixl 11 _+_
infixl 11 _*_

infix 14 !_
infix 15 `_
infix 20 #_

infix 21 #_⇑_
infixl 25 _/_


{--
Artimetične, booleove izraze in ukaze parametriziramo z naravnim številom `n`. 
Parameter `n` pove, da lahko izraz uporabi spremenljivke indeksirane med `0` in `n - 1`.
Omejitev naravno predstavimo s tipom `Fin n`.
Vrednosti tipa `Fin n` so v naravni sinergiji z vrednostmi tipa `Vector A n`, 
s katerim bomo tudi predstavili stanje spremenljivk v jeziku.
Spremenljivk bodo enostavno kar indeksi posameznih mest v vektorju.
To nam zagotavlja, da bo agda že vnaprej zavrnila programe, ki bomo
poskušali uporabiti več spremenljivk kot je dovoljeno.

--}


data Exp (n : Nat) : Set where
    `_ : Nat → Exp n
    !_ : Fin n → Exp n -- Spremenljivke nazivamo z naravnimi števili manjšimi od `n`
    _+_ : Exp n → Exp n → Exp n
    _*_ : Exp n → Exp n → Exp n

data BExp (n : Nat) : Set where
    _≡_ : Exp n → Exp n → BExp n
    _<_ : Exp n → Exp n → BExp n
    _>_ : Exp n → Exp n → BExp n

data Cmd : (n : Nat) → Set where
    IF_THEN_ELSE_END : {n : Nat} → BExp n → Cmd n → Cmd n → Cmd n
    WHILE_DO_DONE : {n : Nat} → BExp n → Cmd n → Cmd n
    _；_ : {n : Nat} → Cmd n → Cmd n → Cmd n
    _:=_ : {n : Nat} → (Fin n) → Exp n → Cmd n
    SKIP : {n : Nat} → Cmd n

State : Nat → Set
State n = Vec Nat n

-- Pomožne funkcije za pretvarjanje med velikostmi

#_ : (n : Nat) → Fin (suc n) 
#_ = fromNat

#_⇑_ : (m : Nat) → ∀ (n : Nat) → Fin (suc (m naravna.+ n))
# m ⇑ n = fromNat m ↑ n

_/_ : (m : Nat) → ∀ (n : Nat) → Exp (suc (m naravna.+ n))
m / n =  !(fromNat m ↑ n)

{--
Da bo pisanje tolmača enostavnejše bomo eksplicitno povečamo tip posameznih izrazov že v sintaksi.
Če želimo izraz ki naziva največ prvih `n` spremenljivk uporabiti v programu, ki 
lahko naziva največ prvih `m` spremenljivk (kjer je n ≤ m) potem umetno povečamo
tip izraza na `m`.

Najlažji način da naredimo to je da ustrezno povečamo tip indeksa spremenljivke kot to kažejo spodnji primeri.
--}

primer : Exp 1
primer = ! # 0 -- Vrednost z indeksom `0`, kjer program lahko naziva največ eno spremenljivko 

primer2 : Exp 2
primer2 = ! # 1 -- Vrednost z indeksom `0`, kjer program lahko naziva prvi dve spremenljivki (celici v vektorju) 

primer3 : Exp 5
primer3 = 1 / 3 -- Vrednost z indeksom `1`, kjer program lahko naziva prvih pet spremenljivk. Da to storimo eksplicitno povečamo tip pri indeksu

primer4 : Exp 3
primer4 = 1 / 1 + 0 / 2 -- Da lahko uporabimo vrednost na mestu 0 in 1 v izrazu velikosti do 3, moramo tip indeksiranja 0 povečati za 2, tip indeksiranja na 1 pa za 1

-- Programo uporablja največ 3 spremenljivke
vsota : Nat → Cmd 3
vsota n = 
    # 0 ⇑ 2 := ` n ； -- Indeksiramo prvo spremenljivo, in tip vseh možnih spremenljivk povečamo za 2, saj bomo v celotnem programo potrebovali tri spremenljivke
    # 1 ⇑ 1 := ` 0 ；
    # 2 ⇑ 0 :=  ! (# 0 ⇑ 2) ；
    WHILE ! (# 1 ⇑ 1) < ! (# 0 ⇑ 2) DO
        # 2 ⇑ 0 := 2 / 0 + 1 / 1 ；
        # 1 ⇑ 1 := 1 / 1 + ` 1
    DONE

-- Uporabno za nadgradnjo
{--
data Res {a} (A : Set a) : Set a where
    ok : A -> Res A
    outOfGas : Res A

Result : Nat -> Set
Result n = Pair (Res (State n)) (List Nat)
--}

lookup : {n : Nat} → Fin n → State n → Nat
lookup i s = s [ i ]

evalExp : {n : Nat} → State n → Exp n → Nat
evalExp st (` x) = x
evalExp st (! i) = {!   !}
evalExp st (exp₁ + exp₂) = (evalExp st exp₁) naravna.+ (evalExp st exp₂)
evalExp st (exp₁ * exp₂) = {!   !}

evalBExp : {n : Nat} → State n → BExp n → Bool
evalBExp = {!   !}

evalCmd : {n : Nat} → Nat → State n → Cmd n → State n
evalCmd n st IF bexp THEN cmd₁ ELSE cmd₂ END = {!   !}
evalCmd (suc n) st WHILE bexp DO cmd DONE =
    if evalBExp st bexp then
        evalCmd n (evalCmd n st cmd) (WHILE bexp DO cmd DONE)
    else
        st
evalCmd n st (cmd₁ ； cmd₂) = evalCmd n (evalCmd n st cmd₁) cmd₂
evalCmd _ st (ℓ := exp) = st [ ℓ ]← (evalExp st exp) 
evalCmd _ st SKIP = st
evalCmd zero st (WHILE bexp DO cmd DONE) = st


run : Cmd 3 → State 3
run cmd = evalCmd 125  ( 0 :: (0 :: (0  :: []))) cmd

a : Nat → Nat
a n = (run (vsota n)) [ fromNat 2 ]