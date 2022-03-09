module VajeNaloge where

open import naravna using (ℕ; S; O; _+_)
open import boole using (𝕥; 𝕗; 𝔹)

-- Iz tipov in imena razberite namen funkcije in pripravite ustrezno implementacijo
-- Naloge rešujte brez uporabe dokazov. 
-- V kolikor se agda pritoži to pomeni, da je potrebno implementacijo nekoliko popraviti.

module Maybe where
    data Maybe (A : Set) : Set where
        nothing : Maybe A
        just : A → Maybe A
    
open Maybe

-- Tip `Fin n` uporabimo za zapis vseh naravnih števil manjših od `n`

module Fin where
    data Fin : ℕ -> Set where
        Fo : {n : ℕ} -> Fin (S n)
        Fs : {n : ℕ} -> Fin n -> Fin (S n)
    
open Fin


module Pair where

    record Pair (A B : Set) : Set where
        constructor _,_
        field
            fst : A
            snd : B
open Pair

par : Pair ℕ (Pair 𝔹 𝔹)
-- Uporabimo record in konstruktor
par = record { fst = O; snd = (𝕥 , 𝕗) }

-- Destrukcija
swap : {A B : Set} → Pair A B → Pair B A
-- Prek vzorca ali s funkcijo
swap x@(fst , snd) = (snd , Pair.fst x)

-- Najprej ponovimo osnovno programiranje s seznami

module List where

    infixr 5 _∷_
    infixr 3 _++_
    infixl 4 _[_]

    data List (A : Set) : Set where
        [] : List A
        _∷_ : A → List A → List A

    l1 : List ℕ
    l1 = []

    l2 : List ℕ
    l2 = S O ∷ (S (S O)) ∷ []

    l3 : List ℕ
    l3 = (S (S (S O))) ∷ l2

    -- Definirajte nekaj osnovnih operacij na seznamih
    -- V pomoč naj vam bodo testi na koncu funkcij
    _++_ : {A : Set} → List A → List A → List A
    [] ++ ys = ys
    x ∷ xs ++ ys = x ∷ (xs ++ ys)

    len : { A : Set} -> List A -> ℕ
    len [] = O
    len (x ∷ x₁) = S (len x₁)

    reverse : { A : Set} -> List A -> List A
    reverse xs = rev xs []
        where 
            rev : {A : Set} -> List  A -> List A -> List A 
            rev [] acc = acc
            rev (x ∷ xs) acc = rev xs (x ∷ acc)

    map : { A B : Set} -> (A -> B) -> List A -> List B  
    map f [] = []
    map f (x ∷ xs) =  f x ∷ map f xs  

    -- Ko potrebujemo dodatno informacijo si pomagamo z with

    filter : {A : Set} → (A → 𝔹) → List A → List A
    filter f [] = []
    filter f (x ∷ l) with f x   
    ... | 𝕗 = filter f l
    ... | 𝕥 = x ∷ (filter f l)

    _[_] : {A : Set} -> List A -> ℕ -> Maybe A
    [] [ _ ] = nothing
    x ∷ xs [ O ] = just x
    x ∷ xs [ S i ] = xs [ i ]

-- Odvisni tipi

-- Na predavanjih smo spoznali odvisni tip Vektor (seznam z doližno)
-- Pripravimo si nekaj pomožnih funkcij

module Vector where

    infixr 5 _∷_
    infixr 3 _++_
    infixl 4 _[_]

    data Vector (A : Set) : ℕ → Set where
        []  : Vector A O
        _∷_ : {n : ℕ} → A → Vector A n → Vector A (S n)
    
    _++_ : {A : Set} {n m : ℕ} → Vector A n → Vector A m → Vector A (n + m)
    []       ++ ys  =  ys
    (x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)

    -- Za določene tipe vektorjev lahko vedno dobimo glavo in rep

    head : {A : Set} → {n : ℕ} → Vector A (S n) → A
    head (x ∷ xs) = x

    tail : {A : Set} → {n : ℕ} → Vector A (S n) → Vector A n
    tail (x ∷ xs) = xs

    map : {A B : Set} → {n : ℕ} → (A -> B) → Vector A n → Vector B n
    map f [] = []
    map f (x ∷ xs) = f x ∷ map f xs
    
     
    -- lenV : { A : Set} -> Vector A -> ℕ
    -- lenV [] = O
    -- lenV (x ∷ x₁) = S (lenV x₁) 
    

    -- Sedaj lahko napišemo bolj informativni obliki funkcij `zip` in `unzip`

    zip : {A B : Set} → {n : ℕ} → Vector A n → Vector B n → Vector (Pair A B) n
    zip [] [] = []
    zip (x ∷ xs) (x₁ ∷ ys) = ( x , x₁ ) ∷ zip xs ys

    unzip : {A B : Set} → {n : ℕ} → Vector (Pair A B) n → Pair (Vector A n) (Vector B n)  
    unzip [] = [] , []
    unzip (x ∷ xs) = (Pair.fst x ∷ Pair.fst (unzip xs)) , (Pair.snd x ∷ Pair.snd (unzip xs))

    -- S pomočjo tipa `Fin` je indeksiranje varno
    -- Namig: Naj vam agda pomaga pri vzorcih (hkrati lahko razbijemo več vzorcev nanekrat)
    _[_] : {A : Set} {n : ℕ} -> Vector A n -> Fin n -> A
    [] [ () ]
    x ∷ v [ Fo ] = x
    x ∷ v [ Fs i ] = v [ i ]

    -- Dobro preučite tip in povejte kaj pomeni
    fromℕ : (n : ℕ) → Fin (S n)
    fromℕ O = Fo
    fromℕ (S n) = Fs (fromℕ n)

    toℕ : {n : ℕ} → Fin n → ℕ
    toℕ Fo = O
    toℕ (Fs f) = S (toℕ f)
    
    init : {A : Set} → (n : ℕ) → (x : A) -> Vector A n
    init O x = []
    init (S n) x = x ∷ init n x
    
    vecToList : {A : Set} {n : ℕ} → Vector A n → List.List A
    vecToList [] = List.[]
    vecToList (x ∷ vec) =  x List.∷ vecToList vec

    -- V tipih lahko nastopaju tudi povsem običajne funkcije

    listToVec : {A : Set} {n : ℕ} → (l : List.List A) → Vector A (List.len l)
    listToVec List.[] = []
    listToVec (x List.∷ xs) = x ∷ listToVec xs

    count : {A : Set} {n : ℕ} → (f : A → 𝔹) → (v : Vector A n) → ℕ
    count f v = List.len (List.filter f (vecToList v))

    filterV : {A : Set} {n : ℕ} → (f : A → 𝔹) → (v : Vector A n) → (Vector A (count f v)) 
    filterV f v = listToVec (List.filter f (vecToList v))


-- Nekoliko posplošimo seznam
module Line where

    -- Na vsakem mestu imamo vektor poljubne dolžine
    data Line (A : Set) : ℕ → Set where
        []  : Line A O
        _::_ : {n m : ℕ} → Vector.Vector A m → Line A n → Line A (S n)

    lineLen : {A : Set} {n : ℕ} → Line A n → ℕ
    lineLen [] = O
    lineLen (x :: lin) = lenV x + lineLen lin 
        where
            lenV : {A : Set} {n : ℕ} → Vector.Vector A n → ℕ
            lenV Vector.[] = O
            lenV (x Vector.∷ vec) = S (lenV vec)

    flattenL : {A : Set} {n : ℕ} → (lin : Line A n) → Vector.Vector A (lineLen lin) 
    flattenL [] = Vector.[]
    flattenL (x :: lin) = {!  !} Vector.++ {!   !}
    
    map : ∀ { A B : Set } {n : ℕ}  → (A -> B) → Line A n → Line B n
    map f [] = []
    map f (x :: lin) = Vector.map f x :: map f lin

    foldrL : ∀ {A B : Set} {n : ℕ} → (∀ {n : ℕ} → Vector.Vector A n → B → B) → B → (Line A n) → B
    foldrL = {!   !}

    lineLen2 : ∀ {A : Set} {n : ℕ} → (Line A n) → ℕ
    lineLen2 = foldrL (λ {n} _ s → n + s ) O 


module Tree where
    data Tree (A : Set) : ℕ → Set where
        Leaf : A → Tree A (S O)
        Node : ∀ (n m : ℕ) → Tree A m → A → Tree A n → Tree A ((m + S n))

    collect : ∀ {n : ℕ} {A : Set} → Tree A n → Vector.Vector A n
    collect (Leaf x) = x Vector.∷ Vector.[]
    collect (Node n m l x r) = {!   !} 

    -- Malo popravi definicijo drevesa in potem ustrezno popravi še definicijo collect da se izogneš dokazom


module Variadic where
    -- S pomočjo odvisnih tipov lahko definiramo funkcije, ki sprejmejo več argumentov
    
    variadicType : ℕ → Set → Set → Set
    variadicType O _ val    = val
    variadicType (S n) t r = t -> variadicType n t r

    variadicSum : (n : ℕ) → variadicType n ℕ ℕ
    variadicSum n = variadicSum' n O
        where
            variadicSum' : (n : ℕ) → ℕ → variadicType n ℕ ℕ
            variadicSum' O cur = cur
            variadicSum' (S a) cur = \x → variadicSum' a (cur + x)

    a : ℕ
    a = variadicSum (S (S (S O))) O (S O) (S O)