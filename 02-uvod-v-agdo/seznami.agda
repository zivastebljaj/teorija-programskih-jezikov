-- seznami so parametrizirani podatkovni tip,
-- kar pomeni, da kot argument sprejmejo tip elementov

data Sez : Set → Set where
    -- Da konstruktor Empty ve, sezname katerega tipa naj vrača,
    -- mu moramo ta tip podati kot argument. Ker je kodomena odvisna
    -- od vrednosti, moramo argument eksplicitno poimenovati.
    Empty : (A : Set) → Sez A
    -- Če vrednost argumenta lahko Agda določi samodejno iz preostalih
    -- argumentov, lahko argument pustimo impliciten
    Cons : {A : Set} → A → Sez A → Sez A

-- Tudi stikanje seznamov kot argument sprejme tip elementov seznamov,
-- ki jih bo stikal
expApp : (A : Set) → Sez A → Sez A → Sez A
expApp A (Empty A') ys = ys
expApp A (Cons x xs) ys = Cons x (expApp A xs ys)

-- Seveda tudi ta tipp lahko naredimo impliciten
impApp : {A : Set} → Sez A → Sez A → Sez A
impApp (Empty A') ys = ys
impApp (Cons x xs) ys = Cons x (impApp xs ys)


data 𝕊 : Set → Set where
    [] : {A : Set} → 𝕊 A
    _∷_ : {A : Set} → A → 𝕊 A → 𝕊 A

infixr 15 _++_
infixr 20 _∷_

_++_ : {A : Set} → 𝕊 A → 𝕊 A → 𝕊 A
[] ++ ys = ys
x ∷ xs ++ ys = x ∷ (xs ++ ys)

map : {A B : Set} → (A → B) → 𝕊 A → 𝕊 B
map f [] = []
map f (x ∷ xs) = map f xs

infix 10 _∈_

data _∈_ {A : Set} : A → 𝕊 A → Set where
    here : {x : A} {xs : 𝕊 A} → x ∈ x ∷ xs
    there : {x y : A} {xs : 𝕊 A} → x ∈ xs → x ∈ y ∷ xs
