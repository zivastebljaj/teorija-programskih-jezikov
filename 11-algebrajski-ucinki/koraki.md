Imejmo program

```
print("T");
print("P");
print("J")
```

ki izpiše `T`, `P` in `J` ter prestreznik

```
h = {
    print(msg; k) -> k (); in print(msg)
}
```

ki izpise izvaja v obratnem vrstnem redu - najprej pokliče kontinuacijo, nato izpiše sporočilo `msg`.

Najprej stvari spravimo v pravi zapis `print(msg)` je okrajšava za klic s trivialno kontinuacijo `print(msg, y. return y)`, med tem ko je `c1; c2` okrajšava za `do _ <- c1 in c2`. Tako naš program pomeni

```
do _ <- print("T"; y1. return y1) in
do _ <- print("P"; y2. return y2) in
print("J"; y3. return y3)
```

Tudi prestrezniku `h` manjka veja za vrednosti. Zanjo vzamemo tirivalno vejo, ki vrednosti ohranja:

```
h = {
    print(msg; k) -> do _ <- k () in print(msg; y. return y),
    return x -> return x
}
```

------------------------------------------------------


    handle
        do _ <- print("T"; y1. return y1) in
        do _ <- print("P"; y2. return y2) in
        print("J"; y3. return y3)
    with h
    

Ker velja
    `do x <- op(v; y. c1) in c2 ~~> op(v; y. do x <- c1 in c2)`
naredimo korak v

    handle
        print("T"; y1.
            do _ <- return y1 in
            do _ <- print("P"; y2. return y2) in
            print("J"; y3. return y3)
        )
    with h

Ker velja
    `handle op(v; y. c) with h ~~> c_op[v / x, (λ y. handle c with h) / k]`
naredimo korak v

    (do _ <- k () in print(msg; y. return y))[
        "T" / msg
        (fun y1 ->
            handle
                do _ <- return y1 in
                do _ <- print("P"; y2. return y2) in
                print("J"; y3. return y3)
            with h
        ) / k
    ]

razpišemo substitucijo in dobimo

    do _ <- (lambda y1.
            handle
                do _ <- return y1 in
                do _ <- print("P"; y2. return y2) in
                print("J"; y3. return y3)
            with h
    ) ()
    in
    print("T"; y. return y)

Ker velja
    `(λ x. c) v ~~> c[v / x]`
naredimo korak v

    do _ <-
        handle
            do _ <- return () in
            do _ <- print("P"; y2. return y2) in
            print("J"; y3. return y3)
        with h
    in
    print("T"; y. return y)

Ker velja
    `do x <- return v in c ~~> c[v / x]`
naredimo korak v

    do _ <-
        handle
            do _ <- print("P"; y2. return y2) in
            print("J"; y3. return y3)
        with h
    in
    print("T"; y. return y)

Print `T` je pripotoval ven in še enkrat ponovimo isti postopek, da dobimo isto še za `P`

    do _ <-
        do _ <- 
            handle
                print("J"; y3. return y3)
            with h
            in
            print("P"; y2. return y2)
    in
    print("T"; y. return y)

in še enkrat za `J`

    do _ <-
        do _ <- 
            do _ <-
                handle
                    return ()
                with h
            in
            print("J"; y1. return y1)
        in
        print("P"; y2. return y2)
    in
    print("T"; y. return y)

Ker velja
    `handle (return v) with h ~~> c_ret[v / x]`
naredimo korak v

    do _ <-
        do _ <- 
            do _ <-
                return ()
            in
            print("J"; y1. return y1)
        in
        print("P"; y2. return y2)
    in
    print("T"; y. return y)

Ker velja
    `do x <- return v in c ~~> c[v / x]`
naredimo korak v

    do _ <-
        do _ <- 
            print("J"; y1. return y1)
        in
        print("P"; y2. return y2)
    in
    print("T"; y. return y)

Ker velja
    `do x <- op(v; y. c1) in c2 ~~> op(v; y. do x <- c1 in c2)`
naredimo korak v

    do _ <-
        print("J"; y1. do _ <- return y1)
        in
        print("P"; y2. return y2)
    in
    print("T"; y. return y)

Ker velja
    `do x <- op(v; y. c1) in c2 ~~> op(v; y. do x <- c1 in c2)`
naredmo korak v

    print("J"; y1.
        do _ <- 
            do _ <- return y1
            in
            print("P"; y2. return y2)
        in
        print("T"; y. return y)
    )

Zdaj je `print` pripotoval do vrha in izpiše se črka `J`, v `y1` pa se vrne rezultat `()`.

    do _ <- 
        do _ <- return ()
        in
        print("P"; y2. return y2)
    in
    print("T"; y. return y)

Ker velja
    `do x <- return v in c ~~> c[v / x]`
naredimo korak v

    print("P"; y2.
        do _ <- return y2
        in
        print("T"; y. return y)
    )

Zdaj je `print` pripotoval do vrha in izpiše se črka `P`, v `y2` pa se vrne rezultat `()`.

    do _ <- return ()
    in
    print("T"; y. return y)

Ker velja
    `do x <- return v in c ~~> c[v / x]`
naredimo korak v

    print("T"; y. return y)

Zdaj je `print` pripotoval do vrha in izpiše se črka `T`, v `y` pa se vrne rezultat `()`.

    return ()

S čimer končamo. Izpisali so se `J`, `P` in `T`, na koncu pa smo vrnili `()`.