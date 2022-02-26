# NAVODILA ZA PRVO DOMAČO NALOGO

NALOGO MORATE REŠEVATI SAMOSTOJNO. ČE NE VESTE, ALI DOLOČENA STVAR POMENI SODELOVANJE, RAJE VPRAŠAJTE!

Naloga obsega implementacijo tolmača za jezik `imp` v Agdi.

Za oddajo naloge si podvojite repozitorij (*fork*) na vaš uporabniški račun.
Razširitve jezika in dodatne datoteke nato dodajte na vaš repozitorij (prav tako na vejo `domaca-naloga-01`), na spletni učilnici pa oddatje zgolj povezavo do vašega repozitorija.
Vse potrebne datoteke se nahajajo v mapi `domaca-naloga-01`, kjer tudi rešujte domačo nalogo, datotek izven te mape ne spreminjajte.

## JEZIK IMP

Na predavanjih in vajah smo na kratko pogledali jezik `imp` in pripravili delno implementacijo tolmača.
Vaša naloga je dokončati obstoječ tolmač in ga razširiti z dodatnimi konstrukti.

Pri pisanju tolmača uporabljajte tipe in module, ki smo jih napisali na predavanjih in vajah (`boole.agda`, `seznami.agda`, `naravna.agda`, `par.agda`, `vektorji.agda`, `fin.agda`), nekatere od njih bo celo potrebno razširiti.

Okolje v jeziku `imp` predstavimo z vektorjem dolžine `n`, kjer se na spremenljivke sklicujemo kar z lokacijo v vektorju tipa `Fin n`.
Da je implementacija lažja in se izognemo dokazovanju predpostavimo, da ima začetno okolje že predefinirane neke (smiselne) vrednosti vseh spremenljivk, ki jih bomo potrebovali.
Prav tako za lažje pisanje tolmača eksplicitno "povečamo" tip spremenljivk v sami sintaksi jezika s pomočjo funkcij `#_⇑_` in `_↑_`.  

### Popravki tolmača

V mapi `agda.imp` se nahaja delno dokončana implementacija tolmača, ki je polna lukenj.
Vaša naloga je zapolniti lunkje na smiselen način, da se bo tolmač uspešno prevedel in bo pravilno izvedel ukaz v programskem jeziku `imp`.
Za pomoč je nekaj primer ukaza že pripravljen, priporočamo pa, da si za testiranje pripravite še nekaj novih.
Pomožne funkcije, ki jih boste potrebovali za razširitev tolmača dodajte v smiselne datoteke in jih priložite domači nalogi.

### Razširitev tolmača

Obstoječ jezik razširite z novimi konstrukti:

- Artimetični izrazi naj dodatno podpirajo potenciranje `_**_`
- Booleovi izrazi naj podpirajo logična IN in ALI `_&&_, _||_`
- V jezik dodajte ukaz `PrintInt_`, ki izpiše vrednost aritmetičnega izraza.

    Izpis celih števil bomo modelirali tako, da bo izvajanje ukazov namesto okolja vrnilo par okolja in seznama izpisanih števil. Kot argument še vedno dobi samo okolje, saj v seznam izpisa zgolj dodajamo. Pri tem si lahko pomagate s tipom `Pair`, ki smo ga definirali na vajah.

### Sporočanje napak

Ko trenutna implementacija konča z izvajanjem nimamo podatka, ali smo porabili preveč korakov, ali je tolmač uspešno končal z izvajanjem.
Popravite implementacijo tolmača, ki bo namesto okolja in izpisani števil vrnila tip, ki signalizira na kakšen način se je izvajanje končalo.
V priloženi datoteki je v komentarju dodan tip, s katerim si lahko pomagate.
Če tekom izvajanja zmanjka goriva je rezultat izvajanja `outOfGas`, druga komponenta pa nam ne glede na način končanja pove, katera števila smo izpisali preden je zmanjkalo goriva.

### For zanka

V jezik dodajte nov ukaz `FOR_:=_TO_DO_DONE`, ki se obnaša na enak način kot for zanka v jeziku `OCaml`.
Že podan primer ukaza zapišite s for zanko in preverite, da je rezultat enak.
Za lažjo implementacijo predpostavite, da je spremenljivka po kateri iteriramo že definirana v okolju.

--------------------------------------------------------------------------------

NALOGO MORATE REŠEVATI SAMOSTOJNO. ČE NE VESTE, ALI DOLOČENA STVAR POMENI SODELOVANJE, RAJE VPRAŠAJTE!

Dovoljno je brskanje in uporaba idej iz standardne knjižnjice Agde, obstoječe kode na internetu, zapiskov s predavanj, vaj, pogovor s sošolci o idejah reševanja in težavah.

Strogo prepovedano je med drugim deljenje kode in rešitev, ki se dotikajo te specifične domače naloge, tako med sošolci, kot prek interneta in direktno spraševanje za pomoč o podanih nalogah.
