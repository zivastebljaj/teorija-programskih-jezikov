-- Syntax
def loc := string

inductive aexp : Type
| Lookup : loc -> aexp
| Int : int -> aexp
| Plus : aexp -> aexp -> aexp
| Minus : aexp -> aexp -> aexp
| Times : aexp -> aexp -> aexp

inductive bexp : Type
| Bool : bool -> bexp
| Equal : aexp -> aexp -> bexp
| Less : aexp -> aexp -> bexp
| Greater : aexp -> aexp -> bexp

inductive cmd : Type
| Assign : loc -> aexp -> cmd
| IfThenElse  : bexp -> cmd -> cmd -> cmd
| Seq : cmd -> cmd -> cmd
| Skip : cmd
| WhileDo : bexp -> cmd -> cmd

-- Example 'fact.imp' in LEAN notation.

def fact : cmd :=
  cmd.Seq
    (cmd.Seq
      (cmd.Assign "n" (aexp.Int 10))
      (cmd.Assign "fact" (aexp.Int 10)) )
    (cmd.WhileDo
      (bexp.Greater
        (aexp.Lookup "n")
        (aexp.Int 0) )
      (cmd.Seq
        (cmd.Assign "fact" 
          (aexp.Times (aexp.Lookup "fact") (aexp.Lookup "n")) )
        (cmd.Assign "n"
          (aexp.Minus (aexp.Lookup "n") (aexp.Int 1)) ) ) )

-- State

inductive env : Type
| Nil : env
| Cons : loc -> int -> env -> env

inductive lookup : loc -> env -> int -> Prop
| Find {loc i E} : 
    lookup loc (env.Cons loc i E) i 
| Search {loc loc' i' E' i} : 
    loc'≠loc -> lookup loc E' i -> 
    lookup loc (env.Cons loc' i' E') i

-- Operational Semantics

inductive aeval : env -> aexp -> int -> Prop
| Lookup {E loc i} :
    lookup loc E i -> aeval E (aexp.Lookup loc) i
| Int {E i} :
    aeval E (aexp.Int i) i
| Plus {E a1 a2 i1 i2} :
    aeval E a1 i1 -> aeval E a2 i2 ->
    aeval E (aexp.Plus a1 a2) (i1 + i2)
| Minus {E a1 a2 i1 i2} :
    aeval E a1 i1 -> aeval E a2 i2 ->
    aeval E (aexp.Minus a1 a2) (i1 - i2)
| Times {E a1 a2 i1 i2} :
    aeval E a1 i1 -> aeval E a2 i2 ->
    aeval E (aexp.Times a1 a2) (i1 * i2)

inductive beval : env -> bexp -> bool -> Prop
| Bool {E b} :
    beval E (bexp.Bool b) b
| Equal_t {E a1 a2 i1 i2}:
    aeval E a1 i1 -> aeval E a2 i2 -> i1 = i2 ->
    beval E (bexp.Equal a1 a2) true
| Equal_f {E a1 a2 i1 i2}:
    aeval E a1 i1 -> aeval E a2 i2 -> i1 ≠ i2 ->
    beval E (bexp.Equal a1 a2) false
| Less_t {E a1 a2 i1 i2}:
    aeval E a1 i1 -> aeval E a2 i2 -> i1 < i2 ->
    beval E (bexp.Less a1 a2) true
| Less_f {E a1 a2 i1 i2}:
    aeval E a1 i1 -> aeval E a2 i2 -> ¬ i1 < i2 ->
    beval E (bexp.Less a1 a2) false
| Greater_t {E a1 a2 i1 i2}:
    aeval E a1 i1 -> aeval E a2 i2 -> ¬ i1 ≤ i2 ->
    beval E (bexp.Greater a1 a2) true
| Greater_f {E a1 a2 i1 i2}:
    aeval E a1 i1 -> aeval E a2 i2 -> i1 ≤ i2 ->
    beval E (bexp.Greater a1 a2) false

inductive ceval : env -> cmd -> env -> Prop
| Assign {loc a i E} :
    aeval E a i ->
    ceval E (cmd.Assign loc a) (env.Cons loc i E)
| IfThenElse_t {E b c1 c2 M'} :
    beval E b true -> ceval E c1 M' ->
    ceval E (cmd.IfThenElse b c1 c2) M'
| IfThenElse_f {E b c1 c2 E'} :
    beval E b false -> ceval E c2 E' ->
    ceval E (cmd.IfThenElse b c1 c2) E'
| Seq {E c1 E' c2 E''} :
    ceval E c1 E' -> ceval E' c2 E'' ->
    ceval E (cmd.Seq c1 c2) E''
| Skip {E} :
    ceval E cmd.Skip E
| WhileDo_t {E b c E' E''} :
    beval E b true -> ceval E c E' ->
    ceval E' (cmd.WhileDo b c) E'' ->
    ceval E (cmd.WhileDo b c) E''
| WhileDo_f {E b c} :
    beval E b false -> 
    ceval E (cmd.WhileDo b c) E

-- Safety

inductive locs : Type
| Nil : locs
| Cons : loc -> locs -> locs

inductive safe_in : locs -> loc -> Prop
| Find {loc L} : 
    safe_in (locs.Cons loc L) loc 
| Search {loc loc' L} : 
    loc'≠loc -> safe_in L loc -> 
    safe_in (locs.Cons loc' L) loc 

inductive asafe : locs -> aexp -> Prop
| Lookup {L loc}:
    safe_in L loc -> asafe L (aexp.Lookup loc)
| Int {L i}:
    asafe L (aexp.Int i)
| Plus {L a1 a2} :
    asafe L a1 -> asafe L a2 ->
    asafe L (aexp.Plus a1 a2)
| Minus {L a1 a2} :
    asafe L a1 -> asafe L a2 ->
    asafe L (aexp.Minus a1 a2)
| Times {L a1 a2} :
    asafe L a1 -> asafe L a2 ->
    asafe L (aexp.Times a1 a2)

inductive bsafe : locs -> bexp -> Prop
| Bool {L b} :
    bsafe L (bexp.Bool b)
| Equal {L a1 a2} :
    asafe L a1 -> asafe L a2 ->
    bsafe L (bexp.Equal a1 a2)
| Less {L a1 a2} :
    asafe L a1 -> asafe L a2 ->
    bsafe L (bexp.Less a1 a2)
| Greater {L a1 a2} :
    asafe L a1 -> asafe L a2 ->
    bsafe L (bexp.Greater a1 a2)

inductive csafe : locs -> cmd -> locs -> Prop
| Assign {L loc a} :
    asafe L a ->
    csafe L (cmd.Assign loc a) (locs.Cons loc L)
-- | IfThenElse {L b c1 c2} :
--     bsafe L b -> csafe L c1 L' -> csafe L c2 L'' ->
--     ???  
| Seq {L c1 L' c2 L''} :
    csafe L c1 L' -> csafe L' c2 L'' ->
    csafe L (cmd.Seq c1 c2) L''
| Skip {L} :
    csafe L cmd.Skip L
| WhileDo {L b c L'} :
    bsafe L b -> csafe L c L' ->
    csafe L (cmd.WhileDo b c) L'

-- Checks for envirnoment safety with regard to locations
inductive env_safe : env -> locs -> Prop
| Nil {E} :
    env_safe E locs.Nil
| Cons {loc E L} :
    env_safe E L -> (∃i, lookup loc E i) ->
    env_safe E (locs.Cons loc L)

theorem env_safe_weaken {E L loc i}:
  env_safe E L -> env_safe (env.Cons loc i E) L
:=
begin
  intro es, induction es,
  apply env_safe.Nil,
  apply env_safe.Cons, assumption,
  cases string.has_decidable_eq loc es_loc,
  { cases es_a_1 with i', existsi i',
    apply lookup.Search, assumption, assumption, },
  subst h, existsi i, apply lookup.Find,
end

theorem safe_lookup {L E loc}:
  safe_in L loc -> env_safe E L -> ∃ (i:int), lookup loc E i
:=
begin
  intros sloc es, induction es,
  { cases sloc, },
  cases sloc, assumption, apply es_ih, assumption,
end

-- Safety theorems
theorem asafety {L E a}:
  asafe L a -> env_safe E L -> ∃ (i:int), aeval E a i
:=
begin
  intros s es,
  induction s,
  { cases safe_lookup s_a es,
    existsi w, apply aeval.Lookup, assumption, },
  { existsi s_i, apply aeval.Int, },
  { cases s_ih_a es with i1,
    cases s_ih_a_1 es with i2,
    existsi (i1+i2), apply aeval.Plus, assumption, assumption },
  { cases s_ih_a es with i1,
    cases s_ih_a_1 es with i2,
    existsi (i1-i2), apply aeval.Minus, assumption, assumption },
  { cases s_ih_a es with i1,
    cases s_ih_a_1 es with i2,
    existsi (i1*i2), apply aeval.Times, assumption, assumption },
end

theorem bsafety {L E b}:
  bsafe L b -> env_safe E L -> ∃ (v:bool), beval E b v
:=
begin
  intros s es,
  induction s,
  { existsi s_b, apply beval.Bool, },
  { cases asafety s_a es with i1,
    cases asafety s_a_1 es with i2,
    cases int.decidable_eq i1 i2 with eq,
    { existsi (false:bool), apply beval.Equal_f,
      assumption, assumption, assumption,},
    { existsi (true:bool), apply beval.Equal_t,
      assumption, assumption, assumption,}, },
  { cases asafety s_a es with i1,
    cases asafety s_a_1 es with i2,
    cases int.decidable_lt i1 i2 with eq,
    { existsi (false:bool), apply beval.Less_f,
      assumption, assumption, assumption,},
    { existsi (true:bool), apply beval.Less_t,
      assumption, assumption, assumption,}, },
  { cases asafety s_a es with i1,
    cases asafety s_a_1 es with i2,
    cases int.decidable_le i1 i2 with eq,
    { existsi (true:bool), apply beval.Greater_t,
      assumption, assumption, assumption,},
    { existsi (false:bool), apply beval.Greater_f,
      assumption, assumption, assumption,}, },
end

theorem csafety {L L' E c }:
  csafe L c L' -> env_safe E L -> 
  ∃ (E':env), ceval E c E' ∧ env_safe E' L'
:=
begin
  intros safe, revert E,
  induction safe; intros E es,
  { cases asafety safe_a_1 es with i,
    existsi (env.Cons safe_loc i E),
    constructor,
    { apply ceval.Assign, assumption, },
    apply env_safe.Cons,
    { apply env_safe_weaken, assumption, },
    existsi i, apply lookup.Find, },
  { cases (safe_ih_a es) with E',
    destruct h, intros c1safe es',
    cases (safe_ih_a_1 es') with E'',
    destruct h_1, intros c2safe es'',
    existsi E'', constructor,
    { apply ceval.Seq, assumption, assumption, },
    assumption, },
  { existsi E, constructor, apply ceval.Skip, assumption, },
  { cases (safe_ih es) with E',
    destruct h, intros csafe es',
    cases bsafety safe_a es,
    cases w,
    { existsi E, constructor,
      apply ceval.WhileDo_f,
      assumption, sorry, }, -- subset?
    { existsi E', constructor,
      apply ceval.WhileDo_t,
      assumption, assumption, sorry, sorry, } 
      -- need to recursively check stuff?
     },
end