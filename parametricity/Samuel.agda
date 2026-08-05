id : {a : Set}
   → a
   → a
id x = x

ff : {a : Set}
   → {s : a → a}
   → (F : a → Set)
   → (f : {x : a}
        → F x
        → F (s x))
   → {x : a}
   → (y : F x)
   → F (s (s x))
ff F f y = f (f y)

id₁ : {a : Set1}
    → a
    → a
id₁ x = x

ff₁ : {a : Set1}
    → {s : a → a}
    → (F : a → Set1)
    → (f : {x : a}
         → (F x)
         → (F (s x)))
    → {x : a}
    → (y : (F x))
    → (F (s (s x)))
ff₁ F f y = f (f y)

record Set# : Set1 where
  field
    a  : Set
    a' : Set
    a~ : a → a' → Set

record value# (a# : Set#) : Set where
  open Set# a#
  field
    x  : a
    x' : a'
    x~ : a~ x x'

id# : {a : Set#}
    → value# a
    → value# a
id# x = x

ff# : {a : Set#}
    → {s : value# a → value# a}
    → (F : value# a → Set#)
    → (f : {x : value# a}
         → value# (F x)
         → value# (F (s x)))
    → {x : value# a}
    → (y : value# (F x))
    → value# (F (s (s x)))
ff# F f y = f (f y)

free-id' : {a : Set}
         → {a' : Set}
         → {a~ : a → a' → Set}
         → {x  : a }
         → {x' : a'}
         → a~ x x'
         → a~ (id x) (id x')
free-id' {a} {a'} {a~} {u} {u'} u~ = value#.x~ r# where
  a# : Set#
  a# = record {a = a; a' = a'; a~ = a~}

  u# : value# a#
  u# = record {x = u; x' = u'; x~ = u~}

  r# : value# a#
  r# = u#

free-ff' : {a : Set}
         → {a' : Set}
         → {a~ : a → a'
               → Set}
         → {s : a → a }
         → {s' : a' → a'}
         → {s~ : ∀ {x x'}
               → a~ x x'
               → a~ (s x) (s' x')}
         → {F : a → Set}
         → {F' : a' → Set}
         → (F~ : ∀ {x x'}
               → a~ x x'
               → F x → F' x'
               → Set)
         → {f : ∀ {x}
              → F x
              → F (s x)}
         → {f' : ∀ {x'}
               → F' x'
               → F' (s' x')}
         → (f~ : ∀ {x x' x~}
               → {y : F x }
               → {y' : F' x'}
               → F~ x~ y y'
               → F~ (s~ x~)
                    (f y) (f' y'))
         → ∀ {u u' u~}
         → {y : F u }
         → {y' : F' u'}
         → F~ u~ y y'
         → F~ (s~ (s~ u~))
              (ff F f y) (ff F' f' y')
free-ff' {a} {a'} {a~}
         {s} {s'} {s~}
         {F} {F'} F~
         {f} {f'} f~
         {u} {u'} {u~}
         {y} {y'} y~
         = value#.x~ r# where
  a# : Set#
  a# = record {a = a; a' = a'; a~ = a~}

  s# : value# a# → value# a#
  s# x# = let open value# x# in record
        { x = s x
        ; x' = s' x'
        ; x~ = s~ x~
        }

  F# : value# a# → Set#
  F# x# = let open value# x# in record
        { a = F x
        ; a' = F' x'
        ; a~ = F~ x~
        }

  f# : {x# : value# a#}
     → value# (F# x#)
     → value# (F# (s# x#))
  f# {x#} y# = let open value# y# in record
             { x = f x
             ; x' = f' x'
             ; x~ = f~ x~
             }

  u# : value# a#
  u# = record {x = u; x' = u'; x~ = u~}

  y# : value# (F# u#)
  y# = record {x = y; x' = y'; x~ = y~}

  r# : value# (F# (s# (s# u#)))
  r# = ff# F# f# y#
