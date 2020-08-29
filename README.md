# Zaphod
A two headed language

How is Zaphod a two headed language?  In several ways:
- Zaphod is like Scheme with Haskell's type system[[1]](#1) bolted on
- Zaphod's type system includes an explicit `Top` type, so "untyped"
  functions and macros are possible
- [todo] Zaphod supports an alternative syntax that looks much more
  like Python

## Why does Zaphod exist?
### Dual foundation
Haskell's type system is great, but metaprogramming with Template
Haskell is clunky.  Scheme has a great metaprogramming via macros, but
is untyped.  Zaphod combines the two, with a powerful type system for
normal programming and macros for metaprogramming.

### Dual syntax [todo]
Lisps are great for manipulating ASTs, but many programmers do not
enjoy the parenthesis heavy syntax.  Python has a nice, clean syntax,
but is clunky for AST manipulations.  Zaphod uses the same AST for
both Scheme and Python syntaxes, so code can be written with Python
syntax while AST manipulations (macros) can be written with Scheme
syntax.

## What does Zaphod look like?

### Basics
```scheme
;; line comments
(* block
   comment *)

;; the unit value
()

;; a (quoted) symbol
'zaphod

;; a tuple of three symbols - the following 4 produce the same value
['a 'b 'c]
(tuple 'a 'b 'c)
(cons 'a (cons 'b (cons c ())))
'(a b c)

;; a lambda expression
(lambda (x) [x x])
```

### Types
```scheme
()      ;; the unit type
Symbol  ;; the type for symbols
Top     ;; universal return type
(x . y) ;; pair type

;; tuple types, the following two are equivalent
[x y z]
(x . (y . (z . ())))

;; function types, eg, a function from one symbol to another symbol
(-> [Symbol] Symbol)

;; universal quantification, for parametric polymorphism
(forall a (-> [a] a)) ;; the type of the identity function

;; hard to demonstrate, but symbols can also be types, eg, the type 'Bool
```

### Defining a value
```scheme
;; Explicit type
(def name
     Symbol
     'Zaphod)

;; Inferred type
(def unit ())
```

### Defining a function
```scheme
(defn (id x)
      (forall a (-> [a] a))
      x)
```

### Macros
```scheme
(def defn
     (-> [(Symbol . Top) Type Top] Top)
     (macro (p t e)
       ['def (car p) t ['lambda (cdr p) e]]))
```

### ADTs
```scheme
(data Bool
      True
      False)

(data (Maybe a)
      Nothing
      (Just a))

(defn (not p)
  (-> [Bool] Bool)
  (if p
      False
      True))
```

## Why is Zaphod interesting?
Zaphod takes the minimalism of Scheme and applies it to Haskell's type
system.  Take the `data` "special form" is not a special form at all,
but a macro!  `Bool` is a symbol masquerading as a type, and `Maybe`
is a function from a type to tuple type.  `True`, `False` and `Nil`
are all symbols that have had their types overwritten, and `(Just x)`
is, similarly a coerced tuple.

Consider Haskell's
[maybe](https://hackage.haskell.org/package/base-4.14.0.0/docs/Prelude.html#v:maybe)
function.  Normally, we would implement this with pattern matching,
but Zaphod doesn't have pattern matching yet, so we can abuse the
underlying representation.

```scheme
(defn (maybe d f m)
  (forall a (forall b (-> [b
                           (-> [a] b)
                           (Maybe a)]
                          b)))
  (if (is-symbol m)
      d
      (f (unsafe-coerce (cadr m)))))
```

## Future work
- Records
- Type classes
- Numeric, string, character types

## References
<a id="1">[1]</a>
Dunfield, Joshua, and Neelakantan R. Krishnaswami. “Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism.” Proceedings of the 18th ACM SIGPLAN international conference on Functional programming - ICFP  ’13 (2013): n. pag. Crossref. Web.
