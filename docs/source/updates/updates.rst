.. _updates-index:

#####################
Changes since Idris 1
#####################

Idris 2 is mostly backwards compatible with Idris 1, with some minor
exceptions. This document describes the changes, approximately in order of
likelihood of encountering them in practice. New features are described at
the end, in Section :ref:`sect-new-features`.

The Section :ref:`typedd-index` describes how these changes affect the code
in the book `Type-Driven Development with Idris <https://www.manning.com/books/type-driven-development-with-idris>`_
by Edwin Brady, available from `Manning <https://www.manning.com>`_.

.. note::
   The documentation for Idris has been published under the Creative
   Commons CC0 License. As such to the extent possible under law, *The
   Idris Community* has waived all copyright and related or neighboring
   rights to Documentation for Idris.

   More information concerning the CC0 can be found online at: http://creativecommons.org/publicdomain/zero/1.0/

New Core Language: Quantities in Types
======================================

Idris 2 is based on `Quantitative Type Theory (QTT)
<https://bentnib.org/quantitative-type-theory.html>`_, a core language
developed by Bob Atkey and Conor McBride. In practice, this means that every
variable in Idris 2 has a *quantity* associated with it. A quantity is one of:

* ``0``, meaning that the variable is *erased* at run time
* ``1``, meaning that the variable is used *exactly once* at run time
* *Unrestricted*, which is the same behaviour as Idris 1

For more details on this, see Section :ref:`sect-multiplicities`. In practice,
this might cause some Idris 1 programs not to type check in Idris 2 due to
attempting to use an argument which is erased at run time.

Erasure
-------

In Idris, names which begin with a lower case letter are automatically bound
as implicit arguments in types, for example in the following skeleton
definition, ``n``, ``a`` and ``m`` are implicitly bound:

.. code-block:: idris

    append : Vect n a -> Vect m a -> Vect (n + m) a
    append xs ys = ?append_rhs

One of the difficulties in compiling a dependently typed programming language
is deciding which arguments are used at run time and which can safely be
erased. More importantly, it's one of the difficulties when programming: how
can a programmer *know* when an argument will be erased?

In Idris 2, a variable's quantity tells us whether it will be available at
run time or not. We can see the quantities of the variables in scope in
``append_rhs`` by inspecting the hole at the REPL:

::

    Main> :t append_rhs
     0 m : Nat
     0 a : Type
     0 n : Nat
       ys : Vect m a
       xs : Vect n a
    -------------------------------------
    append_rhs : Vect (plus n m) a

The ``0`` next to ``m``, ``a`` and ``n`` mean that they are in scope, but there
will be ``0`` occurrences at run-time. That is, it is *guaranteed* that they
will be erased at run-time.

This does lead to some potential difficulties when converting Idris 1 programs,
if you are using implicit arguments at run time.  For example, in Idris 1 you
can get the length of a vector as follows:

.. code-block:: idris

    vlen : Vect n a -> Nat
    vlen {n} xs = n

This might seem like a good idea, since it runs in constant time and takes
advantage of the type level information, but the trade off is that ``n`` has to
be available at run time, so at run time we always need the length of the
vector to be available if we ever call ``vlen``. Idris 1 can infer whether the
length is needed, but there's no easy way for a programmer to be sure.

In Idris 2, we need to state explicitly that ``n`` is needed at run time

.. code-block:: idris

    vlen : {n : Nat} -> Vect n a -> Nat
    vlen xs = n

(Incidentally, also note that in Idris 2, names bound in types are also available
in the definition without explicitly rebinding them.)

This also means that when you call ``vlen``, you need the length available. For
example, this will give an error

.. code-block:: idris

    sumLengths : Vect m a -> Vect n a —> Nat
    sumLengths xs ys = vlen xs + vlen ys

Idris 2 reports::

  vlen.idr:7:20--7:28:While processing right hand side of Main.sumLengths at vlen.idr:7:1--10:1:
  m is not accessible in this context

This means that it needs to use ``m`` as an argument to pass to ``vlen xs``,
where it needs to be available at run time, but ``m`` is not available in
``sumLengths`` because it has multiplicity ``0``.

We can see this more clearly by replacing the right hand side of
``sumLengths`` with a hole...

.. code-block:: idris

    sumLengths : Vect m a -> Vect n a -> Nat
    sumLengths xs ys = ?sumLengths_rhs

...then checking the hole's type at the REPL::

  Main> :t sumLengths_rhs
   0 n : Nat
   0 a : Type
   0 m : Nat
     ys : Vect n a
     xs : Vect m a
  -------------------------------------
  sumLengths_rhs : Nat

Instead, we need to give bindings for ``m`` and ``n`` with
unrestricted multiplicity

.. code-block:: idris

    sumLengths : {m, n : _} -> Vect m a -> Vect n a —> Nat
    sumLengths xs ys = vlen xs + vlen xs

Remember that giving no multiplicity on a binder, as with ``m`` and ``n`` here,
means that the variable has unrestricted usage.

If you're converting Idris 1 programs to work with Idris 2, this is probably the
biggest thing you need to think about. It is important to note,
though, that if you have bound implicits, such as...

.. code-block:: idris

    excitingFn : {t : _} -> Coffee t -> Moonbase t

...then it's a good idea to make sure ``t`` really is needed, or performance
might suffer due to the run time building the instance of ``t`` unnecessarily!

One final note on erasure: it is an error to try to pattern match on an
argument with multiplicity ``0``, unless its value is inferrable from
elsewhere. So, the following definition is rejected

.. code-block:: idris

    badNot : (0 x : Bool) -> Bool
    badNot False = True
    badNot True = False

This is rejected with the error::

  badnot.idr:2:1--3:1:Attempt to match on erased argument False in
  Main.badNot

The following, however, is fine, because in ``sNot``, even though we appear
to match on the erased argument ``x``, its value is uniquely inferrable from
the type of the second argument

.. code-block:: idris

    data SBool : Bool -> Type where
         SFalse : SBool False
         STrue  : SBool True

    sNot : (0 x : Bool) -> SBool x -> Bool
    sNot False SFalse = True
    sNot True  STrue  = False

Experience with Idris 2 so far suggests that, most of the time, as long as
you're using unbound implicits in your Idris 1 programs, they will work without
much modification in Idris 2. The Idris 2 type checker will point out where you
require an unbound implicit argument at run time - sometimes this is both
surprising and enlightening!


Linearity
---------

Full details on linear arguments with multiplicity ``1`` are given in Section
:ref:`sect-multiplicities`. In brief, the intuition behind multiplicity ``1`` is
that if we have a function with a type of the following form...

.. code-block:: idris

    f : (1 x : a) -> b

...then the guarantee given by the type system is that *if* ``f x`` *is used
exactly once, then* ``x`` *is used exactly once* in the process.

Prelude and ``base`` libraries
==============================

The Prelude in Idris 1 contained a lot of definitions, many of them rarely
necessary. The philosophy in Idris 2 is different. The (rather vaguely
specified) rule of thumb is that it should contain the basic functions
required by almost any non-trivial program.

This is a vague specification since different programmers will consider
different things absolutely necessary, but the result is that it contains:

- Anything the elaborator can desugar to (e.g. tuples, ``()``, ``=``)
- Basic types ``Bool``, ``Nat``, ``List``, ``Stream``, ``Dec``, ``Maybe``,
  ``Either``
- The most important utility functions: ``id``, ``the``, composition, etc
- Interfaces for arithmetic and implementations for the primitives and
  basic types
- Basic ``Char`` and ``String`` manipulation
- ``Show``, ``Eq``, ``Ord``, and implementations for all types in the prelude
- Interfaces and functions for basic proof (``cong``, ``Uninhabited``, etc)
- ``Semigroup``, ``Monoid``
- ``Functor``, ``Applicative``, ``Monad`` and related functions
- ``Foldable``, ``Alternative`` and ``Traversable``
- ``Enum``, for list range syntax
- Console ``IO``

Anything which doesn't fit in here has been moved to the ``base`` libraries.
Among other places, you can find some of the functions which used to be
in the prelude in:

- ``Data.List`` and ``Data.Nat``
- ``Data.Maybe`` and ``Data.Either``
- ``System.File`` and ``System.Directory``, (file management was previously
  part of the prelude)
- ``Decidable.Equality``

Smaller Changes
===============

Ambiguous Name Resolution
-------------------------

Idris 1 worked very hard to resolve ambiguous names, by type, even if this
involved some complicated interaction with interface resolution. This could
sometimes be the cause of long type checking times. Idris 2 simplifies this, at
the cost of sometimes requiring more programmer annotations on ambiguous
names.

As a general rule, Idris 2 will be able to disambiguate between names which
have different concrete return types (such as data constructors), or which have
different concrete argument types (such as record projections). It may struggle
to resolve ambiguities if one name requires an interface to be resolved.
It will postpone resolution if a name can't be resolved immediately, but unlike
Idris 1, it won't attempt significant backtracking. If you have deeply nested
ambiguous names (beyond a small threshold, default 3) Idris 2 will report an
error.  You can change this threshold with a directive, for example:

.. code-block:: idris

    %ambiguity_depth 10

However, in such circumstances it is almost certainly a better idea to
disambiguate explicitly.

Indeed in general, if you get an ambiguous name error, the best approach is to
give the namespace explicitly. You can also rebind names locally:

.. code-block:: idris

    Main> let (::) = Prelude.(::) in [1,2,3]
    [1, 2, 3]

One difficulty which remains is resolving ambiguous names where one possibility
is an interface method, and another is a concrete top level function.
For example, we may have:

.. code-block:: idris

    Prelude.(>>=) : Monad m => m a -> (a -> m b) -> m b
    LinearIO.(>>=) : (1 act : IO a) -> (1 k : a -> IO b) -> IO b

As a pragmatic choice, if type checking in a context where the more concrete
name is valid (``LinearIO.(>>=)`` here, so if type checking an expression known
to have type ``IO t`` for some ``t``), the more concrete name will be chosen.

This is somehow unsatisfying, so we may revisit this in future!

Modules, namespaces and export
------------------------------

The visibility rules, as controlled by the ``private``, ``export`` and
``public export`` modifiers, now refer to the visibility of names from
other *namespaces*, rather than other *files*.

So if you have the following, all in the same file...

.. code-block:: idris

    namespace A
      private
      aHidden : Int -> Int
      aHidden x = x * 2

      export
      aVisible : Int -> Int
      aVisibile x = aHidden x

    namespace B
      export
      bVisible : Int -> Int
      bVisible x = aVisible (x * 2)

...then ``bVisible`` can access ``aVisible``, but not ``aHidden``.

Records are, as before, defined in their own namespace, but fields are always
visible from the parent namespace.

Also, module names must now match the filename in which they're defined, with
the exception of the module ``Main``, which can be defined in a file with
any name.

``%language`` pragmas
---------------------

There are several ``%language`` pragmas in Idris 1, which define various
experimental extensions. None of these are available in Idris 2, although
extensions may be defined in the future.

Also removed was the ``%access`` pragma for default visibility, use visibility
modifiers on each declaration instead.

``let`` bindings
----------------

``let`` bindings, i.e. expressions of the form ``let x = val in e`` have
slightly different behaviour. Previously, you could rely on the computational
behaviour of ``x`` in the scope of ``e``, so type checking could take into
account that ``x`` reduces to ``val``. Unfortunately, this leads to complications
with ``case`` and ``with`` clauses: if we want to preserve the computational
behaviour, we would need to make significant changes to the way ``case`` and
``with`` are elaborated.

So, for simplicity and consistency (and, realistically, because I don't have
enough time to resolve the problem for ``case`` and ``with``) the above
expression ``let x = val in e`` is equivalent to ``(\x => e) val``.

So, ``let`` now effectively generalises a complex subexpression.
If you do need the computational behaviour of a definition, it is now possible
using local function definitions instead - see Section :ref:`sect-local-defs`
below.

``auto``-implicits and Interfaces
---------------------------------

Interfaces and ``auto``-implicit arguments are similar, in that they invoke an
expression search mechanism to find the value of an argument. In Idris 1,
they were implemented separately, but in Idris 2, they use the same mechanism.
Consider the following *total* definition of ``fromMaybe``:

.. code-block:: idris

    data IsJust : Maybe a -> Type where
         ItIsJust : IsJust (Just val)

    fromMaybe : (x : Maybe a) -> {auto p : IsJust x} -> a
    fromMaybe (Just x) {p = ItIsJust} = x

Since interface resolution and ``auto``-implicits are now the same thing,
the type of ``fromMaybe`` can be written as:

.. code-block:: idris

    fromMaybe : (x : Maybe a) -> IsJust x => a

So now, the constraint arrow ``=>`` means that the argument will be found
by ``auto``-implicit search.

When defining a ``data`` type, there are ways to control how ``auto``-implicit
search will proceed, by giving options to the data type. For example:

.. code-block:: idris

    data Elem : (x : a) -> (xs : List a) -> Type where
         [search x]
         Here : Elem x (x :: xs)
         There : Elem x xs -> Elem x (y :: xs)

The ``search x`` option means that ``auto``-implicit search for a value of
type ``Elem t ts`` will start as soon as the type checker has resolved the
value ``t``, even if ``ts`` is still unknown.

By default, ``auto``-implicit search uses the constructors of a data type
as search hints. The ``noHints`` option on a data type turns this behaviour
off.

You can add your own search hints with the ``%hint`` option on a function.
For example:

.. code-block:: idris

    data MyShow : Type -> Type where
         [noHints]
         MkMyShow : (myshow : a -> String) -> MyShow a

    %hint
    showBool : MyShow Bool
    showBool = MkMyShow (\x => if x then "True" else "False")

    myShow : MyShow a => a -> String
    myShow @{MkMyShow myshow} = myshow

In this case, searching for ``MyShow Bool`` will find ``showBool``, as we
can see if we try evaluating ``myShow True`` at the REPL:

::

    Main> myShow True
    "True"

In fact, this is how interfaces are elaborated. However, ``%hint`` should be
used with care. Too many hints can lead to a large search space!

Record fields
-------------

Record fields can now be accessed via a ``.``. For example, if you have:

.. code-block:: idris

    record Person where
        constructor MkPerson
        firstName, middleName, lastName : String
        age : Int

and you have a record ``fred : Person``, then you can use ``fred.firstName``
to access the ``firstName`` field.

Totality and Coverage
---------------------

``%default covering`` is now the default status, so all functions must cover
all their inputs unless stated otherwise with a ``partial`` annotation, or
switching to ``%default partial`` (which is not recommended - use a ``partial``
annotation instead to have the smallest possible place where functions are
partial).

Build artefacts
---------------

This is not really a language change, but a change in the way Idris saves
checked files, and still useful to know. All checked modules are now saved in a
directory ``build/ttc``, in the root of the source tree, with the directory
structure following the directory structure of the source.  Executables are
placed in ``build/exec``.

Packages
--------

Dependencies on other packages are now indicated with the ``depends`` field,
the ``pkgs`` field is no longer recognized. Also, fields with URLS or other
string data (other than module or package names), must be enclosed in double
quotes.
For example:

::

        package lightyear

        sourceloc  = "git://git@github.com:ziman/lightyear.git"
        bugtracker = "http://www.github.com/ziman/lightyear/issues"

        depends = effects

        modules = Lightyear
                , Lightyear.Position
                , Lightyear.Core
                , Lightyear.Combinators
                , Lightyear.StringFile
                , Lightyear.Strings
                , Lightyear.Char
                , Lightyear.Testing


.. _sect-new-features:

New features
============

As well as the change to the core language to use quantitative type theory,
described above, there are several other new features.

.. _sect-local-defs:

Local function definitions
--------------------------

Functions can now be defined locally, using a ``let`` block. For example,
``greet`` in the following example, which is defined in the scope of a local
variable ``x``:

.. code-block:: idris

    chat : IO ()
    chat
        = do putStr "Name: "
             x <- getLine
             let greet : String -> String
                 greet msg = msg ++ " " ++ x
             putStrLn (greet "Hello")
             putStrLn (greet "Bye")

These ``let`` blocks can be used anywhere (in the middle of ``do`` blocks
as above, but also in any function, or in type declarations).
``where`` blocks are now elaborated by translation into a local ``let``.

However, Idris no longer attempts to infer types for functions defined in
``where`` blocks, because this was fragile. This may be reinstated, if we can
come up with a good, predictable approach.

Scope of implicit arguments
---------------------------

Implicit arguments in a type are now in scope in the body of a definition.
We've already seen this above, where ``n`` is in scope automatically in the
body of ``vlen``:

.. code-block:: idris

    vlen : {n : Nat} -> Vect n a -> Nat
    vlen xs = n

This is important to remember when using ``where`` blocks, or local definitions,
since the names in scope will also be in scope when declaring the *type* of
the local definition. For example, the following definition, where we attempt
to define our own version of ``Show`` for ``Vect``, will fail to type check:

.. code-block:: idris

    showVect : Show a => Vect n a -> String
    showVect xs = "[" ++ showBody xs ++ "]"
      where
        showBody : Vect n a -> String
        showBody [] = ""
        showBody [x] = show x
        showBody (x :: xs) = show x ++ ", " ++ showBody xs

This fails because ``n`` is in scope already, from the type of ``showVect``,
in the type declaration for ``showBody``, and so the first clause ``showBody
[]`` will fail to type check because ``[]`` has length ``Z``, not ``n``. We can
fix this by locally binding ``n``:

.. code-block:: idris

    showVect : Show a => Vect n a -> String
    showVect xs = "[" ++ showBody xs ++ "]"
      where
        showBody : forall n . Vect n a -> String
        ...

Or, alternatively, using a new name:

.. code-block:: idris

    showVect : Show a => Vect n a -> String
    showVect xs = "[" ++ showBody xs ++ "]"
      where
        showBody : Vect n' a -> String
        ...

Idris 1 took a different approach here: names which were parameters to data
types were in scope, other names were not. The Idris 2 approach is, we hope,
more consistent and easier to understand.

.. _sect-imp-lambda-args:

Positional implicit lambda arguments
-------------------------

In Idris2 you can now declare positional implicit arguments for lambda expressions,
where positional means that whichever names you choose for the arguments, the i-th
positional implicit argument will always correspond to the i-th implicit binder in
the type of the lambda:

.. code-block:: idris

    \${1 len : Nat}, val => replicate len val

As for explicit arguments, you can specify the multiplicity and the type
also for positional implicit arguments, and the two type of arguments can be
interleaved:

.. code-block:: idris

    \exp1, ${imp1}, exp2, ${imp2}, ..., ${imp3} => ...

Sequence of consecutive positional implicit arguments can be grouped in a single pair
of braces:

.. code-block:: idris

    \exp1, ${imp1, imp2 : Type, 1 imp3, 0 imp4 : Type}, exp2, ${imp5} => ...

.. _sect-app-syntax-additions:

Function application syntax additions
-------------------------------------

From now on you can utilise the new syntax of function applications:

.. code-block:: idris

    f {x1 [= e1], x2 [= e2], ...}

There are three additions here:

1. More than one argument can be written in braces, separated with commas:

.. code-block:: idris

    record Dog where
      constructor MkDog
      name : String
      age : Nat

    -- Notice that `name` and `age` are explicit arguments.
    -- See paragraph (2)
    haveADog : Dog
    haveADog = MkDog {name = "Max", age = 3}

    pairOfStringAndNat : (String, Nat)
    pairOfStringAndNat = MkPair {x = "year", y = 2020}

    myPlus : (n : Nat) -> (k : Nat) -> Nat
    myPlus {n = Z   , k} = k
    myPlus {n = S n', k} = S (myPlus n' k)

    twoPlusTwoIsFour : myPlus {n = 2, k = 2} === 4
    twoPlusTwoIsFour = Refl

2. Arguments in braces can now correspond to explicit, implicit and auto implicit
   dependent function types (``Pi`` types), provided the domain type is named:

.. code-block:: idris

    myPointlessFunction : (exp : String) -> {imp : String} -> {auto aut : String} -> String
    myPointlessFunction exp = exp ++ imp ++ aut

    callIt : String
    callIt = myPointlessFunction {imp = "a ", exp = "Just ", aut = "test"}

Order of the arguments doesn't matter as long as they are in braces and the names are distinct.
It is better to stick named arguments in braces at the end of your argument list, because
regular unnamed explicit arguments are processed first and take priority:

.. code-block:: idris

    myPointlessFunction' : (a : String) -> String -> (c : String) -> String
    myPointlessFunction' a b c = a ++ b ++ c

    badCall : String
    badCall = myPointlessFunction' {a = "a", c = "c"} "b"

This snippet won't type check, because "b" in ``badCall`` is passed first,
although logically we want it to be second.
Idris will tell you that it couldn't find a spot for ``a = "a"`` (because "b" took its place),
so the application is ill-formed.

Thus if you want to use the new syntax, it is worth naming your ``Pi`` types.

3. Multiple explicit arguments can be "skipped" more easily with the following syntax:

.. code-block:: idris

    f {x1 [= e1], x2 [= e2], ..., xn [= en], _}

or

.. code-block:: idris

    f {}

in case none of the named arguments are wanted.

Examples:

.. code-block:: idris

    import Data.Nat

    record Four a b c d where
      constructor MkFour
      x : a
      y : b
      z : c
      w : d

    firstTwo : Four a b c d -> (a, b)
    firstTwo $ MkFour {x, y, _} = (x, y)
    -- firstTwo $ MkFour {x, y, z = _, w = _} = (x, y)

    dontCare : (x : Nat) -> Nat -> Nat -> Nat -> (y : Nat) -> x + y = y + x
    dontCare {} = plusCommutative {}
    --dontCare _ _ _ _ _ = plusCommutative _ _

Last rule worth noting is the case of named applications with repeated argument names, e.g:

.. code-block:: idris

    data WeirdPair : Type -> Type -> Type where
      MkWeirdPair : (x : a) -> (x : b) -> WeirdPair a b

    weirdSnd : WeirdPair a b -> b
    --weirdSnd $ MkWeirdPair {x, x} = x
    --                        ^
    -- Error: "Non linear pattern variable"
    -- But that one is okay:
    weirdSnd $ MkWeirdPair {x = _, x} = x

In this example the name ``x`` is given repeatedly to the ``Pi`` types of the data constructor ``MkWeirdPair``.
In order to deconstruct the ``WeirdPair a b`` in ``weirdSnd``, while writing the left-hand side of the pattern-matching clause
in a named manner (via the new syntax), we have to rename the first occurrence of ``x`` to any fresh name or the ``_`` as we did.
Then the definition type checks normally.

In general, duplicate names are bound sequentially on the left-hand side and must be renamed for the pattern expression to be valid.

The situation is similar on the right-hand side of pattern-matching clauses:

.. code-block:: idris

   0 TypeOf : a -> Type
   TypeOf _ = a

   weirdId : {0 a : Type} -> (1 a : a) -> TypeOf a
   weirdId a = a

   zero : Nat
   -- zero = weirdId { a = Z }
   --                      ^
   -- Error: "Mismatch between: Nat and Type"
   -- But this works:
   zero = weirdId { a = Nat, a = Z }

Named arguments should be passed sequentially in the order they were defined in the ``Pi`` types,
regardless of their (imp)explicitness.

Better inference
----------------

In Idris 1, holes (that is, unification variables arising from implicit
arguments) were local to an expression, and if they were not resolved while
checking the expression, they would not be resolved at all. In Idris 2,
they are global, so inference works better. For example, we can now say:

.. code-block:: idris

    test : Vect ? Int
    test = [1,2,3,4]

    Main> :t test
    Main.test : Vect (S (S (S (S Z)))) Int

The ``?``, incidentally, differs from ``_`` in that ``_`` will be bound as
an implicit argument if unresolved after checking the type of ``test``, but
``?`` will be left as a hole to be resolved later. Otherwise, they can be
used interchangeably.

Dependent case
--------------

``case`` blocks were available in Idris 1, but with some restrictions. Having
better inference means that ``case`` blocks work more effectively in Idris 2,
and dependent case analysis is supported.

.. code-block:: idris

    append : Vect n a -> Vect m a -> Vect (n + m) a
    append xs ys
        = case xs of
               [] => ys
               (x :: xs) => x :: append xs ys

The implicit arguments and original values are still available in the body of
the ``case``. Somewhat contrived, but the following is valid:

.. code-block:: idris

    info : {n : _} -> Vect n a -> (Vect n a, Nat)
    info xs
        = case xs of
               [] => (xs, n)
               (y :: ys) => (xs, n)


Record updates
--------------

Dependent record updates work, provided that all relevant fields are updated
at the same time. Dependent record update is implemented via dependent ``case``
blocks rather than by generating a specific update function for each field as
in Idris 1, so you will no longer get mystifying errors when trying to update
dependent records!

For example, we can wrap a vector in a record, with an explicit length
field:

.. code-block:: idris

    record WrapVect a where
      constructor MkVect
      purpose : String
      length : Nat
      content : Vect length a

Then, we can safely update the ``content``, provided we update the ``length``
correspondingly:

.. code-block:: idris

    addEntry : String -> WrapVect String -> WrapVect String
    addEntry val = record { length $= S,
                            content $= (val :: ) }

Another novelty - new update syntax (previous one still functional):

.. code-block:: idris

    record Three a b c where
      constructor MkThree
      x : a
      y : b
      z : c

    -- Yet another contrived example
    mapSetMap : Three a b c -> (a -> a') -> b' -> (c -> c') -> Three a' b' c'
    mapSetMap three@(MkThree x y z) f y' g = {x $= f, y := y', z $= g} three

The ``record`` keyword has been discarded for brevity, symbol ``:=`` replaces ``=``
in order to not introduce any ambiguity.

Generate definition
-------------------

A new feature of the IDE protocol supports generating complete definitions from
a type signature. You can try this at the REPL, for example, given our
favourite introductory example...

.. code-block:: idris

    append : Vect n a -> Vect m a -> Vect (n + m) a

...assuming this is defined on line 3, you can use the ``:gd`` command as
follows:

.. code-block:: idris

    Main> :gd 3 append
    append [] ys = ys
    append (x :: xs) ys = x :: append xs ys

This works by a fairly simple brute force search, which tries searching for a
valid right hand side, and case splitting on the left if that fails, but is
remarkably effective in a lot of situations. Some other examples which work:

.. code-block:: idris

    my_cong : forall f . (x : a) -> (y : a) -> x = y -> f x = f y
    my_curry : ((a, b) -> c) -> a -> b -> c
    my_uncurry : (a -> b -> c) -> (a, b) -> c
    append : Vect n a -> Vect m a -> Vect (n + m) a
    lappend : (1 xs : List a) -> (1 ys : List a) -> List a
    zipWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c

This is available in the IDE protocol via the ``generate-def`` command.

Chez Scheme target
------------------

The default code generator is, for the moment, `Chez Scheme
<https://www.scheme.com/>`_. Racket and Gambit code generators are also
available. There is not yet a way to plug in code generators as in Idris 1,
but this is coming.
To change the code generator, you can use the ``:set cg`` command:

::

    Main> :set cg racket

Early experience shows that both are much faster than the Idris 1 C code
generator, in both compile time and execution time (but we haven't done any
formal study on this yet, so it's just anecdotal evidence).
