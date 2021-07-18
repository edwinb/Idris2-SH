# Changelog

## [Next version]

### Language changes

* Missing methods in implementations now give a compile time error. This was
  always the intended behaviour, but until now had not been implemented!
* Records now work in `parameters` blocks and `where` clauses.
* Implementations of interfaces now work in `parameters` blocks and
  `where` clauses
* The syntax for Name reflection has changed, and now requires a single brace
  instead of a double brace, e.g. `` `{x} ``

### Compiler changes

* Added incremental compilation, using either the `--inc` flag or the
  `IDRIS2_INC_CGS` environment variable, which compiles modules incrementally.
  In incremental mode, the final build step is much faster than in whole
  program mode (the default), at the cost of runtime performance being about
  half as good. The `--whole-program` flag overrides incremental compilation,
  and reverts to whole program compilation. Incremental compilation is currently
  supported only by the Chez Scheme back end.
  This is currently supported only on Unix-like platforms (not yet Windows)

### Library Changes

#### Prelude

Changed

- Removed `Data.Strings`.  Use `Data.String` instead.

#### System.Concurrency

* Reimplement the `Channels` primitive in the Chez-Scheme backend since it had
  some non-deterministic properties (see issue
  [#1552](https://github.com/idris-lang/idris2/issues/1552)).
  NOTE: Due to complications with race-conditions, Chez not having channels
  built in, etc, the reimplementation changes the semantics slightly:
  `channelPut` no longer blocks until the value has been received under the
  `chez` backend, but instead only blocks if there is already a value in the
  channel that has not been received.
  With thanks to Alain Zscheile (@zseri) for help with understanding condition
  variables, and figuring out where the problems were and how to solve them.

#### Control.Relation, Control.Order

* The old system of interfaces for defining order relations (to say,
  for instance, that LTE is a partial order) is replaced with a new
  system of interfaces. These interfaces defines properties of binary
  relations (functions of type `ty -> ty -> Type`), and orders are
  defined simply as bundles of these properties.

## v0.4.0

### Syntax changes

* Desugar non-binding sequencing in do blocks to (`>>`)
  ([#1095](https://github.com/idris-lang/idris2/pull/1095))
* Multiline Strings with `"""` as delimiters
  ([#1097](https://github.com/idris-lang/idris2/pull/1097))
* Force strict indentation after usage of `with` keyword
  ([#1107](https://github.com/idris-lang/idris2/pull/1107))
* The syntax for parameter blocks has been updated. It now allows to declare
  implicit parameters and give multiplicities for parameters. The old syntax is
  still available for compatibility purposes but will be removed in the future.
* Add support for SnocList syntax: `[< 1, 2, 3]` desugars into `Lin :< 1 :< 2 :<
  3` and their semantic highlighting.
* Underscores can be used as visual separators for digit grouping purposes in
  integer literals: `10_000_000` is equivalent to `10000000` and
  `0b1111_0101_0000` is equivalent to `0b111101010000`. This can aid readability
  of long literals, or literals whose value should clearly separate into parts,
  such as bytes or words in hexadecimal notation.

### Compiler changes

* Added more optimisations and transformations, particularly on case blocks,
  list-shaped types, and enumerations, so generated code will often be slightly
  faster.
* Added `--profile` flag, which generates profile data if supported by a back
  end. Currently supported by the Chez and Racket back ends.
* New `%builtin` pragma for compiling user defined natural numbers to primitive
  `Integer`s (see the
  [docs](https://idris2.readthedocs.io/en/latest/reference/builtins.html))
* The `version` field in `.ipkg` files is now used. Packages are installed into
  a directory which includes its version number, and dependencies can have
  version number ranges using `<=`, `<`, `>=`, `>`, `==` to express version
  constraints. Version numbers must be in the form of integers, separated by
  dots (e.g. `1.0`, `0.3.0`, `3.1.4.1.5` etc)
* Idris now looks in the current working directory, under a subdirectory
  `depends` for local installations of packages before looking globally.
* Added an environment variable `IDRIS2_PACKAGE_PATH` for extending where to
  look for packages.
* Added compiler warnings flags (`-W` prefix):
  - `-Wno-shadowing`: disable shadowing warnings.
  - `-Werror`: treat warnings as errors.
* Experimental flag (`-Xcheck-hashes`) to check hashes instead of filesystem
  times to determine if files should be recompiled. Should help with CI/CD
  caching.

### REPL/IDE mode changes

* Added `:search` command, which searches for functions by type
* `:load`/`:l` and `:cd` commands now only accept paths surrounded by double
  quotes
* Added a timeout to "generate definition" and "proof search" commands,
  defaulting to 1 second (1000 milliseconds) and configurable with
  `%search_timeout <time in milliseconds>`

### Library Changes

#### Prelude

Added

- `Bifoldable` and `Bitraversable` interfaces.
- `Foldable` add `foldlM`, `foldMap`, and `toList`.
- `Monad` interface `>=>`, `<=<` (Kleisli Arrows), and flipped bind (`=<<`).
- `Pair` Applicative and Monad implementations.
- `SnocList` datatype (fliped cons of a linked list).
- `(.:)` function "blackbird operator" (Composition of a two-argument function
  with a single-argument one.)
- `on` function (Eg, ```((+) `on` f) x y = f x + f y```)

Changed

- `===`, `~=~`, and `<+>` operator precedence
- Exctracted `Cast` interface and implementations from `Prelude.Types` to
  `Prelude.Cast`
- Renamed `Data.Strings` to `Data.String`

Hidden

- `countFrom`

#### Base

Added

- `Control.Applicative.Const`.
- New `Control.Monad` Monad Transformers types.
- `Data.Bits`, an interface for bitwise operations.
- `Data.Colist` and `Data.Colist1`.
- `Data.Contravariant` interface for contravariant functors.
- `Data.List` `unzip` function.
- `Data.List1` `zip*` and `unzip*` functions.
- `Data.SnocList`.
- `Data.Stream` `unzipWith` and `unzipWith3` fuctions.
- `Data.Vect` `unzipWith` and `unzipWith3` functions.
- `System.File` `withFile` and total read functions.

Changed:

- Restructured Monad Transformers in `Control.Monad`
- `zip` precedence

#### Contrib

Added

- `Control.Validation`, a library for dependent types input validation.
- `System.Console.GetOpt`, a library for specifying and parsing command line
  options.
- `System.Concurrency.Queue` and `System.Concurrency.BufferedChannel`,
  non-blocking, MT-Safe tools for inter-process communication.

#### New test package

- Moved `tests/Lib.idr` to package as `Test/Golden.idr`.
- Removed `contrib/Test/Golden.idr` which duplicated the test framework now in
  the `test` package.

### Codegen changes

#### Racket

* Now always uses `blodwen-sleep` instead of `idris2_sleep` in order to not
  block the Racket runtime when `sleep` is called.
* Redid condition variables in the Racket codegen based on page 5 of the
  Microsoft [Implementing CVs paper](https://www.microsoft.com/en-us/research/wp-content/uploads/2004/12/ImplementingCVs.pdf).
  Previously, they were based on an implementation using semaphores and
  asynchronous channels, which worked apart from `broadcast`. The rework fixes
  `broadcast` at the cost of losing `wait-timeout` due to increased complexity
  of their internals and interactions between their associated functions.

#### Javascript

* Now use `Number` to represent up to 32 bit precision signed and unsigned
  integers. `Int32` still goes via `BigInt` for multiplication to avoid
  precision issues when getting results larger than `Number.MAX_SAFE_INTEGER`.
  `Bits32` goes via `BigInt` for multiplication for the same reason as well as
  for all bitops, since `Number` uses signed 32 bit integers for those.
* Now use `Number` instead of `BigInt` to represent up to 32 bit fixed precision
  signed and unsigned integers. This should make interop with the FFI more
  straight forward, and might also improve performance.

#### New chez-sep

* This code generator produces many Chez Scheme files and compiles them
  separately instead of producing one huge Scheme program. This significantly
  reduces the amount of memory needed to build large programs. Since this
  backend will skip calling the Chez compiler on modules that haven't changed,
  it also leads to shorter compilation times in large codebases where only some
  files have changed -- for example when developing Idris2 code generators. The
  codegen has a large parallelisation potential but at the moment, it is
  significantly slower for a full rebuild of a large code base (the code
  generation stage takes about 3x longer).

### API changes

* The API now exposes `Compiler.Separate.getCompilationUnits`, which
  can be used for separate code generation by any backend.
* New fixed precision signed integer types `Int8`, `Int16`, `Int32`,
  and `Int64` where added. In addition, all integral types now properly support
  all arithmetic and bitwise operations.
* The compiler now provides primitive cast operations for all combinations
  of primitives with the exception of going from `Double` to `Char` and
  back, and going from `String` to `Char`.
* A new pragma `%doubleLit` to support overloaded floating point literals
  was added.

### Other changes

* Lots of small performance improvements, some of which may be especially
  noticeable in programs that do a lot of type level evaluation.
* Added HTML documentation generation, using the `--mkdoc` flag
* Support for auto-completion in bash-like shells was added.
* Fixed case-splitting to respect any indentation there may be in the term being
  case-split and the surrounding symbols, instead of filtering out the
  whitespace and putting it back as indentation.

## v0.3.0

Library changes:

* Overhaul of the concurrency primitives:

  - Renamed `System.Concurrency.Raw` to `System.Concurrency`.

  - Modified the implementation of `Prelude.IO.fork` in the Chez Scheme RTS, which
    now returns a semaphore instead of a thread object. This allows the main
    thread to wait for the child thread to finish (see next bullet). The Racket
    implementation already returned a thread descriptor, which could be used to
    wait for the thread to finish.

  - Added `Prelude.IO.threadWait` which waits for a thread, identified by a
    `ThreadID`, to finish. This operation is supported by both the Chez Scheme and
    the Racket RTS'es.

  - Added semaphores to `System.Concurrency`, supported by both the Chez Scheme
    and Racket RTS'es.

  - Added barriers to `System.Concurrency`, supported by both the Chez Scheme
    and Racket RTS'es.

  - Added synchronous channels to `System.Concurrency`, supported by both the Chez
    Scheme and Racket RTS'es.

  - Fixed the support for mutexes in the Racket RTS. Formerly, they were
    implemented with semaphores, and calling`mutexRelease` multiple times would
    increment the internal counter multiple times, allowing multiple concurrent
    `mutexAcquire` operations to succeed simultaneously. Currently, `mutexRelease`
    fails when called on a mutex which isn't owned. (However, `mutexRelease` does
    not check whether the mutex is in fact owned by the current thread, which may
    be a bug.)

  - Modified the support for condition variables in the Racket RTS. Formerly,
    they were implemented using synchronous channels, meaning that:
        + `conditionSignal` was a blocking operation; and
        + calling `conditionSignal` on a condition variable on which no thread
          was waiting would wake the next thread to call `conditionWait`,
          whereas condition variables are supposed to be stateless, and only
          wake threads already in the queue.
    The implementation was replaced with an implementation based on asynchronous
    channels and mutexes, based on the following paper:
    [Implementing Condition Variables with Semaphores](https://www.microsoft.com/en-us/research/wp-content/uploads/2004/12/ImplementingCVs.pdf) by Andrew Birrell

  - Removed `threadID` and `blodwen-thisthread`. Formerly, in the Chez Scheme
    backend, this function returned "the thread id of the current thread" as a
    value of type `ThreadID`. However, `fork` returned a "thread object" as a
    value of type `ThreadID`. These are *different kinds of values* in Chez
    Scheme. As there was nothing one could do with a value of type `ThreadID`, I
    chose to remove `threadID`, as it allowed me to implement `threadWait` more
    easily.

  - Renamed `blodwen-lock` and `blodwen-unlock` to `blodwen-mutex-acquire` and
    `blodwen-mutex-release` for consistency, as these functions are referred to
    with acquire and release both in Chez Scheme and in the Idris2 concurrency
    module.

* Added `Data.HVect` in `contrib`, for heterogeneous vectors.
* Various other library functions added throughout `base` and `contrib`

Command-line options changes:

* Added `--color` and `--no-color` options for colored terminal output.
  Color is enabled by default.
* Added `--console-width <auto|n>` option for printing margins.  By default the
  `auto` option is selected, the result is that the compiler detects the current
  terminal width and sets it as the option value, otherwise a user value can be
  provided.  An explicit `0` has the effect of simulating a terminal with
  unbounded width.

Language and compiler changes:

* Removed multiplicity subtyping, as this is unsound and unfortunately causes
  more problems than it solves. This means you sometimes now need to write
  linear versions of functions as special cases. (Though note that the 1
  multiplicity is still considered experimental, so hopefully this will change
  for the better in the future!)
* Added new syntax for named applications of explicit arguments:

     `f {x [= t], x [= t], ...}`
     `f {x [= t], x [= t], ..., _}`

* Added syntax for binding all explicit arguments (in the left hand side);

     `f {}`

* Added new syntax for record updates (without the need for the `record`
  keyword):

     `{x := t, x $= t, ...}`

* Local implementations of interfaces (in `let` or `where` blocks) now work,
  along with `%hint` annotations on local definitions, meaning that local
  definitions can be searched in auto implicit search.
  + Note, though, that there are still some known limitations (with both local
    hints and local implementations) which will be resolved in the next version.
* New experimental ``refc`` code generator, which generates C with reference
  counting.
* Added primitives to the parsing library used in the compiler to get more precise
  boundaries to the AST nodes `FC`.

REPL/IDE mode changes:

* Added `:color (on|off)` option for colored terminal output.
* Added `:consolewidth (auto|n)` option for printing margins.  Mirrors the
  command line option.

## v0.2.1

Language changes:

* `Bits8`, `Bits16`, `Bits32` and `Bits64` primitive types added, with:
  + `Num`, `Eq`, `Ord` and `Show` implementations.
  + Casts from `Integer`, for literals
  + Casts to `Int` (except for `Bits64` which might not fit),
    `Integer` and `String`
  + Passed to C FFI as `unsigned`
  + Primitives added in `Data.Buffer`
* Elaborator reflection and quoting terms
  + Requires extension `%language ElabReflection`
  + API defined in `Language.Reflection`, including functions for getting
    types of global names, constructors of data types, and adding new top
    level declarations
  + Implemented `%macro` function flag, to remove the syntactic noise of
    invoking elaborator scripts. This means the function must always
    be fully applied, and is run under `%runElab`
* Add `import X as Y`
  + This imports the module `X`, adding aliases for the definitions in
    namespace `Y`, so they can be referred to as `Y`.
* `do` notation can now be qualified with a namespace
  + `MyDo.do` opens a `do` block where the `>>=` operator used is `MyDo.(>>=)`

Library changes:

* `IO` operations in the `prelude` and `base` libraries now use the
  `HasIO` interface, rather than using `IO` directly.
* Experimental `Data.Linear.Array` added to `contrib`, supporting mutable
  linear arrays with constant time read/write, convertible to immutable arrays
  with constant time read.
  + Anything in `Data.Linear` in `contrib`, just like the rest of `contrib`,
    should be considered experimental with the API able to change at any time!
    Further experiments in `Data.Linear` are welcome :).
* Experimental `Control.Linear.LIO` added to `contrib`, supporting computations
  which track the multiplicities of their return values, which allows linear
  resources to be tracked.
* Added `Control.Monad.ST`, for update in-place via `STRef` (which is like
  `IORef`, but can escape from `IO`). Also added `Data.Ref` which provides an
  interface to both `IORef` and `STRef`.
* Added `Control.ANSI` in `contrib`, for usage of ANSI escape codes for text
  styling and cursor/screen control in terminals.

Command-line options changes:

* Removed `--ide-mode-socket-with` option.  `--ide-mode-socket` now accepts an
  optional `host:port` argument.
* Added options to override source directory, build directory and output
  directory: `--source-dir`, `--build-dir`, `--output-dir`.
  + These options are also available as fields in the package description:
    `sourcedir`, `builddir`, `outputdir`.

Compiler changes:

* It is now possible to create new backends with minimal overhead.
  `Idris.Driver` exposes the function `mainWithCodegens` that takes
  a list of codegens. The feature in documented [here](https://idris2.readthedocs.io/en/latest/backends/custom.html).
* New code generators `node` and `javascript`.

REPL/IDE mode changes:

* Implemented `:module` command, to load a module during a REPL session.
* Implemented `:doc`, which displays documentation for a name.
* Implemented `:browse`, which lists the names exported by a namespace.
* Added `:psnext`, which continues the previous proof search, looking for the
  next type correct expression
  + Correspondingly, added the IDE mode command `proof-search-next` (which takes
    no arguments)
* Added `:gdnext`, which continues the previous program search, looking for the
  next type correct implementation
  + Correspondingly, added the IDE mode command `generate-def-next` (which takes
    no arguments)
* Improved program search to allow deconstructing intermediate values, and in
  simple cases, the result of recursive calls.

## v0.2.0

The implementation is now self-hosted. To initialise the build, either use
the [bootstrapping version of Idris2](https://github.com/edwinb/Idris2-boot)
or build from the generated Scheme, using `make bootstrap`.

Language changes:

* `total`, `covering` and `partial` flags on functions now have an effect.
* `%default <totality status>` has been implemented. By default, functions must
  be at least `covering`
  + That is, `%default covering` is the default status.
* Fields of records can be accessed (and updated) using the dot syntax,
  such as `r.field1.field2` or `record { field1.field2 = 42 }`.
  For details, see [the "records" entry in the user manual](https://idris2.readthedocs.io/en/latest/reference/records.html)
* New function flag `%tcinline` which means that the function should be
  inlined for the purposes of totality checking (but otherwise not inlined).
  This can be used as a hint for totality checking, to make the checker look
  inside functions that it otherwise might not.
* %transform directive, for declaring transformation rules on runtime
  expressions. Transformation rules are automatically added for top level
  implementations of interfaces.
* A %spec flag on functions which allows arguments to be marked for partial
  evaluation, following the rules from "Scrapping Your Inefficient Engine"
  (ICFP 2010, Brady & Hammond)
* To improve error messages, one can use `with NS.name <term>`
  or `with [NS.name1, NS.name2, ...] <term>` to disable disambiguation
  for the given names in `<term>`. Example: `with MyNS.(>>=) do ...`.

Library additions:

* Additional file management operations in `base`
* New module in `base` for time (`System.Clock`)
* New modules in `contrib` for JSON (`Language.JSON.*`); random numbers
  (`System.Random`)

Compiler updates:

* Data types with a single constructor, with a single unerased arguments,
  are translated to just that argument, to save repeated packing and unpacking.
  (c.f. `newtype` in Haskell)
  + A data type can opt out of this behaviour by specifying `noNewtype` in its
    options list. `noNewtype` allows code generators to apply special handling
    to the generated constructor/deconstructor, for a newtype-like data type,
    that would otherwise be optimised away.
* 0-multiplicity constructor arguments are now properly erased, not just
  given a placeholder null value.

Other improvements:

* Various performance improvements in the typechecker:
  + Noting which metavariables are blocking unification constraints, so that
    they only get retried if those metavariables make progress.
  + Evaluating `fromInteger` at compile time.
* Extend Idris2's literate mode to support reading Markdown and OrgMode files.
  For more details see: ["literate" in the user manual](https://idris2.readthedocs.io/en/latest/reference/literate.html).

## Changes since Idris 1

Everything :). For full details, see:
[updates](https://idris2.readthedocs.io/en/latest/updates/updates.html)
