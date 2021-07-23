*************************
C with Reference Counting
*************************

There is an experimental code generator which compiles to an executable via C,
using a reference counting garbage collector. This is intended as a lightweight
(i.e. minimal dependencies) code generator that can be ported to multiple
platforms, especially those with memory constraints.

Performance is not as good as the Scheme based code generators, partly because
the reference counting has not yet had any optimisation, and partly because of
the limitations of C. However, the main goal is portability: the generated
code should run on any platform that supports a C compiler.

This code generator can be accessed via the REPL command:

::

    Main> :set cg refc

Alternatively, you can set it via the ``IDRIS2_CG`` environment variable:

::

    $ export IDRIS2_CG=refc

The C compiler it invokes is determined by either the ``IDRIS2_CC`` or ``CC``
environment variables. If neither is set, it uses ``cc``.

This code generator does not yet support `:exec`, just `:c`.

Also note that, if you link with any dynamic libraries for interfacing with
C, you will need to arrange for them to be accessible via ``LD_LIBRARY_PATH``
when running the executable. The default Idris 2 support libraries are
statically linked.

Using LibBF
===========

By default, arbitrary precision integers are implemented with
`The GNU Multiple Precision Arithmetic Library <https://gmplib.org/>`_. 
It is under the dual licenses, GNU LGPL v3 and GNU GPL v2, and available via 
most package managers.

There is also an experimental implementation of arbitrary precision integers
with `LibBF Library <https://bellard.org/libbf/>`_, written by Fabrice Bellard
and released under the MIT license. LibBF is much more lightweight: just two 
C files and two headers, compiled size is about 90 KB of x86 code and has no 
dependency on other libraries.

Before using it, you need to build Idris with `BUILD_REFC_WITH_LIBBF=1`. Then 
`LibBf` will be downloaded automatically from official `QuickJS Library <https://bellard.org/quickjs/>`_,
which is more up-to-date than the standalone `LibBf` release. Alternatively, 
if you already have `LibBf` (`libbf.*` and `cutils.*`), you can place them in 
RefC's source code directory ``support/refc``, then no downloading will be performed.

When building your idris source codes, you can set an environment variable 
`IDRIS_REFC_INTEGER=libbf` to use `LibBf`, and you can still use `gmp` by omitting 
it.

Currently the libbf integration is tested against `2021-03-27` version of `QuickJS`.

Extending RefC
==============

RefC can be extended to produce a new backend for languages that support C
foreign functions. For example, a
`Python backend for Idris <https://github.com/madman-bob/idris2-python>`_.

In your backend, use the ``Compiler.RefC`` functions ``generateCSourceFile``,
``compileCObjectFile {asLibrary = True}``, and
``compileCFile {asShared = True}`` to generate a ``.so`` shared object file.

.. code-block:: idris

    _ <- generateCSourceFile defs cSourceFile
    _ <- compileCObjectFile {asLibrary = True} cSourceFile cObjectFile
    _ <- compileCFile {asShared = True} cObjectFile cSharedObjectFile

To run a compiled Idris program, call the ``int main(int argc, char *argv[])``
function in the compiled ``.so`` file, with the arguments you wish to pass to
the running program.

For example, in Python:

.. code-block:: python

    import ctypes
    import sys

    argc = len(sys.argv)
    argv = (ctypes.c_char_p * argc)(*map(str.encode, sys.argv))

    cdll = ctypes.CDLL("main.so")
    cdll.main(argc, argv)

Extending RefC FFIs
-------------------

To make the generated C code recognize additional FFI languages beyond the
standard RefC FFIs, pass the ``additionalFFILangs`` option to
``generateCSourceFile``, with a list of the language identifiers your backend
recognizes.

.. code-block:: idris

    _ <- generateCSourceFile {additionalFFILangs = ["python"]} defs cSourceFile

This will generate stub FFI function pointers in the generated C file, which
your backend should set to the appropriate C functions before ``main`` is
called.

Each ``%foreign "lang: funcName, opts"`` definition will produce a stub whose
name is given by ``cName (UN $ lang ++ "_" ++ funcName)``, of the appropriate
function pointer type.

So the ``%foreign`` function

.. code-block:: idris

    %foreign "python: abs"
    abs : Int -> Int

produces a stub ``python_abs``, which can be backpatched in Python by:

.. code-block:: python

    abs_ptr = ctypes.CFUNCTYPE(ctypes.c_int64, ctypes.c_int64)(abs)
    ctypes.c_void_p.in_dll(cdll, "python_abs").value = ctypes.cast(abs_ptr, ctypes.c_void_p).value
