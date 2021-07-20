.. _sect-starting:

***************
Getting Started
***************

Installing from Source
======================

Prerequisites
-------------

Idris 2 is implemented in Idris 2 itself, so to bootstrap it you can build from
generated Scheme sources. To do this, you need either Chez Scheme (default, and
currently preferred since it is the fastest) or Racket. You can get one of
these from:

- `Chez Scheme <https://cisco.github.io/ChezScheme/>`_
- `Racket <https://download.racket-lang.org/>`_

Both are also available from MacPorts/Homebrew and all major Linux
distributions.

**Note**: If you install Chez Scheme from source files, building it locally, make sure
you run ``./configure --threads`` to build multithreading support in.

Downloading and Installing
--------------------------

You can download the Idris 2 source from the `Idris web site
<https://www.idris-lang.org/pages/download.html>`_ or get the latest
development version from `idris-lang/Idris2
<https://github.com/idris-lang/Idris2>`_ on Github.  This includes the Idris 2
source code and the Scheme code generated from that.  Once you have
unpacked the source, you can install it as follows::

    make bootstrap SCHEME=chez

Where `chez` is the executable name of the Chez Scheme compiler. This will
vary from system to system, but is often one of ``scheme``, ``chezscheme``, or
``chezscheme9.5``. If you are building via Racket, you can install it as
follows::

    make bootstrap-racket

Once you've successfully bootstrapped with any of the above commands, you can
install with the command ``make install``.  This will, by default, install into
``${HOME}/.idris2``. You can change this by editing the options in
``config.mk``. For example, to install into ``/usr/local``, you can edit the
``PREFIX`` as follows::

    PREFIX ?= /usr/local

Installing from a Package Manager
=================================

Installing Using Homebrew
-------------------------

If you are Homebrew user you can install Idris 2 together with all the requirements
by running following command::

    brew install idris2

Checking Installation
=====================

To check that installation has succeeded, and to write your first
Idris program, create a file called ``hello.idr`` containing the
following text:

.. code-block:: idris

    module Main

    main : IO ()
    main = putStrLn "Hello world"

If you are familiar with Haskell, it should be fairly clear what the
program is doing and how it works, but if not, we will explain the
details later. You can compile the program to an executable by
entering ``idris2 hello.idr -o hello`` at the shell prompt. This will,
by default, create an executable called ``hello``, which invokes a generated
and compiled Chez Schem program, in the destination directory ``build/exec``
which you can run:

::

    $ idris2 hello.idr -o hello
    $ ./build/exec/hello
    Hello world

Please note that the dollar sign ``$`` indicates the shell prompt!
Some useful options to the Idris command are:

- ``-o prog`` to compile to an executable called ``prog``.

- ``--check`` type check the file and its dependencies without starting the interactive environment.

- ``--package pkg`` add package as dependency, e.g. ``--package contrib`` to make use of the contrib package.

- ``--help`` display usage summary and command line options.

You can find out more about compiling to executables in
Section :ref:`sect-execs`.

The Interactive Environment
===========================

Entering ``idris2`` at the shell prompt starts up the interactive
environment. You should see something like the following:

.. literalinclude:: ../listing/idris-prompt-start.txt

This gives a ``ghci`` style interface which allows evaluation of, as
well as type checking of, expressions; theorem proving, compilation;
editing; and various other operations. The command ``:?`` gives a list
of supported commands. Below, we see an example run in
which ``hello.idr`` is loaded, the type of ``main`` is checked and
then the program is compiled to the executable file ``hello``,
available in the destination directory ``build/exec/``. Type
checking a file, if successful, creates a bytecode version of the file (in this
case ``build/ttc/hello.ttc``) to speed up loading in future. The bytecode is
regenerated if the source file changes.

.. _run1:
.. literalinclude:: ../listing/idris-prompt-helloworld.txt
