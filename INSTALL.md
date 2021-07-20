# Installing

- [Installing from source](#installing-from-source)
- [Installing from a package manager](#installing-from-a-package-manager)

## Installing from source

The easiest way to install is via the existing generated Scheme code.
The requirements are:

- A Scheme compiler; either Chez Scheme (default), or Racket.
- `bash`, `GNU make` and `sha256sum`.  On Linux, you probably already have
  this.  On macOS and major BSD flavours, you can install them using a package
  manager: for instance, on macOS, you can install this with the `brew install
  coreutils` and on OpenBSD, with the `pkg_add coreutils bash gmake` command.

On Windows, it has been reported that installing via `MSYS2` works
[MSYS2](https://www.msys2.org/). On Windows older than Windows 8, you may need to
set an environment variable `OLD_WIN=1` or modify it in `config.mk`.

On Raspberry Pi, you can bootstrap via Racket.

By default, code generation is via Chez Scheme. You can use Racket instead,
by setting the environment variable `IDRIS2_CG=racket` before running `make`.
If you install Chez Scheme from source files, building it locally,
make sure you run `./configure --threads` to build multithreading support in.

**NOTE**: On FreeBSD, OpenBSD and NetBSD you need to use `gmake` command instead
of `make` in the following steps.

**NOTE**: If you're running macOS on Apple Silicon (arm64) you may need to run
"`arch -x86_64 make ...`" instead of `make` in the following steps.

### 1: Set installation target directory

- Change the `PREFIX` in `config.mk` to the absolute path of your chosen
installation destination. The default is to install in `$HOME/.idris2`

If you have an existing Idris 2, go to Step 3. Otherwise, read on...

Make sure that:

- `$PREFIX/bin` is in your `PATH`
- `$PREFIX/lib` is in your `LD_LIBRARY_PATH` or `DYLD_LIBRARY_PATH` if on
  `macOS` (so that the system knows where to look for library support code)

### 2: Installing without an existing Idris 2

You can build from pre-built Chez Scheme source, as long as you have Chez Scheme
installed (or, alternatively, Racket). To do this, enter one of the following:

- `make bootstrap SCHEME=chez`
- `make bootstrap-racket`

`chez` is the executable name of the Chez Scheme compiler. You may need to
replace this with the executable for Chez Scheme on your system. This could be
`scheme`, `chezscheme` or `chezscheme9.5` or something else, depending on your
system and the Chez Scheme version.

This builds an Idris 2 compiler from scheme code output from a working Idris 2
compiler (which isn't necessarily up to date, but is up to date enough to
build the current repository). It then rebuilds using the result, and runs
the tests.

If all is well, to install, type:

- `make install`

### 3: Installing with an existing Idris 2

If you have an earlier version of Idris 2 (minimum version 0.2.2) installed:

- `make all`
- `make install`

### 4: (Optional) Self-hosting step

As a final step, you can rebuild from the newly installed Idris 2 to verify
that everything has worked correctly. Assuming that `idris2` is in your
`PATH`.

- `make clean` -- to make sure you're building everything with the new version
- `make all && make install` -- OR
`make all IDRIS2_BOOT='idris2 --codegen racket' && make install`
if using Racket.

### 5: Running tests

After `make all`, type `make test` to check everything works. This uses the
executable in `./build/exec`.

### 6: (Optional) Enabling incremental compilation

If you are working on Idris, incremental compilation means that rebuilds are
much faster, at the cost of runtime performance being slower. To enable
incremental compilation for the Chez back end, set the environment variable
`IDRIS2_INC_CGS=chez`, or set the `--inc chez` flag in `idris2.ipkg`.

### 7: (Optional) Installing the Idris 2 API

You'll only need this if you're developing support tools, such as an external
code generator. To do so, once everything is successfully installed, type:

- `make install-api`

The API will only work if you've completed the self-hosting step, step 4, since
the intermediate code versions need to be consistent throughout. Otherwise, you
will get an `Error in TTC: TTC data is in an older format` error.

### 8: (Optional) Shell Auto-completion

Idris2 supports tab auto-completion for Bash-like shells.

#### For Bash Users

From within bash, run the following command:

```sh
eval "$(idris2 --bash-completion-script idris2)"
```

You can also add it to your `.bashrc` file.

#### For ZSH Users

From within ZSH, run the following commands:

```sh
autoload -U +X compinit && compinit
autoload -U +X bashcompinit && bashcompinit
eval "$(idris2 --bash-completion-script idris2)"
```

You can also add them to your `.zshrc` file.

### Troubleshooting

If you get the message `variable make-thread-parameter is not bound` while
bootstrapping via Chez Scheme, or while running the tests when bootstrapping via
Racket, then your copy of Chez Scheme was built without thread support. Pass
`--threads` to `./configure` while building Chez Scheme to correct the issue.

## Installing from a package manager

### Installing using Homebrew

If you are Homebrew user you can install Idris 2 together with all the requirements
by running the following command:

```sh
brew install idris2
```

### Installing from nix

If you are a [nix](https://nixos.org/features.html) user you can install Idris
2 together with all the requirements by running the following command:

```sh
nix-env -i idris2
```

### Install from nix flakes

If you are a [nix flakes](https://nixos.wiki/wiki/Flakes) user you can install
Idris 2 together with all the requirements by running the following command:

```sh
nix profile install github:idris-lang/Idris2
```

## Running in text editor

### Run on emacs using nix flakes

If you are a [nix flakes](https://nixos.wiki/wiki/Flakes) user you can run
Idris 2 in emacs by running the following command:

```sh
nix run github:idris-lang/Idris2#emacs-with-idris idrisCode.idr
```
