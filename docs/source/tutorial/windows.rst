.. _windows-install:

Prerequisites for Windows
=========================

MSYS2
-----

To build Idris 2 on Windows, an Unix-like environment is needed for 
all the utilities used during the build. `MSYS2 <https://www.msys2.org>`_ provides that for us.

    1. Download the latest version of MSYS2
    2. Run the installer. Don't install it under Program files
       as it needs to write files (the "unix" home directory lies 
       under there, for example)
    3. In the directory where you installed MSYS2, find the file
       ``mingw64.ini`` and add the line ``MSYS2_PATH_TYPE=inherit``.
       This adds the normal windows PATH to the shell in MSYS2.
    4. Start MSYS2 (click on mingw64.exe, as the icon in the start
       menu won't pick up the MSYS2_PATH_TYPE from the ini, it can be
       added to the system settings)
    5. Update the installation with the latest releases with
       ``pacman -Syu``
    5. Install the programs that the build needs with::

            $ pacman -S make mingw-w64-x86_64-gcc


Chez Scheme
-----------

Chez Scheme has a ready-made installer at `GitHub <https://github.com/cisco/ChezScheme/releases>`_

    1. Download the installer and run it, do not install it in a path with spaces, currently Idris2
       has trouble with them.
    2. Add the threaded 64-bit scheme to the PATH. It is the
       ``\bin\ta6nt`` subdirectory to where Chez Scheme was installed. So if you used "C:\Chez" it 
       will be in ``C:\Chez\bin\ta6nt``

Building
--------

1. Start a fresh MSYS2 shell so that it knows about your 
   modified PATH (it's important to use Mingw64 to get
   access to the right compilers).
2. Navigate to the Idris2 directory.
3. Set the SCHEME environment variable that Idris2 needs
   ``export SCHEME=scheme``. This can be set permanently in the 
   bash profile file or the Windows settings.
4. Now ``make bootstrap && make install`` should build Idris2 and
   install it in ``home/<username>/.idris2/bin`` under your MSYS2
   installation. If you add that to the PATH in Windows settings it
   will be usable from any command line (including Powershell or DOS), that you open.