module System.File

import public Data.Fuel

import Data.Buffer
import Data.List
import Data.String
import System.Info
import System.Errno

%default total

public export
data Mode = Read | WriteTruncate | Append | ReadWrite | ReadWriteTruncate | ReadAppend

public export
FilePtr : Type
FilePtr = AnyPtr

support : String -> String
support fn = "C:" ++ fn ++ ", libidris2_support, idris_file.h"

%foreign support "idris2_openFile"
         "node:support:openFile,support_system_file"
prim__open : String -> String -> PrimIO FilePtr

%foreign support "idris2_closeFile"
         "node:lambda:(fp) => require('fs').closeSync(fp.fd)"
prim__close : FilePtr -> PrimIO ()

%foreign support "idris2_fileError"
         "node:lambda:x=>(x===1?1:0)"
prim__error : FilePtr -> PrimIO Int

%foreign support "idris2_fileErrno"
         "node:support:fileErrno,support_system_file"
prim__fileErrno : PrimIO Int

%foreign support "idris2_seekLine"
         "node:support:seekLine,support_system_file"
prim__seekLine : FilePtr -> PrimIO Int

%foreign support "idris2_readLine"
         "node:support:readLine,support_system_file"
prim__readLine : FilePtr -> PrimIO (Ptr String)

%foreign support "idris2_readChars"
prim__readChars : Int -> FilePtr -> PrimIO (Ptr String)
%foreign "C:fgetc,libc 6"
prim__readChar : FilePtr -> PrimIO Int

%foreign support "idris2_writeLine"
         "node:lambda:(filePtr, line) => require('fs').writeSync(filePtr.fd, line, undefined, 'utf-8')"
prim__writeLine : FilePtr -> String -> PrimIO Int

%foreign support "idris2_eof"
         "node:lambda:x=>(x.eof?1:0)"
prim__eof : FilePtr -> PrimIO Int

%foreign "C:fflush,libc 6"
prim__flush : FilePtr -> PrimIO Int
%foreign support "idris2_popen"
prim__popen : String -> String -> PrimIO FilePtr
%foreign support "idris2_pclose"
prim__pclose : FilePtr -> PrimIO ()

%foreign support "idris2_removeFile"
prim__removeFile : String -> PrimIO Int

%foreign support "idris2_fileSize"
         "node:lambda:fp=>require('fs').fstatSync(fp.fd).size"
prim__fileSize : FilePtr -> PrimIO Int

%foreign support "idris2_fileSize"
prim__fPoll : FilePtr -> PrimIO Int

%foreign support "idris2_fileAccessTime"
prim__fileAccessTime : FilePtr -> PrimIO Int

%foreign support "idris2_fileModifiedTime"
         "node:lambda:fp=>require('fs').fstatSync(fp.fd).mtimeMs / 1000"
prim__fileModifiedTime : FilePtr -> PrimIO Int

%foreign support "idris2_fileStatusTime"
prim__fileStatusTime : FilePtr -> PrimIO Int

%foreign support "idris2_stdin"
         "node:lambda:x=>({fd:0, buffer: Buffer.alloc(0), name:'<stdin>', eof: false})"
prim__stdin : FilePtr

%foreign support "idris2_stdout"
         "node:lambda:x=>({fd:1, buffer: Buffer.alloc(0), name:'<stdout>', eof: false})"
prim__stdout : FilePtr

%foreign support "idris2_stderr"
         "node:lambda:x=>({fd:2, buffer: Buffer.alloc(0), name:'<stderr>', eof: false})"
prim__stderr : FilePtr

%foreign "C:chmod, libc 6, sys/stat.h"
         "node:support:chmod,support_system_file"
prim__chmod : String -> Int -> PrimIO Int

modeStr : Mode -> String
modeStr Read              = if isWindows then "rb" else "r"
modeStr WriteTruncate     = if isWindows then "wb" else "w"
modeStr Append            = if isWindows then "ab" else "a"
modeStr ReadWrite         = if isWindows then "rb+" else "r+"
modeStr ReadWriteTruncate = if isWindows then "wb+" else "w+"
modeStr ReadAppend        = if isWindows then "ab+" else "a+"

public export
data FileError = GenericFileError Int -- errno
               | FileReadError
               | FileWriteError
               | FileNotFound
               | PermissionDenied
               | FileExists

returnError : HasIO io => io (Either FileError a)
returnError
    = do err <- primIO prim__fileErrno
         pure $ Left $
           case err of
              0 => FileReadError
              1 => FileWriteError
              2 => FileNotFound
              3 => PermissionDenied
              4 => FileExists
              _ => GenericFileError (err-5)

export
Show FileError where
  show (GenericFileError errno) = strerror errno
  show FileReadError = "File Read Error"
  show FileWriteError = "File Write Error"
  show FileNotFound = "File Not Found"
  show PermissionDenied = "Permission Denied"
  show FileExists = "File Exists"

ok : HasIO io => a -> io (Either FileError a)
ok x = pure (Right x)

public export
data File : Type where
     FHandle : FilePtr -> File

export
stdin : File
stdin = FHandle prim__stdin

export
stdout : File
stdout = FHandle prim__stdout

export
stderr : File
stderr = FHandle prim__stderr

export
openFile : HasIO io => String -> Mode -> io (Either FileError File)
openFile f m
    = do res <- primIO (prim__open f (modeStr m))
         if prim__nullAnyPtr res /= 0
            then returnError
            else ok (FHandle res)

export
closeFile : HasIO io => File -> io ()
closeFile (FHandle f) = primIO (prim__close f)

||| Check if a file exists for reading.
export
exists : HasIO io => String -> io Bool
exists f
    = do Right ok <- openFile f Read
             | Left err => pure False
         closeFile ok
         pure True

||| Pick the first existing file
export
firstExists : HasIO io => List String -> io (Maybe String)
firstExists [] = pure Nothing
firstExists (x :: xs) = if !(exists x) then pure (Just x) else firstExists xs

export
fileError : HasIO io => File -> io Bool
fileError (FHandle f)
    = do x <- primIO $ prim__error f
         pure (x /= 0)

||| Seek through the next newline.
||| This is @fGetLine@ without the overhead of copying
||| any characters.
export
fSeekLine : HasIO io => (h : File) -> io (Either FileError ())
fSeekLine (FHandle f)
    = do res <- primIO (prim__seekLine f)
         if res /= 0
            then returnError
            else ok ()

export
fGetLine : HasIO io => (h : File) -> io (Either FileError String)
fGetLine (FHandle f)
    = do res <- primIO (prim__readLine f)
         if prim__nullPtr res /= 0
            then returnError
            else ok (prim__getString res)

export
fGetChars : HasIO io => (h : File) -> Int -> io (Either FileError String)
fGetChars (FHandle f) max
    = do res <- primIO (prim__readChars max f)
         if prim__nullPtr res /= 0
            then returnError
            else ok (prim__getString res)

export
fGetChar : HasIO io => (h : File) -> io (Either FileError Char)
fGetChar (FHandle h)
    = do c <- primIO (prim__readChar h)
         ferr <- primIO (prim__error h)
         if (ferr /= 0)
            then returnError
            else ok (cast c)

export
fPutStr : HasIO io => (h : File) -> String -> io (Either FileError ())
fPutStr (FHandle f) str
    = do res <- primIO (prim__writeLine f str)
         if res == 0
            then returnError
            else ok ()

export
fPutStrLn : HasIO io => (h : File) -> String -> io (Either FileError ())
fPutStrLn f str = fPutStr f (str ++ "\n")

export
fEOF : HasIO io => (h : File) -> io Bool
fEOF (FHandle f)
    = do res <- primIO (prim__eof f)
         pure (res /= 0)

export
fflush : HasIO io => (h : File) -> io ()
fflush (FHandle f)
    = ignore $ primIO (prim__flush f)

export
popen : HasIO io => String -> Mode -> io (Either FileError File)
popen f m = do
    ptr <- primIO (prim__popen f (modeStr m))
    if prim__nullAnyPtr ptr /= 0
        then returnError
        else pure (Right (FHandle ptr))

export
pclose : HasIO io => File -> io ()
pclose (FHandle h) = primIO (prim__pclose h)

export
fileAccessTime : HasIO io => (h : File) -> io (Either FileError Int)
fileAccessTime (FHandle f)
    = do res <- primIO (prim__fileAccessTime f)
         if res > 0
            then ok res
            else returnError

export
fileModifiedTime : HasIO io => (h : File) -> io (Either FileError Int)
fileModifiedTime (FHandle f)
    = do res <- primIO (prim__fileModifiedTime f)
         if res > 0
            then ok res
            else returnError

export
fileStatusTime : HasIO io => (h : File) -> io (Either FileError Int)
fileStatusTime (FHandle f)
    = do res <- primIO (prim__fileStatusTime f)
         if res > 0
            then ok res
            else returnError

export
removeFile : HasIO io => String -> io (Either FileError ())
removeFile fname
    = do res <- primIO (prim__removeFile fname)
         if res == 0
            then ok ()
            else returnError

export
fileSize : HasIO io => (h : File) -> io (Either FileError Int)
fileSize (FHandle f)
    = do res <- primIO (prim__fileSize f)
         if res >= 0
            then ok res
            else returnError

export
fPoll : HasIO io => File -> io Bool
fPoll (FHandle f)
    = do p <- primIO (prim__fPoll f)
         pure (p > 0)

||| Perform a given operation on successful file open
||| and ensure the file is closed afterwards or perform
||| a different operation if the file fails to open.
export
withFile : HasIO io => (filename : String) ->
                       Mode ->
                       (onError : FileError -> io a) ->
                       (onOpen  : File -> io (Either a b)) ->
                       io (Either a b)
withFile filename mode onError onOpen =
  do Right h <- openFile filename mode
       | Left err => Left <$> onError err
     res <- onOpen h
     closeFile h
     pure res

readLinesOnto : HasIO io => (acc : List String) ->
                            (offset : Nat) ->
                            (fuel : Fuel) ->
                            File ->
                            io (Either FileError (Bool, List String))
readLinesOnto acc _ Dry h = pure (Right (False, reverse acc))
readLinesOnto acc offset (More fuel) h
  = do False <- fEOF h
         | True => pure $ Right (True, reverse acc)
       case offset of
            (S offset') => (fSeekLine h *> readLinesOnto acc offset' (More fuel) h) @{Applicative.Compose}
            0           => (fGetLine h >>= \str => readLinesOnto (str :: acc) 0 fuel h) @{Monad.Compose}

||| Read a chunk of a file in a line-delimited fashion.
||| You can use this function to read an entire file
||| as with @readFile@ by reading until @forever@ or by
||| iterating through pages until hitting the end of
||| the file.
|||
||| The @limit@ function can provide you with enough
||| fuel to read exactly a given number of lines.
|||
||| On success, returns a tuple of whether the end of
||| the file was reached or not and the lines read in
||| from the file.
|||
||| Note that each line will still have a newline
||| character at the end.
|||
||| Important: because we are chunking by lines, this
||| function's totality depends on the assumption that
||| no single line in the input file is infinite.
export
readFilePage : HasIO io => (offset : Nat) -> (until : Fuel) -> String -> io (Either FileError (Bool, List String))
readFilePage offset fuel file
  = withFile file Read pure $
      readLinesOnto [] offset fuel

export
partial
readFile : HasIO io => String -> io (Either FileError String)
readFile = (map $ map (fastConcat . snd)) . readFilePage 0 forever

||| Write a string to a file
export
writeFile : HasIO io =>
            (filepath : String) -> (contents : String) ->
            io (Either FileError ())
writeFile file contents
  = withFile file WriteTruncate pure $
      (flip fPutStr contents)

namespace FileMode
  public export
  data FileMode = Read | Write | Execute

public export
record Permissions where
  constructor MkPermissions
  user   : List FileMode
  group  : List FileMode
  others : List FileMode

mkMode : Permissions -> Int
mkMode p
    = getMs (user p) * 64 + getMs (group p) * 8 + getMs (others p)
  where
    getM : FileMode -> Int
    getM Read = 4
    getM Write = 2
    getM Execute = 1

    getMs : List FileMode -> Int
    getMs = sum . map getM

export
chmodRaw : HasIO io => String -> Int -> io (Either FileError ())
chmodRaw fname p
    = do ok <- primIO $ prim__chmod fname p
         if ok == 0
            then pure (Right ())
            else returnError

export
chmod : HasIO io => String -> Permissions -> io (Either FileError ())
chmod fname p = chmodRaw fname (mkMode p)

%foreign "C:idris2_readBufferData, libidris2_support, idris_file.h"
         "RefC:readBufferData"
         "node:lambda:(f,b,l,m) => require('fs').readSync(f.fd,b,l,m)"
prim__readBufferData : FilePtr -> Buffer -> Int -> Int -> PrimIO Int

%foreign "C:idris2_writeBufferData, libidris2_support, idris_file.h"
         "RefC:writeBufferData"
         "node:lambda:(f,b,l,m) => require('fs').writeSync(f.fd,b,l,m)"
prim__writeBufferData : FilePtr -> Buffer -> Int -> Int -> PrimIO Int

export
readBufferData : HasIO io => File -> Buffer ->
                 (loc : Int) -> -- position in buffer to start adding
                 (maxbytes : Int) -> -- maximums size to read, which must not
                                     -- exceed buffer length
                 io (Either FileError ())
readBufferData (FHandle h) buf loc max
    = do read <- primIO (prim__readBufferData h buf loc max)
         if read >= 0
            then pure (Right ())
            else pure (Left FileReadError)

export
writeBufferData : HasIO io => File -> Buffer ->
                  (loc : Int) -> -- position in buffer to write from
                  (maxbytes : Int) -> -- maximums size to write, which must not
                                      -- exceed buffer length
                  io (Either FileError ())
writeBufferData (FHandle h) buf loc max
    = do written <- primIO (prim__writeBufferData h buf loc max)
         if written >= 0
            then pure (Right ())
            else pure (Left FileWriteError)

export
writeBufferToFile : HasIO io => String -> Buffer -> Int -> io (Either FileError ())
writeBufferToFile fn buf max
    = do Right f <- openFile fn WriteTruncate
             | Left err => pure (Left err)
         Right ok <- writeBufferData f buf 0 max
             | Left err => pure (Left err)
         closeFile f
         pure (Right ok)

export
createBufferFromFile : HasIO io => String -> io (Either FileError Buffer)
createBufferFromFile fn
    = do Right f <- openFile fn Read
             | Left err => pure (Left err)
         Right size <- fileSize f
             | Left err => pure (Left err)
         Just buf <- newBuffer size
             | Nothing => pure (Left FileReadError)
         Right ok <- readBufferData f buf 0 size
             | Left err => pure (Left err)
         closeFile f
         pure (Right buf)
