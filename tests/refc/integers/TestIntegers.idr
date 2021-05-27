module TestIntegers

import Data.Bits
import Data.List.Quantifiers

put : Show a => a -> IO ()
put = putStrLn . show

castAllTo : (to : Type)
         -> {0 types : List Type}
         -> All (flip Cast to) types => HList types -> List to
castAllTo to = forget . imapProperty (flip Cast to) (cast {to})

interface Num a => Bits a => SomeBits a where
    one : Index {a}

SomeBits Bits8 where
    one = fromNat 1

SomeBits Bits16 where
    one = fromNat 1

SomeBits Bits32 where
    one = fromNat 1

SomeBits Bits64 where
    one = fromNat 1

SomeBits Int where
    one = fromNat 1

SomeBits Integer where
    one = 1

main : IO ()
main = do
    let ints = the (HList _) [
        the Bits8 0, -- Bits8 min
        the Bits8 50,
        the Bits8 255, -- Bits8 max
        the Bits16 0, -- Bits16 min
        the Bits16 10000,
        the Bits16 65535, -- Bits16 max
        the Bits32 0, -- Bits32 min
        the Bits32 1000000000,
        the Bits32 4294967295, -- Bits32 max
        the Bits64 0, -- Bits64 min
        the Bits64 5000000000000000000,
        the Bits64 18446744073709551615, -- Bits64 max
        the Int $ -9223372036854775808, -- Int min
        the Int 1000000000000000000,
        the Int 9223372036854775807, -- Int max
        the Integer $ -9223372036854775809, -- Int min - 1
        the Integer 9223372036854775808 -- Int max + 1
    ]

    putStrLn "Cast to String:"
    put ints

    putStrLn "Cast to Bits8:"
    put $ castAllTo Bits8 ints

    putStrLn "Cast to Bits16:"
    put $ castAllTo Bits16 ints

    putStrLn "Cast to Bits32:"
    put $ castAllTo Bits32 ints

    putStrLn "Cast to Bits64:"
    put $ castAllTo Bits64 ints

    putStrLn "Cast to Int:"
    put $ castAllTo Int ints

    putStrLn "Cast to Integer:"
    put $ castAllTo Integer ints

    putStrLn "Add:"
    put $ imapProperty Num (+ 1) ints

    putStrLn "Subtract:"
    put $ imapProperty Neg (flip (-) 1) ints

    putStrLn "Negate:"
    put $ imapProperty Neg negate ints

    putStrLn "Multiply:"
    put $ imapProperty Num (* 2) ints

    putStrLn "Divide:"
    put $ imapProperty Integral (`div` 3) ints
    put $ imapProperty Integral (`div` -3) ints

    putStrLn "Mod:"
    put $ imapProperty Integral (`mod` 17) ints
    put $ imapProperty Integral (`mod` -17) ints

    putStrLn "Division Euclidean:"
    put $ imapProperty Integral (\x => (x `div` 19) * 19 + (x `mod` 19)) ints
    put $ imapProperty Integral (\x => (x `div` -19) * -19 + (x `mod` -19)) ints

    putStrLn "Shift:"
    put $ imapProperty SomeBits (`shiftL` one) ints
    put $ imapProperty SomeBits (`shiftR` one) ints

    putStrLn "Bit Ops:"
    put $ imapProperty SomeBits (.&. 0xAA) ints
    put $ imapProperty SomeBits (.|. 0xAA) ints
    put $ imapProperty SomeBits (`xor` 0xAA) ints
