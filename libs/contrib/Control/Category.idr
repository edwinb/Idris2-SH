module Control.Category

import Data.Morphisms


public export
interface Semigroupoid (0 cat : obj -> obj -> Type) | cat where
  (.) : cat b c -> cat a b -> cat a c

public export
interface Semigroupoid cat => Category (0 cat : obj -> obj -> Type) where
  id  : cat a a

public export
Semigroupoid Morphism where
  -- disambiguation needed below, because unification can now get further
  -- here with Category.(.) and it's only interface resolution that fails!
  (Mor f) . (Mor g) = Mor $ Basics.(.) f g

public export
Category Morphism where
  id                = Mor id

public export
Bind m => Semigroupoid (Kleislimorphism m) where
  (Kleisli f) . (Kleisli g) = Kleisli $ \a => g a >>= f

public export
Monad m => Category (Kleislimorphism m) where
  id                        = Kleisli (pure . id)

infixr 1 >>>

public export
(>>>) : Semigroupoid cat => cat a b -> cat b c -> cat a c
f >>> g = g . f
