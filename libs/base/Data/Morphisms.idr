module Data.Morphisms

import Data.Contravariant

%default total

public export
record Morphism a b where
  constructor Mor
  applyMor : a -> b

infixr 1 ~>

public export
(~>) : Type -> Type -> Type
(~>) = Morphism

public export
record Endomorphism a where
  constructor Endo
  applyEndo : a -> a

public export
record Kleislimorphism (f : Type -> Type) a b where
  constructor Kleisli
  applyKleisli : a -> f b

public export
record Op b a where
  constructor MkOp
  applyOp : a -> b

export
Functor (Morphism r) where
  map f (Mor a) = Mor $ f . a

export
Applicative (Morphism r) where
  pure a = Mor $ const a
  (Mor f) <*> (Mor a) = Mor $ \r => f r $ a r

export
Monad (Morphism r) where
  (Mor h) >>= f = Mor $ \r => applyMor (f $ h r) r

export
Semigroup a => Semigroup (Morphism r a) where
  f <+> g = Mor $ \r => (applyMor f) r <+> (applyMor g) r

export
Monoid a => Monoid (Morphism r a) where
  neutral = Mor $ \_ => neutral

export
Semigroup (Endomorphism a) where
  (Endo f) <+> (Endo g) = Endo $ g . f

export
Monoid (Endomorphism a) where
  neutral = Endo id

export
Functor f => Functor (Kleislimorphism f a) where
  map f (Kleisli g) = Kleisli (map f . g)

export
Applicative f => Applicative (Kleislimorphism f a) where
  pure a = Kleisli $ const $ pure a
  (Kleisli f) <*> (Kleisli a) = Kleisli $ \r => f r <*> a r

export
Monad f => Monad (Kleislimorphism f a) where
  (Kleisli f) >>= g = Kleisli $ \r => do
    k1 <- f r
    applyKleisli (g k1) r

public export
Contravariant (Op b) where
  contramap f (MkOp g) = MkOp (g . f)
  v >$ (MkOp f) = MkOp $ \_ => f v

-- Applicative is a bit too strong, but there is no suitable superclass
export
(Semigroup a, Applicative f) => Semigroup (Kleislimorphism f r a) where
  f <+> g = Kleisli $ \r => (<+>) <$> (applyKleisli f) r <*> (applyKleisli g) r

export
(Monoid a, Applicative f) => Monoid (Kleislimorphism f r a) where
  neutral = Kleisli $ \_ => pure neutral

export
Cast (Endomorphism a) (Morphism a a) where
  cast (Endo f) = Mor f

export
Cast (Morphism a a) (Endomorphism a) where
  cast (Mor f) = Endo f

export
Cast (Morphism a (f b)) (Kleislimorphism f a b) where
  cast (Mor f) = Kleisli f

export
Cast (Kleislimorphism f a b) (Morphism a (f b)) where
  cast (Kleisli f) = Mor f

export
Cast (Endomorphism a) (Op a a) where
  cast (Endo f) = MkOp f

export
Cast (Op a a) (Endomorphism a) where
  cast (MkOp f) = Endo f

export
Cast (Op (f b) a) (Kleislimorphism f a b) where
  cast (MkOp f) = Kleisli f

export
Cast (Kleislimorphism f a b) (Op (f b) a) where
  cast (Kleisli f) = MkOp f

export
Cast (Morphism a b) (Op b a) where
  cast (Mor f) = MkOp f

export
Cast (Op b a) (Morphism a b) where
  cast (MkOp f) = Mor f
