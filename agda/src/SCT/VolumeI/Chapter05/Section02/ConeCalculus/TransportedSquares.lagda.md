# Reflecting a transported comparison square

The reflection of a transported comparison square is a vertical
calculation in one theory. It is proved in
`Chapter01/Section04/Substitution/TransportedSquares`, beside the
endpoint calculus it uses. This module re-exports it for the Chapter 5
clients while they migrate to the Chapter 1 module.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)

module SCT.VolumeI.Chapter05.Section02.ConeCalculus.TransportedSquares
  {c m a : Level} (𝒯 : Theory c m a) where

open import SCT.VolumeI.Chapter01.Section04.Substitution.TransportedSquares 𝒯 public
  using (reflect-transported-square)
```
