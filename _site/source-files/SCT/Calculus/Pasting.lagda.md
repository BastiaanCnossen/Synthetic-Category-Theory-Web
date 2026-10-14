# Pasting projected triangles

The same calculation occurs when proving both unit laws for product functors.
A composite is first projected, its two factors are computed by their triangles,
and the middle coordinate comparison is replaced by its unit computation.
This proof is independent of products and of how any comparison was built.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.Calculus.Composition using (Composition; Laws)

module SCT.Calculus.Pasting {o h p : Level}
  (C : Composition o h p) (L : Laws C) where

open Composition C
open Laws L

abstract
  projected-triangles : {a b c c′ d y z : Obj}
    (frame : Hom c z) (out : Hom b c) (step : Hom a b)
    (unit : Hom y z) (middle : Hom b y)
    (coordinate : Hom d y) (transport : Hom a d)
    (result-frame : Hom c′ z) (result : Hom d c′)
    (projected : Hom a z)
    → projected ≈ ((frame ∘ out) ∘ step)
    → (frame ∘ out) ≈ (unit ∘ middle)
    → (middle ∘ step) ≈ (coordinate ∘ transport)
    → (unit ∘ coordinate) ≈ (result-frame ∘ result)
    → projected ≈ (result-frame ∘ (result ∘ transport))
  projected-triangles frame out step unit middle coordinate transport result-frame result
    projected project out-triangle step-triangle coordinate-unit =
    trans (assoc result-frame result transport)
      (trans (congr coordinate-unit (refl transport))
      (trans (sym (assoc unit coordinate transport))
      (trans (congr (refl unit) step-triangle)
      (trans (assoc unit middle step)
      (trans (congr out-triangle (refl step)) project)))))
```
