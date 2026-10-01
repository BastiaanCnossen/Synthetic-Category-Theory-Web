# Identification animae with changing endpoints

When the source and target categories change by equivalences, a functor is compared by a square. The corresponding identification animae are compared using those equivalences and the two specified squares.

```agda
{-# OPTIONS --safe --without-K #-}
open import SCT.VolumeI.Chapter05.Section01.Prelude
import SCT.VolumeI.Chapter01.Section03.Whiskering as Whiskering

module SCT.VolumeI.Chapter05.Section01.Expressions.RebasedPaths {l : Level} (T : Theory l l l) where
open View T
open Whiskering vocabulary terminal products productLaws composition vertical whiskering
  using (leftMultiply; rightMultiply; leftMultiply-isEquiv; rightMultiply-isEquiv;
         postWhisker-isEquiv; preWhisker-isEquiv)

join : {A B C : CAT} → Equiv A B → Equiv B C → Equiv A C
join p q = record
  { functor = Equiv.functor q ∘ Equiv.functor p
  ; isEquiv = equiv-compose _ _ (Equiv.isEquiv p) (Equiv.isEquiv q) }

reverse : {A B : CAT} → Equiv A B → Equiv B A
reverse p = record
  { functor = IsEquiv.inverse (Equiv.isEquiv p)
  ; isEquiv = record
      { inverse = Equiv.functor p
      ; sectionIso = IsEquiv.retractionIso (Equiv.isEquiv p)
      ; retractionIso = IsEquiv.sectionIso (Equiv.isEquiv p) } }

-- A functor expression with varying source and target must be compared by
-- a square, not by an ill-typed equality of the two underlying functors.
record Square {C D C' D' : CAT} (c : Equiv C C') (d : Equiv D D')
  (f : MAP C D) (f' : MAP C' D') : Set l where
  field
    comparison : (Equiv.functor d ∘ f) =₁ (f' ∘ Equiv.functor c)

opaque
  -- Rebase the ENTIRE identification anima, not just its absolute points.
  paths : {C D C' D' : CAT} (c : Equiv C C') (d : Equiv D D')
    (f g : MAP C D) (f' g' : MAP C' D')
    → Square c d f f' → Square c d g g' → Equiv (f ＝ g) (f' ＝ g')
  paths {C} {D} {C'} {D'} c d f g f' g' sf sg =
    join (join (join postD rightF) leftG) (reverse preC)
    where
    cf : MAP C C'
    cf = Equiv.functor c
    df : MAP D D'
    df = Equiv.functor d
    p : (df ∘ f) =₁ (f' ∘ cf)
    p = Square.comparison sf
    q : (df ∘ g) =₁ (g' ∘ cf)
    q = Square.comparison sg
    postD : Equiv (f ＝ g) ((df ∘ f) ＝ (df ∘ g))
    postD = record { functor = postWhisker df ; isEquiv = postWhisker-isEquiv df (Equiv.isEquiv d) f g }
    rightF : Equiv ((df ∘ f) ＝ (df ∘ g)) ((f' ∘ cf) ＝ (df ∘ g))
    rightF = record { functor = rightMultiply (p ⁻¹) ; isEquiv = rightMultiply-isEquiv (p ⁻¹) }
    leftG : Equiv ((f' ∘ cf) ＝ (df ∘ g)) ((f' ∘ cf) ＝ (g' ∘ cf))
    leftG = record { functor = leftMultiply q ; isEquiv = leftMultiply-isEquiv q }
    preC : Equiv (f' ＝ g') ((f' ∘ cf) ＝ (g' ∘ cf))
    preC = record { functor = preWhisker cf ; isEquiv = preWhisker-isEquiv cf (Equiv.isEquiv c) f' g' }
```
