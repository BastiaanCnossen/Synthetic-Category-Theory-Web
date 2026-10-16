# Recognizing animae

The groupoid recognition axiom identifies the primitive anima predicate with
the structural groupoid condition (`axiom:D_Groupoid_Core`). Its two directions
are the only assumptions introduced here. The groupoid condition uses the
chosen identity-arrow functor, through the equivalent characterization proved
in Section04.

Closure under equivalence and the fact that the initial category is an anima
are consequences. In particular, equivalence closure is not added to the
primitive anima interface of Chapter01.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section05.Recognition where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open import SCT.VolumeI.Chapter01.Section05.Initial using (Zero)
open import SCT.VolumeI.Chapter02.Section04.Groupoids
  using (IsGroupoid; empty-isGroupoid)
open import SCT.VolumeI.Chapter02.Section04.BasicClosure
  using (equivalence-preserves-groupoid; equivalence-reflects-groupoid)

module _ {Γ : Context} where
  postulate
    anima-isGroupoid : {C : CAT Γ} → isAn C → IsGroupoid C
    groupoid-isAn : {C : CAT Γ} → IsGroupoid C → isAn C

  equivalence-preserves-anima : {C D : CAT Γ} (f : MAP C D)
    → IsEquiv f → isAn C → isAn D
  equivalence-preserves-anima f e h =
    groupoid-isAn (equivalence-preserves-groupoid f e (anima-isGroupoid h))

  equivalence-reflects-anima : {C D : CAT Γ} (f : MAP C D)
    → IsEquiv f → isAn D → isAn C
  equivalence-reflects-anima f e h =
    groupoid-isAn (equivalence-reflects-groupoid f e (anima-isGroupoid h))

  zero-isAn : isAn (Zero {Γ = Γ})
  zero-isAn = groupoid-isAn empty-isGroupoid
```
