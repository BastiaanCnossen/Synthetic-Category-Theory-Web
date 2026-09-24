# Detecting equivalences by all base changes

A functor is an equivalence precisely when every base change is an
equivalence. For the converse, base change along the identity suffices.
This elementary pullback lemma supplies the universal-parameter version
of unique lifting in Chapter 5 without an objectwise detection axiom.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level; _⊔_)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.UniversalBaseChangeEquivalences
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯 public
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P
  using (pullback-equivalenceʳ; pullback-unitˡ)

AllBaseChangesEquivalences : {C D : CAT} → MAP C D → Set (c ⊔ m)
AllBaseChangesEquivalences {D = D} f =
  {Γ : CAT} (q : MAP Γ D) → IsEquiv (pullback₂ {f = f} {q})

equivalence-all-base-changes : {C D : CAT} {f : MAP C D} →
  IsEquiv f → AllBaseChangesEquivalences f
equivalence-all-base-changes {f = f} e q = pullback-equivalenceʳ f q e

all-base-changes-equivalence : {C D : CAT} {f : MAP C D} →
  AllBaseChangesEquivalences f → IsEquiv f
all-base-changes-equivalence {D = D} {f} e =
  equiv-cancel-right pullback₁ f (pullback-unitˡ f)
    (equiv-transport ((comp-unitˡ pullback₂ ∙ pullbackMatch) ⁻¹) (e (id D)))
```
