# Dependent products of terminal categories over the base

The identity of `T` is a dependent product of the identity of `S` along
any functor `S → T`. This is the terminal-object calculation used in
`cor:Dependent_Product_Preserves_Embeddings`.

More generally, a category equivalent to its base has this dependent
product. Every relevant relative mapping anima is contractible, so the
actual base-change-and-evaluation composite is an equivalence.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks

module SCT.VolumeI.Chapter03.Section05.TerminalDependentProducts
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section05.Initial 𝒯 M using (contractible-source; contractible-compare)
open import SCT.VolumeI.Chapter01.Section07.Contractible 𝒯 M ℱ
  using (maps-to-terminal-contractible; contractible-map)
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M ℱ using (funPost; funPost-isEquiv)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P using (pullbackCone-isPullback)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (coneSwap)
open import SCT.VolumeI.Chapter01.Section06.PullbackSymmetry 𝒯 P using (pullback-swap)
open import SCT.VolumeI.Chapter01.Section06.PullbackEquivalences 𝒯 P using (degenerate-pullback-converse)
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
open import SCT.VolumeI.Chapter01.Section06.Cones 𝒯 using (ConeIso)
open import SCT.VolumeI.Chapter03.Section05.DependentProducts 𝒯 M ℱ P

module EquivalenceTarget {C D S : CAT} (f : MAP C S) (g : MAP D S) (eg : IsEquiv g) where
  abstract
    projection-isEquiv : IsEquiv (pullback₂ {f = funPost g} {nameFun f})
    projection-isEquiv = degenerate-pullback-converse (funPost-isEquiv g eg)
      (coneSwap (pullbackCone (funPost g) (nameFun f)))
      (pullback-swap (pullbackCone (funPost g) (nameFun f))
        (pullbackCone-isPullback (funPost g) (nameFun f)))

    maps-contractible : IsContractible (MapOver f g)
    maps-contractible = contractible-source (mapPost {C = One} (pullback₂ {f = funPost g} {nameFun f}))
      (mapPost-isEquiv pullback₂ projection-isEquiv) (maps-to-terminal-contractible One)

module Along {S T C : CAT} (p : MAP S T) (f : MAP C S) (ef : IsEquiv f)
  (ε : FunctorOver (pullback₂ {f = id T} {p}) f) where

  abstract
    universal : IsDependentProduct p f (id T) ε
    universal = record { universal = λ t → contractible-map
      (EvaluationAlong.uncurrying p f (id T) ε t)
      (EquivalenceTarget.maps-contractible t (id T) (id-isEquiv T))
      (EquivalenceTarget.maps-contractible (pullback₂ {f = t} {p}) f ef) }

  product : DependentProduct p f
  product = record
    { category = T ; projection = id T ; evaluation = ε ; isDependentProduct = universal }

module Identity {S T : CAT} (p : MAP S T) where
  evaluation : FunctorOver (pullback₂ {f = id T} {p}) (id S)
  evaluation = record { lift = pullback₂ ; comparison = comp-unitˡ pullback₂ }

  dependent-product : DependentProduct p (id S)
  dependent-product = Along.product p (id S) (id-isEquiv S) evaluation

equivalence-dependent-product : {S T C : CAT} (p : MAP S T) (f : MAP C S) →
  IsEquiv f → DependentProduct p f
equivalence-dependent-product p f ef = Along.product p f ef (equiv-lift ef pullback₂)
```

The conclusion also holds for any other supplied dependent product of
the same terminal category over the base. Its relative mapping animae
are contractible by its universal property. A point over `id T` gives a
section, and contractibility over its own projection identifies the
other composite with the identity.

```agda
module AnyChoice {S T C : CAT} (p : MAP S T) (f : MAP C S) (ef : IsEquiv f)
  (Π : DependentProduct p f) where
  D = DependentProduct.category Π
  g = DependentProduct.projection Π

  abstract
    maps-contractible : {E : CAT} (t : MAP E T) → IsContractible (MapOver t g)
    maps-contractible t = contractible-source (RelativeCurrying.At.uncurry p f Π t)
      (RelativeCurrying.At.uncurry-isEquiv p f Π t)
      (EquivalenceTarget.maps-contractible (pullback₂ {f = t} {p}) f ef)

  section-point : Obj-abs (MapOver (id T) g)
  section-point = IsEquiv.inverse (maps-contractible (id T))

  section-over : FunctorOver (id T) g
  section-over = Over.decode-over (id T) g section-point

  section : MAP T D
  section = FunctorLift.lift section-over

  to-base : FunctorOver g (id T)
  to-base = record { lift = g ; comparison = comp-unitˡ g }

  abstract
    section-projection-point :
      Over.name-over g g (compose-over section-over to-base) =₁ Over.name-over g g (identity-over g)
    section-projection-point = contractible-compare (maps-contractible g) _ _

    projection-section-point :
      Over.name-over (id T) (id T) (compose-over to-base section-over) =₁
        Over.name-over (id T) (id T) (identity-over (id T))
    projection-section-point = contractible-compare
      (EquivalenceTarget.maps-contractible (id T) (id T) (id-isEquiv T)) _ _

    section-projection-cone :
      ConeIso (Over.Name.cone g g (compose-over section-over to-base))
        (Over.Name.cone g g (identity-over g))
    section-projection-cone = Over.identify-cones g g
      (compose-over section-over to-base) (identity-over g) section-projection-point

    projection-section-cone :
      ConeIso (Over.Name.cone (id T) (id T) (compose-over to-base section-over))
        (Over.Name.cone (id T) (id T) (identity-over (id T)))
    projection-section-cone = Over.identify-cones (id T) (id T)
      (compose-over to-base section-over) (identity-over (id T)) projection-section-point

    section-projection : (section ∘ g) =₁ id D
    section-projection = Over.identify-underlying g g (compose-over section-over to-base) (identity-over g)
      section-projection-point

    projection-isEquiv : IsEquiv g
    projection-isEquiv = record
      { inverse = section ; sectionIso = section-projection ⁻¹
      ; retractionIso = (FunctorLift.comparison section-over) ⁻¹ }
```

The two `-point` comparisons live in the relative mapping animae, and
the two `-cone` comparisons expose their triangle compatibility. The
exported `projection-isEquiv` is the ordinary equivalence of categories;
it does not package a separate category of equivalences over the base.
