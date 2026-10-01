# Elementary closure properties of groupoids

This proves `ex:Terminal_Category_Is_Groupoid`,
`ex:Products_Of_Groupoids_Is_Groupoid`,
`lem:Groupoids_Closed_Under_Equivalence`,
`lem:Groupoids_Closed_Under_Retracts`, and
`lem:Empty_Category_Is_Groupoid`.

For retracts we explicitly construct a section of the constant-arrow
functor. Its endpoint evaluation already gives the other inverse, so
no additional coherence of the chosen retract is required by the proof.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws
import SCT.VolumeI.Chapter02.Section01.WalkingMorphism as Walking
import SCT.VolumeI.Chapter02.Section01.IntervalEndpoints as Endpoints
import SCT.VolumeI.Chapter02.Section03.RezkAxiom as Rezk

module SCT.VolumeI.Chapter02.Section04.BasicClosure
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Laws.PullbackStructure 𝒯)
  (I : Walking.WalkingMorphism 𝒯) (E : Endpoints.IntervalEndpoints 𝒯 M ℱ P I)
  (R : Rezk.RezkAxiom 𝒯 M ℱ P I E) where

open import SCT.VolumeI.Chapter02.Section04.Groupoids 𝒯 M ℱ P I E R public
open import SCT.VolumeI.Chapter02.Section04.ConstantDiagrams.ConstantExponential 𝒯 M ℱ using (constant-natural)
open import SCT.VolumeI.Chapter01.Section07.Contractible 𝒯 M ℱ using (contractible-map; fun-terminal-contractible)
open import SCT.VolumeI.Chapter01.Section07.FunctorProducts 𝒯 M ℱ using (module ProductComparison)
open import SCT.VolumeI.Chapter01.Section05.RestrictionCalculus 𝒯 using (productMap-isEquiv)
open import SCT.VolumeI.Chapter01.Section05.Initial 𝒯 M using (InitialStructure; StrictInitial)

terminal-isGroupoid : IsGroupoid One
terminal-isGroupoid = contractible-map identityArrow
  (equiv-transport (terminal-iso _ _) (id-isEquiv One)) (fun-terminal-contractible [1])

product-isGroupoid : {C D : CAT} → IsGroupoid C → IsGroupoid D → IsGroupoid (C × D)
product-isGroupoid {C} {D} ec ed = equiv-cancel-left identityArrow A.forward A.forward-isEquiv
  (equiv-transport (comparison ⁻¹) (productMap-isEquiv identityArrow identityArrow ec ed))
  where
  module A = ProductComparison [1] C D
    using (forward; forward-isEquiv)
  comparison : (A.forward ∘ identityArrow) =₁ (productMap (identityArrow {C}) (identityArrow {D}))
  comparison = pair-cong (constant-natural [1] pr₁) (constant-natural [1] pr₂) ∙
    pair-pre (funPost pr₁) (funPost pr₂) identityArrow

equivalence-preserves-groupoid : {C D : CAT} (f : MAP C D) →
  IsEquiv f → IsGroupoid C → IsGroupoid D
equivalence-preserves-groupoid f ef ec = equiv-cancel-right f identityArrow ef
  (equiv-transport (constant-natural [1] f)
    (equiv-compose identityArrow (funPost f) ec (funPost-isEquiv f ef)))

equivalence-reflects-groupoid : {C D : CAT} (f : MAP C D) →
  IsEquiv f → IsGroupoid D → IsGroupoid C
equivalence-reflects-groupoid f ef = equivalence-preserves-groupoid
  (IsEquiv.inverse ef) (equiv-inverse ef)

retract-isGroupoid : {X Y : CAT} (s : MAP Y X) (r : MAP X Y) →
  (r ∘ s) =₁ (id Y) → IsGroupoid X → IsGroupoid Y
retract-isGroupoid {X} {Y} s r ε ex = identity-section-to-groupoid
  (record { section = r ∘ (j ∘ funPost s) ; comparison = counit })
  where
  j = IsEquiv.inverse ex
  counit : (identityArrow ∘ (r ∘ (j ∘ funPost s))) =₁ (id (Ar Y))
  counit = funPost-id [1] Y ∙ (funPost-cong ε ∙ (funPost-comp s r ∙
    ((funPost r ◁ (comp-unitˡ (funPost s) ∙
      (((IsEquiv.retractionIso ex) ⁻¹ ▷ funPost s) ∙
        (comp-assoc (funPost s) j identityArrow) ⁻¹))) ∙
    (comp-assoc (j ∘ funPost s) identityArrow (funPost r) ∙
      (((constant-natural [1] r) ⁻¹ ▷ (j ∘ funPost s)) ∙
        (comp-assoc (j ∘ funPost s) r identityArrow) ⁻¹)))))

empty-isGroupoid : (Z : InitialStructure) → StrictInitial Z → IsGroupoid (InitialStructure.Zero Z)
empty-isGroupoid Z strict = equiv-cancel-left identityArrow ev₀
  (StrictInitial.into-zero-isEquiv strict ev₀)
  (equiv-transport (identity-source ⁻¹) (id-isEquiv (InitialStructure.Zero Z)))
```
