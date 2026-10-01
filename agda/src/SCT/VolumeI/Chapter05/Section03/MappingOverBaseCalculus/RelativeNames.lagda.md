# Relative names in the mapping fiber

The mapping-fiber comparison sends a relative name to the transport of
its named cone. This comparison retains the entire matching, including
the two specified comparisons between the mapping cospans.

The resulting cone is kept in these transported coordinates. Identifying
its matching with the expression formed from `nameMapIso` requires the
computation of those cospan comparisons on names.

```agda
{-# OPTIONS --safe --without-K #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section04.MappingAnimae as Mapping
import SCT.VolumeI.Chapter01.Section07.FunctorCategories as Categories
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Pullbacks
import SCT.VolumeI.Chapter01.Section03.IdentificationCalculus.Structural as Structural
import SCT.VolumeI.Chapter01.Section02.Isomorphisms as Isomorphisms
import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.PointReductionCoherence as PointReduction

module SCT.VolumeI.Chapter05.Section03.MappingOverBaseCalculus.RelativeNames
  {c m a : Level} (𝒯 : Theory c m a) (M : Mapping.MappingAnimae 𝒯)
  (ℱ : Categories.FunctorCategories 𝒯 M) (P : Pullbacks.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section05.Setup 𝒯 M
open Pullbacks.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section07.AbsoluteObjects 𝒯 M ℱ using (nameFun)
open import SCT.VolumeI.Chapter01.Section07.Functoriality 𝒯 M ℱ using (funPost)
open import SCT.VolumeI.Chapter01.Section07.Currying 𝒯 M ℱ
  using (Fun; funUncurry; funUncurry-restrict; funUncurry-cong; funCurry-β)
open import SCT.VolumeI.Chapter01.Section07.CoreOfFun 𝒯 M ℱ using (module CoreOfFun)
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.UncurryingAction 𝒯 M ℱ
  using (funUncurryIso; uncurry-restrict-substitution; uncurryFamily-absolute)
open import SCT.VolumeI.Chapter01.Section04.Substitution.Compatibility 𝒯 M
  using (mapUncurry-restrict-substitution; productFamily-single-absolute; slice-comparison)
open import SCT.VolumeI.Chapter01.Section04.Substitution.SubstitutionCoherence 𝒯 M
  using (mapUncurry-restrict-iterated)
open import SCT.VolumeI.Chapter01.Section07.EvaluationCalculus.SubstitutionCoherence 𝒯 M ℱ
  using (funUncurry-restrict-iterated)
open import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.CoreInclusions 𝒯 M
  using (coreInclusion; coreInclusion-name)
open import SCT.VolumeI.Chapter01.Section06.PullbackSquares 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeSymmetry 𝒯 using (cone-match-change)
open import SCT.VolumeI.Chapter01.Section04.Substitution.CoherenceTransport 𝒯
  using (changeEndpoints-reflect)
open import SCT.VolumeI.Chapter05.Section02.ConeCalculus.TransportedSquares 𝒯
  using (reflect-transported-square)
open import SCT.VolumeI.Chapter01.Section06.MappingCalculus.MappingCompatibility 𝒯 M
  using (mapPost-uncurry-natural)
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P using (CospanMap)
open import SCT.VolumeI.Chapter01.Section06.MappingPullbacks 𝒯 M P
  using (mappedCone; mappedCone-iso; mappedCone-pre; module MappingPullback)
import SCT.VolumeI.Chapter01.Section06.Cospans.ConeAction as Cospans
open import SCT.VolumeI.Chapter03.RelativeCategories.Functors 𝒯 M ℱ P
import SCT.VolumeI.Chapter03.RelativeCategories.Evaluation.MappingFibers as Fibers
import SCT.VolumeI.Chapter03.RelativeCategories.IdentificationCalculus.CoreNamingNaturality as CoreNaming
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as Pairing
open Pairing vocabulary terminal products productLaws composition vertical whiskering
  using (cancel-right; move-square; cancel-left-reflect)
open import SCT.VolumeI.Chapter01.Section06.MappingCalculus.ConeUncurrying 𝒯 M
  using (paste-iso-squares)
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
open Structural vocabulary terminal products productLaws composition whiskering
  using (whisker-mixed-at; preWhisker-comp-at)
open Isomorphisms vocabulary terminal products productLaws composition vertical whiskering
  using (reassociateFour; cancel-inverse)

decodeMap-post : {B C D : CAT} (g : MAP C D) (x : MAP One (Map B C)) →
  decodeMap (mapPost g ∘ x) =₁ (g ∘ decodeMap x)
decodeMap-post {B} g x = comp-assoc (oneProduct-in B) (mapUncurry x) g ∙
  (mapPost-uncurry g x ▷ oneProduct-in B)

post-nameMap-uncurried : {B C D : CAT} (g : MAP C D) (h : MAP B C) →
  mapUncurry (mapPost g ∘ nameMap h) =₁ mapUncurry (nameMap (g ∘ h))
post-nameMap-uncurried g h = (mapCurry-β one-isAn ((g ∘ h) ∘ pr₂)) ⁻¹ ∙
  ((comp-assoc pr₂ h g) ⁻¹ ∙
    ((g ◁ mapCurry-β one-isAn (h ∘ pr₂)) ∙ mapPost-uncurry g (nameMap h)))

post-nameMap-decode-image : {B C D : CAT} (g : MAP C D) (h : MAP B C) →
  decodeMapIso (mapPost-name g h) =₂ (post-nameMap-uncurried g h ▷ oneProduct-in B)
post-nameMap-decode-image {B} g h =
  (preWhisker (oneProduct-in B) ◁ mapReflect-β one-isAn _ _ (post-nameMap-uncurried g h)) ∙
    decodeMapIso-at (mapPost-name g h)

decodeMapIso-comp : {C D : CAT} {x y z : Obj-abs (Map C D)}
  (β : y =₁ z) (α : x =₁ y) → decodeMapIso (β ∙ α) =₂ (decodeMapIso β ∙ decodeMapIso α)
decodeMapIso-comp {C} β α = isoComp-cong ((decodeMapIso-at β) ⁻¹) ((decodeMapIso-at α) ⁻¹) ∙
  (preWhisker-isoComp-at (mapUncurryIso β) (mapUncurryIso α) (oneProduct-in C) ∙
    ((preWhisker (oneProduct-in C) ◁ mapUncurryIso-comp β α) ∙ decodeMapIso-at (β ∙ α)))

fun-restrict-substitution : {X Y C D : CAT} (p : MAP X (Fun C D))
  {x y : MAP Y X} (α : x =₁ y) →
  (funUncurry-restrict p y ∙ funUncurryIso (p ◁ α)) =₂
    ((funUncurry p ◁ productMap-cong α (idIso (id C))) ∙ funUncurry-restrict p x)
fun-restrict-substitution p {x} {y} α =
  isoComp-cong (postWhisker (funUncurry p) ◁ productFamily-single-absolute α)
    (const-One (funUncurry-restrict p x)) ∙
  (uncurry-restrict-substitution p α ∙
    (isoComp-cong (const-One (funUncurry-restrict p y))
      (uncurryFamily-absolute (p ◁ α))) ⁻¹)

module EvaluationComparison {X C D : CAT}
  (p : MAP X (Map C D)) (q : MAP X (Fun C D))
  (ε : mapUncurry p =₁ funUncurry q) where

  comparison : {Y : CAT} (x : MAP Y X) →
    mapUncurry (p ∘ x) =₁ funUncurry (q ∘ x)
  comparison x = (funUncurry-restrict q x) ⁻¹ ∙
    ((ε ▷ productMap x (id C)) ∙ mapUncurry-restrict p x)

  opaque
    naturality : {Y : CAT} {x y : MAP Y X} (α : x =₁ y) →
      (comparison y ∙ mapUncurryIso (p ◁ α)) =₂
        (funUncurryIso (q ◁ α) ∙ comparison x)
    naturality {x = x} {y} α = paste-iso-squares
      ((ε ▷ productMap x (id C)) ∙ mapUncurry-restrict p x)
      ((ε ▷ productMap y (id C)) ∙ mapUncurry-restrict p y)
      ((funUncurry-restrict q x) ⁻¹) ((funUncurry-restrict q y) ⁻¹)
      (mapUncurryIso (p ◁ α))
      (funUncurry q ◁ productMap-cong α (idIso (id C)))
      (funUncurryIso (q ◁ α))
      (paste-iso-squares (mapUncurry-restrict p x) (mapUncurry-restrict p y)
        (ε ▷ productMap x (id C)) (ε ▷ productMap y (id C))
        (mapUncurryIso (p ◁ α))
        (mapUncurry p ◁ productMap-cong α (idIso (id C)))
        (funUncurry q ◁ productMap-cong α (idIso (id C)))
        (mapUncurry-restrict-substitution p α)
        (interchange-at ε (productMap-cong α (idIso (id C)))))
      (move-square (funUncurry-restrict q y)
        (funUncurryIso (q ◁ α))
        (funUncurry q ◁ productMap-cong α (idIso (id C))) (funUncurry-restrict q x)
        (fun-restrict-substitution q α))

  module Iterated {Y Z : CAT} (σ : MAP Y X) (r : MAP Z Y) where
    R = productMap r (id C)
    S = productMap σ (id C)
    κ = slice-comparison {C = C} σ r
    LM = mapUncurry-restrict p σ ▷ R
    LF = funUncurry-restrict q σ ▷ R
    RM = mapUncurry-restrict (p ∘ σ) r
    RF = funUncurry-restrict (q ∘ σ) r
    AM = mapUncurry-restrict p (σ ∘ r)
    AF = funUncurry-restrict q (σ ∘ r)
    aM = mapUncurryIso (comp-assoc r σ p)
    aF = funUncurryIso (comp-assoc r σ q)
    HM = (mapUncurry p ◁ κ) ∙ comp-assoc R S (mapUncurry p)
    HF = (funUncurry q ◁ κ) ∙ comp-assoc R S (funUncurry q)
    J = (ε ▷ S) ▷ R
    ell = comparison σ ▷ R
    total = ε ▷ productMap (σ ∘ r) (id C)
    successive = RF ⁻¹ ∙ (ell ∙ RM)
    whole = comparison (σ ∘ r)

    opaque
      first-square : (LF ∙ ell) =₂ (J ∙ LM)
      first-square = preWhisker-isoComp-at (ε ▷ S) (mapUncurry-restrict p σ) R ∙
        ((preWhisker R ◁ cancel-inverse (funUncurry-restrict q σ)
          ((ε ▷ S) ∙ mapUncurry-restrict p σ)) ∙
          (preWhisker-isoComp-at (funUncurry-restrict q σ) (comparison σ) R) ⁻¹)

      outer-square : (HF ∙ J) =₂ (total ∙ HM)
      outer-square = isoComp-assoc-at total (mapUncurry p ◁ κ)
          (comp-assoc R S (mapUncurry p)) ∙
        (isoComp-cong ((interchange-at ε κ) ⁻¹) (idIso (comp-assoc R S (mapUncurry p))) ∙
          ((isoComp-assoc-at (funUncurry q ◁ κ) (ε ▷ (S ∘ R))
            (comp-assoc R S (mapUncurry p))) ⁻¹ ∙
            (isoComp-cong (idIso (funUncurry q ◁ κ)) (preWhisker-comp-at ε S R) ∙
              isoComp-assoc-at (funUncurry q ◁ κ) (comp-assoc R S (funUncurry q)) J)))

      combined-square : (((HF ∙ LF) ∙ RF) ∙ successive) =₂
        (total ∙ ((HM ∙ LM) ∙ RM))
      combined-square = paste-iso-squares RM RF (HM ∙ LM) (HF ∙ LF)
        successive ell total (cancel-inverse RF (ell ∙ RM))
        (paste-iso-squares LM LF HM HF ell J total first-square outer-square)

      source-normal : (AM ∙ aM) =₂ ((HM ∙ LM) ∙ RM)
      source-normal = (isoComp-assoc-at HM LM RM) ⁻¹ ∙
        ((isoComp-assoc-at (mapUncurry p ◁ κ) (comp-assoc R S (mapUncurry p)) (LM ∙ RM)) ⁻¹ ∙
          mapUncurry-restrict-iterated p σ r)

      target-normal : (AF ∙ aF) =₂ ((HF ∙ LF) ∙ RF)
      target-normal = (isoComp-assoc-at HF LF RF) ⁻¹ ∙
        ((isoComp-assoc-at (funUncurry q ◁ κ) (comp-assoc R S (funUncurry q)) (LF ∙ RF)) ⁻¹ ∙
          funUncurry-restrict-iterated q σ r)

      coherence : (whole ∙ aM) =₂
        (aF ∙ successive)
      coherence = cancel-left-reflect AF
        (isoComp-assoc-at AF aF successive ∙
          (isoComp-cong (target-normal ⁻¹) (idIso successive) ∙
            (combined-square ⁻¹ ∙
              (isoComp-cong (idIso total) source-normal ∙
                (isoComp-assoc-at total AM aM ∙
                  (isoComp-cong (cancel-inverse AF (total ∙ AM)) (idIso aM) ∙
                    (isoComp-assoc-at AF
                      (whole) aM) ⁻¹))))))

module CoreName {C D : CAT} (h : MAP C D) where
  module U = CoreOfFun C D using (uncurrying; uncurrying-evaluation)

  image : mapUncurry (U.uncurrying ∘ nameMap (nameFun h)) =₁
    mapUncurry (nameMap h)
  image = (mapCurry-β one-isAn (h ∘ pr₂)) ⁻¹ ∙
    (funCurry-β (h ∘ pr₂) ∙
      (funUncurry-cong (coreInclusion-name (nameFun h)) ∙
        ((funUncurry-restrict (coreInclusion (Fun C D)) (nameMap (nameFun h))) ⁻¹ ∙
          ((U.uncurrying-evaluation ▷ productMap (nameMap (nameFun h)) (id C)) ∙
            mapUncurry-restrict U.uncurrying (nameMap (nameFun h))))))

  opaque
    comparison : (U.uncurrying ∘ nameMap (nameFun h)) =₁ nameMap h
    comparison = mapReflect one-isAn _ _ image

    comparison-β : mapUncurryIso comparison =₂ image
    comparison-β = mapReflect-β one-isAn _ _ image

module Named {C D S : CAT} (f : MAP C S) (g : MAP D S)
  (u : FunctorOver f g) where

  module O = Over f g using (name-over; module Name)
  module N = O.Name u using (object; cone; comparison)
  module RM = Fibers.MappingFiber 𝒯 M ℱ P f g using (comparison; cospan)
  module Source = MappingPullback One (funPost g) (nameFun f)
    using (comparison; square)
  module Change = CospanMap RM.cospan using (mapCone; pullbackMap; pullbackMap-β)
  module ChangeCones = Cospans.Action 𝒯 P RM.cospan using (map-iso; map-pre)
  module U = CoreOfFun C D using (uncurrying)
  h = FunctorLift.lift u

  identity-name : MAP One (Map One One)
  identity-name = nameMap (id One)

  named-source : Cone (mapPost {C = One} (funPost {C = C} g))
    (mapPost {C = One} (nameFun f)) One
  named-source = conePre identity-name (mappedCone One N.cone)

  transported : Cone (mapPost {C = C} g) (nameMap f) One
  transported = Change.mapCone named-source

  opaque
    unfolding O.name-over
    source-name : (mapPost N.object ∘ identity-name) =₁ O.name-over u
    source-name = nameMapIso (comp-unitʳ N.object) ∙ mapPost-name N.object (id One)

  opaque
    source-comparison : ConeIso (conePre (O.name-over u) Source.square) named-source
    source-comparison = coneIso-compose
      (coneIso-pre identity-name (mappedCone-iso One N.comparison))
      (coneIso-compose
        (coneIso-pre identity-name (mappedCone-pre One N.object
          (pullbackCone (funPost g) (nameFun f))))
        (coneIso-compose
          (coneIso-inverse (conePre-assoc identity-name (mapPost N.object) Source.square))
          (cone-action Source.square (source-name ⁻¹))))

    factor-comparison : ConeIso
      (conePre RM.comparison (pullbackCone (mapPost {C = C} g) (nameMap f)))
      (Change.mapCone Source.square)
    factor-comparison = coneIso-compose
      (ChangeCones.map-iso (pullbackLift-β Source.square))
      (coneIso-compose
        (coneIso-inverse (ChangeCones.map-pre Source.comparison
          (pullbackCone (mapPost {C = One} (funPost {C = C} g))
            (mapPost {C = One} (nameFun f)))))
        (coneIso-compose
          (coneIso-pre Source.comparison Change.pullbackMap-β)
          (coneIso-inverse (conePre-assoc Source.comparison Change.pullbackMap
            (pullbackCone (mapPost {C = C} g) (nameMap f))))))

    comparison : ConeIso
      (conePre (RM.comparison ∘ O.name-over u)
        (pullbackCone (mapPost {C = C} g) (nameMap f))) transported
    comparison = coneIso-compose (ChangeCones.map-iso source-comparison)
      (coneIso-compose
        (coneIso-inverse (ChangeCones.map-pre (O.name-over u) Source.square))
        (coneIso-compose
          (coneIso-pre (O.name-over u) factor-comparison)
          (coneIso-inverse (conePre-assoc (O.name-over u) RM.comparison
            (pullbackCone (mapPost {C = C} g) (nameMap f))))))

    left-comparison : Cone.left transported =₁ nameMap h
    left-comparison = CoreName.comparison h ∙
      (U.uncurrying ◁ (nameMapIso (comp-unitʳ (nameFun h)) ∙
        mapPost-name (nameFun h) (id One)))

  normalized : Cone (mapPost {C = C} g) (nameMap f) One
  normalized = coneRetarget transported (nameMap h) (id One)
    left-comparison (terminal-iso _ _)

  opaque
    normalized-comparison : ConeIso
      (conePre (RM.comparison ∘ O.name-over u)
        (pullbackCone (mapPost {C = C} g) (nameMap f))) normalized
    normalized-comparison = coneIso-compose
      (coneRetarget-β transported (nameMap h) (id One)
        left-comparison (terminal-iso _ _)) comparison
module PostNaming {B C D : CAT} (g : MAP C D) (h : MAP B C) where
  i : MAP B (One × B)
  i = oneProduct-in B
  module Reduce = PointReduction.Reduction 𝒯 i (pr₂ {C = One}) (oneProduct-retraction B)
  module ReducePost = Reduce.Post h g
  β : mapUncurry (nameMap h) =₁ (h ∘ (pr₂ {C = One}))
  β = mapCurry-β one-isAn (h ∘ (pr₂ {C = One}))
  γ : mapUncurry (nameMap (g ∘ h)) =₁ ((g ∘ h) ∘ (pr₂ {C = One}))
  γ = mapCurry-β one-isAn ((g ∘ h) ∘ (pr₂ {C = One}))
  η : mapUncurry (mapPost g ∘ nameMap h) =₁ (g ∘ mapUncurry (nameMap h))
  η = mapPost-uncurry g (nameMap h)
  assoc : ((g ∘ h) ∘ (pr₂ {C = One})) =₁ (g ∘ (h ∘ (pr₂ {C = One})))
  assoc = comp-assoc (pr₂ {C = One}) h g

  abstract
    name-normal : {E : CAT} (f : MAP B E) →
      (Reduce.reduce f ∙ (mapCurry-β one-isAn (f ∘ (pr₂ {C = One})) ▷ i)) =₂ decode-name f
    name-normal f = isoComp-cong (idIso (comp-unitʳ f))
        (isoComp-assoc-at (f ◁ oneProduct-retraction B) (comp-assoc i (pr₂ {C = One}) f) (mapCurry-β one-isAn (f ∘ (pr₂ {C = One})) ▷ i)) ∙
      isoComp-assoc-at (comp-unitʳ f) ((f ◁ oneProduct-retraction B) ∙ comp-assoc i (pr₂ {C = One}) f)
        (mapCurry-β one-isAn (f ∘ (pr₂ {C = One})) ▷ i)

    raw-at : (post-nameMap-uncurried g h ▷ i) =₂
      ((γ ▷ i) ⁻¹ ∙ ((assoc ▷ i) ⁻¹ ∙ (((g ◁ β) ▷ i) ∙ (η ▷ i))))
    raw-at = isoComp-cong (pre-inverse γ i)
      (isoComp-cong (pre-inverse assoc i) (preWhisker-isoComp-at (g ◁ β) η i) ∙
        preWhisker-isoComp-at (assoc ⁻¹) ((g ◁ β) ∙ η) i) ∙
      preWhisker-isoComp-at (γ ⁻¹) (assoc ⁻¹ ∙ ((g ◁ β) ∙ η)) i

    first : (decode-name (g ∘ h) ∙ decodeMapIso (mapPost-name g h)) =₂
      ((Reduce.reduce (g ∘ h) ∙ (γ ▷ i)) ∙
        ((γ ▷ i) ⁻¹ ∙ ((assoc ▷ i) ⁻¹ ∙ (((g ◁ β) ▷ i) ∙ (η ▷ i)))))
    first = isoComp-cong ((name-normal (g ∘ h)) ⁻¹) (raw-at ∙ post-nameMap-decode-image g h)

    cancelled :
      ((Reduce.reduce (g ∘ h) ∙ (γ ▷ i)) ∙
        ((γ ▷ i) ⁻¹ ∙ ((assoc ▷ i) ⁻¹ ∙ (((g ◁ β) ▷ i) ∙ (η ▷ i))))) =₂
      ((Reduce.reduce (g ∘ h) ∙ (assoc ▷ i) ⁻¹) ∙ (((g ◁ β) ▷ i) ∙ (η ▷ i)))
    cancelled = (isoComp-assoc-at (Reduce.reduce (g ∘ h)) ((assoc ▷ i) ⁻¹) (((g ◁ β) ▷ i) ∙ (η ▷ i))) ⁻¹ ∙
      (isoComp-cong (idIso (Reduce.reduce (g ∘ h)))
        (cancel-inverse (γ ▷ i) ((assoc ▷ i) ⁻¹ ∙ (((g ◁ β) ▷ i) ∙ (η ▷ i)))) ∙
        isoComp-assoc-at (Reduce.reduce (g ∘ h)) (γ ▷ i)
          ((γ ▷ i) ⁻¹ ∙ ((assoc ▷ i) ⁻¹ ∙ (((g ◁ β) ▷ i) ∙ (η ▷ i)))))

    prefix : (Reduce.reduce (g ∘ h) ∙ (assoc ▷ i) ⁻¹) =₂
      ((g ◁ Reduce.reduce h) ∙ comp-assoc i (h ∘ (pr₂ {C = One})) g)
    prefix = ReducePost.cancel-associator ∙
      isoComp-cong (idIso (Reduce.reduce (g ∘ h))) ((pre-inverse assoc i) ⁻¹)

    middle : ((Reduce.reduce (g ∘ h) ∙ (assoc ▷ i) ⁻¹) ∙ (((g ◁ β) ▷ i) ∙ (η ▷ i))) =₂
      ((g ◁ Reduce.reduce h) ∙ ((g ◁ (β ▷ i)) ∙ decodeMap-post g (nameMap h)))
    middle = isoComp-cong (idIso (g ◁ Reduce.reduce h))
        (isoComp-assoc-at (g ◁ (β ▷ i)) (comp-assoc i (mapUncurry (nameMap h)) g) (η ▷ i)) ∙
      (isoComp-cong (idIso (g ◁ Reduce.reduce h))
        (isoComp-cong (whisker-mixed-at β i g) (idIso (η ▷ i))) ∙
        (reassociateFour (g ◁ Reduce.reduce h) (comp-assoc i (h ∘ (pr₂ {C = One})) g) ((g ◁ β) ▷ i) (η ▷ i) ∙
          isoComp-cong prefix (idIso (((g ◁ β) ▷ i) ∙ (η ▷ i)))))

    last : ((g ◁ Reduce.reduce h) ∙ ((g ◁ (β ▷ i)) ∙ decodeMap-post g (nameMap h))) =₂
      ((g ◁ decode-name h) ∙ decodeMap-post g (nameMap h))
    last = isoComp-cong (postWhisker g ◁ name-normal h) (idIso (decodeMap-post g (nameMap h))) ∙
      (isoComp-cong ((postWhisker-isoComp-at g (Reduce.reduce h) (β ▷ i)) ⁻¹)
        (idIso (decodeMap-post g (nameMap h))) ∙
        (isoComp-assoc-at (g ◁ Reduce.reduce h) (g ◁ (β ▷ i)) (decodeMap-post g (nameMap h))) ⁻¹)

    comparison : (decode-name (g ∘ h) ∙ decodeMapIso (mapPost-name g h)) =₂
      ((g ◁ decode-name h) ∙ decodeMap-post g (nameMap h))
    comparison = last ∙ (middle ∙ (cancelled ∙ first))

module Direct {C D S : CAT} (f : MAP C S) (g : MAP D S) (u : FunctorOver f g) where
  h = FunctorLift.lift u
  θ = FunctorLift.comparison u
  ρ = comp-unitʳ (nameMap f)
  π = mapPost-name g h
  κ = decodeMap-post g (nameMap h)

  cone : Cone (mapPost {C = C} g) (nameMap f) One
  cone = record
    { left = nameMap h ; right = id One
    ; match = ρ ⁻¹ ∙ (nameMapIso θ ∙ π) }
  τ = Cone.match cone

  decoded : (g ∘ decodeMap (nameMap h)) =₁ f
  decoded = (decode-name f ∙ decodeMapIso ρ) ∙ (decodeMapIso τ ∙ κ ⁻¹)

  opaque
    named-matching : (ρ ∙ τ) =₂ (nameMapIso θ ∙ π)
    named-matching = cancel-inverse ρ (nameMapIso θ ∙ π)

    decoded-name-composition : (decodeMapIso ρ ∙ decodeMapIso τ) =₂
      (decodeMapIso (nameMapIso θ) ∙ decodeMapIso π)
    decoded-name-composition = decodeMapIso-comp (nameMapIso θ) π ∙
      (decodeMap-Iso₂ named-matching ∙ (decodeMapIso-comp ρ τ) ⁻¹)

    prefix : ((decode-name f ∙ decodeMapIso ρ) ∙ decodeMapIso τ) =₂
      (θ ∙ ((g ◁ decode-name h) ∙ κ))
    prefix = isoComp-cong (idIso θ) (PostNaming.comparison g h) ∙
      (isoComp-assoc-at θ (decode-name (g ∘ h)) (decodeMapIso π) ∙
        (isoComp-cong (CoreNaming.Named.square 𝒯 M (g ∘ h) f θ) (idIso (decodeMapIso π)) ∙
          ((isoComp-assoc-at (decode-name f) (decodeMapIso (nameMapIso θ)) (decodeMapIso π)) ⁻¹ ∙
            (isoComp-cong (idIso (decode-name f)) decoded-name-composition ∙
              isoComp-assoc-at (decode-name f) (decodeMapIso ρ) (decodeMapIso τ)))))

    triangle : decoded =₂ (θ ∙ (g ◁ decode-name h))
    triangle = cancel-right κ (θ ∙ (g ◁ decode-name h)) ∙
      (isoComp-cong
        ((isoComp-assoc-at θ (g ◁ decode-name h) κ) ⁻¹ ∙ prefix) (idIso (κ ⁻¹)) ∙
        (isoComp-assoc-at (decode-name f ∙ decodeMapIso ρ) (decodeMapIso τ) (κ ⁻¹)) ⁻¹)

module NormalizationCriterion {C D S : CAT} (f : MAP C S) (g : MAP D S)
  (u : FunctorOver f g) where
  module Source = Named f g u using (normalized; normalized-comparison)
  module Target = Direct f g u using (h; θ; ρ; κ; cone; triangle)
  module RM = Fibers.MappingFiber 𝒯 M ℱ P f g using (comparison)

  decoded : (g ∘ decodeMap (nameMap Target.h)) =₁ f
  decoded = (decode-name f ∙ decodeMapIso Target.ρ) ∙
    (decodeMapIso (Cone.match Source.normalized) ∙ Target.κ ⁻¹)

  opaque
    reflect : decoded =₂ (Target.θ ∙ (g ◁ decode-name Target.h)) →
      ConeIso
        (conePre (RM.comparison ∘ Over.name-over f g u)
          (pullbackCone (mapPost {C = C} g) (nameMap f))) Target.cone
    reflect calculation = coneIso-compose
      (cone-match-change _ _ _ _
        (decodeMap-reflect-Iso₂ _ _
          (changeEndpoints-reflect Target.κ (decode-name f ∙ decodeMapIso Target.ρ) _ _
            (Target.triangle ⁻¹ ∙ calculation))))
      Source.normalized-comparison
module DecodePost {B C D : CAT} (g : MAP C D) {u v : Obj-abs (Map B C)} (α : u =₁ v) where
  i : MAP B (One × B)
  i = oneProduct-in B
  ηu : mapUncurry (mapPost g ∘ u) =₁ (g ∘ mapUncurry u)
  ηu = mapPost-uncurry g u
  ηv : mapUncurry (mapPost g ∘ v) =₁ (g ∘ mapUncurry v)
  ηv = mapPost-uncurry g v
  Au : ((g ∘ mapUncurry u) ∘ i) =₁ (g ∘ decodeMap u)
  Au = comp-assoc i (mapUncurry u) g
  Av : ((g ∘ mapUncurry v) ∘ i) =₁ (g ∘ decodeMap v)
  Av = comp-assoc i (mapUncurry v) g
  raw : mapUncurry (mapPost g ∘ u) =₁ mapUncurry (mapPost g ∘ v)
  raw = mapUncurryIso (mapPost g ◁ α)
  decoded : mapUncurry u =₁ mapUncurry v
  decoded = mapUncurryIso α

  abstract
    natural : (decodeMap-post g v ∙ decodeMapIso (mapPost g ◁ α)) =₂
      ((g ◁ decodeMapIso α) ∙ decodeMap-post g u)
    natural = isoComp-cong (postWhisker g ◁ (decodeMapIso-at α) ⁻¹) (idIso (decodeMap-post g u)) ∙
      (isoComp-assoc-at (g ◁ (decoded ▷ i)) Au (ηu ▷ i) ∙
        (isoComp-cong (whisker-mixed-at decoded i g) (idIso (ηu ▷ i)) ∙
          ((isoComp-assoc-at Av ((g ◁ decoded) ▷ i) (ηu ▷ i)) ⁻¹ ∙
            (isoComp-cong (idIso Av) (preWhisker-isoComp-at (g ◁ decoded) ηu i) ∙
              (isoComp-cong (idIso Av) (preWhisker i ◁ mapPost-uncurry-natural g α) ∙
                (isoComp-cong (idIso Av) ((preWhisker-isoComp-at ηv raw i) ⁻¹) ∙
                  (isoComp-assoc-at Av (ηv ▷ i) (raw ▷ i) ∙
                    isoComp-cong (idIso (decodeMap-post g v)) (decodeMapIso-at (mapPost g ◁ α)))))))))

module FiberDecoding {C D S : CAT} (f : MAP C S) (g : MAP D S) where
  right-adjust : (r : MAP One One) → (nameMap f ∘ r) =₁ nameMap f
  right-adjust r = comp-unitʳ (nameMap f) ∙ (nameMap f ◁ terminal-iso r (id One))

  right-change : (r : MAP One One) → decodeMap (nameMap f ∘ r) =₁ f
  right-change r = decode-name f ∙ decodeMapIso (right-adjust r)

  opaque
    terminal-composite : {r s : MAP One One} (β : r =₁ s) →
      (terminal-iso s (id One) ∙ β) =₂ terminal-iso r (id One)
    terminal-composite {r} β = equiv-reflect (terminalIso-isEquiv r (id One)) _ _
      (terminal-iso _ _)

    right-adjust-natural : {r s : MAP One One} (β : r =₁ s) →
      (right-adjust s ∙ (nameMap f ◁ β)) =₂ right-adjust r
    right-adjust-natural {r} {s} β =
      isoComp-cong (idIso (comp-unitʳ (nameMap f)))
        ((postWhisker (nameMap f) ◁ terminal-composite β) ∙
          (postWhisker-isoComp-at (nameMap f) (terminal-iso s (id One)) β) ⁻¹) ∙
        isoComp-assoc-at (comp-unitʳ (nameMap f))
          (nameMap f ◁ terminal-iso s (id One)) (nameMap f ◁ β)

    right-natural : {r s : MAP One One} (β : r =₁ s) →
      (right-change s ∙ decodeMapIso (nameMap f ◁ β)) =₂ right-change r
    right-natural {r} {s} β =
      isoComp-cong (idIso (decode-name f))
        (decodeMap-Iso₂ (right-adjust-natural β) ∙
          (decodeMapIso-comp (right-adjust s) (nameMap f ◁ β)) ⁻¹) ∙
      isoComp-assoc-at (decode-name f) (decodeMapIso (right-adjust s))
        (decodeMapIso (nameMap f ◁ β))

  triangle : (s : Cone (mapPost {C = C} g) (nameMap f) One) →
    (g ∘ decodeMap (Cone.left s)) =₁ f
  triangle s = right-change (Cone.right s) ∙
    (decodeMapIso (Cone.match s) ∙ (decodeMap-post g (Cone.left s)) ⁻¹)

  module Reflection (s t : Cone (mapPost {C = C} g) (nameMap f) One)
    (α : decodeMap (Cone.left s) =₁ decodeMap (Cone.left t))
    (compatible : (triangle t ∙ (g ◁ α)) =₂ triangle s) where

    left = decodeMap-reflect (Cone.left s) (Cone.left t) α
    right = terminal-iso (Cone.right s) (Cone.right t)
    fs = decodeMap-post g (Cone.left s)
    ft = decodeMap-post g (Cone.left t)
    gs = right-change (Cone.right s)
    gt = right-change (Cone.right t)
    τs = decodeMapIso (Cone.match s)
    τt = decodeMapIso (Cone.match t)
    left-image = decodeMapIso (mapPost g ◁ left)
    right-image = decodeMapIso (nameMap f ◁ right)

    opaque
      adjusted : (triangle t ∙ (g ◁ decodeMapIso left)) =₂ (idIso f ∙ triangle s)
      adjusted = (isoComp-unitˡ-at (triangle s)) ⁻¹ ∙
        (compatible ∙ isoComp-cong (idIso (triangle t))
          (postWhisker g ◁ decodeMap-reflect-β (Cone.left s) (Cone.left t) α))

      right-square : (gt ∙ right-image) =₂ (idIso f ∙ gs)
      right-square = (isoComp-unitˡ-at gs) ⁻¹ ∙ right-natural right

      raw-square : (τt ∙ left-image) =₂ (right-image ∙ τs)
      raw-square = reflect-transported-square fs gs ft gt τs τt
        left-image right-image (g ◁ decodeMapIso left) (idIso f)
        (DecodePost.natural g left) right-square adjusted

      comparison : ConeIso s t
      comparison = record
        { leftIso = left ; rightIso = right
        ; compatible = decodeMap-reflect-Iso₂ _ _
            ((decodeMapIso-comp (nameMap f ◁ right) (Cone.match s)) ⁻¹ ∙
              (raw-square ∙ decodeMapIso-comp (Cone.match t) (mapPost g ◁ left))) }
```
