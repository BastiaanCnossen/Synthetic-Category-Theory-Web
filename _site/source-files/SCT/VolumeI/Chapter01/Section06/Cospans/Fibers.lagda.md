# Fibers of a map of cospans

A map of cospans and a family in its target pullback determine a cospan
of fibers. Its two maps retain their actual matching identifications,
including the target family's matching on the right side.

A cone over the source cospan, together with a whole comparison of its
image to the target family, also factors through the fiber of the induced
pullback functor. The comparison is lifted as a whole: both leg equations
and the compatibility with the matching remain available. The construction
below provides comparison and reconstruction functors. Their inverse laws,
and hence the pullback assertion for the fiber cone, are not established here.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Agda.Primitive using (Level)
open import SCT.VolumeI.Chapter01.Theory using (Theory)
import SCT.VolumeI.Chapter01.Section06.PullbackLaws as Laws

module SCT.VolumeI.Chapter01.Section06.Cospans.Fibers
  {c m a : Level} (𝒯 : Theory c m a) (P : Laws.PullbackStructure 𝒯) where

open import SCT.VolumeI.Chapter01.Section04.Setup 𝒯
open Laws.PullbackStructure P
open import SCT.VolumeI.Chapter01.Section06.PullbackFunctor 𝒯 P
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeRestriction 𝒯
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.ConeAction 𝒯 using (cone-action)
import SCT.VolumeI.Chapter01.Section06.Cospans.ConeAction as Actions
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanAction as Normalized
import SCT.VolumeI.Chapter01.Section03.ProductCalculus.PairingNaturality as PN
import SCT.VolumeI.Chapter01.Section06.Cospans.FiberImages as Images
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackLifting as Lifting
import SCT.VolumeI.Chapter01.Section06.PullbackComparison as Comparisons
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.HigherComparisons as Higher
open import SCT.VolumeI.Chapter01.Section06.ConeCalculus.InverseCalculus 𝒯 using (pre-inverse)
open PN vocabulary terminal products productLaws composition vertical whiskering using (cancel-right; cancel-left)
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.SquareTransport as Transport
open import SCT.VolumeI.Chapter01.Section04.SquareCalculus.ProjectionSquares 𝒯 using (post-inverse)
open import SCT.VolumeI.Chapter01.Section02.Isomorphisms vocabulary terminal products productLaws composition vertical whiskering using (cancel-inverse)

module At {C D E C′ D′ E′ Γ : CAT}
  {f : MAP C E} {g : MAP D E} {f′ : MAP C′ E′} {g′ : MAP D′ E′}
  (F : CospanMap f g f′ g′) (x : MAP Γ (Pullback f′ g′)) where
  private
    module F = CospanMap F
      using (mapCone; pullbackMap; pullbackMap-β)
      renaming (left to u; right to v; base to w; leftSquare to α; rightSquare to β)
    module Action = Actions.Action 𝒯 P F using (map-iso; map-pre)
    top = pullbackCone f g
    bottom = pullbackCone f′ g′

  family : Cone f′ g′ Γ
  family = conePre x bottom
  left-family : MAP Γ C′
  left-family = Cone.left family
  right-family : MAP Γ D′
  right-family = Cone.right family
  base-family : MAP Γ E′
  base-family = f′ ∘ left-family
  matching : base-family =₁ (g′ ∘ right-family)
  matching = Cone.match family

  left-fiber = Pullback F.u left-family
  right-fiber = Pullback F.v right-family
  base-fiber = Pullback F.w base-family
  total-fiber = Pullback F.pullbackMap x

  private
    A = pullbackCone F.u left-family
    B = pullbackCone F.v right-family
    Z = pullbackCone F.w base-family
    T = pullbackCone F.pullbackMap x

  private
    module LeftImage = Images.Along 𝒯 F.u left-family f F.w f′ base-family F.α (idIso base-family)
      using (value; action; restrict; left-normal; right-normal; right-natural)
    module RightImage = Images.Along 𝒯 F.v right-family g F.w g′ base-family F.β (matching ⁻¹)
      using (value; action; restrict; left-normal; right-normal; right-natural)

  left-image-cone : Cone F.w base-family left-fiber
  left-image-cone = LeftImage.value A
  right-image-cone : Cone F.w base-family right-fiber
  right-image-cone = RightImage.value B

  left-map : MAP left-fiber base-fiber
  left-map = pullbackLift left-image-cone
  right-map : MAP right-fiber base-fiber
  right-map = pullbackLift right-image-cone
  left-image : ConeIso (conePre left-map Z) left-image-cone
  left-image = pullbackLift-β left-image-cone
  right-image : ConeIso (conePre right-map Z) right-image-cone
  right-image = pullbackLift-β right-image-cone

  left-restriction : {X : CAT} (k : MAP X left-fiber) →
    ConeIso (conePre (left-map ∘ k) Z) (LeftImage.value (conePre k A))
  left-restriction k = coneIso-compose (coneIso-inverse (LeftImage.restrict k A))
    (coneIso-compose (coneIso-pre k left-image) (coneIso-inverse (conePre-assoc k left-map Z)))
  right-restriction : {X : CAT} (k : MAP X right-fiber) →
    ConeIso (conePre (right-map ∘ k) Z) (RightImage.value (conePre k B))
  right-restriction k = coneIso-compose (coneIso-inverse (RightImage.restrict k B))
    (coneIso-compose (coneIso-pre k right-image) (coneIso-inverse (conePre-assoc k right-map Z)))
```

The factorization below accepts a specified compatible cone, rather than
separate comparisons of its two legs. Its lifted matching has an explicit
whole-cone computation. This is the construction needed for a subsequent
pullback-interchange proof, not a claim that the fiber cospan is already
proved universal.

```agda
  module FactorWithSource {X : CAT} (q : Cone f g X) (r : MAP X Γ)
    (χ : ConeIso (F.mapCone q) (conePre r family))
    (source : MAP X (Pullback f g)) (source-image : ConeIso (conePre source top) q) where
    image-comparison : ConeIso
      (conePre (F.pullbackMap ∘ source) bottom) (F.mapCone q)
    image-comparison = coneIso-compose (Action.map-iso source-image)
      (coneIso-compose (coneIso-inverse (Action.map-pre source top))
      (coneIso-compose (coneIso-pre source F.pullbackMap-β)
        (coneIso-inverse (conePre-assoc source F.pullbackMap bottom))))

    prescribed : ConeIso
      (conePre (F.pullbackMap ∘ source) bottom) (conePre (x ∘ r) bottom)
    prescribed = coneIso-compose (conePre-assoc r x bottom)
      (coneIso-compose χ image-comparison)

    private
      module Lift = Lifting.Lift 𝒯 P (F.pullbackMap ∘ source) (x ∘ r) prescribed
        using (lift; comparison-image; encoded-image)
    comparison : (F.pullbackMap ∘ source) =₁ (x ∘ r)
    comparison = Lift.lift
    comparison-image : ConeIso₂ (cone-action bottom comparison) prescribed
    comparison-image = Lift.comparison-image

    private
      module Encoded = Comparisons.IsoComparison 𝒯 dataPullback (F.pullbackMap ∘ source) (x ∘ r)
        using (comparisonCone; module A)
    encoded-comparison-image : ConeIso (conePre comparison Encoded.comparisonCone)
      (Encoded.A.Boundary.encode prescribed)
    encoded-comparison-image = Lift.encoded-image

    cone : Cone F.pullbackMap x X
    cone = record { left = source ; right = r ; match = comparison }
    functor : MAP X total-fiber
    functor = pullbackLift cone
    computation : ConeIso (conePre functor T) cone
    computation = pullbackLift-β cone

    source-computation : ConeIso (conePre (pullback₁ ∘ functor) top) q
    source-computation = coneIso-compose source-image
      (cone-action top (ConeIso.leftIso computation))
    base-computation : (pullback₂ ∘ functor) =₁ r
    base-computation = ConeIso.rightIso computation

  module Factor {X : CAT} (q : Cone f g X) (r : MAP X Γ)
    (χ : ConeIso (F.mapCone q) (conePre r family)) where
    source : MAP X (Pullback f g)
    source = pullbackLift q
    source-image : ConeIso (conePre source top) q
    source-image = pullbackLift-β q
    open FactorWithSource q r χ source source-image public

  module Normalization {X : CAT} (q : Cone f g X) (r : MAP X Γ) where
    private
      W = F.w ◁ Cone.match q
      G = Cone.match (conePre r family)
      AL = LeftImage.left-normal (Cone.left q)
      AR = RightImage.left-normal (Cone.right q)
      CL = LeftImage.right-normal r
      CR = RightImage.right-normal r
      Ω = Cone.match (F.mapCone q)
      U = comp-assoc r left-family f′
      V = comp-assoc r right-family g′
      γ = matching ▷ r
      γinv = matching ⁻¹ ▷ r

    abstract
      image-normal : (AR ⁻¹ ∙ W) =₂ (Ω ∙ AL ⁻¹)
      image-normal = isoComp-cong (Normalized.Action.Normalization.matching 𝒯 P F q) (idIso (AL ⁻¹)) ∙
        (isoComp-cong (isoComp-assoc-at (AR ⁻¹) W AL) (idIso (AL ⁻¹)) ∙
          (cancel-right AL (AR ⁻¹ ∙ W)) ⁻¹)

      family-normal : (CR ∙ G) =₂ CL
      family-normal =
        isoComp-cong ((preWhisker-idIso base-family r) ⁻¹) (idIso (U ⁻¹)) ∙
        ((isoComp-unitˡ-at (U ⁻¹)) ⁻¹ ∙
        (cancel-left γ (U ⁻¹) ∙
        (isoComp-cong (pre-inverse matching r) (idIso (γ ∙ U ⁻¹)) ∙
        (isoComp-cong (idIso γinv) (cancel-left V (γ ∙ U ⁻¹)) ∙
          isoComp-assoc-at γinv (V ⁻¹) (V ∙ (γ ∙ U ⁻¹))))))


```

To display the corresponding cone of fibers, lift its two component
cones and lift the comparison between their base images. The middle
comparison uses the source cone's matching and the identity of the
parameter. `WithFactors` retains supplied component factorizations;
the default instance uses precisely the chosen pullback lifts.

```agda
  module Display {X : CAT} (q : Cone f g X) (r : MAP X Γ)
    (χ : ConeIso (F.mapCone q) (conePre r family)) where
    left-cone : Cone F.u left-family X
    left-cone = record { left = Cone.left q ; right = r ; match = ConeIso.leftIso χ }
    right-cone : Cone F.v right-family X
    right-cone = record { left = Cone.right q ; right = r ; match = ConeIso.rightIso χ }
    left-leg : MAP X left-fiber
    left-leg = pullbackLift left-cone
    right-leg : MAP X right-fiber
    right-leg = pullbackLift right-cone
    left-computation : ConeIso (conePre left-leg A) left-cone
    left-computation = pullbackLift-β left-cone
    right-computation : ConeIso (conePre right-leg B) right-cone
    right-computation = pullbackLift-β right-cone

    private
      W = F.w ◁ Cone.match q
      L = f′ ◁ ConeIso.leftIso χ
      R = g′ ◁ ConeIso.rightIso χ
      G = Cone.match (conePre r family)
      AL = LeftImage.left-normal (Cone.left q)
      AR = RightImage.left-normal (Cone.right q)
      CR = RightImage.right-normal r
      Ω = Cone.match (F.mapCone q)
      ML = Cone.match (LeftImage.value left-cone)
      MR = Cone.match (RightImage.value right-cone)

    private
      module N = Normalization q r
    abstract
      middle-equation : (MR ∙ W) =₂ ML
      middle-equation = isoComp-cong N.family-normal (idIso (L ∙ AL ⁻¹)) ∙
        ((isoComp-assoc-at CR G (L ∙ AL ⁻¹)) ⁻¹ ∙
        (isoComp-cong (idIso CR) (isoComp-assoc-at G L (AL ⁻¹)) ∙
        (isoComp-cong (idIso CR)
          (isoComp-cong ((ConeIso.compatible χ) ⁻¹) (idIso (AL ⁻¹))) ∙
        (isoComp-cong (idIso CR) ((isoComp-assoc-at R Ω (AL ⁻¹)) ⁻¹) ∙
        (isoComp-cong (idIso CR) (isoComp-cong (idIso R) N.image-normal) ∙
        (isoComp-cong (idIso CR) (isoComp-assoc-at R (AR ⁻¹) W) ∙
          isoComp-assoc-at CR (R ∙ AR ⁻¹) W))))))

    middle : ConeIso (LeftImage.value left-cone) (RightImage.value right-cone)
    middle = record { leftIso = Cone.match q ; rightIso = idIso r
      ; compatible = isoComp-cong ((postWhisker-idIso base-family r) ⁻¹) (idIso ML) ∙
          ((isoComp-unitˡ-at ML) ⁻¹ ∙ middle-equation) }

    module WithFactors (a₀ : MAP X left-fiber) (b₀ : MAP X right-fiber)
      (θA : ConeIso (conePre a₀ A) left-cone)
      (θB : ConeIso (conePre b₀ B) right-cone) where
      left-base-image : ConeIso (conePre (left-map ∘ a₀) Z) (LeftImage.value left-cone)
      left-base-image = coneIso-compose (LeftImage.action θA)
        (left-restriction a₀)
      right-base-image : ConeIso (conePre (right-map ∘ b₀) Z) (RightImage.value right-cone)
      right-base-image = coneIso-compose (RightImage.action θB)
        (right-restriction b₀)


      prescribed : ConeIso (conePre (left-map ∘ a₀) Z) (conePre (right-map ∘ b₀) Z)
      prescribed = coneIso-compose (coneIso-inverse right-base-image)
        (coneIso-compose middle left-base-image)
      private
        module Lift = Lifting.Lift 𝒯 P (left-map ∘ a₀) (right-map ∘ b₀) prescribed
          using (lift; comparison-image)
      comparison : (left-map ∘ a₀) =₁ (right-map ∘ b₀)
      comparison = Lift.lift
      comparison-image : ConeIso₂ (cone-action Z comparison) prescribed
      comparison-image = Lift.comparison-image
      square : Cone left-map right-map X
      square = record { left = a₀ ; right = b₀ ; match = comparison }


    open WithFactors left-leg right-leg left-computation right-computation public

```

Conversely, a cone of fibers determines a source cone and a compatible
comparison with the target family. The two parameter maps need not
agree: their identification transports the right matching. Recovering
the square witness through `SquareTransport` retains a computation for
the actual input compatibility. This computation concerns that named
transport operation; agreement with `Display.middle` still requires a
separate higher comparison.

```agda
  module Decode {X : CAT} (s : Cone left-map right-map X) where
    left-cone = conePre (Cone.left s) A
    right-cone = conePre (Cone.right s) B
    base-comparison : ConeIso (LeftImage.value left-cone) (RightImage.value right-cone)
    base-comparison = coneIso-compose (right-restriction (Cone.right s))
      (coneIso-compose (cone-action Z (Cone.match s))
        (coneIso-inverse (left-restriction (Cone.left s))))
    δ = ConeIso.leftIso base-comparison
    ε = ConeIso.rightIso base-comparison
    q : Cone f g X
    q = record { left = Cone.left left-cone ; right = Cone.left right-cone ; match = δ }
    r : MAP X Γ
    r = Cone.right left-cone
    t : MAP X Γ
    t = Cone.right right-cone
    right-matching : (F.v ∘ Cone.right q) =₁ (right-family ∘ r)
    right-matching = (right-family ◁ ε) ⁻¹ ∙ Cone.match right-cone

    private
      module N = Normalization q r
      AL = LeftImage.left-normal (Cone.left q)
      AR = RightImage.left-normal (Cone.right q)
      CL = LeftImage.right-normal r
      CR = RightImage.right-normal t
      W = F.w ◁ δ
      Ω = Cone.match (F.mapCone q)
      G = Cone.match (conePre r family)
      L = f′ ◁ Cone.match left-cone
      R = g′ ◁ Cone.match right-cone
      J = g′ ◁ (right-family ◁ ε)
      K = base-family ◁ ε
      Rnew = g′ ◁ right-matching

    abstract
      left-boundary : (AR ∙ Ω) =₂ (W ∙ AL)
      left-boundary = cancel-inverse AR (W ∙ AL) ∙
        isoComp-cong (idIso AR) ((Normalized.Action.Normalization.matching 𝒯 P F q) ⁻¹)
      right-boundary : (CR ∙ (J ∙ G)) =₂ (K ∙ CL)
      right-boundary = isoComp-cong (idIso K) N.family-normal ∙
        (isoComp-assoc-at K (RightImage.right-normal r) G ∙
        (isoComp-cong (RightImage.right-natural ε) (idIso G) ∙
          (isoComp-assoc-at CR J G) ⁻¹))
    private
      module Rotation = Transport.At 𝒯 AL AR CL CR L R Ω (J ∙ G) W K
        left-boundary right-boundary
      module Recovered = Rotation.Recover (ConeIso.compatible base-comparison)
    reflected-square : (R ∙ Ω) =₂ ((J ∙ G) ∙ L)
    reflected-square = Recovered.witness
    reflected-computation : Rotation.apply reflected-square =₃ ConeIso.compatible base-comparison
    reflected-computation = Recovered.computation

    recovered-comparison : ConeIso (LeftImage.value left-cone) (RightImage.value right-cone)
    recovered-comparison = record { leftIso = δ ; rightIso = ε
      ; compatible = Rotation.apply reflected-square }
    private
      module HC = Higher.Calculus 𝒯 P (LeftImage.value left-cone) (RightImage.value right-cone)
        using (compatibility-change)
    recovered-image : ConeIso₂ recovered-comparison base-comparison
    recovered-image = HC.compatibility-change recovered-comparison
      (ConeIso.compatible base-comparison) reflected-computation

    abstract
      right-normal : Rnew =₂ (J ⁻¹ ∙ R)
      right-normal = isoComp-cong (post-inverse g′ (right-family ◁ ε)) (idIso R) ∙
        postWhisker-isoComp-at g′ ((right-family ◁ ε) ⁻¹) (Cone.match right-cone)
      decoded-equation : (Rnew ∙ Ω) =₂ (G ∙ L)
      decoded-equation = cancel-left J (G ∙ L) ∙
        (isoComp-cong (idIso (J ⁻¹)) (isoComp-assoc-at J G L) ∙
        (isoComp-cong (idIso (J ⁻¹)) reflected-square ∙
        (isoComp-assoc-at (J ⁻¹) R Ω ∙ isoComp-cong right-normal (idIso Ω))))

    comparison : ConeIso (F.mapCone q) (conePre r family)
    comparison = record { leftIso = Cone.match left-cone ; rightIso = right-matching
      ; compatible = decoded-equation ⁻¹ }
    module Lift = Factor q r comparison
      using (functor; cone; computation; source-computation; base-computation; comparison-image)
    functor : MAP X total-fiber
    functor = Lift.functor

```

The total fiber has a canonical compatible source cone, obtained from
its matching and the whole computation for the induced pullback map.
It therefore gives the comparison to the pullback of component fibers.
Decoding the latter's chosen cone gives the reconstruction in the other
direction. Both complete factorization computations are retained.

```agda
  module Total where
    source-cone : Cone f g total-fiber
    source-cone = conePre (Cone.left T) top
    comparison : ConeIso (F.mapCone source-cone) (conePre (Cone.right T) family)
    comparison = coneIso-compose (coneIso-inverse (conePre-assoc (Cone.right T) x bottom))
      (coneIso-compose (cone-action bottom (Cone.match T))
      (coneIso-compose (conePre-assoc (Cone.left T) F.pullbackMap bottom)
      (coneIso-compose (coneIso-pre (Cone.left T) (coneIso-inverse F.pullbackMap-β))
        (Action.map-pre (Cone.left T) top))))

    module Components = Display source-cone (Cone.right T) comparison
      using (square; comparison-image)
    cone : Cone left-map right-map total-fiber
    cone = Components.square

  comparison : MAP total-fiber (Pullback left-map right-map)
  comparison = pullbackLift Total.cone
  comparison-computation : ConeIso
    (conePre comparison (pullbackCone left-map right-map)) Total.cone
  comparison-computation = pullbackLift-β Total.cone

  private
    module Reconstruction = Decode (pullbackCone left-map right-map)
      using (functor; module Lift)
  reconstruction : MAP (Pullback left-map right-map) total-fiber
  reconstruction = Reconstruction.functor
  reconstruction-computation : ConeIso
    (conePre reconstruction T) Reconstruction.Lift.cone
  reconstruction-computation = Reconstruction.Lift.computation
```
