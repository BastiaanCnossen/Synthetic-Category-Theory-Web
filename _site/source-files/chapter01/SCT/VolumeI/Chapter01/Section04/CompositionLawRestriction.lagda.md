# Composition laws under restriction

The identity evaluation square has the actual chosen identity comparison on
both sides. Its comparison with the identity square is the checked normalized
identity restriction law. The existing unit laws of square pasting then remove
it from either side of an actual evaluation square.

The square comparisons are constructed here with the chosen evaluation and
term endpoint frames. Their side maps compute the specified unit images,
which identify the default unit laws with recovered laws at an anima source.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter01.Section04.CompositionLawRestriction where

open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal using (module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence using (id₌; inv₌; comp-unitˡ; comp-unitʳ; comp-assoc; preWhisker-id₌; postWhisker-id₌; module Composition; module Boundaries)
open Composition
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section02.Specialization
import SCT.VolumeI.Chapter01.Section02.Specialization as Specialization
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
open import SCT.VolumeI.Chapter01.Section03.Identifications.EndpointTransport
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses using (comp₌-unitˡ-One; comp₌-unitʳ-One; inverse-identity; cancel-right; cancel-left)
open import SCT.VolumeI.Chapter01.Section03.Squares
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions using (productMap)
open import SCT.VolumeI.Chapter01.Section03.RelativeFunctors using (FunctorOverBase)
open import SCT.VolumeI.Chapter01.Section03.Identifications.OverBase using (IdentificationOver)
open import SCT.VolumeI.Chapter01.Section04.Composition using (identity-map; mapId; mapComp; compose; compose-pre; compose⁼; compose⁼-composition)
open import SCT.VolumeI.Chapter01.Section04.EvaluationOverBase using (evaluation-over; evaluation-identity; evaluation-compose; evaluation⁼; evaluation-recover)
open import SCT.VolumeI.Chapter01.Section04.MappingAnimae
open import SCT.VolumeI.Chapter01.Section04.EvaluationRestriction using (evaluation-restrict; evaluation-restrict-natural; evaluation-recover-after-change)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence using (hcomp-id-inner-One; hcomp-id-outer-One)
open import SCT.VolumeI.Chapter01.Section04.EvaluationCoherence using (evaluation-compose-natural)
open import SCT.VolumeI.Chapter01.Section04.CompositionLaws using (evaluation-unitˡ; evaluation-unitʳ; mapComp-unitˡ; mapComp-unitʳ; compose-unitˡ; compose-unitʳ; compose-assoc; mapComp-assoc; evaluation-assoc; module Recovered)
open import SCT.VolumeI.Chapter01.Section04.CompositionCoherence
  using (evaluation⁼-composition; evaluation⁼-cong; evaluation⁼-identity)
open import SCT.VolumeI.Chapter01.Section04.CompositionRestriction using (module CompositionUnderRestriction)
open import SCT.VolumeI.Chapter01.Section04.IdentityRestriction using (module IdentityUnderRestriction)
import SCT.VolumeI.Chapter01.Section03.Products.BinaryFunctors as Binary
open import SCT.VolumeI.Chapter01.Section04.CompositionNaturality using (module RecoveredNaturality)

private
  module NormalizedEndpointChange {Γ : Context} {P Q A B : CAT Γ}
    (r : MAP Q P) (v : MAP P (Map A B)) where
    sA : MAP (Q × A) (P × A)
    sA = productMap r (id A)
    sB : MAP (Q × B) (P × B)
    sB = productMap r (id B)
    original = FunctorOverBase.functor (evaluation-over v)
    basic = evaluation-restrict v r

    normalized : {v′ : MAP Q (Map A B)} (δ : (v ∘ r) =₁ v′)
      → (sB ∘ FunctorOverBase.functor (evaluation-over v′)) =₁ (original ∘ sA)
    normalized δ = basic ∙ (sB ◁ evaluation⁼ δ) ⁻¹

    change-square : {v′ : MAP Q (Map A B)} (δ : (v ∘ r) =₁ v′) → Square sA sB
    change-square {v′} δ = square (FunctorOverBase.functor (evaluation-over v′)) original (normalized δ)
    raw-square : Square sA sB
    raw-square = square (FunctorOverBase.functor (evaluation-over (v ∘ r))) original basic

    opaque
      extend-normalization : {v′ v″ : MAP Q (Map A B)} (δ : (v ∘ r) =₁ v′) (η : v′ =₁ v″)
        → (normalized (η ∙ δ) ∙ (sB ◁ evaluation⁼ η)) =₂ normalized δ
      extend-normalization δ η =
        let first = sB ◁ evaluation⁼ δ
            second = sB ◁ evaluation⁼ η
            composite = sB ◁ evaluation⁼ (η ∙ δ)
            composition = postWhisker-comp₌ sB (evaluation⁼ η) (evaluation⁼ δ) ∙
              (postWhisker sB ◁ evaluation⁼-composition η δ)
        in cancel-right first ((inv-comp-right basic first) ⁻¹ ∙
          (inv-comp-right basic composite ∙
            (comp₌-cong (id₌ (normalized (η ∙ δ))) (composition ⁻¹) ∙
              comp₌-assoc (normalized (η ∙ δ)) second first)))

    raw-to-normalized : {v′ : MAP Q (Map A B)} (δ : (v ∘ r) =₁ v′)
      → SquareEquality raw-square (change-square δ)
    raw-to-normalized δ = record
      { source-identification = evaluation⁼ δ
      ; target-identification = id₌ original
      ; compatibility = (inv-comp-right basic (sB ◁ evaluation⁼ δ)) ⁻¹ ∙
          (comp₌-unitˡ-One basic ∙ comp₌-cong (preWhisker-id₌ original sA) (id₌ basic))
      }

    extend-square : {v′ v″ : MAP Q (Map A B)} (δ : (v ∘ r) =₁ v′) (η : v′ =₁ v″)
      → SquareEquality (change-square δ) (change-square (η ∙ δ))
    extend-square δ η = record
      { source-identification = evaluation⁼ η
      ; target-identification = id₌ original
      ; compatibility = (extend-normalization δ η) ⁻¹ ∙
          (comp₌-unitˡ-One (normalized δ) ∙
            comp₌-cong (preWhisker-id₌ original sA) (id₌ (normalized δ)))
      }


module IdentitySquare {Γ : Context} {P Q A : CAT Γ} (r : MAP Q P) where
  private
    R = productMap r (id A)
    Jq = FunctorOverBase.functor (evaluation-over (identity-map {P = Q} A))
    Jp = FunctorOverBase.functor (evaluation-over (identity-map {P = P} A))
    module Restricted = IdentityUnderRestriction {C = A} r
      using (normalized-change; natural)

  chosen : Square R R
  chosen = square Jq Jp Restricted.normalized-change

  comparison : SquareEquality chosen (id-square R)
  comparison = record
    { source-identification = IdentificationOver.identification (evaluation-identity Q A)
    ; target-identification = IdentificationOver.identification (evaluation-identity P A)
    ; compatibility = Restricted.natural
    }

module _ {Γ : Context} {P Q C D : CAT Γ} (r : MAP Q P) where
  private
    RC = productMap r (id C)
    RD = productMap r (id D)
    module SourceIdentity = IdentitySquare {A = C} r using (chosen; comparison)
    module TargetIdentity = IdentitySquare {A = D} r using (chosen; comparison)

  evaluation-left-unit : (F : Square RC RD)
    → SquareEquality (comp-square TargetIdentity.chosen F) F
  evaluation-left-unit F = square-equality-trans
    (comp-square-congˡ TargetIdentity.comparison F) (comp-square-unitˡ F)

  evaluation-right-unit : (F : Square RC RD)
    → SquareEquality (comp-square F SourceIdentity.chosen) F
  evaluation-right-unit F = square-equality-trans
    (comp-square-congʳ F SourceIdentity.comparison) (comp-square-unitʳ F)
```

The evaluation square retains a supplied endpoint identification after
restriction. In the default-unit application f is the universal mapping
identity, f′ is x, and η is comp-unitˡ x.

```agda
module EvaluatedInput {Γ : Context} {P Q C D : CAT Γ}
  (r : MAP Q P) (f : MAP P (Map C D)) (f′ : MAP Q (Map C D))
  (η : (f ∘ r) =₁ f′) where
  private
    RC = productMap r (id C)
    RD = productMap r (id D)
    Fq = FunctorOverBase.functor (evaluation-over f′)
    Fp = FunctorOverBase.functor (evaluation-over f)

  private
    module Endpoint = NormalizedEndpointChange {P = P} {Q = Q} {A = C} {B = D} r f
      using (normalized; change-square; raw-square; raw-to-normalized; extend-normalization; extend-square)

  normalized-change : (RD ∘ Fq) =₁ (Fp ∘ RC)
  normalized-change = Endpoint.normalized η

  chosen : Square RC RD
  chosen = Endpoint.change-square η

  original : Square RC RD
  original = Endpoint.raw-square

  endpoint-comparison : SquareEquality original chosen
  endpoint-comparison = Endpoint.raw-to-normalized η

  extend-square : {f″ : MAP Q (Map C D)} (ζ : f′ =₁ f″)
    → SquareEquality chosen
      (square (FunctorOverBase.functor (evaluation-over f″)) Fp
        (Endpoint.normalized (ζ ∙ η)))
  extend-square ζ = Endpoint.extend-square η ζ

  left-unit = evaluation-left-unit r chosen
  right-unit = evaluation-right-unit r chosen

  private
    module SourceIdentity = IdentitySquare {A = C} r using (chosen)
    module TargetIdentity = IdentitySquare {A = D} r using (chosen)
    IpD = IdentificationOver.identification (evaluation-identity P D)
    IqD = IdentificationOver.identification (evaluation-identity Q D)
    IpC = IdentificationOver.identification (evaluation-identity P C)
    IqC = IdentificationOver.identification (evaluation-identity Q C)

  left-tail-natural :
    (((comp-unitˡ Fp ∙ (IpD ▷ Fp)) ▷ RC) ∙
      Square.cell (comp-square TargetIdentity.chosen chosen)) =₂
    (normalized-change ∙ (RD ◁ (comp-unitˡ Fq ∙ (IqD ▷ Fq))))
  left-tail-natural = SquareEquality.compatibility left-unit

  right-tail-natural :
    (((comp-unitʳ Fp ∙ (Fp ◁ IpC)) ▷ RC) ∙
      Square.cell (comp-square chosen SourceIdentity.chosen)) =₂
    (normalized-change ∙ (RD ◁ (comp-unitʳ Fq ∙ (Fq ◁ IqC))))
  right-tail-natural = SquareEquality.compatibility right-unit
```

The two unit pastings retain the original raw evaluation restriction cells.
The endpoint comparisons carry the supplied mapping input and the actual
constant identity restriction to the normalized unit square. Both results
are complete square identifications.

```agda
module UnitPasting {Γ : Context} {P Q C D : CAT Γ}
  (r : MAP Q P) (f : MAP P (Map C D)) (f′ : MAP Q (Map C D))
  (η : (f ∘ r) =₁ f′) where
  module Input = EvaluatedInput r f f′ η
    using (original; chosen; endpoint-comparison; left-unit; right-unit)
  private
    module LeftIdentity = EvaluatedInput r
      (identity-map {P = P} D) (identity-map {P = Q} D)
      (const-pre (mapId D) r)
      using (original; chosen; endpoint-comparison)
    module RightIdentity = EvaluatedInput r
      (identity-map {P = P} C) (identity-map {P = Q} C)
      (const-pre (mapId C) r)
      using (original; chosen; endpoint-comparison)

  left : SquareEquality
    (comp-square LeftIdentity.original Input.original) Input.chosen
  left = square-equality-trans
    (comp-square-cong LeftIdentity.endpoint-comparison Input.endpoint-comparison)
    Input.left-unit

  right : SquareEquality
    (comp-square Input.original RightIdentity.original) Input.chosen
  right = square-equality-trans
    (comp-square-cong Input.endpoint-comparison RightIdentity.endpoint-comparison)
    Input.right-unit
```

Composition restriction itself is a full comparison of evaluation squares.
The fixed horizontal functors are the changes of parameter; the side functors
are the evaluations of the original and restricted mapping terms.

```agda
module CompositionSquare {Γ : Context} {P Q C D E : CAT Γ}
  (r : MAP Q P) (g : MAP P (Map D E)) (f : MAP P (Map C D)) where
  private
    RC = productMap r (id C)
    RE = productMap r (id E)
    evaluated : {S A B : CAT Γ} → MAP S (Map A B) → MAP (S × A) (S × B)
    evaluated h = FunctorOverBase.functor (evaluation-over h)
    module Restricted = CompositionUnderRestriction r g f
      using (normalized-change; natural)
  module Source = EvaluatedInput r (compose g f)
    (compose (g ∘ r) (f ∘ r)) (compose-pre g f r)
    using (original; chosen; endpoint-comparison; extend-square)

  pasted : Square RC RE
  pasted = comp-square
    (square (evaluated (g ∘ r)) (evaluated g) (evaluation-restrict g r))
    (square (evaluated (f ∘ r)) (evaluated f) (evaluation-restrict f r))

  comparison : SquareEquality Source.chosen pasted
  comparison = record
    { source-identification = IdentificationOver.identification (evaluation-compose (g ∘ r) (f ∘ r))
    ; target-identification = IdentificationOver.identification (evaluation-compose g f)
    ; compatibility = Restricted.natural
    }
```

The actual unit input frames include compose-pre and both term changes.
The comparison below is assembled from those endpoint frames, native
composition restriction, and the actual unit pasting. Its side identifications compute the literal unit images used by the
specialization-and-recovery criterion.

```agda
module UnitRestriction {Γ : Context} {P Q C D : CAT Γ}
  (r : MAP Q P) (f : MAP P (Map C D)) (f′ : MAP Q (Map C D))
  (η : (f ∘ r) =₁ f′) where
  private
    JpD = identity-map {P = P} D
    JqD = identity-map {P = Q} D
    JpC = identity-map {P = P} C
    JqC = identity-map {P = Q} C
    ξD = const-pre (mapId D) r
    ξC = const-pre (mapId C) r

  left-frame = compose⁼ ξD η ∙ compose-pre JpD f r
  right-frame = compose⁼ η ξC ∙ compose-pre f JpC r

  module Target = UnitPasting r f f′ η using (module Input; left; right)
  module Left = CompositionSquare r JpD f using (module Source; comparison)
  module Right = CompositionSquare r f JpC using (module Source; comparison)
  module LeftSource = EvaluatedInput r (compose JpD f) (compose JqD f′) left-frame
    using (chosen; endpoint-comparison)
  module RightSource = EvaluatedInput r (compose f JpC) (compose f′ JqC) right-frame
    using (chosen; endpoint-comparison)

  left : SquareEquality LeftSource.chosen Target.Input.chosen
  left = square-equality-trans
    (square-equality-sym (Left.Source.extend-square (compose⁼ ξD η)))
    (square-equality-trans Left.comparison Target.left)

  right : SquareEquality RightSource.chosen Target.Input.chosen
  right = square-equality-trans
    (square-equality-sym (Right.Source.extend-square (compose⁼ η ξC)))
    (square-equality-trans Right.comparison Target.right)

  private
    RC = productMap r (id C)
    RD = productMap r (id D)
    Fp = FunctorOverBase.functor (evaluation-over f)
    Fq = FunctorOverBase.functor (evaluation-over f′)
    JpDF = FunctorOverBase.functor (evaluation-over JpD)
    JpCF = FunctorOverBase.functor (evaluation-over JpC)
    HpL = FunctorOverBase.functor (evaluation-over (compose JpD f))
    HpR = FunctorOverBase.functor (evaluation-over (compose f JpC))
    IpD = IdentificationOver.identification (evaluation-identity P D)
    IqD = IdentificationOver.identification (evaluation-identity Q D)
    IpC = IdentificationOver.identification (evaluation-identity P C)
    IqC = IdentificationOver.identification (evaluation-identity Q C)
    tailLp = comp-unitˡ Fp ∙ (IpD ▷ Fp)
    tailLq = comp-unitˡ Fq ∙ (IqD ▷ Fq)
    tailRp = comp-unitʳ Fp ∙ (Fp ◁ IpC)
    tailRq = comp-unitʳ Fq ∙ (Fq ◁ IqC)
    VpL = IdentificationOver.identification (evaluation-compose JpD f)
    VpR = IdentificationOver.identification (evaluation-compose f JpC)
    VqL = IdentificationOver.identification (evaluation-compose (JpD ∘ r) (f ∘ r))
    VqR = IdentificationOver.identification (evaluation-compose (f ∘ r) (JpC ∘ r))
    VL = IdentificationOver.identification (evaluation-compose JqD f′)
    VR = IdentificationOver.identification (evaluation-compose f′ JqC)
    actionL = evaluation⁼ (compose⁼ ξD η)
    actionR = evaluation⁼ (compose⁼ η ξC)
    pairL = evaluation⁼ ξD ⋆ evaluation⁼ η
    pairR = evaluation⁼ η ⋆ evaluation⁼ ξC

    normalize-source : {A B : CAT Γ} {u v v₀ w z : MAP A B}
      (tail : w =₁ z) (before : u =₁ v₀) (after : v =₁ w)
      (action : u =₁ v) (paired : v₀ =₁ w)
      → (after ∙ action) =₂ (paired ∙ before)
      → (((tail ∙ paired) ∙ before) ∙ action ⁻¹) =₂ (tail ∙ after)
    normalize-source tail before after action paired natural =
      comp-inv-right (tail ∙ after) action ∙
        comp₌-cong
          ((comp₌-assoc tail after action) ⁻¹ ∙
            (comp₌-cong (id₌ tail) (natural ⁻¹) ∙ comp₌-assoc tail paired before))
          (id₌ (action ⁻¹))

  left-source : SquareEquality.source-identification left =₂
    IdentificationOver.identification (evaluation-unitˡ f′)
  left-source = comp₌-assoc (comp-unitˡ Fq) (IqD ▷ Fq) VL ∙
    normalize-source tailLq VqL VL actionL pairL
      (unconst-sides₌ (evaluation-compose-natural ξD η))

  right-source : SquareEquality.source-identification right =₂
    IdentificationOver.identification (evaluation-unitʳ f′)
  right-source = comp₌-assoc (comp-unitʳ Fq) (Fq ◁ IqC) VR ∙
    normalize-source tailRq VqR VR actionR pairR
      (unconst-sides₌ (evaluation-compose-natural η ξC))

  private
    normalize-target : {A B : CAT Γ} {u w z : MAP A B}
      (tail : w =₁ z) (before : u =₁ w) (fixed : w =₁ w)
      → fixed =₂ id₌ w
      → (((tail ∙ fixed) ∙ before) ∙ (id₌ u) ⁻¹) =₂ (tail ∙ before)
    normalize-target {u = u} tail before fixed fixed-identity =
      comp₌-unitʳ-One (tail ∙ before) ∙
        comp₌-cong
          (comp₌-cong
            (comp₌-unitʳ-One tail ∙ comp₌-cong (id₌ tail) fixed-identity)
            (id₌ before))
          (inverse-identity u)

  left-target : SquareEquality.target-identification left =₂
    IdentificationOver.identification (evaluation-unitˡ f)
  left-target = comp₌-assoc (comp-unitˡ Fp) (IpD ▷ Fp) VpL ∙
    normalize-target tailLp VpL (id₌ JpDF ⋆ id₌ Fp)
      (preWhisker-id₌ JpDF Fp ∙ hcomp-id-inner-One (id₌ JpDF) Fp)

  right-target : SquareEquality.target-identification right =₂
    IdentificationOver.identification (evaluation-unitʳ f)
  right-target = comp₌-assoc (comp-unitʳ Fp) (Fp ◁ IpC) VpR ∙
    normalize-target tailRp VpR (id₌ Fp ⋆ id₌ JpCF)
      (preWhisker-id₌ Fp JpCF ∙ hcomp-id-inner-One (id₌ Fp) JpCF)

  left-natural :
    ((IdentificationOver.identification (evaluation-unitˡ f) ▷ RC) ∙
      Square.cell LeftSource.chosen) =₂
    (Square.cell Target.Input.chosen ∙
      (RD ◁ IdentificationOver.identification (evaluation-unitˡ f′)))
  left-natural =
    comp₌-cong (id₌ (Square.cell Target.Input.chosen)) (postWhisker RD ◁ left-source) ∙
      (SquareEquality.compatibility left ∙
        (comp₌-cong (preWhisker RC ◁ left-target) (id₌ (Square.cell LeftSource.chosen))) ⁻¹)

  right-natural :
    ((IdentificationOver.identification (evaluation-unitʳ f) ▷ RC) ∙
      Square.cell RightSource.chosen) =₂
    (Square.cell Target.Input.chosen ∙
      (RD ◁ IdentificationOver.identification (evaluation-unitʳ f′)))
  right-natural =
    comp₌-cong (id₌ (Square.cell Target.Input.chosen)) (postWhisker RD ◁ right-source) ∙
      (SquareEquality.compatibility right ∙
        (comp₌-cong (preWhisker RC ◁ right-target) (id₌ (Square.cell RightSource.chosen))) ⁻¹)
```

The final specialization criterion reflects an actual supplied route square.
Only the new term source Q needs to be an anima for recovery.

```agda
module _ {Γ : Context} {P Q C D : CAT Γ} where
  evaluation-recover-specialize : (qAn : isAn Q) (r : MAP Q P)
    {x y : MAP P (Map C D)} {x′ y′ : MAP Q (Map C D)}
    (alpha : x =₁ y) (l : (x ∘ r) =₁ x′) (t : (y ∘ r) =₁ y′)
    (U : FunctorOverBase.functor (evaluation-over x) =₁
      FunctorOverBase.functor (evaluation-over y))
    → evaluation⁼ alpha =₂ U
    → (given : IdentificationOver {A = One {Γ}}
        (evaluation-over x′) (evaluation-over y′))
    → (let RC = productMap r (id C)
           RD = productMap r (id D)
       in ((U ▷ RC) ∙
            (evaluation-restrict x r ∙ (RD ◁ evaluation⁼ l) ⁻¹)) =₂
          ((evaluation-restrict y r ∙ (RD ◁ evaluation⁼ t) ⁻¹) ∙
            (RD ◁ IdentificationOver.identification given)))
    → Specialization.specialize alpha r l t =₂ evaluation-recover qAn given
  evaluation-recover-specialize qAn r {x} {y} alpha l t U image-alpha given route =
    let RC = productMap r (id C)
        RD = productMap r (id D)
        raw = alpha ▷ r
        beta = Specialization.specialize alpha r l t
        U′ = U ▷ RC
        source = evaluation-restrict x r
        target = evaluation-restrict y r
        L = RD ◁ evaluation⁼ l
        T = RD ◁ evaluation⁼ t
        Sy = target ∙ T ⁻¹
        defining = changeEndpoints-to-square l t raw beta (id₌ beta)
        evaluated = evaluation⁼-composition beta l ∙
          (evaluation⁼-cong defining ∙ (evaluation⁼-composition t raw) ⁻¹)
        changed-image = square-to-changeEndpoints L T
          (RD ◁ evaluation⁼ raw) (RD ◁ evaluation⁼ beta)
          (post-square₌ RD evaluated)
        natural = replace-edges₌ (id₌ (RD ◁ evaluation⁼ raw))
          (preWhisker RC ◁ image-alpha)
          (unconst-sides₌ (evaluation-restrict-natural alpha r))
        extended = changeEndpoints-extend-square L T (RD ◁ evaluation⁼ raw)
          {l = source} {r = target} {δ = U′} natural
        normalized = replace-edges₌ changed-image (id₌ U′) extended
        after-change = cancel-left Sy (route ∙ normalized)
    in evaluation-recover-after-change qAn r beta given after-change

```

The universal unit laws specialize through their literal composition and
identity frames. At an anima source, the complete restricted unit squares
identify these default choices with the directly recovered laws.

```agda
module _ {Γ : Context} {Q C D : CAT Γ} where
  default-unitˡ-recovered : (qAn : isAn Q) (x : MAP Q (Map C D))
    → compose-unitˡ x =₂ Recovered.unitˡ qAn x
  default-unitˡ-recovered qAn x =
    let i = id (Map C D)
        module Unit = UnitRestriction {P = Map C D} {Q = Q} {C = C} {D = D}
          x i x (comp-unitˡ x) using (left-frame; left-natural)
    in evaluation-recover-specialize qAn x (mapComp-unitˡ C D)
        Unit.left-frame (comp-unitˡ x)
        (IdentificationOver.identification (evaluation-unitˡ i))
        (Recovered.unitˡ-image (map-isAn C D) i)
        (evaluation-unitˡ x) Unit.left-natural

  default-unitʳ-recovered : (qAn : isAn Q) (x : MAP Q (Map C D))
    → compose-unitʳ x =₂ Recovered.unitʳ qAn x
  default-unitʳ-recovered qAn x =
    let i = id (Map C D)
        module Unit = UnitRestriction {P = Map C D} {Q = Q} {C = C} {D = D}
          x i x (comp-unitˡ x) using (right-frame; right-natural)
    in evaluation-recover-specialize qAn x (mapComp-unitʳ C D)
        Unit.right-frame (comp-unitˡ x)
        (IdentificationOver.identification (evaluation-unitʳ i))
        (Recovered.unitʳ-image (map-isAn C D) i)
        (evaluation-unitʳ x) Unit.right-natural
```

The associator uses four actual composition squares. The two outer squares
normalize only their composed input, using the chosen composition naturality.
Pasting the inner comparisons supplies the two complete triple frames. The
associativity of square pasting and the specified relative associator routes
then give the restriction square. Recovery at the raw restricted terms and
the exact projection endpoint frames identify the default associator.

```agda
private
  module BinaryUnderChange {Γ : Context} {P Q A B C : CAT Γ}
    (r : MAP Q P) (g : MAP P (Map B C)) (f : MAP P (Map A B)) where
    module Base = CompositionSquare {P = P} {Q = Q} {C = A} {D = B} {E = C} r g f
      using (pasted; comparison)
    comparison-before = IdentificationOver.identification (evaluation-compose g f)
    comparison-after = IdentificationOver.identification (evaluation-compose (g ∘ r) (f ∘ r))

    module Endpoint = NormalizedEndpointChange {P = P} {Q = Q} {A = A} {B = C} r (compose g f)
    sA : MAP (Q × A) (P × A)
    sA = productMap r (id A)
    sC : MAP (Q × C) (P × C)
    sC = productMap r (id C)

    opaque
      -- The two callers below supply the one-sided source normalization and
      -- the actual selected composition-naturality square, respectively.
      normalize-one-side : {g′ : MAP Q (Map B C)} {f′ : MAP Q (Map A B)}
        (η : compose (g ∘ r) (f ∘ r) =₁ compose g′ f′)
        (H : (FunctorOverBase.functor (evaluation-over (g ∘ r)) ∘
              FunctorOverBase.functor (evaluation-over (f ∘ r))) =₁
            (FunctorOverBase.functor (evaluation-over g′) ∘ FunctorOverBase.functor (evaluation-over f′)))
        (changed-paste : (sC ∘ (FunctorOverBase.functor (evaluation-over g′) ∘
              FunctorOverBase.functor (evaluation-over f′))) =₁
            ((FunctorOverBase.functor (evaluation-over g) ∘ FunctorOverBase.functor (evaluation-over f)) ∘ sA))
        → (changed-paste ∙ (sC ◁ H)) =₂ Square.cell Base.pasted
        → ((IdentificationOver.identification (evaluation-compose g′ f′) ∙ evaluation⁼ η)) =₂
            (H ∙ comparison-after)
        → ((comparison-before ▷ sA) ∙ Endpoint.normalized (η ∙ compose-pre g f r)) =₂
            (changed-paste ∙ (sC ◁ IdentificationOver.identification (evaluation-compose g′ f′)))
      normalize-one-side {g′} {f′} η H changed-paste source-normalization naturality =
        let before = comparison-before ▷ sA
            after = sC ◁ IdentificationOver.identification (evaluation-compose g′ f′)
            raw-after = sC ◁ comparison-after
            action = sC ◁ evaluation⁼ η
            horizontal = sC ◁ H
            next = Endpoint.normalized (η ∙ compose-pre g f r)
            natural-post = postWhisker-comp₌ sC H comparison-after ∙
              ((postWhisker sC ◁ naturality) ∙
                (postWhisker-comp₌ sC
                  (IdentificationOver.identification (evaluation-compose g′ f′)) (evaluation⁼ η)) ⁻¹)
            left-normal = comp₌-cong (id₌ before) (Endpoint.extend-normalization (compose-pre g f r) η) ∙
              comp₌-assoc before next action
            right-normal = (SquareEquality.compatibility Base.comparison) ⁻¹ ∙
              (comp₌-cong source-normalization (id₌ raw-after) ∙
              ((comp₌-assoc changed-paste horizontal raw-after) ⁻¹ ∙
              (comp₌-cong (id₌ changed-paste) natural-post ∙
                comp₌-assoc changed-paste after action)))
        in cancel-right action (right-normal ⁻¹ ∙ left-normal)

module _ {Γ : Context} {P : CAT Γ} where
  module AssociatorEndpointFactorization {U A B C D : CAT Γ}
    (r : MAP P U) (z₀ : MAP U (Map C D)) (y₀ : MAP U (Map B C)) (x₀ : MAP U (Map A B))
    {z : MAP P (Map C D)} {y : MAP P (Map B C)} {x : MAP P (Map A B)}
    (lz : (z₀ ∘ r) =₁ z) (ly : (y₀ ∘ r) =₁ y) (lx : (x₀ ∘ r) =₁ x) where

    private
      zr = z₀ ∘ r
      yr = y₀ ∘ r
      xr = x₀ ∘ r
      dzy = compose-pre z₀ y₀ r
      dyx = compose-pre y₀ x₀ r
      qzy = compose⁼ lz ly
      qyx = compose⁼ ly lx
      outerL = compose-pre (compose z₀ y₀) x₀ r
      outerR = compose-pre z₀ (compose y₀ x₀) r

    δL : (compose (compose z₀ y₀) x₀ ∘ r) =₁ compose (compose zr yr) xr
    δL = compose⁼ dzy (id₌ xr) ∙ outerL
    δR : (compose z₀ (compose y₀ x₀) ∘ r) =₁ compose zr (compose yr xr)
    δR = compose⁼ (id₌ zr) dyx ∙ outerR

    λL : compose (compose zr yr) xr =₁ compose (compose z y) x
    λL = compose⁼ qzy lx
    λR : compose zr (compose yr xr) =₁ compose z (compose y x)
    λR = compose⁼ lz qyx

    Ldefault : (compose (compose z₀ y₀) x₀ ∘ r) =₁ compose (compose z y) x
    Ldefault = compose⁼ (qzy ∙ dzy) lx ∙ outerL
    Rdefault : (compose z₀ (compose y₀ x₀) ∘ r) =₁ compose z (compose y x)
    Rdefault = compose⁼ lz (qyx ∙ dyx) ∙ outerR

    left-factorization : Ldefault =₂ (λL ∙ δL)
    left-factorization =
      comp₌-assoc λL (compose⁼ dzy (id₌ xr)) outerL ∙
        comp₌-cong
          (compose⁼-composition qzy dzy lx (id₌ xr) ∙
            Binary.binary-cong₂ mapComp (id₌ (qzy ∙ dzy)) ((comp₌-unitʳ-One lx) ⁻¹))
          (id₌ outerL)

    right-factorization : Rdefault =₂ (λR ∙ δR)
    right-factorization =
      comp₌-assoc λR (compose⁼ (id₌ zr) dyx) outerR ∙
        comp₌-cong
          (compose⁼-composition lz (id₌ zr) qyx dyx ∙
            Binary.binary-cong₂ mapComp ((comp₌-unitʳ-One lz) ⁻¹) (id₌ (qyx ∙ dyx)))
          (id₌ outerR)


private
  module _ {Γ : Context} {Q : CAT Γ} where
    evaluated-one : {A B : CAT Γ} → MAP Q (Map A B) → MAP (Q × A) (Q × B)
    evaluated-one v = FunctorOverBase.functor (evaluation-over v)

    opaque
      evaluation-id-One : {A B : CAT Γ} (v : MAP Q (Map A B))
        → evaluation⁼ (id₌ v) =₂ id₌ (evaluated-one v)
      evaluation-id-One v = const-One (id₌ (evaluated-one v)) ∙
        (evaluation⁼-identity v ∙ evaluation⁼-cong ((const-One (id₌ v)) ⁻¹))

      compose-natural-outer-One : {A B C : CAT Γ}
        {g g′ : MAP Q (Map B C)} (α : g =₁ g′) (f : MAP Q (Map A B))
        → SquareCell₌ (evaluation⁼ (compose⁼ α (id₌ f))) (evaluation⁼ α ▷ evaluated-one f)
            (IdentificationOver.identification (evaluation-compose g f))
            (IdentificationOver.identification (evaluation-compose g′ f))
      compose-natural-outer-One α f = replace-edges₌ (id₌ _)
        (hcomp-id-inner-One (evaluation⁼ α) (evaluated-one f) ∙
          hcomp-cong (id₌ (evaluation⁼ α)) (evaluation-id-One f))
        (unconst-sides₌ (evaluation-compose-natural α (id₌ f)))

      compose-natural-inner-One : {A B C : CAT Γ}
        (g : MAP Q (Map B C)) {f f′ : MAP Q (Map A B)} (β : f =₁ f′)
        → SquareCell₌ (evaluation⁼ (compose⁼ (id₌ g) β)) (evaluated-one g ◁ evaluation⁼ β)
            (IdentificationOver.identification (evaluation-compose g f))
            (IdentificationOver.identification (evaluation-compose g f′))
      compose-natural-inner-One g β = replace-edges₌ (id₌ _)
        (hcomp-id-outer-One (evaluated-one g) (evaluation⁼ β) ∙
          hcomp-cong (evaluation-id-One g) (id₌ (evaluation⁼ β)))
        (unconst-sides₌ (evaluation-compose-natural (id₌ g) β))

  module RawAssociatorRestriction {Γ : Context} {P Q A B C D : CAT Γ}
    (r : MAP Q P) (z : MAP P (Map C D)) (y : MAP P (Map B C)) (x : MAP P (Map A B)) where
    sA : MAP (Q × A) (P × A)
    sA = productMap r (id A)
    sB : MAP (Q × B) (P × B)
    sB = productMap r (id B)
    sC : MAP (Q × C) (P × C)
    sC = productMap r (id C)
    sD : MAP (Q × D) (P × D)
    sD = productMap r (id D)
    Fp = FunctorOverBase.functor (evaluation-over x)
    Gp = FunctorOverBase.functor (evaluation-over y)
    Hp = FunctorOverBase.functor (evaluation-over z)
    Fq = FunctorOverBase.functor (evaluation-over (x ∘ r))
    Gq = FunctorOverBase.functor (evaluation-over (y ∘ r))
    Hq = FunctorOverBase.functor (evaluation-over (z ∘ r))
    HGp = FunctorOverBase.functor (evaluation-over (compose z y))
    GFp = FunctorOverBase.functor (evaluation-over (compose y x))
    xr = x ∘ r
    yr = y ∘ r
    zr = z ∘ r
    dzy = compose-pre z y r
    dyx = compose-pre y x r
    left-action = compose⁼ dzy (id₌ xr)
    right-action = compose⁼ (id₌ zr) dyx
    δL = left-action ∙ compose-pre (compose z y) x r
    δR = right-action ∙ compose-pre z (compose y x) r
    Ex : Square sA sB
    Ex = square Fq Fp (evaluation-restrict x r)
    Ey : Square sB sC
    Ey = square Gq Gp (evaluation-restrict y r)
    Ez : Square sC sD
    Ez = square Hq Hp (evaluation-restrict z r)
    module HG = CompositionSquare {P = P} {Q = Q} {C = B} {D = C} {E = D} r z y
      using (module Source; comparison)
    module GF = CompositionSquare {P = P} {Q = Q} {C = A} {D = B} {E = C} r y x
      using (module Source; comparison)
    module OuterLeft = BinaryUnderChange {P = P} {Q = Q} {A = A} {B = B} {C = D} r (compose z y) x
      using (normalize-one-side)
    module OuterRight = BinaryUnderChange {P = P} {Q = Q} {A = A} {B = C} {C = D} r z (compose y x)
      using (normalize-one-side)
    module LeftSource = EvaluatedInput {P = P} {Q = Q} {C = A} {D = D} r
      (compose (compose z y) x) (compose (compose zr yr) xr) δL using (chosen; normalized-change)
    module RightSource = EvaluatedInput {P = P} {Q = Q} {C = A} {D = D} r
      (compose z (compose y x)) (compose zr (compose yr xr)) δR using (chosen; normalized-change)
    left-inputs : Square sA sD
    left-inputs = comp-square HG.Source.chosen Ex
    right-inputs : Square sA sD
    right-inputs = comp-square Ez GF.Source.chosen

    opaque
      left-input-normalization : (Square.cell left-inputs ∙ (sD ◁ (evaluation⁼ dzy ▷ Fq))) =₂
        Square.cell (comp-square HG.Source.original Ex)
      left-input-normalization =
        let comparison = comp-square-congˡ HG.Source.endpoint-comparison Ex
            pasted = Square.cell (comp-square HG.Source.original Ex)
            target-normal = preWhisker-id₌ (HGp ∘ Fp) sA ∙
              (preWhisker sA ◁ preWhisker-id₌ HGp Fp)
        in comp₌-unitˡ-One pasted ∙
          (comp₌-cong target-normal (id₌ pasted) ∙ (square-equality-cell comparison) ⁻¹)

      right-input-normalization : (Square.cell right-inputs ∙ (sD ◁ (Hq ◁ evaluation⁼ dyx))) =₂
        Square.cell (comp-square Ez GF.Source.original)
      right-input-normalization =
        let comparison = comp-square-congʳ Ez GF.Source.endpoint-comparison
            pasted = Square.cell (comp-square Ez GF.Source.original)
            target-normal = preWhisker-id₌ (Hp ∘ GFp) sA ∙
              (preWhisker sA ◁ postWhisker-id₌ Hp GFp)
        in comp₌-unitˡ-One pasted ∙
          (comp₌-cong target-normal (id₌ pasted) ∙ (square-equality-cell comparison) ⁻¹)

    left-outer : SquareEquality LeftSource.chosen left-inputs
    left-outer = record
      { source-identification = IdentificationOver.identification (evaluation-compose (compose zr yr) xr)
      ; target-identification = IdentificationOver.identification (evaluation-compose (compose z y) x)
      ; compatibility = OuterLeft.normalize-one-side left-action (evaluation⁼ dzy ▷ Fq)
          (Square.cell left-inputs) left-input-normalization (compose-natural-outer-One dzy xr)
      }
    right-outer : SquareEquality RightSource.chosen right-inputs
    right-outer = record
      { source-identification = IdentificationOver.identification (evaluation-compose zr (compose yr xr))
      ; target-identification = IdentificationOver.identification (evaluation-compose z (compose y x))
      ; compatibility = OuterRight.normalize-one-side right-action (Hq ◁ evaluation⁼ dyx)
          (Square.cell right-inputs) right-input-normalization (compose-natural-inner-One zr dyx)
      }

    left-frame : SquareEquality LeftSource.chosen (comp-square (comp-square Ez Ey) Ex)
    left-frame = square-equality-trans left-outer (comp-square-congˡ HG.comparison Ex)
    right-frame : SquareEquality RightSource.chosen (comp-square Ez (comp-square Ey Ex))
    right-frame = square-equality-trans right-outer (comp-square-congʳ Ez GF.comparison)

    left-original = SquareEquality.target-identification left-frame
    right-original = SquareEquality.target-identification right-frame
    left-changed = SquareEquality.source-identification left-frame
    right-changed = SquareEquality.source-identification right-frame
    associator-original = IdentificationOver.identification (evaluation-assoc z y x)
    associator-changed = IdentificationOver.identification (evaluation-assoc zr yr xr)
    Ap = comp-assoc Fp Gp Hp
    Aq = comp-assoc Fq Gq Hq

    opaque
      original-route-square : SquareCell₌ associator-original Ap left-original right-original
      original-route-square = inverse-route-square left-original
        (Hp ◁ IdentificationOver.identification (evaluation-compose y x))
        (IdentificationOver.identification (evaluation-compose z (compose y x)))
        associator-original Ap (id₌ associator-original)

      changed-route-square : SquareCell₌ associator-changed Aq left-changed right-changed
      changed-route-square = inverse-route-square left-changed
        (Hq ◁ IdentificationOver.identification (evaluation-compose yr xr))
        (IdentificationOver.identification (evaluation-compose zr (compose yr xr)))
        associator-changed Aq (id₌ associator-changed)

      associator-route-under-change : ((associator-original ▷ sA) ∙ LeftSource.normalized-change) =₂
        (RightSource.normalized-change ∙ (sD ◁ associator-changed))
      associator-route-under-change = (fill-cube₌
        (post-square₌ sD changed-route-square) (pre-square₌ sA original-route-square)
        ((SquareEquality.compatibility left-frame) ⁻¹)
        ((SquareEquality.compatibility right-frame) ⁻¹)
        (square-equality-cell (comp-square-assoc Ez Ey Ex))) ⁻¹

      recovered-restriction : (pAn : isAn P) (qAn : isAn Q)
        → Specialization.specialize (Recovered.assoc pAn z y x) r δL δR =₂
            Recovered.assoc qAn zr yr xr
      recovered-restriction pAn qAn = evaluation-recover-specialize qAn r
        (Recovered.assoc pAn z y x) δL δR associator-original
        (Recovered.assoc-image pAn z y x) (evaluation-assoc zr yr xr) associator-route-under-change

module _ {Γ : Context} {P A B C D : CAT Γ} where
  opaque
    compose-assoc-agreement : (pAn : isAn P)
      (z : MAP P (Map C D)) (y : MAP P (Map B C)) (x : MAP P (Map A B))
      → compose-assoc z y x =₂ Recovered.assoc pAn z y x
    compose-assoc-agreement pAn z y x =
      let U = (Map C D × Map B C) × Map A B
          uAn = product-isAn (product-isAn (map-isAn C D) (map-isAn B C)) (map-isAn A B)
          z₀ : MAP U (Map C D)
          z₀ = pr₁ ∘ pr₁
          y₀ : MAP U (Map B C)
          y₀ = pr₂ ∘ pr₁
          x₀ : MAP U (Map A B)
          x₀ = pr₂
          triple = pair (pair z y) x
          first = pair-β₁ z y ∙ ((pr₁ ◁ pair-β₁ (pair z y) x) ∙ comp-assoc triple pr₁ pr₁)
          second = pair-β₂ z y ∙ ((pr₂ ◁ pair-β₁ (pair z y) x) ∙ comp-assoc triple pr₁ pr₂)
          third = pair-β₂ (pair z y) x
          module Frames = AssociatorEndpointFactorization {P = P} {U = U} {A = A} {B = B} {C = C} {D = D}
            triple z₀ y₀ x₀ first second third
            using (δL; δR; λL; λR; Ldefault; Rdefault; left-factorization; right-factorization)
          module Raw = RawAssociatorRestriction {P = U} {Q = P} {A = A} {B = B} {C = C} {D = D}
            triple z₀ y₀ x₀ using (recovered-restriction)
          universal = mapComp-assoc A B C D ▷ triple
          factor-frames = comp₌-cong Frames.right-factorization
            (comp₌-cong (id₌ universal) (inv₌ ◁ Frames.left-factorization))
          raw = Raw.recovered-restriction uAn pAn
          normalized = square-to-changeEndpoints Frames.λL Frames.λR
            (Recovered.assoc pAn (z₀ ∘ triple) (y₀ ∘ triple) (x₀ ∘ triple))
            (Recovered.assoc pAn z y x)
            (transpose-square₌ (RecoveredNaturality.assoc-natural-One pAn first second third))
      in normalized ∙
        (changeEndpoints-cong Frames.λL Frames.λR raw ∙
          ((changeEndpoints-iterated Frames.δL Frames.δR Frames.λL Frames.λR universal) ⁻¹ ∙ factor-frames))
```
