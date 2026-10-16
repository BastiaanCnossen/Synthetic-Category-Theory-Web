# Point evaluation under parameter and point change

Point evaluation retains its chosen uncurrying triangle when the family
parameter or the evaluated point changes. These squares are the common
input to identity-family restriction and composition of shape restrictions.
The native insertion comparison and its image remain explicit.

```agda
{-# OPTIONS --without-K #-}
module SCT.VolumeI.Chapter02.Section01.PointEvaluationParameters where
open import SCT.VolumeI.Chapter01.Section01.Vocabulary
open Operations
open import SCT.VolumeI.Chapter01.Section01.Terminal
  using (terminate; module Constructions)
open Constructions
open import SCT.VolumeI.Chapter01.Section02.Coherence
  using (id₌; comp-assoc; comp-unitˡ; comp-unitʳ; module Composition; postWhisker-id₌; preWhisker-id₌; module Boundaries; inv₌)
open Composition
open import SCT.VolumeI.Chapter01.Section02.Specialization
  using (const-One; const-pre; comp₌-assoc; comp₌-cong; inv-comp-left; comp-inv-right; inv-comp-right; comp-inv-left; preWhisker-comp₌; interchange-fixedInner; interchange-fixedOuter; interchange; reassociateFour; postWhisker-comp₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Inverses
  using (postWhisker-inverse; preWhisker-inverse; comp₌-unitˡ-One; comp₌-unitʳ-One; cancel-left; inverse-inverse)
open import SCT.VolumeI.Chapter01.Section02.Products
  using (module Calculus)
open Calculus
open import SCT.VolumeI.Chapter01.Section02.IdentificationSquares
  using (unconst-sides₌; paste-square₌; inverse-square₌; replace-edges₌; post-square₌; identity-square₌)
open import SCT.VolumeI.Chapter01.Section03.ProductConstructions
  using (productMap; productMap-id)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctor
  using (productMap-cong; productMap-cong-triangle₁; productMap-cong-triangle₂)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductRestriction
  using (product-restriction; restriction-compositor)
open import SCT.VolumeI.Chapter01.Section07.FunctorCategories
  using (Fun; funEval; funUniversal)
open import SCT.VolumeI.Chapter01.Section07.Evaluation
  using (evaluate-cong; evaluate⁼-absolute; evaluate-id; evaluate-restrict)
open import SCT.VolumeI.Chapter01.Section07.Currying
  using (funUncurry; funCurry-β; reflect; reflect-β-One)
open import SCT.VolumeI.Chapter02.Section01.Morphisms
  using (Ar; ev₀; ev₁; evAt; insert; identity-family; MorphismFamily; module AtPoint; evAt-cong; evAt-pre)
open Boundaries using (SquareCell₌)
open import SCT.VolumeI.Chapter01.Section03.Identifications.FunctorCoherence
  using (preWhisker-comp-One; postWhisker-comp-One; postWhisker-id-One; whisker-mixed-One; left-unitor-comp; right-unitor-comp; triangle-whiskered; pentagon-whiskered-right)
open import SCT.VolumeI.Chapter01.Section03.Products.BinaryFunctors
  using (binary-pre; binary-pre-inputs-One)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductPairing
  using (productMap-pair; productMap-pair-inner-One)
open import SCT.VolumeI.Chapter01.Section03.Products.Pairing
  using (pair⁼-square; pair₌-unique; pair⁼-comp; pair⁼-cong; pair⁼-id-One)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingRestriction
  using (pair-evaluation-over₁-One; pair-evaluation-over₂-One; pair-pre-natural-inputs-One)
open import SCT.VolumeI.Chapter01.Section03.Products.PairingSquares
  using (pair-compatible-One)
open import SCT.VolumeI.Chapter01.Section03.Identifications.RestrictionDiagrams
  using (RestrictionDiagram; Evaluation; restriction-diagram; evaluation)
open import SCT.VolumeI.Chapter01.Section03.Identifications.Triangles
  using (post-square-cell; post-square-cell-id; post-square-cell-comp; restrict-triangle; lies-over-comp; post-triangle)
open import SCT.VolumeI.Chapter01.Section03.Identifications.TriangleCoherence
  using (post-triangle-change; const-pre-iterated; post-iterated-restriction; post-triangle-comp)
open import SCT.VolumeI.Chapter01.Section03.Products.ProductFunctorCoherence
  using (productMap-first-comp)
open import SCT.VolumeI.Chapter01.Section03.Products.FirstFactorSubstitution
  using (module PairInput; at-pair-input-change; at-pair-restrict)
open import SCT.VolumeI.Chapter01.Section07.EvaluationSubstitution
  using (evaluation-restriction-triangle; evaluate-restrict-inverse-triangle)
open import SCT.VolumeI.Chapter01.Section07.Functoriality using (funPre; funPre-β)


module PointNaturality {Γ : Context} {I C P : CAT Γ}
  (h : MAP P (Fun I C)) where
  private
    F : CAT Γ
    F = Fun I C
    e : MAP (F × I) C
    e = funEval

  insertion-action : {Q : CAT Γ} {a b : MAP One I}
    → a =₁ b → insert {P = Q} a =₁ insert b
  insertion-action {Q} α = pair⁼ (const (id₌ (id Q))) (α ▷ terminate Q)

  left-normal : (a : MAP One I)
    → (evAt a ∘ h) =₁ (e ∘ pair h (const a))
  left-normal a = (e ◁ pair⁼ (comp-unitˡ h) (const-pre a h)) ∙
    binary-pre e (id F) (const {P = F} a) h

  right-normal : (a : MAP One I)
    → (funUncurry h ∘ insert a) =₁ (e ∘ pair h (const a))
  right-normal a = (e ◁ pair⁼ (comp-unitʳ h) (comp-unitˡ (const {P = P} a))) ∙
    ((e ◁ productMap-pair h (id I) (id P) (const a)) ∙
      comp-assoc (insert a) (productMap h (id I)) e)

  module _ {a b : MAP One I} (α : a =₁ b) where
    private
      first-left : SquareCell₌ (const (id₌ (id F)) ▷ h)
        (const (id₌ h)) (comp-unitˡ h) (comp-unitˡ h)
      first-left = replace-edges₌
        ((preWhisker-id₌ (id F) h ∙
          (preWhisker h ◁ const-One (id₌ (id F)))) ⁻¹)
        ((const-One (id₌ h)) ⁻¹)
        ((comp₌-unitˡ-One (comp-unitˡ h)) ⁻¹ ∙ comp₌-unitʳ-One (comp-unitˡ h))

      second-left : SquareCell₌ ((α ▷ terminate F) ▷ h)
        (α ▷ terminate P) (const-pre a h) (const-pre b h)
      second-left = paste-square₌ (preWhisker-comp-One α (terminate F) h)
        (unconst-sides₌ ((interchange-fixedInner α
          (terminal-identification (terminate F ∘ h) (terminate P))) ⁻¹))

      left-square : SquareCell₌ (evAt-cong α ▷ h)
        (e ◁ pair⁼ (const (id₌ h)) (α ▷ terminate P))
        (left-normal a) (left-normal b)
      left-square = paste-square₌
        (binary-pre-inputs-One e (const (id₌ (id F))) (α ▷ terminate F) h)
        (post-square₌ e (pair⁼-square first-left second-left))

      first-right : SquareCell₌ (h ◁ const (id₌ (id P)))
        (const (id₌ h)) (comp-unitʳ h) (comp-unitʳ h)
      first-right = replace-edges₌
        ((postWhisker-id₌ h (id P) ∙
          (postWhisker h ◁ const-One (id₌ (id P)))) ⁻¹)
        ((const-One (id₌ h)) ⁻¹)
        ((comp₌-unitˡ-One (comp-unitʳ h)) ⁻¹ ∙ comp₌-unitʳ-One (comp-unitʳ h))

      right-square : SquareCell₌ (funUncurry h ◁ insertion-action α)
        (e ◁ pair⁼ (const (id₌ h)) (α ▷ terminate P))
        (right-normal a) (right-normal b)
      right-square = paste-square₌
        (paste-square₌ (postWhisker-comp-One (insertion-action α) (productMap h (id I)) e)
          (post-square₌ e (productMap-pair-inner-One h (id I)
            (const (id₌ (id P))) (α ▷ terminate P))))
        (post-square₌ e (pair⁼-square first-right (postWhisker-id-One (α ▷ terminate P))))

    uncurry-point-square : SquareCell₌ (evAt-cong α ▷ h)
      (funUncurry h ◁ insertion-action α)
      (AtPoint.uncurry-image a h) (AtPoint.uncurry-image b h)
    uncurry-point-square = paste-square₌ left-square (inverse-square₌ right-square)

module RestrictionPointNaturality {Γ : Context} {I J C : CAT Γ}
  (d : MAP I J) where
  private
    F : CAT Γ
    F = Fun J C
    e : MAP (F × J) C
    e = funEval
    k : MAP F (Fun I C)
    k = funPre d
    D : MAP (F × I) (F × J)
    D = productMap (id F) d
  module μ = PointNaturality {C = C} k

  module _ {a b : MAP One I} (α : a =₁ b) where
    private
      beta-square : SquareCell₌ (funUncurry k ◁ μ.insertion-action α)
        ((e ∘ D) ◁ μ.insertion-action α)
        (funPre-β d ▷ insert a) (funPre-β d ▷ insert b)
      beta-square = unconst-sides₌
        (interchange-fixedOuter (funPre-β d) (μ.insertion-action α))

      close-square : SquareCell₌
        (pair⁼ (id F ◁ const (id₌ (id F))) (d ◁ (α ▷ terminate F)))
        (pair⁼ (const (id₌ (id F))) ((d ◁ α) ▷ terminate F))
        (pair⁼ (comp-unitˡ (id F)) ((comp-assoc (terminate F) a d) ⁻¹))
        (pair⁼ (comp-unitˡ (id F)) ((comp-assoc (terminate F) b d) ⁻¹))
      close-square = pair⁼-square (postWhisker-id-One (const (id₌ (id F))))
        (inverse-square₌ (whisker-mixed-One α (terminate F) d))

    point-square : SquareCell₌ (evAt-cong α ▷ k) (evAt-cong (d ◁ α))
      (evAt-pre a d) (evAt-pre b d)
    point-square = paste-square₌
      (paste-square₌
        (paste-square₌ (paste-square₌ (μ.uncurry-point-square α) beta-square)
          (postWhisker-comp-One (μ.insertion-action α) D e))
        (post-square₌ e (productMap-pair-inner-One (id F) d
          (const (id₌ (id F))) (α ▷ terminate F))))
      (post-square₌ e close-square)

module UncurryRoute {Γ : Context} {P I C : CAT Γ}
  (a : MAP One I) (h : MAP P (Fun I C)) where
  private
    F = Fun I C
    e = funEval {C = I} {D = C}
    module Normal = PointNaturality h
    front = pair⁼ (comp-unitˡ h) (const-pre a h) ∙
      pair-pre (id F) (const {P = F} a) h
    θ = pair⁼ (comp-unitʳ h) (comp-unitˡ (const {P = P} a)) ∙
      productMap-pair h (id I) (id P) (const a)
    AL = comp-assoc h (insert a) e
    AR = comp-assoc (insert a) (productMap h (id I)) e
    L = Normal.left-normal a
    R = Normal.right-normal a

  insertion : (insert {P = F} a ∘ h) =₁
    (productMap h (id I) ∘ insert {P = P} a)
  insertion = θ ⁻¹ ∙ front

  private
    left-normalized : L =₂ ((e ◁ front) ∙ AL)
    left-normalized = comp₌-cong
      ((postWhisker-comp₌ e (pair⁼ (comp-unitˡ h) (const-pre a h))
        (pair-pre (id F) (const {P = F} a) h)) ⁻¹) (id₌ AL) ∙
      ((comp₌-assoc _ _ AL) ⁻¹)
    right-normalized : R =₂ ((e ◁ θ) ∙ AR)
    right-normalized = comp₌-cong
      ((postWhisker-comp₌ e (pair⁼ (comp-unitʳ h) (comp-unitˡ (const {P = P} a)))
        (productMap-pair h (id I) (id P) (const a))) ⁻¹) (id₌ AR) ∙
      ((comp₌-assoc _ _ AR) ⁻¹)
    tail = (e ◁ insertion) ∙ AL
    route = AR ⁻¹ ∙ tail
    route-image : (R ∙ route) =₂ L
    route-image = left-normalized ⁻¹ ∙
      (comp₌-cong (postWhisker e ◁ comp-inv-left θ front) (id₌ AL) ∙
      (comp₌-cong ((postWhisker-comp₌ e θ insertion) ⁻¹) (id₌ AL) ∙
      ((comp₌-assoc (e ◁ θ) (e ◁ insertion) AL) ⁻¹ ∙
      (comp₌-cong (id₌ (e ◁ θ)) (comp-inv-left AR tail) ∙
      (comp₌-assoc (e ◁ θ) AR route ∙
        comp₌-cong right-normalized (id₌ route))))))

  factorization : AtPoint.uncurry-image a h =₂
    (AR ⁻¹ ∙ ((e ◁ insertion) ∙ AL))
  factorization = cancel-left R (route-image ⁻¹ ∙ comp-inv-left R L)

module ParameterInsertion {Γ : Context} {I : CAT Γ} (a : MAP One I) where
  front : {P Q : CAT Γ} (h : MAP P Q)
    → (insert {P = Q} a ∘ h) =₁ pair h (const {P = P} a)
  front {Q = Q} h = pair⁼ (comp-unitˡ h) (const-pre a h) ∙
    pair-pre (id Q) (const {P = Q} a) h
  back : {P Q : CAT Γ} (h : MAP P Q)
    → (productMap h (id I) ∘ insert {P = P} a) =₁ pair h (const {P = P} a)
  back {P} h = pair⁼ (comp-unitʳ h) (comp-unitˡ (const {P = P} a)) ∙
    productMap-pair h (id I) (id P) (const a)
  value : {P Q : CAT Γ} (h : MAP P Q)
    → (insert {P = Q} a ∘ h) =₁ (productMap h (id I) ∘ insert {P = P} a)
  value h = (back h) ⁻¹ ∙ front h

  module _ {Q P R : CAT Γ} (h : MAP P R) (k : MAP Q P) where
    private
      ρ : RestrictionDiagram {E = One} {Q = Q} P R
      ρ = restriction-diagram h k (h ∘ k) (id₌ (h ∘ k))
      step-normal : {D : CAT Γ} (b : MAP R D)
        → ((b ◁ id₌ (h ∘ k)) ∙ comp-assoc k h b) =₂ comp-assoc k h b
      step-normal b = comp₌-unitˡ-One (comp-assoc k h b) ∙
        comp₌-cong (postWhisker-id₌ b (h ∘ k)) (id₌ (comp-assoc k h b))
      first-evaluation : Evaluation ρ (id R) h (h ∘ k) (h ∘ k)
      first-evaluation = evaluation (comp-unitˡ (h ∘ k)) (comp-unitˡ h)
        (id₌ (h ∘ k)) (id₌ (h ∘ k))
      second-evaluation : Evaluation ρ (const {P = R} a) (const {P = P} a)
        (const {P = Q} a) (const {P = Q} a)
      second-evaluation = evaluation (const-pre a (h ∘ k)) (const-pre a h)
        (const-pre a k) (id₌ (const {P = Q} a))
      first-compatible =
        ((comp₌-unitˡ-One (comp-unitˡ h ▷ k) ∙
            comp₌-unitˡ-One (id₌ (h ∘ k) ∙ (comp-unitˡ h ▷ k))) ⁻¹) ∙
        (left-unitor-comp k h ∙ comp₌-cong (id₌ (comp-unitˡ (h ∘ k))) (step-normal (id R)))
      second-compatible =
        ((comp₌-unitˡ-One (const-pre a k ∙ (const-pre a h ▷ k))) ⁻¹) ∙
        (const-pre-iterated a h k ∙
          comp₌-cong (id₌ (const-pre a (h ∘ k))) (step-normal (const {P = R} a)))
      paired = pair-compatible-One ρ first-evaluation second-evaluation
        first-compatible second-compatible
      tail = pair⁼ (id₌ (h ∘ k)) (const-pre a k) ∙
        (pair-pre h (const {P = P} a) k ∙ (front h ▷ k))
    front-composition :
      (front (h ∘ k) ∙ comp-assoc k h (insert {P = R} a)) =₂ tail
    front-composition = comp₌-unitˡ-One tail ∙
      (comp₌-cong (pair⁼-id-One (h ∘ k) (const {P = Q} a)) (id₌ tail) ∙
        (comp₌-cong (id₌ (pair⁼ (id₌ (h ∘ k)) (id₌ (const {P = Q} a))))
          (comp₌-assoc (pair⁼ (id₌ (h ∘ k)) (const-pre a k))
            (pair-pre h (const {P = P} a) k) (front h ▷ k)) ∙
        (paired ∙ comp₌-cong (id₌ (front (h ∘ k))) ((step-normal (insert {P = R} a)) ⁻¹))))

  module _ {Q P : CAT Γ} (h : MAP Q P) where
    private
      x = const {P = Q} a
      raw = productMap-pair h (id I) (id Q) x
      unit = pair⁼ (comp-unitʳ h) (id₌ x)
      close = pair⁼ (id₌ (h ∘ id Q)) (comp-unitˡ x)
      close-normal : (unit ∙ close) =₂ pair⁼ (comp-unitʳ h) (comp-unitˡ x)
      close-normal = pair⁼-cong (comp₌-unitʳ-One (comp-unitʳ h))
        (comp₌-unitˡ-One (comp-unitˡ x)) ∙
        ((pair⁼-comp (comp-unitʳ h) (id₌ (h ∘ id Q)) (id₌ x) (comp-unitˡ x)) ⁻¹)
    back-factorization : back h =₂
      (pair⁼ (comp-unitʳ h) (id₌ x) ∙ PairInput.at-pair h (id Q) x)
    back-factorization = (comp₌-cong close-normal (id₌ raw) ∙
      ((comp₌-assoc unit close raw) ⁻¹)) ⁻¹

  module _ {Q P R : CAT Γ} (h : MAP P R) (k : MAP Q P) where
    private
      x = const {P = Q} a
      H = productMap h (id I)
      K = productMap k (id I)
      i = insert {P = Q} a
      A = comp-assoc i K H
      κ-first = productMap-first-comp {C = I} h k
      U = pair⁼ (comp-unitʳ k) (id₌ x)
      Bk = PairInput.at-pair k (id Q) x
      Bpre = PairInput.at-pair h (k ∘ id Q) x
      Bafter = PairInput.at-pair h k x
      Bhk = PairInput.at-pair (h ∘ k) (id Q) x
      action = pair⁼ (h ◁ comp-unitʳ k) (id₌ x)
      vertex = pair⁼ (comp-assoc (id Q) k h) (id₌ x)
      output-unit = pair⁼ (comp-unitʳ (h ∘ k)) (id₌ x)
      t = (H ◁ Bk) ∙ A

      input-square : SquareCell₌ (H ◁ U) action Bpre Bafter
      input-square = paste-square₌
        (productMap-pair-inner-One h (id I) (comp-unitʳ k) (id₌ x))
        (pair⁼-square (unconst-sides₌ (identity-square₌ (h ◁ comp-unitʳ k)))
          (postWhisker-id-One (id₌ x)))

      point-normal : (action ∙ vertex) =₂ output-unit
      point-normal = pair⁼-cong ((right-unitor-comp k h) ⁻¹)
        (comp₌-unitˡ-One (id₌ x)) ∙
        ((pair⁼-comp (h ◁ comp-unitʳ k) (comp-assoc (id Q) k h) (id₌ x) (id₌ x)) ⁻¹)

      post-back : (H ◁ back k) =₂ ((H ◁ U) ∙ (H ◁ Bk))
      post-back = postWhisker-comp₌ H U Bk ∙ (postWhisker H ◁ back-factorization k)

      move-input : (Bafter ∙ ((H ◁ U) ∙ t)) =₂ (action ∙ (Bpre ∙ t))
      move-input = comp₌-assoc action Bpre t ∙
        (comp₌-cong input-square (id₌ t) ∙ ((comp₌-assoc Bafter (H ◁ U) t) ⁻¹))

      right-normal : (Bafter ∙ ((H ◁ back k) ∙ A)) =₂ (back (h ∘ k) ∙ (κ-first ▷ i))
      right-normal = comp₌-cong ((back-factorization (h ∘ k)) ⁻¹) (id₌ (κ-first ▷ i)) ∙
        ((comp₌-assoc output-unit Bhk (κ-first ▷ i)) ⁻¹ ∙
        (comp₌-cong point-normal (id₌ (Bhk ∙ (κ-first ▷ i))) ∙
        ((comp₌-assoc action vertex (Bhk ∙ (κ-first ▷ i))) ⁻¹ ∙
        (comp₌-cong (id₌ action) (at-pair-input-change h k (id Q) x) ∙
        (move-input ∙
        (comp₌-cong (id₌ Bafter) (comp₌-assoc (H ◁ U) (H ◁ Bk) A) ∙
          comp₌-cong (id₌ Bafter) (comp₌-cong post-back (id₌ A))))))))

    back-composition : (back (h ∘ k) ∙ (κ-first ▷ i)) =₂
      (PairInput.at-pair h k x ∙ ((H ◁ back k) ∙ A))
    back-composition = right-normal ⁻¹

private
  module ParameterRestriction {Γ : Context} {I Q P R : CAT Γ}
    (a : MAP One I) (h : MAP P R) (k : MAP Q P) where
    private
      module N = ParameterInsertion a
      H = productMap h (id I)
      x = const {P = P} a
      y = const {P = Q} a
      constant-step = const-pre a k
      l = comp-unitˡ k
      r = comp-unitʳ h
      B₀ = PairInput.at-pair h (id P) x
      B₁ = PairInput.at-pair h (id P ∘ k) (x ∘ k)
      B₂ = PairInput.at-pair h k y
      j = pair-pre (id P) x k
      q₀ = pair-pre (h ∘ id P) x k
      q₁ = pair-pre h x k
      U = pair⁼ r (id₌ x)
      V = pair⁼ l constant-step
      A = comp-assoc k (insert {P = P} a) H
      δ = pair⁼ (id₌ (h ∘ k)) constant-step
      D = δ ∙ q₁
      v = pair⁼ (h ◁ l) constant-step
      w = pair⁼ (comp-assoc k (id P) h) (id₌ (x ∘ k))
      z = pair⁼ (r ▷ k) constant-step
      rest = q₀ ∙ (B₀ ▷ k)
      input-square : (B₂ ∙ (H ◁ V)) =₂ (v ∙ B₁)
      input-square = paste-square₌
        (productMap-pair-inner-One h (id I) l constant-step)
        (pair⁼-square (unconst-sides₌ (identity-square₌ (h ◁ l)))
          (postWhisker-id-One constant-step))
      triangle-normal : (v ∙ w) =₂ z
      triangle-normal = pair⁼-cong ((triangle-whiskered k h) ⁻¹)
          (comp₌-unitʳ-One constant-step) ∙
        ((pair⁼-comp (h ◁ l) (comp-assoc k (id P) h) constant-step (id₌ (x ∘ k))) ⁻¹)
      direct-normal : (B₂ ∙ ((H ◁ N.front k) ∙ A)) =₂ (z ∙ rest)
      direct-normal = comp₌-cong triangle-normal (id₌ rest) ∙
        ((comp₌-assoc v w rest) ⁻¹ ∙
        (comp₌-cong (id₌ v) (at-pair-restrict h (id P) x k) ∙
        (comp₌-assoc v B₁ ((H ◁ j) ∙ A) ∙
        (comp₌-cong input-square (id₌ ((H ◁ j) ∙ A)) ∙
        ((comp₌-assoc B₂ (H ◁ V) ((H ◁ j) ∙ A)) ⁻¹ ∙
        (comp₌-cong (id₌ B₂) (comp₌-assoc (H ◁ V) (H ◁ j) A) ∙
          comp₌-cong (id₌ B₂) (comp₌-cong (postWhisker-comp₌ H V j) (id₌ A))))))))
      restricted-input : (q₁ ∙ (U ▷ k)) =₂
        (pair⁼ (r ▷ k) (id₌ (x ∘ k)) ∙ q₀)
      restricted-input = comp₌-cong
          (pair⁼-cong (id₌ (r ▷ k)) (preWhisker-id₌ x k)) (id₌ q₀) ∙
        pair-pre-natural-inputs-One r (id₌ x) k
      finish-normal : (δ ∙ pair⁼ (r ▷ k) (id₌ (x ∘ k))) =₂ z
      finish-normal = pair⁼-cong (comp₌-unitˡ-One (r ▷ k)) (comp₌-unitʳ-One constant-step) ∙
        ((pair⁼-comp (id₌ (h ∘ k)) (r ▷ k) constant-step (id₌ (x ∘ k))) ⁻¹)
      restricted-normal : (D ∙ (N.back h ▷ k)) =₂ (z ∙ rest)
      restricted-normal = comp₌-cong finish-normal (id₌ rest) ∙
        ((comp₌-assoc δ (pair⁼ (r ▷ k) (id₌ (x ∘ k))) rest) ⁻¹ ∙
        (comp₌-cong (id₌ δ)
          (comp₌-assoc (pair⁼ (r ▷ k) (id₌ (x ∘ k))) q₀ (B₀ ▷ k)) ∙
        (comp₌-cong (id₌ δ) (comp₌-cong restricted-input (id₌ (B₀ ▷ k))) ∙
        (comp₌-cong (id₌ δ) ((comp₌-assoc q₁ (U ▷ k) (B₀ ▷ k)) ⁻¹) ∙
        (comp₌-assoc δ q₁ ((U ▷ k) ∙ (B₀ ▷ k)) ∙
          comp₌-cong (id₌ D)
            (preWhisker-comp₌ U B₀ k ∙ (preWhisker k ◁ N.back-factorization h)))))))
    back-front-restriction :
      ((pair⁼ (id₌ (h ∘ k)) (const-pre a k) ∙ pair-pre h x k) ∙ (N.back h ▷ k)) =₂
      (PairInput.at-pair h k y ∙ ((H ◁ N.front k) ∙ A))
    back-front-restriction = direct-normal ⁻¹ ∙ restricted-normal

private
  module ParameterComposition {Γ : Context} {I Q P R : CAT Γ}
    (a : MAP One I) (h : MAP P R) (k : MAP Q P) where
    private
      module N = ParameterInsertion a
      module M = ParameterRestriction a h k
      H = productMap h (id I)
      K = productMap k (id I)
      i = insert {P = Q} a
      A = comp-assoc i K H
      B = comp-assoc k (insert {P = P} a) H
      compositor-at-point = productMap-first-comp {C = I} h k ▷ i
      b = N.back (h ∘ k)
      n = N.value h ▷ k
      W = B ∙ n
      Z = (H ◁ N.value k) ∙ W
      pair-step = PairInput.at-pair h k (const {P = Q} a)
      δ = pair⁼ (id₌ (h ∘ k)) (const-pre a k)
      q = pair-pre h (const {P = P} a) k
      D = δ ∙ q
      tail = δ ∙ (q ∙ (N.front h ▷ k))
      iteration = compositor-at-point ∙ (A ⁻¹ ∙ Z)
      direct = N.value (h ∘ k) ∙ comp-assoc k h (insert {P = R} a)
      back-image : (b ∙ iteration) =₂ (pair-step ∙ ((H ◁ N.back k) ∙ Z))
      back-image = comp₌-cong (id₌ pair-step)
          (comp₌-cong (id₌ (H ◁ N.back k)) (comp-inv-left A Z)) ∙
        (comp₌-cong (id₌ pair-step)
          (comp₌-assoc (H ◁ N.back k) A (A ⁻¹ ∙ Z)) ∙
        (comp₌-assoc pair-step ((H ◁ N.back k) ∙ A) (A ⁻¹ ∙ Z) ∙
        (comp₌-cong (N.back-composition h k) (id₌ (A ⁻¹ ∙ Z)) ∙
          (comp₌-assoc b compositor-at-point (A ⁻¹ ∙ Z)) ⁻¹)))
      post-cancel : ((H ◁ N.back k) ∙ (H ◁ N.value k)) =₂ (H ◁ N.front k)
      post-cancel = (postWhisker H ◁ comp-inv-left (N.back k) (N.front k)) ∙
        (postWhisker-comp₌ H (N.back k) (N.value k)) ⁻¹
      pre-cancel : ((N.back h ▷ k) ∙ n) =₂ (N.front h ▷ k)
      pre-cancel = (preWhisker k ◁ comp-inv-left (N.back h) (N.front h)) ∙
        (preWhisker-comp₌ (N.back h) (N.value h) k) ⁻¹
      post-image : (pair-step ∙ ((H ◁ N.back k) ∙ Z)) =₂
        (pair-step ∙ ((H ◁ N.front k) ∙ W))
      post-image = comp₌-cong (id₌ pair-step)
        (comp₌-cong post-cancel (id₌ W) ∙
          (comp₌-assoc (H ◁ N.back k) (H ◁ N.value k) W) ⁻¹)
      restriction-image : (pair-step ∙ ((H ◁ N.front k) ∙ W)) =₂ tail
      restriction-image = comp₌-assoc δ q (N.front h ▷ k) ∙
        (comp₌-cong (id₌ D) pre-cancel ∙
        (comp₌-assoc D (N.back h ▷ k) n ∙
        (comp₌-cong (M.back-front-restriction ⁻¹) (id₌ n) ∙
        ((comp₌-assoc pair-step ((H ◁ N.front k) ∙ B) n) ⁻¹ ∙
          comp₌-cong (id₌ pair-step) ((comp₌-assoc (H ◁ N.front k) B n) ⁻¹)))))
      iteration-image : (b ∙ iteration) =₂ tail
      iteration-image = restriction-image ∙ (post-image ∙ back-image)
      direct-image : (b ∙ direct) =₂ tail
      direct-image = N.front-composition h k ∙
        (comp₌-cong (comp-inv-left b (N.front (h ∘ k)))
          (id₌ (comp-assoc k h (insert {P = R} a))) ∙
          (comp₌-assoc b (N.value (h ∘ k)) (comp-assoc k h (insert {P = R} a))) ⁻¹)
    composition :
      (N.value (h ∘ k) ∙ comp-assoc k h (insert {P = R} a)) =₂
      ((productMap-first-comp {C = I} h k ▷ insert {P = Q} a) ∙
        ((comp-assoc (insert {P = Q} a) (productMap k (id I)) (productMap h (id I))) ⁻¹ ∙
          ((productMap h (id I) ◁ N.value k) ∙
            (comp-assoc k (insert {P = P} a) (productMap h (id I)) ∙ (N.value h ▷ k)))))
    composition = cancel-left b (iteration-image ⁻¹ ∙ direct-image)

module UncurryParameter {Γ : Context} {I C P Q : CAT Γ}
  (a : MAP One I) (h : MAP P (Fun I C)) (k : MAP Q P) where
  private
    module N = ParameterInsertion a
    module NC = ParameterComposition a h k
    e = funEval {C = I} {D = C}
    H = productMap h (id I)
    K = productMap k (id I)
    J = productMap (h ∘ k) (id I)
    i = insert {P = Q} a
    j = insert {P = P} a
    t = insert {P = Fun I C} a
    κh = productMap-first-comp {C = I} h k
    A = comp-assoc i K H
    B = comp-assoc k j H
    finish = (κh ▷ i) ∙ A ⁻¹
    second = post-triangle H j k (N.value k)
    structural : (N.value (h ∘ k) ∙ comp-assoc k h t) =₂
      (finish ∙ (second ∙ (N.value h ▷ k)))
    structural = (comp₌-assoc (κh ▷ i) (A ⁻¹) (second ∙ (N.value h ▷ k))) ⁻¹ ∙
      (comp₌-cong (id₌ (κh ▷ i))
        (comp₌-cong (id₌ (A ⁻¹))
          ((comp₌-assoc (H ◁ N.value k) B (N.value h ▷ k)) ⁻¹)) ∙ NC.composition)
    T = post-triangle e t h (N.value h)
    T₂ = post-triangle e t (h ∘ k) (N.value (h ∘ k))
    R₁ = comp-assoc j H e
    R₂ = comp-assoc i J e
    μ = R₁ ⁻¹ ∙ T
    μ₂ = R₂ ⁻¹ ∙ T₂
    C₀ = comp-assoc k h (e ∘ t)
    U = post-triangle e (H ∘ j) k second
    V = post-triangle (e ∘ H) j k (N.value k)
    W = comp-assoc (K ∘ i) H e
    E = comp-assoc i K (e ∘ H)
    L = comp-assoc i (H ∘ K) e
    G = comp-assoc K H e
    triangle = evaluation-restriction-triangle e h k
    out = triangle ▷ i
    target = out ∙ (E ⁻¹ ∙ (V ∙ (μ ▷ k)))
    post-law : (T₂ ∙ C₀) =₂ ((e ◁ finish) ∙ (U ∙ (T ▷ k)))
    post-law = post-iterated-restriction e t h k (N.value h) second
      (N.value (h ∘ k)) finish structural
    first-frame : (T ▷ k) =₂ ((R₁ ▷ k) ∙ (μ ▷ k))
    first-frame = ((preWhisker k ◁ comp-inv-left R₁ T) ∙
      (preWhisker-comp₌ R₁ μ k) ⁻¹) ⁻¹
    second-frame : (U ∙ (R₁ ▷ k)) =₂ (W ∙ V)
    second-frame = (post-triangle-comp e H j k (N.value k)) ⁻¹ ∙
      comp₌-assoc (e ◁ second) (comp-assoc k (H ∘ j) e) (R₁ ▷ k)
    middle : ((e ◁ finish) ∙ (U ∙ (T ▷ k))) =₂
      (((e ◁ finish) ∙ W) ∙ (V ∙ (μ ▷ k)))
    middle = (comp₌-assoc (e ◁ finish) W (V ∙ (μ ▷ k))) ⁻¹ ∙
      (comp₌-cong (id₌ (e ◁ finish)) (comp₌-assoc W V (μ ▷ k)) ∙
      (comp₌-cong (id₌ (e ◁ finish)) (comp₌-cong second-frame (id₌ (μ ▷ k))) ∙
      (comp₌-cong (id₌ (e ◁ finish)) ((comp₌-assoc U (R₁ ▷ k) (μ ▷ k)) ⁻¹) ∙
        comp₌-cong (id₌ (e ◁ finish)) (comp₌-cong (id₌ U) first-frame))))
    corner : (L ∙ ((G ▷ i) ∙ E ⁻¹)) =₂ ((e ◁ A) ⁻¹ ∙ W)
    corner = cancel-left (e ◁ A)
      ((comp-inv-left (e ◁ A) W) ⁻¹ ∙
      (comp-inv-right W E ∙
      (comp₌-cong ((pentagon-whiskered-right i K H e) ⁻¹) (id₌ (E ⁻¹)) ∙
      ((comp₌-assoc (e ◁ A) (L ∙ (G ▷ i)) (E ⁻¹)) ⁻¹ ∙
        comp₌-cong (id₌ (e ◁ A)) ((comp₌-assoc L (G ▷ i) (E ⁻¹)) ⁻¹)))))
    output-frame : (R₂ ∙ (out ∙ E ⁻¹)) =₂ ((e ◁ finish) ∙ W)
    output-frame = comp₌-cong ((postWhisker-comp₌ e (κh ▷ i) (A ⁻¹)) ⁻¹) (id₌ W) ∙
      ((comp₌-assoc (e ◁ (κh ▷ i)) (e ◁ A ⁻¹) W) ⁻¹ ∙
      (comp₌-cong (id₌ (e ◁ (κh ▷ i)))
        (comp₌-cong ((postWhisker-inverse e A) ⁻¹) (id₌ W)) ∙
      (comp₌-cong (id₌ (e ◁ (κh ▷ i))) corner ∙
      (comp₌-assoc (e ◁ (κh ▷ i)) L ((G ▷ i) ∙ E ⁻¹) ∙
      (comp₌-cong (whisker-mixed-One κh i e) (id₌ ((G ▷ i) ∙ E ⁻¹)) ∙
      ((comp₌-assoc R₂ ((e ◁ κh) ▷ i) ((G ▷ i) ∙ E ⁻¹)) ⁻¹ ∙
      (comp₌-cong (id₌ R₂) (comp₌-assoc ((e ◁ κh) ▷ i) (G ▷ i) (E ⁻¹)) ∙
        comp₌-cong (id₌ R₂) (comp₌-cong (preWhisker-comp₌ (e ◁ κh) G i) (id₌ (E ⁻¹))))))))))
    finish-image : (((e ◁ finish) ∙ W) ∙ (V ∙ (μ ▷ k))) =₂ (R₂ ∙ target)
    finish-image = comp₌-cong (id₌ R₂) (comp₌-assoc out (E ⁻¹) (V ∙ (μ ▷ k))) ∙
      (comp₌-assoc R₂ (out ∙ E ⁻¹) (V ∙ (μ ▷ k)) ∙
        comp₌-cong (output-frame ⁻¹) (id₌ (V ∙ (μ ▷ k))))
    body-law : (μ₂ ∙ C₀) =₂ target
    body-law = cancel-left R₂
      (finish-image ∙ (middle ∙ (post-law ∙
        (comp₌-cong (comp-inv-left R₂ T₂) (id₌ C₀) ∙
          (comp₌-assoc R₂ μ₂ C₀) ⁻¹))))
    restriction-inverse : (evaluate-restrict e h k) ⁻¹ =₂ triangle
    restriction-inverse = inverse-inverse triangle ∙
      (inv₌ ◁ evaluate-restrict-inverse-triangle e h k)
    target-image :
      (((evaluate-restrict e h k) ⁻¹ ▷ i) ∙
        (E ⁻¹ ∙ (V ∙ (AtPoint.uncurry-image a h ▷ k)))) =₂ target
    target-image = comp₌-cong (preWhisker i ◁ restriction-inverse)
      (comp₌-cong (id₌ (E ⁻¹))
        (comp₌-cong (id₌ V) (preWhisker k ◁ UncurryRoute.factorization a h)))
  composition :
    (AtPoint.uncurry-image a (h ∘ k) ∙ comp-assoc k h (evAt a)) =₂
    (((evaluate-restrict e h k) ⁻¹ ▷ insert {P = Q} a) ∙
      ((comp-assoc (insert {P = Q} a) (productMap k (id I)) (funUncurry h)) ⁻¹ ∙
        ((funUncurry h ◁ N.value k) ∙
          (comp-assoc k (insert {P = P} a) (funUncurry h) ∙ (AtPoint.uncurry-image a h ▷ k)))))
  composition =
    comp₌-cong (id₌ ((evaluate-restrict e h k) ⁻¹ ▷ i))
      (comp₌-cong (id₌ (E ⁻¹))
        (comp₌-assoc (funUncurry h ◁ N.value k)
          (comp-assoc k j (funUncurry h)) (AtPoint.uncurry-image a h ▷ k))) ∙
    (target-image ⁻¹ ∙ (body-law ∙
      comp₌-cong (UncurryRoute.factorization a (h ∘ k)) (id₌ C₀)))
```
