{-# OPTIONS --safe --without-K #-}
module SCT.WebEdition where

import SCT.VolumeI.Chapter01.Section01.Everything
import SCT.VolumeI.Chapter01.Section02.Everything
import SCT.VolumeI.Chapter01.Section03.Everything
import SCT.VolumeI.Chapter01.Section04.Everything
import SCT.VolumeI.Chapter01.Section05.Everything
import SCT.VolumeI.Chapter01.Section06.Everything
import SCT.VolumeI.Chapter01.Section07.Everything
import SCT.VolumeI.Chapter01.Section08.Everything
import SCT.VolumeI.Chapter02.Section01.Everything
import SCT.VolumeI.Chapter02.Section02.Everything
import SCT.VolumeI.Chapter02.Section03.Everything
import SCT.VolumeI.Chapter02.Section04.Everything
import SCT.VolumeI.Chapter02.Section05.Everything
import SCT.VolumeI.Chapter02.Section06.Everything
-- Chapter 3: reviewed manuscript targets and all their dependencies.
-- Unfinished proof investigations are retained in Chapter03.Everything,
-- outside this publication aggregate.
import SCT.VolumeI.Chapter03.RelativeCategories.BaseChange.BaseChange
import SCT.VolumeI.Chapter03.RelativeCategories.Functors
import SCT.VolumeI.Chapter03.Section01.ClosureCalculus.CompositionClosure
import SCT.VolumeI.Chapter03.Section01.ClosureCalculus.IsomorphismClosure
import SCT.VolumeI.Chapter03.Section01.GeneratedMorphisms
import SCT.VolumeI.Chapter03.Section01.IsomorphismCollections
import SCT.VolumeI.Chapter03.Section01.Lifting.PresentationConsequences
import SCT.VolumeI.Chapter03.Section01.MappingCalculus.MappingAction
import SCT.VolumeI.Chapter03.Section01.MorphismCollections
import SCT.VolumeI.Chapter03.Section01.RecoveringSubcategories
import SCT.VolumeI.Chapter03.Section01.Subcategories
import SCT.VolumeI.Chapter03.Section01.SubcategoryAxiom
import SCT.VolumeI.Chapter03.Section01.SubcategoryClosure
import SCT.VolumeI.Chapter03.Section01.SubcategoryFunctoriality
import SCT.VolumeI.Chapter03.Section02.FullSubcategories
import SCT.VolumeI.Chapter03.Section02.FullSubcategoryCharacterization
import SCT.VolumeI.Chapter03.Section02.FullSubcategoryProducts
import SCT.VolumeI.Chapter03.Section02.FullSubcategoryPullbacks
import SCT.VolumeI.Chapter03.Section02.ObjectCollections
import SCT.VolumeI.Chapter03.Section02.SpannedCore
import SCT.VolumeI.Chapter03.Section02.SpannedSubcategories
import SCT.VolumeI.Chapter03.Section03.InvertingFunctors
import SCT.VolumeI.Chapter03.Section03.LocalizationCriterion
import SCT.VolumeI.Chapter03.Section03.LocalizationFunctoriality
import SCT.VolumeI.Chapter03.Section03.LocalizationGroupoids
import SCT.VolumeI.Chapter03.Section03.LocalizationPushouts
import SCT.VolumeI.Chapter03.Section03.LocalizationUniqueness
import SCT.VolumeI.Chapter03.Section03.Localizations
import SCT.VolumeI.Chapter03.Section03.MappingCalculus.InvertingGroupoids
import SCT.VolumeI.Chapter03.Section03.MappingCalculus.InvertingRestriction
import SCT.VolumeI.Chapter03.Section03.MappingCalculus.LocalizationRestriction
import SCT.VolumeI.Chapter03.Section03.MappingCalculus.PreservingIsomorphismMaps
import SCT.VolumeI.Chapter03.Section03.MappingCalculus.PreservingIsomorphisms
import SCT.VolumeI.Chapter03.Section04.FundamentalGroupoids
import SCT.VolumeI.Chapter03.Section04.GeometricRealization
import SCT.VolumeI.Chapter03.Section04.GeometricRealizationCriteria
import SCT.VolumeI.Chapter03.Section04.ObjectwiseNaturalIsomorphisms
import SCT.VolumeI.Chapter03.Section04.RealizationOfGroupoids
import SCT.VolumeI.Chapter03.Section04.RealizationPushouts
import SCT.VolumeI.Chapter03.Section05.BaseChange.BeckChevalley
import SCT.VolumeI.Chapter03.Section05.ConstantFamilyEvaluation
import SCT.VolumeI.Chapter03.Section05.ConstantFamilyUniversalProperty
import SCT.VolumeI.Chapter03.Section05.DependentProductAction
import SCT.VolumeI.Chapter03.Section05.DependentProductActionLaws
import SCT.VolumeI.Chapter03.Section05.DependentProductEmbeddings
import SCT.VolumeI.Chapter03.Section05.DependentProductUniqueness
import SCT.VolumeI.Chapter03.Section05.DependentProducts
import SCT.VolumeI.Chapter03.Section05.ExponentiableFunctors
import SCT.VolumeI.Chapter03.Section05.InternalFunctorCalculus.ConstantFamilyInternalFunctors
import SCT.VolumeI.Chapter03.Section05.InternalFunctorCalculus.InternalEvaluation
import SCT.VolumeI.Chapter03.Section05.InternalFunctorCalculus.RelativeInternalFunctors
import SCT.VolumeI.Chapter03.Section05.InternalFunctorFibers
import SCT.VolumeI.Chapter03.Section05.InternalFunctorSections
import SCT.VolumeI.Chapter03.Section05.InternalFunctorsBaseChange
import SCT.VolumeI.Chapter03.Section05.TerminalExponentiability
import SCT.VolumeI.Chapter03.Section06.CoreOfJoin
import SCT.VolumeI.Chapter03.Section06.JoinAxiom
import SCT.VolumeI.Chapter03.Section06.JoinMappingOut
import SCT.VolumeI.Chapter03.Section06.JoinOfPoints
import SCT.VolumeI.Chapter03.Section06.JoinPushoutAction
import SCT.VolumeI.Chapter03.Section06.JoinUnits
import SCT.VolumeI.Chapter03.Section06.Joins
import SCT.VolumeI.Chapter03.Section06.TriangleJoins
import SCT.VolumeI.Chapter03.Section07.FunctorsIntoSlices
import SCT.VolumeI.Chapter03.Section07.RelativeSlices

import SCT.VolumeI.Chapter03.Section06.JoinMappingIn

import SCT.VolumeI.Chapter03.Section06.JoinFunctoriality

-- Completed supporting calculations for morphisms over a base.
import SCT.VolumeI.Chapter03.RelativeCategories.DecodedMorphisms
import SCT.VolumeI.Chapter03.RelativeCategories.MorphismPostcomposition
import SCT.VolumeI.Chapter03.RelativeCategories.MorphismRetargeting
import SCT.VolumeI.Chapter03.RelativeCategories.MorphismTriangles
import SCT.VolumeI.Chapter03.RelativeCategories.MorphismWhiskering
import SCT.VolumeI.Chapter03.RelativeCategories.NamedMorphisms
import SCT.VolumeI.Chapter03.RelativeCategories.PullbackMorphisms

-- Completed Chapter 1-2 support not yet in the section aggregates.
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.CospanPullbacksLeft
import SCT.VolumeI.Chapter01.Section06.Cospans.SquareSubstitution
import SCT.VolumeI.Chapter01.Section06.Pasting.BaseChangeConeRecovery
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ConstantSourceNaturality
import SCT.VolumeI.Chapter02.Section02.MorphismCalculus.ConstantSourceRestriction
import SCT.VolumeI.Chapter01.Section06.ConeCalculus.PullbackReindexing
import SCT.VolumeI.Chapter02.Section01.EvaluationCalculus.ConstantDiagramEvaluation
