# Roadmap: Flatness and homological dimensions of noncommutative rings

**Summary.** Mathlib has flat modules, `Tor` and the character-module test for flatness only over
commutative rings. Tau Ceti has the tensor product `M ⊗_A N` of a right and a left module over an
arbitrary ring (`TauCeti.BalancedTensorProduct`), finitely presented functors on a preadditive
category (`mod C`), the global dimension of left modules, projective covers and semiperfect rings.
This roadmap develops the homological algebra of flatness over a preadditive category `C`; a ring
`A` is the one-object case `SingleObj A`. Layer 0 lays the foundations: the abelian category
`Mod C` of additive functors; the identification of `A`-modules with modules over `SingleObj A`;
the tensor product `F ⊗_C G` as a coend, linear over a commutative ring `R`, with its adjunctions,
right exactness, projective factors and swap; duals `Hom_R(-, E)`; and the native ring API of
`M ⊗_A N`. On these the roadmap builds `Tor` with its balance; flat modules, Lambek's
character-module criterion and the projectivity of finitely presented flat modules; flat dimension
and weak global dimension, its left-right symmetry, and Auslander's theorem that a left Noetherian
ring has equal left global and weak global dimension; projective covers over semiperfect rings and
the characterization of semiperfect rings by projective covers; and left perfect rings. The summit
is **Bass's Theorem P**: for a ring `A` with Jacobson radical `J`, the following are equivalent:
`A ⧸ J` is semisimple and `J` is left T-nilpotent; every left module has a projective cover; every
flat left module is projective; the principal *right* ideals satisfy the descending chain
condition; every left module has equal flat and projective dimension. Theorem P extends to perfect
categories, functor categories `Mod C` in which every object has a projective cover ([Harada]).
Layers 1–4 are stated for rings for now and are to be converted to the category-primary design of
Layer 0.

## Scope and ownership

This roadmap owns:

- modules over a preadditive category: `Mod C` as a full subcategory of additive functors, its
  abelian structure, representable projectives, enough projectives and derived `R`-linear
  structure, and the inclusion of `mod C`; the comparison of `A`-modules with modules over
  `SingleObj A`; the tensor product `F ⊗_C G` over an `R`-linear category with its API,
  adjunctions, right exactness, Yoneda isomorphisms, independence of `R` and change of base;
  tensoring with projectives; the swap `F ⊗_C G ≅ G ⊗_{Cᵒᵖ} F`; the ring API of `M ⊗_A N` and
  its comparison with the categorical tensor product and with Mathlib's tensor product over a
  commutative ring; and duals with respect to an `R`-module `E` (Layer 0);
- `Tor` over an arbitrary ring, derived in either variable, its long exact sequences, its balance,
  the comparison with Mathlib's `CategoryTheory.Tor` over a commutative ring, and `Tor₁` of two
  cyclic modules (Layer 1);
- flat modules over an arbitrary ring: the definition, the tensor, ideal, character-module and
  `Tor` tests, closure properties, flat quotients, Bass's flat module, and projectivity of finitely
  presented flat modules (Layer 2);
- flat dimension, weak global dimension, its left-right symmetry and its bounds by the global
  dimensions, and Auslander's theorem for left Noetherian rings (Layer 3);
- T-nilpotent sets; projective covers of finitely generated modules over semiperfect rings, the
  characterization of semiperfect rings by projective covers, and finite minimal projective
  presentations over semiperfect rings; left perfect rings, projective covers over them, Bass's
  Theorem P, and the global dimension of perfect rings (Layer 4).

The boundaries are as follows.

- An `R`-linear category is Mathlib's `Linear R C`, and modules are ordinary functors with
  additivity as a property. **Future work, not followed here:** `R`-linear categories as categories
  enriched over `ModuleCat R`, and a bridge from `Mod C` to degree-zero DG modules. Tau Ceti's DG
  categories use Mathlib's `EnrichedCategory` over `CochainComplex (ModuleCat R) ℤ`, with a
  hand-built functor category (`TauCeti/CategoryTheory/DG/Functor/Category.lean`); Mathlib has no
  general category of enriched functors.
- Finitely presented functors `mod C` are Tau Ceti's (`TauCeti.isFinitelyPresentedFunctor`, in
  `TauCeti/CategoryTheory/FinitelyPresentedFunctor/`). They live in the same ambient category
  `Cᵒᵖ ⥤ AddCommGrpCat.{v}` and are additive, so they need no migration; this roadmap states only
  the inclusion `mod C ⊆ Mod C` (0.1).
- Flatness over a commutative ring is Mathlib's `Module.Flat`. Here only its agreement with
  `TauCeti.Module.BalancedFlat` is proved (2.1). Mathlib's `Mathlib/RingTheory/Flat/Basic.lean`
  lists the generalization of `Module.Flat` to noncommutative rings as a TODO; if Mathlib makes
  it, `BalancedFlat` is replaced by `Module.Flat`.
- [Operator K-theory](../OperatorKTheory/README.md), §8.2, owns the computations of `Ext` and
  `Tor` over `ℤ` (free presentations, cyclic groups, universal coefficients). The comparison of
  1.4 covers every commutative ring; no other `ℤ`-specific computation is done here.
- [Derived and module algebra](../DerivedModuleAlgebra/README.md) owns the derived tensor
  product and `Tor` amplitude over commutative rings. This roadmap uses no derived categories.
- [Krull-Schmidt categories and Auslander-Reiten theory of Artin
  algebras](../RepresentationTheory/ArtinAlgebras/README.md), §7.2, owns the comparison of left
  and right global dimension through character modules and the formula for semiprimary rings.
  Layers 3 and 4 give the routes through weak global dimension and perfect rings and do not
  restate those theorems.
- Semiperfect rings are Tau Ceti's `TauCeti.IsSemiperfectRing`, with its idempotent
  characterization. This roadmap owns their projective covers and their characterization by
  projective covers (4.2). Minimal projective presentations are Tau Ceti's
  `TauCeti.IsMinimalProjectivePresentation`; this roadmap owns only their existence over a
  semiperfect ring (4.2).
- Outside this roadmap: the tensor product of additive categories and functors of several
  variables ([Mitchell, §2]); Morita theory for functor categories; Lazard's theorem (flat modules
  are direct limits of free modules) and the conditions of Theorem P on direct limits ([Bass,
  Theorem P (4), (5)]); Chase's theorem, coherent rings and products of flat modules; pure exact
  sequences; faithful flatness over noncommutative rings; the conditions on maximal submodules and
  socles ([AF, 28.4 (c), (f)]), on finitely generated submodules (Björk) and on principal left
  ideals with the ascending chain condition (Jonah); finitistic dimensions ([Bass, Part II]);
  `Tor` of bimodules and its module structure over a base ring; and Hoshino's flat-dominant
  dimension.

Suggested homes in Tau Ceti: `TauCeti/CategoryTheory/Preadditive/ModCat/` (0.1, 0.3–0.5, 0.7),
`TauCeti/CategoryTheory/Preadditive/SingleObj.lean` (0.2),
`TauCeti/LinearAlgebra/TensorProduct/Balanced/` (0.6), `TauCeti/Algebra/Homology/BalancedTor/`
(Layer 1), `TauCeti/RingTheory/Flat/Balanced/`
(Layer 2), `TauCeti/RingTheory/GlobalDimension/Weak.lean` (Layer 3),
`TauCeti/RingTheory/Jacobson/TNilpotent.lean`,
`TauCeti/Algebra/Module/ProjectiveCover/Semiperfect.lean` and
`TauCeti/RingTheory/Jacobson/LeftPerfect.lean` (Layer 4). Nothing goes under
`TauCeti/RingTheory/Perfect/`, which is the characteristic-`p` notion.

## Conventions

1. **Categories and modules.** `C : Type u` is a preadditive category, `[Category.{v} C]
   [Preadditive C]`. A right `C`-module is an additive functor `Cᵒᵖ ⥤ AddCommGrpCat.{w}`, a left
   `C`-module an additive functor `C ⥤ AddCommGrpCat.{w}`. `Mod C` (`TauCeti.ModCat C`) is the full
   subcategory of additive functors in the ordinary functor category, Mathlib's
   `Cᵒᵖ ⥤+ AddCommGrpCat.{w}`; left modules form `TauCeti.LeftModCat C = C ⥤+ AddCommGrpCat.{w}`,
   and `LeftModCat Cᵒᵖ` is `ModCat C`. This is the style of Tau Ceti's `mod C`. No enriched
   functor categories are used.
2. **Linearity.** `R` is a commutative ring and `C` is `R`-linear (Mathlib's `Linear R C`). Every
   preadditive category is `ℤ`-linear (Mathlib's `preadditiveIntLinear`), so `R = ℤ` is the
   general preadditive case. A module carries only its additive structure; its `R`-structure is
   derived: `r` acts on `F(c)` by `F(r • 𝟙 c)` (0.1). This is the analogue of `ModuleCat A`,
   which carries only the `A`-action, with the `R`-action of an `R`-algebra recovered by Tau
   Ceti's `ModuleCat.moduleOfAlgebra`. Tensor products, `Hom_R` and `Tor` take values in
   `ModuleCat R`, and the maps between them are `R`-linear.
3. **Universes.** Statements are universe polymorphic: `C : Type u`, `Category.{v} C`, values in
   `AddCommGrpCat.{w}`. Where colimits indexed by the objects of `C` are needed (coends, enough
   projectives), the hypothesis is `EssentiallySmall.{w} C`. Rings and small categories use
   `w = v`; the category `mod A` of finitely presented modules uses Mathlib's `SmallModel`; a large
   `C` (a large triangulated category, all of `Mod A`) uses `w = max u v`, with representables
   lifted by `ULift`. Finitely presented functors need no smallness.
4. **Rings.** `A` is a ring, `[Ring A]`, not assumed commutative, and an `R`-algebra
   `[Algebra R A]` where an `R`-structure is needed. Modules over a ring are left modules. A right
   `A`-module is a left `Aᵐᵒᵖ`-module, `[Module Aᵐᵒᵖ M]`, as in `TauCeti.BalancedTensorProduct`.
   A right-handed statement is the left-handed one for `Aᵐᵒᵖ`; no separate "right" predicate is
   introduced. A left `A`-module is a right `Aᵐᵒᵖ`-module through `RingEquiv.opOp A`. A right ideal
   of `A` is a `Submodule Aᵐᵒᵖ A` (Mathlib's spelling, e.g. in
   `Mathlib/Topology/Algebra/LinearTopology.lean`), so that `A ⧸ I` is a right module and `I ∩ K`
   makes sense for a left ideal `K : Ideal A`. Mathlib's `SingleObj A` composes as
   `f ≫ g = g * f` (`SingleObj.comp_as_mul`), so left `A`-modules are left modules over
   `SingleObj A` (covariant functors) and right `A`-modules are right modules over `SingleObj A`.
5. **Ring-level objects are native.** For an `R`-algebra `A`, a right module `M` and a left module
   `N` that are `R`-modules compatibly (`IsScalarTower R Aᵐᵒᵖ M`, `IsScalarTower R A N`),
   `M ⊗_A N` is `TauCeti.BalancedTensorProduct R A M N`, with its element API; the maps `f ⊗ N` and
   `M ⊗ g` are `R`-linear and the bifunctor lands in `ModuleCat R` (0.6). Ring-level objects are
   not transported from functor categories. Each ring theorem is proved directly or through the
   comparison of 0.6, whichever is simpler; the rule constrains definitions only. Every later layer
   is to end with a "rings" item restating its theorems for `ModuleCat A`, so that downstream code
   never sees functor categories.
6. `Tor_n^A(M, N)` has the right module first and takes values in `ModuleCat R`. Over a commutative
   ring it is compared directly with Mathlib's `CategoryTheory.Tor` (1.4). Layers 2 and 3 use
   `R = ℤ` for now; by the independence of `R` (0.3, 0.6) this does not change the underlying
   groups. Modules live in `ModuleCat.{v} A` and `ModuleCat.{v} Aᵐᵒᵖ` with `[Small.{v} A]`, as for
   `TauCeti.globalDimension`; the instance `Small.{v} Aᵐᵒᵖ` is part of 1.1.
7. Dimensions take values in `WithBot ℕ∞`, with `⊥` exactly for the zero module, as Mathlib's
   `CategoryTheory.projectiveDimension` and Tau Ceti's `TauCeti.globalDimension`.
   `TauCeti.globalDimension A` is the left global dimension; the right one is
   `TauCeti.globalDimension Aᵐᵒᵖ`.
8. `J = Ring.jacobson A`. A subset `S` of `A` is **left T-nilpotent** if for every sequence
   `a₀, a₁, …` in `S` some product `a₀ a₁ ⋯ aₙ₋₁` is `0` ([Bass, p. 466], [Lam-FC, (23.13)],
   [AF, p. 314]). Right T-nilpotence asks `aₙ₋₁ ⋯ a₀ = 0`; it is left T-nilpotence of the image
   of `S` in `Aᵐᵒᵖ`.
9. `A` is **left perfect** if `A ⧸ J` is a semisimple ring and `J` is left T-nilpotent. By
   Theorem P (4.5) this holds exactly when every left module has a projective cover, which is
   Bass's definition ([Bass, p. 467]), and exactly when the *right* principal ideals satisfy the
   descending chain condition. [Lam-FC] works with right modules: its "right perfect" is
   `IsLeftPerfectRing Aᵐᵒᵖ` here.
10. Mathlib's `PerfectRing R p` and Tau Ceti's `TauCeti/RingTheory/Perfect/` concern the Frobenius
   map in characteristic `p`. The notion here is always called `IsLeftPerfectRing`.
11. **Duals.** For an `R`-module `E`, the dual of a module is `F^E = Hom_R(F(-), E)` (0.7); for
   rings it is Tau Ceti's `TauCeti.MatlisDual R E M`. Hypotheses on `E` (injective, cogenerator)
   sit on the theorems, not on the definition. `CharacterModule M = M →+ ℚ ⧸ ℤ` is Mathlib's, the
   case `R = ℤ`, `E = ℚ ⧸ ℤ`. For a left module `M` it is a right module through Tau Ceti's scoped
   instance `CharacterModule.instModuleMulOpposite`; write `M⁺`.
12. Projective covers are Tau Ceti's `TauCeti.IsProjectiveCover`: a surjection from a projective
   module whose kernel is superfluous (`TauCeti.IsSuperfluous`). "`M` has a projective cover" is
   `∃ (P : Type u) (_ : AddCommGroup P) (_ : Module A P) (p : P →ₗ[A] M), IsProjectiveCover p`,
   with `P` in the universe of `A` (4.2, 4.5). For all modules over a left perfect ring, in every
   universe, it takes the form of Tau Ceti's `TauCeti.exists_isProjectiveCover` (4.4).
13. Proposed names are given in parentheses. Names that `Suggested.lean` states carry the prefix
   `TauCeti.` in the README and live in `TauCetiRoadmap.NoncommutativeFlatness` there.

**Sources and locators.** Citations use the keys of the section "Sources and locators". Pages are
printed pages. A locator that has not been read in the source says so.

## Exact supplier contracts

The baseline is Mathlib `e8ba86fa9744dd8d90f48c1752bc735f61a4ca81` and Tau Ceti
`71ce0a33087999414b8424bf26c3a1d9fbbce54e`. `Suggested.lean` imports
`TauCeti.Algebra.Module.CharacterModule.MulOpposite`,
`TauCeti.CategoryTheory.FinitelyPresentedFunctor.Basic` and
`TauCeti.RingTheory.MatlisDuality.Basic`, which need Tau Ceti at that commit or later.

### From Mathlib

- Functor categories and modules over a category: `CategoryTheory.additiveFunctor`,
  `CategoryTheory.AdditiveFunctor` (`C ⥤+ D`), `ObjectProperty.FullSubcategory`,
  `ObjectProperty.lift`, `ObjectProperty.ιOfLE`; the closure classes
  `ObjectProperty.ContainsZero`, `ObjectProperty.IsClosedUnderKernels`,
  `ObjectProperty.IsClosedUnderCokernels`, `ObjectProperty.IsClosedUnderFiniteProducts` and the
  abelian instance for full subcategories (`Mathlib/CategoryTheory/Abelian/Subcategory.lean`);
  `CategoryTheory.Abelian.functorCategoryAbelian`; `CategoryTheory.preadditiveYoneda`,
  `CategoryTheory.preadditiveCoyoneda`; `CategoryTheory.EnoughProjectives`,
  `CategoryTheory.Projective`, `CategoryTheory.IsCoseparator`.
- Linearity: `CategoryTheory.Linear` with `Linear.preadditiveIntLinear`,
  `Linear.oppositeCategory`, `Linear.smul_comp`, `Linear.comp_smul`;
  `CategoryTheory.linearYoneda`.
- Coends: `CategoryTheory.Limits.HasCoend`, `CategoryTheory.Limits.coend` with `coend.ι`,
  `coend.condition`, `coend.desc`, `coend.hom_ext`, `coend.map`
  (`Mathlib/CategoryTheory/Limits/Shapes/End.lean`); `Adjunction.leftAdjoint_preservesColimits`.
  The monoidal structure of `ModuleCat R` is not used in the definition of `F ⊗_C G`: it needs `R`
  and the modules in one universe.
- One object: `CategoryTheory.SingleObj`, `SingleObj.star`, `SingleObj.comp_as_mul`, the
  `Preadditive (SingleObj A)` instance (`Mathlib/CategoryTheory/Preadditive/SingleObj.lean`);
  `Action.functorCategoryEquivalence` as the pattern for 0.2; `CategoryTheory.unopUnop`.
- Size: `CategoryTheory.EssentiallySmall`, `CategoryTheory.SmallModel`,
  `CategoryTheory.equivSmallModel`, `CategoryTheory.LocallySmall`.
- Derived functors: `CategoryTheory.Functor.leftDerived`, `CategoryTheory.NatTrans.leftDerived`,
  `CategoryTheory.ProjectiveResolution` with `ProjectiveResolution.isoLeftDerivedObj`,
  `CategoryTheory.Functor.leftDerivedZeroIsoSelf`,
  `CategoryTheory.Functor.isZero_leftDerived_obj_projective_succ`,
  `CategoryTheory.HasProjectiveResolutions`, `ModuleCat.enoughProjectives`.
- Homology: `CategoryTheory.ShortComplex.ShortExact.δ` with `homology_exact₁`, `homology_exact₂`
  and `homology_exact₃`; `HomologicalComplex₂` and `HomologicalComplex₂.total`.
- Dimensions: `CategoryTheory.projectiveDimension`, `CategoryTheory.HasProjectiveDimensionLT`,
  `CategoryTheory.HasProjectiveDimensionLE`, `CategoryTheory.injectiveDimension`,
  `CategoryTheory.HasInjectiveDimensionLE`.
- Commutative counterparts: `TensorProduct` with `LinearMap.rTensor` and `LinearMap.lTensor`;
  `CategoryTheory.Tor` and `CategoryTheory.Tor'` on `ModuleCat R`; `Module.Flat` with
  `Module.Flat.iff_characterModule_injective` and `Module.Flat.projective_of_finitePresentation`;
  `CharacterModule` with `CharacterModule.homEquiv`.
- Modules and rings: `Module.Projective`, `Module.Injective`, `Module.Baer` with
  `Module.Baer.injective`, `Module.FinitePresentation`, `Module.finitePresentation_of_finite`,
  `Module.Finite`, `Submodule.IsPrincipal`, `WellFoundedLT`, `Ring.jacobson`, `Module.jacobson`,
  `IsSemisimpleRing`, `IsSemiprimaryRing`, `IsNoetherianRing`, `IsNilpotent`,
  `exists_isIdempotentElem_eq_of_ker_isNilpotent`, `MulOpposite`, `RingEquiv.opOp`,
  `RingEquiv.toOpposite`, `Module.compHom`, `ModuleCat.restrictScalars`,
  `ModuleCat.restrictScalarsEquivalenceOfRingEquiv`, `AddCommGrpCat`, `isSimpleModule_iff_isCoatom`,
  `IsCompactElement`, `Submodule.fg_iff_compact`, `CompleteOrthogonalIdempotents`.

### From Tau Ceti

- Finitely presented functors: `TauCeti.isFinitelyPresentedFunctor` and
  `TauCeti.IsFinitelyPresentedFunctor.additive`
  (`TauCeti.CategoryTheory.FinitelyPresentedFunctor.Basic`).
- Modules over an algebra: `ModuleCat.moduleOfAlgebra` and
  `ModuleCat.isScalarTower_moduleOfAlgebra` (`TauCeti.Algebra.Category.ModuleCat.Algebra`);
  `TauCeti.MatlisDual` with its right- and left-module instances
  (`TauCeti.RingTheory.MatlisDuality.Basic`); `ModuleCat.matlisDual` and `ModuleCat.matlisDualOp`
  (`TauCeti.Algebra.Category.ModuleCat.MatlisDual`).
- The balanced tensor product: `TauCeti.BalancedTensorProduct` with `tmul`, `balance`, `lift`,
  `hom_ext`, `induction_on`, `map` and `congr`
  (`TauCeti.LinearAlgebra.TensorProduct.Balanced.Basic`); `lid` and `rid`
  (`...Balanced.Unit`); `finsuppScalarRight` (`...Balanced.Finsupp`); `assoc`
  (`...Balanced.Associator`).
- Character modules: `TauCeti.CharacterModule.eval_injective`
  (`TauCeti.Algebra.Module.CharacterModule`); `CharacterModule.instModuleMulOpposite`,
  `CharacterModule.opDual`, `CharacterModule.exact_opDual`,
  `CharacterModule.injective_of_projective` and `CharacterModule.projective_of_injective`
  (`TauCeti.Algebra.Module.CharacterModule.MulOpposite`).
- Global dimension: `TauCeti.globalDimension`,
  `TauCeti.globalDimension_le_iff_hasProjectiveDimensionLE`, `TauCeti.globalDimension_le_tfae`,
  `TauCeti.globalDimension_eq_iSup_finite`, `TauCeti.globalDimension_eq_bot_iff` and
  `TauCeti.globalDimension_eq_zero_of_isSemisimpleRing` (`TauCeti.RingTheory.GlobalDimension`);
  `TauCeti.globalDimension_mulOpposite` and `TauCeti.hasInjectiveDimensionLE_characterModule_iff`
  (`TauCeti.RingTheory.GlobalDimension.MulOpposite`).
- Left derived functors: `CategoryTheory.NatTrans.leftDerived_add` and
  `CategoryTheory.Functor.isZero_leftDerived_succ`
  (`TauCeti.CategoryTheory.Abelian.LeftDerived`); the acyclic assembly lemma
  `HomologicalComplex₂.quasiIso_totalAugmentation_of_rows`
  (`TauCeti.Algebra.Homology.TotalComplex.Basic`).
- The Jacobson radical: the instance `TauCeti.IsSemiprimaryRing.mulOpposite`
  (`TauCeti.RingTheory.Jacobson.MulOpposite`); `TauCeti.isSemisimpleModule_quotient_smul_top`
  (`TauCeti.RingTheory.Jacobson.Semiprimary`).
- Semiperfect rings: `TauCeti.IsSemiperfectRing` with the instance
  `TauCeti.IsSemiperfectRing.of_isSemiprimaryRing` (`TauCeti.RingTheory.Jacobson.Semiperfect`);
  `TauCeti.IsSemiperfectRing.exists_completeOrthogonalIdempotents_isLocalRing_corner` and
  `TauCeti.IsSemiperfectRing.of_isLocalRing_corner` (`TauCeti.RingTheory.Idempotents.Semiperfect`);
  `CompleteOrthogonalIdempotents.exists_surjective_of_isSimpleModule`
  (`TauCeti.RingTheory.Idempotents.Primitive.Decomposition`);
  `IsIdempotentElem.isLocalRing_end_of_isLocalRing_corner`
  (`TauCeti.RingTheory.Idempotents.Corner.Local`); `IsIdempotentElem.projective_span_singleton`
  (`TauCeti.RingTheory.Idempotents.Projective`).
- Projective covers: `TauCeti.IsSuperfluous`, `TauCeti.IsSuperfluous.map` and
  `TauCeti.isSuperfluous_map_equiv_iff` (`TauCeti.Algebra.Module.Submodule.Superfluous`);
  `TauCeti.IsProjectiveCover`, `TauCeti.isProjectiveCover_id`,
  `TauCeti.IsProjectiveCover.exists_surjective`, `TauCeti.IsProjectiveCover.bijective_of_comp_eq`,
  `TauCeti.IsProjectiveCover.ker_le_jacobson` and `TauCeti.isProjectiveCover_mkQ_iff_le_jacobson`
  (`TauCeti.Algebra.Module.ProjectiveCover.Basic`); `TauCeti.exists_isProjectiveCover`
  (`...ProjectiveCover.Existence`);
  `TauCeti.isProjectiveCover_of_isSimpleModule_quotient_jacobson_smul_top`
  (`...ProjectiveCover.Simple`); `Module.Projective.sup_ne_top_of_isLocalRing_end`
  (`TauCeti.Algebra.Module.Projective.Local`).
- Projective presentations: `TauCeti.FiniteProjectivePresentation` with `ofFinitePresentation`
  (`TauCeti.Algebra.Module.Projective.FinitePresentation`);
  `TauCeti.IsMinimalProjectivePresentation` and
  `TauCeti.IsProjectiveCover.isMinimalProjectivePresentation`
  (`TauCeti.Algebra.Module.MinimalProjectivePresentation.Basic`);
  `TauCeti.FiniteProjectivePresentation.exists_isMinimal`, for semiprimary Noetherian rings
  (`...MinimalProjectivePresentation.Finite`).

### From other roadmaps

None.

## How to read the build

| Layer | Construction | Principal outputs |
| --- | --- | --- |
| [0](#layer-0-modules-over-a-preadditive-category-and-their-tensor-product) | Modules over a preadditive category | `Mod C`, rings as one-object categories, tensor product over `C`, projective factors, swap, ring API, duals |
| [1](#layer-1-tor-over-an-arbitrary-ring) | `Tor` | Both derivations, long exact sequences, balance, commutative comparison, `Tor₁` of cyclic modules |
| [2](#layer-2-flat-modules) | Flat modules | Tests, closure, flat quotients, Bass's flat module, finitely presented flat modules |
| [3](#layer-3-flat-dimension-and-weak-global-dimension) | Dimensions | Flat dimension, weak global dimension, symmetry, Auslander's theorem |
| [4](#layer-4-semiperfect-and-perfect-rings-and-basss-theorem-p) | Semiperfect and perfect rings | T-nilpotence, covers over semiperfect rings, `IsLeftPerfectRing`, covers over left perfect rings, Theorem P, global dimension |

Each layer needs the previous ones; 4.1 and 4.2 need only Mathlib and Tau Ceti. A name in
parentheses is the proposed Lean name of a headline declaration; auxiliary names are for the
implementer to choose.

## Layer 0: modules over a preadditive category and their tensor product

Throughout, `C : Type u` is preadditive with `Category.{v} C`, modules take values in
`AddCommGrpCat.{w}`, and `R` is a commutative ring.

### 0.1 `Mod C`

(`TauCeti.ModCat C := Cᵒᵖ ⥤+ AddCommGrpCat.{w}`, `TauCeti.LeftModCat C := C ⥤+ AddCommGrpCat.{w}`.)

- **Abelian.** In `D ⥤ AddCommGrpCat`, the additive functors (Mathlib's `additiveFunctor`)
  contain the zero functor and are closed under kernels, cokernels and finite products, all
  computed objectwise (instances of `ObjectProperty.ContainsZero`,
  `ObjectProperty.IsClosedUnderKernels`, `ObjectProperty.IsClosedUnderCokernels` and
  `ObjectProperty.IsClosedUnderFiniteProducts`). Mathlib's instance for full subcategories then
  makes `Mod C` and the left modules abelian.
- **Representables** (`TauCeti.ModCat.yoneda : C ⥤ ModCat.{v} C`, from Mathlib's
  `preadditiveYoneda`; `TauCeti.LeftModCat.coyoneda`). `Hom(-, X)` is projective, since
  `Hom(Hom(-, X), F) ≅ F(X)` by Yoneda. When `C` is `EssentiallySmall.{w}`, every module is a
  quotient of a coproduct of representables (lifted by `ULift` when `w ≠ v`), so `Mod C` has
  enough projectives ([Mitchell, §3, pp. 15–18]).
- **`R`-linear structure** (`TauCeti.Functor.objModule`, `TauCeti.Functor.toModuleCat`, and an
  instance `Linear R (ModCat C)`). For `Linear R C`, `r` acts on `F(c)` by `F(r • 𝟙 c)`; every
  `F(f)` is then `R`-linear, so `F` becomes a functor to `ModuleCat R`, and every natural
  transformation is `R`-linear. `Mod C` is `R`-linear with `(r • α)_c = r • α_c`. [Mitchell, §11,
  p. 51]: for an `R`-linear `C`, the `R`-linear functors to `R`-modules are the additive functors
  to abelian groups.
- **`mod C ⊆ Mod C`** (`TauCeti.isFinitelyPresentedFunctor_le_additiveFunctor`, with the inclusion
  `TauCeti.ModCat.ιFinitelyPresented`; `w = v`). Tau Ceti's finitely presented functors are an
  `ObjectProperty` on the same ambient category `Cᵒᵖ ⥤ AddCommGrpCat.{v}`, and they are additive
  (`TauCeti.IsFinitelyPresentedFunctor.additive`). So the inclusion is an inequality of
  properties, and `mod C` needs no migration.

**Checks.**

- For the `k`-linear category of the quiver `1 → 2` (one nonzero morphism space `Hom(1, 2) = k`
  besides the identities), a left module is a pair of vector spaces with a linear map
  `V₁ → V₂`; the representables `Hom(1, -)` and `Hom(2, -)` are `k → k` and `0 → k`, the
  indecomposable projective representations.
- For `C = SingleObj A`, `Mod C` is `ModuleCat Aᵐᵒᵖ` (0.2).

*Needs:* Mathlib `additiveFunctor`, the closure classes and the full-subcategory abelian instance,
`preadditiveYoneda`, `Linear`, `EssentiallySmall`; Tau Ceti `TauCeti.isFinitelyPresentedFunctor`.

### 0.2 Rings as one-object categories

For a ring `A`, Mathlib's `SingleObj A` is preadditive, with `f ≫ g = g * f`.

- (`TauCeti.moduleCatEquivLeftModCat A : ModuleCat.{v} A ≌ LeftModCat.{v} (SingleObj A)` and
  `TauCeti.moduleCatMulOppositeEquivModCat A : ModuleCat.{v} Aᵐᵒᵖ ≌ ModCat.{v} (SingleObj A)`),
  for any module universe `v`, on the pattern of Mathlib's `Action.functorCategoryEquivalence`.
  The regular modules go to the representables `Hom(∗, -)` and `Hom(-, ∗)`
  (`TauCeti.moduleCatEquivLeftModCatRegularIso`,
  `TauCeti.moduleCatMulOppositeEquivModCatRegularIso`). [ML, IX.6, p. 226] describes left and
  right modules as additive functors on the one-object category in this way. Neither equivalence
  is in Mathlib or Tau Ceti.
- (`TauCeti.singleObjMulOppositeEquiv A : SingleObj Aᵐᵒᵖ ≌ (SingleObj A)ᵒᵖ`), additive. Not in
  Mathlib.
- (an instance `Linear R (SingleObj A)` for an `R`-algebra `A`), with `r • a` the algebra action;
  and the derived `R`-structure of 0.1 at `∗` is the `R`-structure through `algebraMap R A`
  (`TauCeti.moduleCatEquivLeftModCatToModuleCatIso`). Not in Mathlib.
- `SingleObj A` is `EssentiallySmall.{v}` when `A` is `Small.{v}` (an instance).
- Transfer lemmas, stated as later layers need them: the equivalences preserve and reflect
  projectivity, exactness, finite generation and finite presentation; `Tor`, flatness and the
  dimensions transfer once they are defined (Layers 1–3).

**Checks.**

- For `A = k[x]`, a module over `SingleObj A` is a vector space with an endomorphism.
- `SingleObj Aᵐᵒᵖ ≌ (SingleObj A)ᵒᵖ` is the identity on objects and `op a ↦ op a` on morphisms.

*Needs:* 0.1; Mathlib `SingleObj`, `SingleObj.comp_as_mul`, `Action.functorCategoryEquivalence`.

### 0.3 The tensor product over `C`

For an `R`-linear `C`, a right module `F` and a left module `G`, the tensor product `F ⊗_C G`
(`TauCeti.ModCat.tensorObj R F G`) is the coend in `ModuleCat R` of the bifunctor
`(c', c) ↦ F(c') ⊗_R G(c)` (`TauCeti.tensorBifunctor`), with the derived `R`-structures of 0.1.
Concretely it is the quotient of `⊕_c F(c) ⊗_R G(c)` by the elements `x f ⊗ y - x ⊗ f y`
([Mitchell, §6, pp. 26–27, and §11, p. 52]; [ML, IX.6, p. 226]). Mathlib's
`CategoryTheory.coend` is the definition, not a hand-built quotient; it exists when `C` is
`EssentiallySmall.{w}`. The summands are `ModuleCat.of R (F(c') ⊗[R] G(c))`. API:

- the pure tensor `x ⊗ y` at `c` (`TauCeti.ModCat.tmul`), balancing
  `x f ⊗ y = x ⊗ f y` (`TauCeti.ModCat.tmul_balance`), induction
  (`TauCeti.ModCat.tensorObj_induction_on`), extensionality (`TauCeti.ModCat.tensorObj_hom_ext`),
  and the lift of a balanced family of `R`-bilinear maps (`TauCeti.ModCat.tensorLift`,
  `tensorLift_tmul`);
- the bifunctor (`TauCeti.ModCat.tensor R : ModCat C ⥤ LeftModCat C ⥤ ModuleCat R`), additive in
  each variable, with its values on pure tensors (`tensor_map_app_tmul`, `tensor_obj_map_tmul`);
- **adjunctions** (`TauCeti.ModCat.tensorAdjunction`, `TauCeti.ModCat.tensorAdjunction'`):
  `Hom_R(F ⊗_C G, X) ≅ Hom_{Mod C}(F, Hom_R(G(-), X))`, and the mirror
  `Hom_R(F ⊗_C G, X) ≅ Hom(G, Hom_R(F(-), X))`, natural in all variables; the right adjoints come
  from the bifunctors `TauCeti.ModCat.homRightBifunctor` and `TauCeti.ModCat.homLeftBifunctor`
  ([Mitchell, §6, p. 26, (2)]);
- **right exactness**: each partial functor preserves colimits, from the adjunctions
  (`TauCeti.ModCat.preservesColimits_tensor_flip_obj`,
  `TauCeti.ModCat.preservesColimits_tensor_obj`); in particular it is right exact and preserves
  direct sums;
- **Yoneda** (`TauCeti.ModCat.tensorObjYonedaIso`, `TauCeti.ModCat.tensorObjCoyonedaIso`):
  `Hom(-, X) ⊗_C G ≅ G(X)` and `F ⊗_C Hom(X, -) ≅ F(X)` ([Mitchell, §6, p. 26, (1)]);
- **change of base** (`TauCeti.ModCat.tensorObjRestrictScalarsIso`): for `R → R'` such that the
  `R`-structure of `C` comes from its `R'`-structure, the `R'`-tensor product restricted to `R` is
  the `R`-tensor product;
- **independence of `R`** (`TauCeti.ModCat.tensorObjIntIso`), the case `ℤ → R`: the `ℤ`-coend
  already forces `r x ⊗ y = x ⊗ r y`, because `r` acts through the morphism `r • 𝟙` of `C`
  ([Mitchell, §11, p. 52]).

**Checks.**

- For `C = SingleObj A`, 0.6 identifies `F ⊗_C G` with `M ⊗_A N`.
- In the quiver example of 0.1, `F ⊗_C Hom(1, -) ≅ F(1)` by Yoneda.

*Needs:* 0.1; Mathlib `coend`, `HasCoend`, `TensorProduct`, `ModuleCat.restrictScalars`,
`Adjunction.leftAdjoint_preservesColimits`.

### 0.4 Projective factors

(`TauCeti.ModCat.mono_tensor_obj_map_of_projective`,
`TauCeti.ModCat.mono_tensor_map_app_of_projective`.) If `F` is projective in `Mod C`, then
`F ⊗_C -` preserves monomorphisms; symmetrically for a projective left module. Route: for a
representable `F = Hom(-, X)`, Yoneda (0.3) identifies `F ⊗_C g` with `g` at `X`; the tensor
product preserves direct sums (0.3), so the claim holds for coproducts of representables; a
projective is a retract of such a coproduct (0.1) ([Mitchell, Prop. 10.1 and Cor. 10.2, p. 47]).
Layer 2 cites this as "projective modules are flat".

*Needs:* 0.1, 0.3.

### 0.5 The swap

(`TauCeti.LeftModCat.toModCatOp`, `TauCeti.ModCat.tensorObjSwapIso`.) A left `C`-module `G` is a
right `Cᵒᵖ`-module through `Cᵒᵖᵒᵖ ⥤ C` (Mathlib's `unopUnop`), and a right `C`-module `F` is, as
it stands, a left `Cᵒᵖ`-module (`ModCat C` is `LeftModCat Cᵒᵖ`). Then `F ⊗_C G ≅ G ⊗_{Cᵒᵖ} F`,
`R`-linear and natural, by `x ⊗ y ↦ y ⊗ x` on the coends ([Mitchell, §6, p. 26], where
`G ⊗ F` is defined as `F ⊗ G`). It is compatible with `tmul`, `tensorLift` and the adjunctions, so
each statement in the left-module variable follows from the one in the right-module variable.
Mathlib's `Linear.oppositeCategory` makes `Cᵒᵖ` `R`-linear, and `EssentiallySmall` passes to `Cᵒᵖ`.
The ring swap of 0.6 follows from this, `TauCeti.singleObjMulOppositeEquiv` (0.2) and the
comparison of 0.6.

*Needs:* 0.3; Mathlib `unopUnop`, `Linear.oppositeCategory`.

### 0.6 Rings: the balanced tensor product

For an `R`-algebra `A`, the ring-level objects are native (Convention 5).

- **Maps** (`TauCeti.BalancedTensorProduct.rTensor R N f`, `TauCeti.BalancedTensorProduct.lTensor
  R M g`). For an `Aᵐᵒᵖ`-linear map `f : M → M'` of right modules, `f ⊗ N` is `R`-linear;
  symmetrically `M ⊗ g`. The names follow Mathlib's `LinearMap.rTensor` and `LinearMap.lTensor`.
  Both are `BalancedTensorProduct.map` with one identity. API: values on `m ⊗ n`
  (`rTensor_tmul`, `lTensor_tmul`), identities and composites (`rTensor_id`, `rTensor_comp`,
  `lTensor_id`, `lTensor_comp`) and the interchange `rTensor_comp_lTensor`.
- **Bifunctor** (`TauCeti.BalancedTensorProduct.functor R A :
  ModuleCat.{v} Aᵐᵒᵖ ⥤ ModuleCat.{v} A ⥤ ModuleCat.{v} R`), additive in each variable; the
  `R`-actions on bundled modules come from Tau Ceti's `ModuleCat.moduleOfAlgebra`. At the regular
  modules it is the restriction of scalars along `algebraMap R A` (`lid`, `rid`).
- **Adjunction** (`TauCeti.BalancedTensorProduct.adjunction R A N`): `- ⊗_A N` is left adjoint to
  `Hom_R(N, -)` (`TauCeti.BalancedTensorProduct.homRight`, sending `X` to Tau Ceti's
  `MatlisDual R X N` as a right module), and symmetrically. Right exactness and preservation of
  direct sums and colimits follow: `rTensor_exact`, `rTensor_surjective`, `lTensor_exact`,
  `lTensor_surjective` ([Lam-FC, (24.20), p. 365], stated there without proof).
- **Projective factors** (`TauCeti.BalancedTensorProduct.lTensor_injective_of_projective`,
  `TauCeti.BalancedTensorProduct.rTensor_injective_of_projective`): 0.4 through the comparison, or
  directly, for free modules through `finsuppScalarRight` and its mirror, then retracts.
- **Swap** (`TauCeti.BalancedTensorProduct.comm`): `M ⊗_A N ≃ₗ[R] N ⊗_{Aᵐᵒᵖ} M`,
  `m ⊗ n ↦ n ⊗ m`, with `N` a right `Aᵐᵒᵖ`-module through `RingEquiv.opOp A`; natural in both
  factors. It is the left-right symmetry principle: each pair of left and right statements is
  proved once and transferred.
- **Independence of `R` and change of base** (`TauCeti.BalancedTensorProduct.intAddEquiv`,
  `TauCeti.BalancedTensorProduct.changeBaseAddEquiv`): `M ⊗_A N` over `ℤ` and over `R` have the
  same underlying group, and for `R → R' → A` the `R`- and `R'`-balanced tensor products of
  `R'`-modules agree, `R`-linearly, by `m ⊗ n ↦ m ⊗ n`. These, not dropping linearity, handle the
  two `ℤ`-module structures on `M ⊗_A N` for `R = ℤ`.
- **Comparison** (`TauCeti.BalancedTensorProduct.tensorObjSingleObjIso`): for `[Small.{v} A]`,
  the tensor product over `SingleObj A` (0.3) of the modules of 0.2 is `M ⊗_A N`, `R`-linearly and
  naturally, with `x ⊗ y` at `∗` going to `m ⊗ n`. It uses `Linear R (SingleObj A)`, the agreement
  of the derived `R`-structures (0.2) and the independence of `R` (0.3).
- **Commutative rings** (`TauCeti.BalancedTensorProduct.equivTensorProduct`). For a commutative
  ring `R` and `R`-modules `M`, `N`, with `M` an `Rᵐᵒᵖ`-module by `op r • m = r • m`
  (`[IsCentralScalar R M]`), `M ⊗_R N ≃ₗ[R] M ⊗[R] N`, `m ⊗ n ↦ m ⊗ₜ n`
  (`equivTensorProduct_tmul`). Existing users of `BalancedTensorProduct` are unchanged.
- **Duals** (0.7 for rings; `TauCeti.BalancedTensorProduct.homEquiv`): for any `R`-module `E`,
  `Hom_R(M ⊗_A N, E) ≃ₗ[R] Hom_{Aᵐᵒᵖ}(M, MatlisDual R E N)`. For `R = ℤ` and `E = ℚ ⧸ ℤ`
  (`TauCeti.BalancedTensorProduct.rTensor_injective_iff_surjective_comp`): for a map
  `i : M → M'` of right modules, `i ⊗ N` is injective exactly when composition with `i`,
  `(M' →ₗ[Aᵐᵒᵖ] N⁺) → (M →ₗ[Aᵐᵒᵖ] N⁺)`, is surjective, since characters detect elements
  (`TauCeti.CharacterModule.eval_injective`) ([Lambek, Prop. 1, p. 241]).

**Checks.**

- For a right ideal `I : Submodule Aᵐᵒᵖ A`, right exactness applied to `0 → I → A → A ⧸ I → 0`
  and `lid` identify `(A ⧸ I) ⊗_A N` with `N` modulo the additive subgroup generated by the
  `a • n`, `a ∈ I`. Over `ℤ` this gives `ℤ ⧸ m ⊗_ℤ ℤ ⧸ n ≃+ ℤ ⧸ gcd(m, n)`.
- `ℤ ⧸ 2 ⊗_ℤ (2ℤ → ℤ)` is the zero map, while `ℤ ⧸ 2 ⊗_ℤ 2ℤ ≅ ℤ ⧸ 2`: tensoring is not left
  exact.
- `eA ⊗_A Af ≅ eAf` for idempotents `e`, `f` (Tau Ceti's corner identification).
- For `A = M = N = ℤ` and `E = ℚ ⧸ ℤ`, both sides of `homEquiv` are `ℚ ⧸ ℤ`.

*Needs:* 0.2–0.5; Tau Ceti `TauCeti.BalancedTensorProduct` with `map`, `lift`, `lid`, `rid` and
`finsuppScalarRight`, `ModuleCat.moduleOfAlgebra`, `TauCeti.MatlisDual`,
`TauCeti.CharacterModule.eval_injective`; Mathlib `TensorProduct`, `RingEquiv.opOp`.

### 0.7 Duals with respect to an `R`-module `E`

For an `R`-module `E : ModuleCat.{w} R`, the dual of a left module is
`G^E = Hom_R(G(-), E)` (`TauCeti.LeftModCat.dual R E : (LeftModCat C)ᵒᵖ ⥤ ModCat C`), and of a
right module `F^E = Hom_R(F(-), E)` (`TauCeti.ModCat.dual R E`): the right adjoints of 0.3
evaluated at `E`, as Tau Ceti's `MatlisDual R E` for rings. The adjunction of 0.3 at `X = E` is
`Hom_R(F ⊗_C G, E) ≅ Hom_{Mod C}(F, G^E)`. The hypotheses on `E` sit on the theorems:

- `E` injective: the dual is exact (`TauCeti.LeftModCat.dual_shortExact`);
- `E` a cogenerator (Mathlib's `IsCoseparator`): the dual detects zero objects
  (`TauCeti.LeftModCat.isZero_of_isZero_dual`), and with the adjunction, `i ⊗_C G` is a
  monomorphism exactly when composition with `i`, `Hom(F', G^E) → Hom(F, G^E)`, is onto
  (`TauCeti.ModCat.mono_tensor_map_app_iff`);
- Lambek's flatness criterion (Layer 2) uses both.

Special cases: `R = ℤ` and `E = ℚ ⧸ ℤ`, Mathlib's `CharacterModule` (for `Mod C` this gives a
cogenerating family of injectives, [Mitchell, §6, p. 27]); Matlis duals `MatlisDual R E` for
Auslander-Reiten theory. Whether Lambek's criterion holds with a general injective cogenerator `E`
is to be checked in the literature for Layer 2.

*Needs:* 0.3; Mathlib `IsCoseparator`, `ShortComplex.ShortExact`; Tau Ceti `TauCeti.MatlisDual`.

### Examples

Rings (0.2, 0.6); `k`-linear categories of quivers, whose modules are representations; Tau Ceti's
`mod C` inside `Mod C`. The commutative comparison of 0.6 makes every Mathlib tensor computation an
example of `M ⊗_A N`.

### Dependencies

Mathlib and Tau Ceti only.

## Layer 1: `Tor` over an arbitrary ring

*Under review: to be converted to the category-primary design of Layer 0; currently stated for
rings.*

### 1.1 Definition

(`TauCeti.BalancedTor R A n : ModuleCat.{v} Aᵐᵒᵖ ⥤ ModuleCat.{v} A ⥤ ModuleCat.{v} R`), for an
`R`-algebra `A` with `[Small.{v} A]`: the object at `M` is
`((BalancedTensorProduct.functor R A).obj M).leftDerived n`,
and maps act by `NatTrans.leftDerived`. This is the shape of Mathlib's `CategoryTheory.Tor`,
derived in the second variable. (`TauCeti.BalancedTor' R A n`) is derived in the first variable, as
Mathlib's `CategoryTheory.Tor'`. `BalancedTor'` needs projective resolutions of right modules,
so this item includes the instance `Small.{v} Aᵐᵒᵖ` from `Small.{v} A`
(`TauCeti.small_mulOpposite`). API:

- degree zero (`TauCeti.balancedTorZeroIso`, `TauCeti.balancedTor'ZeroIso`):
  `BalancedTor R A 0 ≅ BalancedTensorProduct.functor R A` and the same for `BalancedTor'`
  (`leftDerivedZeroIsoSelf` and 0.6);
- vanishing (`TauCeti.isZero_balancedTor_succ_of_projective`,
  `TauCeti.isZero_balancedTor'_succ_of_projective`): `BalancedTor R A (n + 1)` vanishes at a
  projective left module, `BalancedTor' R A (n + 1)` at a projective right module;
- additivity in the underived variable (`NatTrans.leftDerived_add`).

### 1.2 Long exact sequences in the underived variable

For a short exact sequence `0 → M₁ → M₂ → M₃ → 0` of right modules and a projective resolution
`Q` of a left module `N`, the complexes `Mᵢ ⊗_A Q` form a short exact sequence of complexes, by
the projective factors of 0.6. Mathlib's `ShortComplex.ShortExact.δ` then gives
`δ : Tor_{n+1}(M₃, N) → Tor_n(M₁, N)` (`ShortComplex.ShortExact.balancedTorδ`) and exactness at
the three places (`balancedTor_exact₁`, `balancedTor_exact₂`, `balancedTor_exact₃`), natural in
`N` and in the sequence. The same for `BalancedTor'` in its left-module variable.

### 1.3 Balance

(`TauCeti.balancedTorIso : BalancedTor R A n ≅ BalancedTor' R A n`), natural in both variables.
Route: for projective resolutions `P` of `M` and `Q` of `N`, form the first-quadrant bicomplex
`P_p ⊗_A Q_q`. Its augmented rows `P_p ⊗ Q → P_p ⊗ N` and columns `P ⊗ Q_q → M ⊗ Q_q` are exact,
because tensoring with a projective module is exact (0.4, 0.6). Tau Ceti's
`HomologicalComplex₂.quasiIso_totalAugmentation_of_rows`, for the bicomplex and its flip,
identifies both `H_n(P ⊗ N)` and `H_n(M ⊗ Q)` with the homology of the total complex ([Weibel,
Thm. 2.7.2], not read). Consequently each of `BalancedTor` and `BalancedTor'` has the long exact
sequences of 1.2 in both variables.

**Swap** (`TauCeti.balancedTorSwapIso`). `Tor_n^A(M, N) ≅ Tor_n^{Aᵐᵒᵖ}(N, M)`, naturally, through
0.6's swap and `ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.opOp A)`.

### 1.4 Comparison and first computations

- **Commutative rings** (`TauCeti.balancedTorIsoTor`). For `[CommRing R]`, `BalancedTor R R n`
  is naturally isomorphic to Mathlib's `CategoryTheory.Tor (ModuleCat R) n`, after restricting
  `ModuleCat R` to `ModuleCat Rᵐᵒᵖ` along `(RingEquiv.toOpposite R).symm`; the same for
  `BalancedTor'` and `CategoryTheory.Tor'`. With 1.3 this gives `Tor ≅ Tor'` for `ModuleCat R`,
  the comparison that Mathlib's
  `Mathlib/CategoryTheory/Monoidal/Tor.lean` leaves open.
- **Cyclic modules** (`TauCeti.balancedTorOneQuotientEquiv`). For a right ideal
  `I : Submodule Aᵐᵒᵖ A` and a left ideal `K : Ideal A`, with `R = ℤ`,
  `Tor_1^A(A ⧸ I, A ⧸ K) ≃+ (I ∩ K) ⧸ IK`, where `IK` is the additive subgroup generated by the
  products: from 1.2 for `0 → I → A → A ⧸ I → 0` and the first check of 0.6 (locator not
  checked).

**Checks.**

- `Tor_1^ℤ(ℤ ⧸ m, ℤ ⧸ n) ≅ ℤ ⧸ gcd(m, n)` (cyclic formula: `(mℤ ∩ nℤ) ⧸ mnℤ`).
- For `B = k[ε]/(ε²)`, `Tor_n^B(k, k) ≅ k` for every `n`: `k` has the periodic resolution
  `⋯ → B → B → k` by multiplication by `ε`, which becomes zero after tensoring with `k`.
- For the upper triangular algebra `T = T₂(k)` with radical `J = k e₁₂`,
  `Tor_1^T(T ⧸ J, T ⧸ J) ≅ J ⧸ J² = J` is one-dimensional, and `Tor_n^T(T ⧸ J, -) = 0` for
  `n ≥ 2`, since `J = e₁₂T ≅ e₂₂T` is projective.

*Needs:* Layer 0; Mathlib `Functor.leftDerived`, `ShortComplex.ShortExact.δ`,
`HomologicalComplex₂`, `CategoryTheory.Tor`, `CategoryTheory.Tor'`; Tau Ceti
`HomologicalComplex₂.quasiIso_totalAugmentation_of_rows`, `NatTrans.leftDerived_add`.

### Examples

Over `ℤ`, `B = k[ε]/(ε²)` and `T₂(k)` as in the checks. The balance makes `Tor` computable from a
resolution of either variable, which the checks use for `T₂(k)`.

### Dependencies

Layer 0.

## Layer 2: flat modules

*Under review: to be converted to the category-primary design of Layer 0; currently stated for
rings.*

### 2.1 Definition and tests

(`TauCeti.Module.BalancedFlat A M`), a class for a left module `M`: for every finite right
`A`-module `P` in the universe of `A` and every finitely generated submodule `N ≤ P`, the map
`N ⊗_A M → P ⊗_A M` (over `R = ℤ`) is injective. This is the shape of Mathlib's `Module.Flat`. A
right module `M` is flat when `BalancedFlat Aᵐᵒᵖ M`.

**Tests** (`TauCeti.Module.balancedFlat_tfae`). For `[Small.{v} A]` and `M : Type v`, the
following are equivalent:

1. `BalancedFlat A M`;
2. `i ⊗ M` is injective for every injective map `i` of right modules, in every universe;
3. for every finitely generated right ideal `I`, the map `I ⊗_A M → A ⊗_A M` is injective;
   through `lid` this is the map `I ⊗_A M → M` ([Lam-LMR, (4.12), p. 125]);
4. `Module.Injective Aᵐᵒᵖ M⁺` (Lambek: [Lambek, Theorem, p. 239], [Lam-LMR, (4.9), p. 125]);
5. `Tor_1^A(N, M) = 0` for every right module `N`;
6. `Tor_1^A(A ⧸ I, M) = 0` for every finitely generated right ideal `I`.

Route: (1) ⇒ (3) and (2) ⇒ (1) are immediate. (3) ⇒ (4): an element of `I ⊗_A M` comes from
`I' ⊗_A M` for a finitely generated `I' ≤ I`, so (3) holds for all right ideals; then the duals
of 0.6 and Mathlib's `Module.Baer.injective` over `Aᵐᵒᵖ`. (4) ⇒ (2) by the duals of 0.6. (2) ⇔ (5)
and (3) ⇔ (6) by 1.2, applied to `0 → K → F → N → 0` with `F` free and to `0 → I → A → A ⧸ I → 0`.

**Commutative rings** (`TauCeti.Module.balancedFlat_iff_flat`). For `[CommRing R]`,
`BalancedFlat R M ↔ Module.Flat R M`, through 0.6.

### 2.2 Closure properties and `Tor`

Projective modules are flat (`TauCeti.Module.BalancedFlat.of_projective`, an instance, from 0.4);
flatness is invariant under linear equivalence (`TauCeti.Module.BalancedFlat.of_linearEquiv`),
passes to retracts, and a direct sum is flat exactly when every summand is
(`TauCeti.Module.balancedFlat_directSum_iff`). In a short exact sequence
`0 → M₁ → M₂ → M₃ → 0` of left modules with `M₃` flat, `M₂` is flat exactly when `M₁` is
(`TauCeti.Module.balancedFlat_iff_of_exact`; 1.2; [Lam-LMR, (4.13), p. 126]). Flat modules have
no higher `Tor`: `Tor_{n+1}^A(N, M) = 0` for flat `M`
(`TauCeti.isZero_balancedTor_succ_of_balancedFlat`), by 1.3: compute with `P ⊗_A M` for a
projective resolution `P` of `N`, and use that `- ⊗_A M` is exact.

### 2.3 Flat quotients and Bass's flat module

**Flat quotients.** For a short exact sequence `0 → K → F → M → 0` of left modules with `F` flat,
`M` is flat exactly when `N ⊗ K → N ⊗ F` is injective for every right module `N` ([Lam-FC,
(24.23), p. 367], right-handed). When `M` is flat, `K ⊓ I • F = I • K` for every two-sided ideal
`I` (`TauCeti.Submodule.inf_smul_eq_smul_of_balancedFlat`): the case `N = A ⧸ I`.

**Bass's flat module.** For a sequence `a : ℕ → A`, let `F = ℕ →₀ A` with basis `eᵢ`, and
`G ≤ F` the submodule spanned by the `eᵢ - aᵢ • eᵢ₊₁` (`TauCeti.bassRelations A a`). Then
`F ⧸ G` is flat (`TauCeti.balancedFlat_bassRelations`), and if `F ⧸ G` is projective, the chain of
principal right ideals `a₀A ⊇ a₀a₁A ⊇ a₀a₁a₂A ⊇ ⋯` is eventually constant
(`TauCeti.exists_span_prod_eq_of_projective_bassRelations`; [Bass, Lemma 1.1, p. 468]; [Lam-FC,
(24.24), pp. 367–368], right-handed). Route: `G` is free on the `eᵢ - aᵢ • eᵢ₊₁`, and the test
above is checked on coordinates; a splitting of `G → F` gives the stabilization.

### 2.4 Finitely presented flat modules

(`TauCeti.Module.BalancedFlat.projective_of_finitePresentation`). For `[Small.{v} A]`,
`[Module.FinitePresentation A M]` and `[BalancedFlat A M]`, `M` is projective. Route: 2.1 (4)
and Tau Ceti's `CharacterModule.projective_of_injective` ([Lam-LMR, (4.30), p. 133], for finitely
related modules; Mathlib's `Module.Flat.projective_of_finitePresentation` is the commutative
case). Over a left Noetherian ring every finite flat module is projective
(`Module.finitePresentation_of_finite`).

**Checks.**

- `ℚ` is a flat `ℤ`-module (2.1 and Mathlib's `Module.Flat`) and is not projective
  (`TauCeti.balancedFlat_rat_and_not_projective`); `ℤ ⧸ n` is not flat for `n ≥ 2` (1.4).
- Over `B = k[ε]/(ε²)`, `k` is not flat, since `Tor_1^B(k, k) ≅ k` (1.4).
- Over `T₂(k)`, of the two simple left modules the projective one is flat and the other is not
  (2.4: it is finitely presented and not projective).
- Bass's module over `ℤ` for the constant sequence `p` is `ℤ[1/p]`: flat, not projective, and
  `pℤ ⊋ p²ℤ ⊋ ⋯`.

*Needs:* Layers 0 and 1; Mathlib `Module.Baer.injective`, `Module.FinitePresentation`,
`Module.finitePresentation_of_finite`, `Module.Flat`; Tau Ceti
`CharacterModule.projective_of_injective`, `CharacterModule.injective_of_projective`.

### Examples

`ℚ` and `ℤ[1/p]` over `ℤ`; the simple modules of `T₂(k)` and of `k[ε]/(ε²)`.

### Dependencies

Layers 0 and 1.

## Layer 3: flat dimension and weak global dimension

*Under review: to be converted to the category-primary design of Layer 0; currently stated for
rings.*

### 3.1 Flat dimension

(`TauCeti.HasFlatDimensionLT`, `TauCeti.HasFlatDimensionLE`, `TauCeti.flatDimension`). For
`M : ModuleCat.{v} A` and `n : ℕ`, `HasFlatDimensionLT M n` says `Tor_i^A(N, M) = 0` for every
right module `N` and every `i ≥ n`; `HasFlatDimensionLE M n` is `HasFlatDimensionLT M (n + 1)`;
`flatDimension M : WithBot ℕ∞` is the infimum of the `d` with `HasFlatDimensionLT M i` for all
`i > d`, the shape of Mathlib's `projectiveDimension`. API:

- `flatDimension M = ⊥` exactly when `M` is zero (`TauCeti.flatDimension_eq_bot_iff`);
  `HasFlatDimensionLE M 0 ↔ BalancedFlat A M` (`TauCeti.hasFlatDimensionLE_zero_iff`; 2.1, 2.2);
- `flatDimension M ≤ projectiveDimension M` (`TauCeti.flatDimension_le_projectiveDimension`; 2.2);
- dimension shifting (`TauCeti.hasFlatDimensionLE_succ_iff`): for `0 → K → F → M → 0` with `F`
  flat, `HasFlatDimensionLE M (n + 1) ↔ HasFlatDimensionLE K n` (1.2, 2.2);
- the ideal test (`TauCeti.hasFlatDimensionLE_iff_forall_quotient`): `HasFlatDimensionLE M n`
  exactly when `Tor_{n+1}^A(A ⧸ I, M) = 0` for every finitely generated right ideal `I` (2.1 and
  dimension shifting);
- character modules (`TauCeti.flatDimension_eq_injectiveDimension_characterModule`):
  `flatDimension M = injectiveDimension (M⁺)` in `ModuleCat Aᵐᵒᵖ`
  ([Lam-LMR, (5.57), p. 184]). Route: induction by dimension shifting on both sides, with 2.1 (4),
  `CharacterModule.exact_opDual` and `CharacterModule.injective_of_projective`; the same induction
  as Tau Ceti's `hasInjectiveDimensionLE_characterModule_iff`, without a finiteness hypothesis.

### 3.2 Weak global dimension

(`TauCeti.weakGlobalDimension A := ⨆ M : ModuleCat.{v} A, flatDimension M`). API:

- `weakGlobalDimension A ≤ n` exactly when `Tor_{n+1}^A` vanishes on all pairs
  (`TauCeti.weakGlobalDimension_le_iff`);
- **symmetry** (`TauCeti.weakGlobalDimension_mulOpposite`):
  `weakGlobalDimension Aᵐᵒᵖ = weakGlobalDimension A`, by 1.3 ([Au, p. 70]; [Lam-LMR, (5.63),
  p. 185]);
- **bounds** (`TauCeti.weakGlobalDimension_le_globalDimension`,
  `TauCeti.weakGlobalDimension_le_globalDimension_mulOpposite`):
  `weakGlobalDimension A ≤ globalDimension A` and `weakGlobalDimension A ≤ globalDimension Aᵐᵒᵖ`
  (3.1 and symmetry; [Lam-LMR, (5.58), p. 184]);
- **tests** (`TauCeti.weakGlobalDimension_le_tfae`): for `n : ℕ`, the following are equivalent:
  `weakGlobalDimension A ≤ n`; every finitely presented right module has flat dimension at most
  `n`; for every finitely generated right ideal `I`, the right module `A ⧸ I` has flat dimension at
  most `n` ([Lam-LMR, (5.69), p. 187], for cyclic modules);
- **from projective dimension** (`TauCeti.weakGlobalDimension_le_of_forall_finitePresentation`):
  if every finitely presented right module has projective dimension at most `n`, then
  `weakGlobalDimension A ≤ n`;
- `weakGlobalDimension A = ⊥` exactly when `A` is the zero ring
  (`TauCeti.weakGlobalDimension_eq_bot_iff`); a nonzero semisimple ring has weak global dimension
  `0` (`TauCeti.weakGlobalDimension_eq_zero_of_isSemisimpleRing`).

### 3.3 Auslander's theorem

(`TauCeti.globalDimension_eq_weakGlobalDimension`). For `[IsNoetherianRing A]` and
`[Small.{v} A]`, `globalDimension.{v} A = weakGlobalDimension.{v} A` ([Au, Thm. 4, p. 70];
[Lam-LMR, (5.59), p. 184]). Route: over a left Noetherian ring the syzygies of a finite module are
finite, hence finitely presented, so dimension shifting and 2.4 give
`flatDimension M = projectiveDimension M` for finite `M`
(`TauCeti.flatDimension_eq_projectiveDimension_of_finite`); then
`TauCeti.globalDimension_eq_iSup_finite`.

**Corollaries.**

- **Left bound** (`TauCeti.globalDimension_le_of_forall_finitePresentation_mulOpposite`). If `A` is
  left Noetherian and every finitely presented right module has projective dimension at most `n`,
  then `globalDimension A ≤ n` (3.2 and the theorem). No right Noetherian hypothesis is used.
- For a left and right Noetherian ring, symmetry (3.2) gives
  `globalDimension Aᵐᵒᵖ = globalDimension A` ([Au, Cor. 5, p. 70]). This is Tau Ceti's
  `TauCeti.globalDimension_mulOpposite`; it may be re-proved this way, but is not stated again.

**Checks.**

- A field has weak global dimension `0`, the zero ring `⊥`.
- `ℤ` has weak and global dimension `1` (`Tor_1^ℤ(ℤ ⧸ 2, ℤ ⧸ 2) ≠ 0`, and every right ideal is
  free).
- `B = k[ε]/(ε²)` has weak and global dimension `⊤` (1.4).
- Small's ring `R = [[ℤ, ℚ], [0, ℚ]]` is right Noetherian and right hereditary, not left
  hereditary, and `globalDimension Rᵐᵒᵖ = weakGlobalDimension R = 1 < globalDimension R`
  ([Lam-LMR, (5.62b), p. 185]; the facts on `R` are cited there to (2.33), not read). The
  theorem applies to `Rᵐᵒᵖ`; for `R` it fails, so `R` is not left Noetherian.

*Needs:* Layers 1 and 2; Mathlib `projectiveDimension`, `injectiveDimension`,
`Module.finitePresentation_of_finite`; Tau Ceti `TauCeti.globalDimension`,
`TauCeti.globalDimension_eq_iSup_finite`, `TauCeti.globalDimension_le_tfae`.

### Examples

`ℤ`, `k[ε]/(ε²)`, `T₂(k)` (weak and global dimension `1`), and Small's ring.

### Dependencies

Layers 1 and 2.

## Layer 4: semiperfect and perfect rings, and Bass's Theorem P

*Under review: to be converted to the category-primary design of Layer 0; currently stated for
rings.*

### 4.1 T-nilpotence

(`TauCeti.IsLeftTNilpotent (S : Set A) : Prop`): for every `a : ℕ → A` with values in `S` there is
`n` with `(List.ofFn fun i : Fin n ↦ a i).prod = 0` (Convention 8). API: monotone in `S`
(`IsLeftTNilpotent.mono`); a nilpotent ideal is left T-nilpotent
(`TauCeti.isLeftTNilpotent_of_isNilpotent`); every element of a left T-nilpotent set is nilpotent
(`IsLeftTNilpotent.isNilpotent`); images under ring homomorphisms (`IsLeftTNilpotent.image`).

**Nakayama's lemma for all modules** (`TauCeti.isLeftTNilpotent_tfae`). For a left ideal
`J : Ideal A`, the following are equivalent ([AF, 28.3, pp. 314–315]; [Lam-FC, (23.16), p. 352],
right-handed):

1. `J` is left T-nilpotent;
2. for every left module `M` in the universe of `A`, `J • ⊤ = ⊤` in `Submodule A M` implies
   `M` is zero;
3. for every such `M`, `J • ⊤` is superfluous in `M`;
4. `J • ⊤` is superfluous in the free module `ℕ →₀ A`.

(1) ⇒ (3) holds for modules in every universe (`IsLeftTNilpotent.isSuperfluous_smul_top`).

**Checks.**

- The ideal `(X)` of `PowerSeries k` is not left T-nilpotent (the constant sequence `X`;
  `TauCeti.not_isLeftTNilpotent_span_X`).
- In `F = ℕ →₀ PowerSeries k`, the submodule `G` spanned by the `eᵢ - X • eᵢ₊₁` satisfies
  `G + X • F = F` and `G ≠ F` (`F ⧸ G` is the Laurent series field), so `X • F` is not
  superfluous, as (4) predicts.

### 4.2 Projective covers over semiperfect rings

Here `R` is a ring and `J = Ring.jacobson R`.

- **Covers of projective modules** (`TauCeti.IsProjectiveCover.bijective_of_projective`). A
  projective cover of a projective module is bijective: compare it with the identity cover by
  `TauCeti.IsProjectiveCover.bijective_of_comp_eq`.
- **Local projectives** (`TauCeti.isProjectiveCover_of_isLocalRing_end`). A surjection from a
  projective module with local endomorphism ring onto a nonzero module is a projective cover
  (`Module.Projective.sup_ne_top_of_isLocalRing_end`).
- **Covers of simple modules are local** (`TauCeti.IsProjectiveCover.isLocalRing_end`). If
  `p : P → S` is a projective cover of a simple module, then every proper submodule of `P` lies in
  `ker p`, and `Module.End R P` is local: an onto endomorphism has superfluous kernel, so it is a
  cover of `P` and hence bijective ([Krause, Lemma 3.6]; [Wisbauer, 19.7, p. 161]).
- **Moving covers between universes**
  (`TauCeti.IsProjectiveCover.exists_isProjectiveCover_comp_subtype`). If `M` has a projective
  cover `f`, every surjection `g : Q → M` from a projective module restricts to a projective cover
  on a submodule of `Q`: lift `f` through `g`, split the lift, and transport the kernel along the
  splitting (`TauCeti.isSuperfluous_map_equiv_iff`).
- **Radical of a projective module** (`TauCeti.jacobson_eq_jacobson_smul_top_of_projective`,
  `TauCeti.jacobson_ne_top_of_projective`). For a projective left module `P`,
  `Module.jacobson R P = J • ⊤`, and `Module.jacobson R P ≠ ⊤` when `P` is nonzero ([Lam-FC, (24.7),
  p. 360]; [Sandomierski, Prop. 1 (d), p. 205]).
- **Covers from covers of simple quotients**
  (`TauCeti.exists_isProjectiveCover_pi_of_forall_isCoatom_exists_isProjectiveCover`). Let `M` be
  finitely generated, and suppose every simple quotient `M ⧸ N` has a projective cover with source
  in a universe `w`. Then `M` has a projective cover `f : P₁ × ⋯ × Pₙ → M` whose components lift
  covers `pᵢ : Pᵢ → M ⧸ Nᵢ` of simple quotients. Route: the images of lifts of covers of simple
  quotients generate `M` (a proper submodule lies in a maximal one); `⊤` is compact, so finitely
  many of them suffice, and an irredundant finite choice gives a superfluous kernel ([Wisbauer,
  18.5 (1), p. 152], for the generation step). The finite family is extracted with
  `IsCompactElement` and `Submodule.fg_iff_compact`; finite suprema and finite products of
  superfluous submodules are superfluous, and these two closure facts are part of this item.
- **Covers over a semiperfect ring** (`TauCeti.exists_isProjectiveCover_of_isSemiperfectRing`).
  Over a semiperfect ring every finitely generated left module has a projective cover with source
  in the universe of `R` ([Lam-FC, (24.12), p. 361]; [Bass, Thm. 2.1, p. 471]). Route: by
  `TauCeti.IsSemiperfectRing.exists_completeOrthogonalIdempotents_isLocalRing_corner`, `1` is a sum
  of orthogonal idempotents `eᵢ` with local corners; a simple module is a quotient of some `Reᵢ`
  (`CompleteOrthogonalIdempotents.exists_surjective_of_isSimpleModule`), which is projective with
  local endomorphism ring, so the quotient map is a cover; then the previous item.
- **Decomposition** (`TauCeti.IsSemiperfectRing.of_linearEquiv_pi`). If `R ≃ₗ[R] P₁ × ⋯ × Pₙ`
  with every `Module.End R Pᵢ` local, then `R` is semiperfect: the images of the coordinate
  idempotents are orthogonal idempotents with local corners, and
  `TauCeti.IsSemiperfectRing.of_isLocalRing_corner` applies.
- **Semiperfect rings by projective covers** (`TauCeti.isSemiperfectRing_tfae`). The following are
  equivalent ([Sandomierski, Thm. 4, p. 206]; [Krause, Prop. 4.1]; [Lam-FC, (24.16), p. 364]):
  1. `R` is semiperfect;
  2. `R`, as a left module over itself, is a finite product of projective modules with local
     endomorphism rings;
  3. every finitely generated left module `M : Type u` has a projective cover;
  4. every simple left module `S : Type u` has a projective cover.

  Route: (1) ⇒ (3) is the previous item, (3) ⇒ (4) is immediate, (4) ⇒ (2) applies the cover
  from simple quotients to `M = R`, which is bijective because `R` is projective, with local
  factors because each is the cover of a simple module; (2) ⇒ (1) is the decomposition item.
- **Minimal presentations** (`TauCeti.FiniteProjectivePresentation.exists_isMinimal`, with weaker
  hypotheses). A finitely presented module `M : ModuleCat.{v} R` over a semiperfect ring with
  `[Small.{v} R]` has a finite minimal projective presentation
  (`TauCeti.IsMinimalProjectivePresentation`). Route: cut a cover of `M` out of a finite free
  presentation in the universe `v` (moving covers between universes); its kernel is finitely
  generated because `M` is finitely presented, so it also has a cover; then
  `TauCeti.IsProjectiveCover.isMinimalProjectivePresentation`. The statement replaces the present
  one, whose hypotheses are a semiprimary Noetherian ring and a finitely generated module; that
  case follows, since such a ring is semiperfect and such a module is finitely presented
  (`Module.finitePresentation_of_finite`).

**Checks.**

- `ℤ` is not semiperfect (`TauCeti.not_isSemiperfectRing_int`): the kernel of a projective cover
  `P → ℤ ⧸ 2` would lie in `Module.jacobson ℤ P = J • P = 0`, so `ℤ ⧸ 2` would be projective
  ([Sandomierski, Lemma 2, p. 205]).
- `PowerSeries k` is local, so semiperfect, and the cover of `k` is `PowerSeries k → k`.
- For the upper triangular algebra `T₂(k)`, `T₂(k) = T e₁₁ × T e₂₂` is the decomposition of
  item (2), and the two simple modules have covers `T e₁₁` and `T e₂₂`.

*Needs:* Tau Ceti `TauCeti.IsSemiperfectRing`, the idempotent results listed in "From Tau Ceti",
`TauCeti.IsProjectiveCover` and its API, `TauCeti.FiniteProjectivePresentation`,
`TauCeti.IsMinimalProjectivePresentation`; Mathlib `IsCompactElement`, `Submodule.fg_iff_compact`,
`isSimpleModule_iff_isCoatom`, `Module.jacobson`.

TauCetiProject/TauCeti#38013 contains a version of the items of 4.2.

### 4.3 Left perfect rings

(`TauCeti.IsLeftPerfectRing A`), a class with fields
`isSemisimpleRing : IsSemisimpleRing (A ⧸ Ring.jacobson A)` and
`isLeftTNilpotent : IsLeftTNilpotent (Ring.jacobson A : Set A)`. Right perfect is
`IsLeftPerfectRing Aᵐᵒᵖ`. API:

- instances `IsSemiprimaryRing A → IsLeftPerfectRing A`
  (`TauCeti.IsLeftPerfectRing.of_isSemiprimaryRing`; [Lam-FC, (23.19), p. 353]; with
  `TauCeti.IsSemiprimaryRing.mulOpposite` also for `Aᵐᵒᵖ`) and
  `IsLeftPerfectRing A → TauCeti.IsSemiperfectRing A`
  (`TauCeti.IsLeftPerfectRing.isSemiperfectRing`; the radical is nil, so idempotents lift by
  `exists_isIdempotentElem_eq_of_ker_isNilpotent`; [Lam-FC, (23.19)]);
- surjective images, in particular quotients by two-sided ideals and ring isomorphisms
  (`TauCeti.IsLeftPerfectRing.of_surjective`; [Lam-FC, (24.19), p. 365]; [AF, 28.7, p. 318]).

**Checks.**

- `A = k[x₀, x₁, …] ⧸ (xᵢxⱼ)` (on `MvPolynomial ℕ k`) is semiprimary (`J² = 0`, `A ⧸ J = k`),
  hence perfect, and not Noetherian.
- `A = k[x₁, x₂, …] ⧸ (xᵢ^{i+1}, xᵢxⱼ for i ≠ j)` is perfect but not semiprimary: `J` is not
  nilpotent because `xₙⁿ ≠ 0`, and it is T-nilpotent because an element of `J` involves only
  finitely many variables, so a product `a₀ ⋯ aₙ₋₁` of elements of `J` vanishes once `n` exceeds
  the largest variable index in `a₀` (an instance of [Bass, §3, Example (2), p. 475]).
- Lam's ring: in `Module.End k (ℕ →₀ k)`, let `J` be the endomorphisms with finite matrix
  supported strictly above the diagonal, and `R = k · 1 + J`. Then `R` is local,
  `IsLeftPerfectRing Rᵐᵒᵖ` holds and `IsLeftPerfectRing R` fails: the products
  `E₀₁E₁₂ ⋯ Eₙ₋₁,ₙ = E₀ₙ` never vanish ([Lam-FC, (23.22), p. 356]).
- `PowerSeries k` is semiperfect and not left perfect (4.1).

### 4.4 Projective covers over left perfect rings

(`TauCeti.IsLeftPerfectRing.exists_isProjectiveCover`). Over a left perfect ring every left
module, in every universe, has a projective cover, in the form of Tau Ceti's
`TauCeti.exists_isProjectiveCover`, which it generalizes from semiprimary rings ([Lam-FC, (24.12)];
[AF, 28.4, (b) ⇒ (a), p. 315]). Route: `M ⧸ J • M` is semisimple
(`TauCeti.isSemisimpleModule_quotient_smul_top`), a direct sum of simple modules; each has a
cover `Ae_α` (4.2); lift `⊕ Ae_α → M ⧸ J • M` to `M`. The lift is onto because `J • M` is
superfluous in `M` (4.1), and its kernel lies in `J • P`, which is superfluous in `P` (4.1;
`TauCeti.isProjectiveCover_mkQ_iff_le_jacobson`).

### 4.5 Bass's Theorem P

(`TauCeti.isLeftPerfectRing_tfae (A : Type u) [Ring A]`). The following are equivalent:

1. `IsLeftPerfectRing A`;
2. every left module `M : Type u` has a projective cover (Convention 12);
3. every flat left module `M : Type u` is projective;
4. `WellFoundedLT {I : Submodule Aᵐᵒᵖ A // I.IsPrincipal}`: the principal right ideals satisfy
   the descending chain condition;
5. `flatDimension M = projectiveDimension M` for every `M : ModuleCat.{u} A`.

Sources: [Bass, Theorem P, pp. 467–468], whose items (1), (2), (6) and (3) are (1), (2), (4)
and (5) here; [AF, 28.4, pp. 315–317], left-handed as here; [Lam-FC, (24.18), p. 365, and
(24.25), p. 369], right-handed. Route ([Lam-FC], mirrored):

- (1) ⇒ (2) is 4.4.
- (2) ⇒ (1): simple modules have covers, so `A` is semiperfect (`TauCeti.isSemiperfectRing_tfae`,
  4.2). A nonzero module `M` with a cover `P → M` has `J • M ≠ M`, because
  `J • P = Module.jacobson A P ≠ P` (4.2); so `J` is left T-nilpotent by 4.1.
- (1) ⇒ (3): take a cover `P → M` with kernel `K`; then `K ≤ Module.jacobson A P = J • P`
  (`TauCeti.IsProjectiveCover.ker_le_jacobson`, 4.2). Flatness of `M` gives
  `K = K ⊓ J • P = J • K` (2.3), so `K = 0` by 4.1.
- (3) ⇒ (4): Bass's flat module (2.3).
- (4) ⇒ (1): if `a₀ ⋯ aₙ A = a₀ ⋯ aₙ₊₁ A` with `aₙ₊₁ ∈ J`, then
  `a₀ ⋯ aₙ (1 - aₙ₊₁ r) = 0` for some `r`, and `1 - aₙ₊₁ r` is a unit; so `J` is left
  T-nilpotent. The ring `A ⧸ J` inherits the chain condition and has zero radical, so it is
  semisimple (`TauCeti.isSemisimpleRing_of_wellFoundedLT_isPrincipal`: a ring with zero Jacobson
  radical and the descending chain condition on principal right ideals is semisimple; [Lam-FC,
  (4.14)], cited in the proof of (24.25), not read).
- (3) ⇔ (5): flat dimension is at most projective dimension (3.1). Given (3), if
  `flatDimension M = n`, the `n`-th syzygy of a projective resolution is flat (dimension shifting),
  hence projective, so `projectiveDimension M ≤ n` ([Lam-LMR, (5.70), p. 187]). Conversely (5)
  at a flat module gives projective dimension `≤ 0`.

### 4.6 Global dimension of perfect rings

- (`TauCeti.globalDimension_eq_weakGlobalDimension_of_isLeftPerfectRing`) For
  `[IsLeftPerfectRing A]` and `[Small.{v} A]`, `globalDimension A = weakGlobalDimension A`
  (4.5 (5), in the universe `v` through 4.4; [Lam-LMR, (5.70), p. 187]).
- (`TauCeti.globalDimension_mulOpposite_of_isLeftPerfectRing`) For `[IsLeftPerfectRing A]` and
  `[IsLeftPerfectRing Aᵐᵒᵖ]`, `globalDimension Aᵐᵒᵖ = globalDimension A` (with 3.2). In
  particular, for every semiprimary ring the left, right and weak global dimensions agree, with no
  Noetherian hypothesis ([Au, Cor. 9, p. 73]; [Lam-LMR, (5.71), p. 188]).

**Checks.**

- `ℤ` is not semiperfect (4.2), so not perfect; `ℚ` is flat and not projective.
- `PowerSeries k` is local, hence semiperfect, and not left perfect; Bass's module for the
  constant sequence `X` is the Laurent series field, flat and not projective.
- `k[ε]/(ε²)` is semiprimary, hence perfect; its modules have equal flat and projective dimension,
  and global dimension `⊤ = ` weak global dimension.
- The second commutative ring of 4.3 satisfies the descending chain condition on principal ideals
  by Theorem P, although it is not Noetherian.
- Lam's ring `R` of 4.3: `E₀₁R ⊋ E₀₂R ⊋ ⋯` (the strict inclusions show directly that (4) fails),
  and Bass's module for `E₀₁, E₁₂, E₂₃, …` is a flat left `R`-module that is not projective.

*Needs:* Layers 2 and 3; 4.1–4.4; Tau Ceti `TauCeti.IsSemiperfectRing`,
`TauCeti.IsProjectiveCover`, `TauCeti.IsProjectiveCover.ker_le_jacobson`,
`TauCeti.exists_isProjectiveCover`, `TauCeti.isSemisimpleModule_quotient_smul_top`; Mathlib
`WellFoundedLT`, `Submodule.IsPrincipal`, `IsSemiprimaryRing`,
`exists_isIdempotentElem_eq_of_ker_isNilpotent`.

### Examples

Semiprimary rings (Artin algebras among them) are perfect; the commutative ring of 4.3 is perfect
and not semiprimary; Lam's ring is perfect on one side only; `PowerSeries k` is semiperfect and not
perfect; `ℤ` is not semiperfect.

### Dependencies

4.1 and 4.2 need only Mathlib and Tau Ceti; 4.3 needs 4.1; 4.4 needs 4.1, 4.2 and 4.3; 4.5 needs
Layers 2 and 3 and 4.1–4.4; 4.6 needs 4.5 and 3.2.

## Downstream consumers

- [ArtinAlgebras](../RepresentationTheory/ArtinAlgebras/README.md), §7.2: Auslander's theorem
  (3.3) gives the left-right symmetry of global dimension for Noetherian rings through weak
  dimension, and 4.6 gives it for semiprimary rings without a Noetherian hypothesis.
- ArtinAlgebras, §7.5, the forward direction: for an additive generator `M` of `mod A`, every
  finitely presented right `End_A(M)`-module has projective dimension at most two, and
  `TauCeti.globalDimension_le_of_forall_finitePresentation_mulOpposite` (3.3) turns this into
  `globalDimension (Module.End A M) ≤ 2` using only that `End_A(M)` is left Noetherian.
- ArtinAlgebras, §§4.1–4.2, through Tau Ceti's
  `LinearMap.auslanderReitenTransposeTensorEquivCokernel`
  (`Tr M ⊗_A N` as the cokernel of `Hom_A(P₀, N) → Hom_A(P₁, N)`) and
  `ModuleCat.tensorHomCokernelEquivProjectiveStableHom` (the stable Hom as the cokernel of
  `Hom_A(M, A) ⊗_A N → Hom_A(M, N)`): with Layer 1, for finitely presented `M`,
  `Tor_1^A(Tr M, N)` is the stable `Hom_A(M, N)` (Auslander–Bridger; not read).
- ArtinAlgebras, Layer 4: the Auslander-Reiten translate is built from finite minimal projective
  presentations (`TauCeti.FiniteProjectivePresentation.exists_isMinimal`); 4.2 provides them for
  finitely presented modules over any semiperfect ring.
- Hoshino's flat-dominant dimension ([Ho], [Xi, §1], as cited in ArtinAlgebras §7.3) asks the
  terms of a minimal injective coresolution to be flat; ArtinAlgebras leaves it out because
  flatness over noncommutative rings is missing. Layer 2 supplies that flatness.

## Sources and locators

- [AF] F. W. Anderson, K. R. Fuller, *Rings and Categories of Modules*, 2nd ed., Graduate Texts in
  Mathematics 13, Springer (1992). §28: left and right T-nilpotence, p. 314; Lemma 28.3,
  pp. 314–315; Theorem 28.4 (Bass), pp. 315–317; Corollary 28.7, p. 318.
- [Au] M. Auslander, *On the dimension of modules and algebras III. Global dimension*, Nagoya Math.
  J. 9 (1955), 67–77. Thm. 1, p. 68; weak dimensions, Thm. 4 and Cor. 5, p. 70; Cor. 8, p. 72;
  Cor. 9, p. 73.
- [Bass] H. Bass, *Finitistic dimension and a homological generalization of semi-primary rings*,
  Trans. Amer. Math. Soc. 95 (1960), 466–488. T-nilpotence, p. 466; Theorem P, pp. 467–468;
  Lemma 1.1, p. 468; Theorem 2.1, p. 471; §3, Examples, p. 475.
- [Harada] M. Harada, *Perfect categories I*, Osaka J. Math. 10 (1973), 329–341. Introduction,
  pp. 329–330: perfect Grothendieck categories, and Theorem P for the functor category `(C, Ab)`
  of a small additive category `C`. The final section, where the theorem is proved, and parts
  II–IV were not read.
- [Krause] H. Krause, *Krull-Schmidt categories and projective covers*, Expo. Math. 33 (2015),
  535–549; arXiv:1410.2822. Lemma 3.6 and Proposition 4.1, read in the arXiv TeX source; the
  journal page range and numbering were not checked.
- [Lam-FC] T. Y. Lam, *A First Course in Noncommutative Rings*, 2nd ed., Graduate Texts in
  Mathematics 131, Springer (2001). (23.13)–(23.16), pp. 351–352; (23.19), p. 353; (23.20),
  p. 354; (23.22), p. 356; (24.7), p. 360; (24.12), p. 361; (24.16), p. 364; (24.18)–(24.20),
  p. 365; (24.22), p. 366; (24.23)–(24.24), pp. 367–368; (24.25), pp. 369–370. (4.14) is cited in
  the proof of (24.25) and was not read.
- [Lam-LMR] T. Y. Lam, *Lectures on Modules and Rings*, Graduate Texts in Mathematics 189,
  Springer (1999). (4.9) and (4.12), p. 125; (4.13), p. 126; (4.30), p. 133; (5.53)–(5.57),
  pp. 183–184; (5.58)–(5.59), p. 184; (5.62b) and (5.63), p. 185; (5.69)–(5.70), p. 187; (5.71),
  p. 188. (2.33), cited in (5.62b), was not read.
- [Lambek] J. Lambek, *A module is flat if and only if its character module is injective*, Canad.
  Math. Bull. 7 (1964), 237–243. Theorem, p. 239; Proposition 1 and `Ext(N, M*) ≅ Tor(N, M)*`,
  p. 241.
- [ML] S. Mac Lane, *Categories for the Working Mathematician*, 2nd ed., Graduate Texts in
  Mathematics 5, Springer (1998). IX.6, p. 226: coends; the tensor product over a ring as a coend,
  with modules as additive functors on the one-object category; the tensor product of functors.
- [Mitchell] B. Mitchell, *Rings with several objects*, Adv. Math. 8 (1972), 1–161. §3,
  pp. 15–18: functor categories, representables, free and finitely presented functors; §6,
  pp. 26–27: the tensor product `F ⊗_C G`, its value on representables (1), the adjunction (2),
  preservation of colimits in both variables, the swap as a definition, the explicit quotient, and
  cogenerating injectives from `ℚ ⧸ ℤ`; §10, Prop. 10.1 and Cor. 10.2, p. 47: projectives are
  retracts of free functors, and tensoring with a projective is exact; §11, pp. 50–52:
  `K`-categories, `K`-linear functors to `K`-modules as additive functors to abelian groups
  (p. 51), the tensor product over `K` and its independence of `K` (p. 52). Mitchell writes
  morphisms on the right and his modules are covariant; the statements are mirrored here.
- [Sandomierski] F. L. Sandomierski, *On semiperfect and perfect rings*, Proc. Amer. Math. Soc. 21
  (1969), 205–207. Proposition 1 (d) and Lemma 2, p. 205; Theorem 4, p. 206 (stated for right
  modules).
- [Weibel] C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994). Thm. 2.7.2 (balance of `Tor`); not read.
- [Wisbauer] R. Wisbauer, *Foundations of Module and Ring Theory*, Gordon and Breach (1991).
  18.5 (1), p. 152 (a projective module that maps onto every simple module is a generator; the
  argument of the generation step), stated in `σ[M]`; 19.7, p. 161 (projective covers of simple
  modules have local endomorphism rings).
- H. Cartan, S. Eilenberg, *Homological Algebra*, Princeton University Press (1956). Ch. VI,
  Exer. 3 (flat and projective dimension of finite modules over a Noetherian ring), cited through
  [Au, p. 70]; not read.
- M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969). `Tor₁` of the
  transpose; not read.
- [Ho] M. Hoshino, *On dominant dimension of Noetherian rings*, Osaka J. Math. 26 (1989), 275–280;
  [Xi] C. Xi, *Frobenius bimodules and flat-dominant dimensions*, arXiv:1903.07921v1. Cited for
  the consumer only, as in ArtinAlgebras.
