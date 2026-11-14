# Roadmap: Flatness and homological dimensions of noncommutative rings

**Summary.** Mathlib has flat modules, `Tor` and the character-module test for flatness only over
commutative rings. Tau Ceti has the tensor product `M ⊗_A N` of a right and a left module over an
arbitrary ring (`TauCeti.BalancedTensorProduct`), finitely presented functors on a preadditive
category (`mod C`), the global dimension of left modules, projective covers and semiperfect rings.
This roadmap is the home of flat modules over noncommutative rings and of flat functors over
preadditive categories. It develops the homological algebra of flatness over a preadditive category
`C`; a ring `A` is the one-object case `SingleObj A`. Layer 0 lays the foundations: the abelian
category `Mod C` of additive functors; the identification of `A`-modules with modules over
`SingleObj A`; the tensor product `F ⊗_C G` as a coend, linear over a commutative ring `R`, with its
adjunctions, right exactness, projective factors and swap; duals `Hom_R(-, E)`; and the native ring
API of `M ⊗_A N`. On these the roadmap builds `Tor` over `C` as a left derived functor, with its
long exact sequences, its balance, `Tor` of the Auslander–Bridger transpose and its duality with
`Ext`, and compares a category with finitely many objects with its category algebra. Layer 2 treats
flat modules and flat functors: the ideal test, the `Tor` and Lambek tests with a Baer criterion for
`Mod C`, the Lazard characterizations (equational criterion, factorization, filtered colimits of
finite sums of representables, purity) and the projectivity of finitely presented flat modules, flat
= left exact, flat = cohomological on triangulated categories, Crawley-Boevey's representation of
finitely accessible additive categories, Bass's flat module of a chain, and closure properties.
Layer 3 treats flat dimension, the global dimension of an abelian category, the weak global
dimension with its left-right symmetry, and Auslander's theorem that a left Noetherian category (or
ring) has equal left global and weak global dimension. Then come projective covers over
semiperfect rings and the characterization of semiperfect rings by projective covers; and left
perfect rings. The summit is **Bass's Theorem P**: for a ring `A` with Jacobson radical `J`, the
following are equivalent: `A ⧸ J` is semisimple and `J` is left T-nilpotent; every left module has a
projective cover; every flat left module is projective; the principal *right* ideals satisfy the
descending chain condition; every left module has equal flat and projective dimension. For small
preadditive categories the summit is **Simson's Theorem 5.4** ([Simson, Thm. 5.4, p. 108]): every
flat left module is projective exactly when every left module has a projective cover, exactly when
`J(C)` is left T-nilpotent and `C ⧸ J(C)` is semisimple, exactly when every countable inverse system
in `C` is factorizable; these are the perfect categories ([Harada]). Layers 0–3 are
category-primary; Layer 4 is stated for rings for now and is to be converted to that design.

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
- `Tor` over a preadditive category and over an arbitrary ring as a left derived functor, its long
  exact sequences, its balance, the formula `stable Hom(X, N) ≅ Tor_1(Tr X, N)`, its duality with
  `Ext`, the comparison with Mathlib's
  `CategoryTheory.Tor` over a commutative ring, change of base, `Tor₁` of two cyclic modules, and
  the comparison of a category with finitely many objects with its category algebra (Layer 1);
- flat modules and flat functors over a preadditive category and over an arbitrary ring: the ideal
  test, the `Tor` and Lambek tests, a Baer criterion for `Mod C`, `Tor` and filtered colimits, the
  Lazard characterizations and purity, projectivity of finitely presented flat modules, flat = left
  exact, the triangulated case, Crawley-Boevey's representation theorem, Bass's flat module of a
  chain, closure properties, and the bridge to Mathlib's ind-objects (Layer 2);
- flat dimension; the global dimension of an abelian category, Auslander's lemma on cyclic
  modules and universe independence; the weak global dimension, its left-right symmetry and its
  bounds by the global dimensions; the `FP_∞` lemma and Auslander's theorem for left Noetherian
  categories and rings; kernels of flat modules and countably presented flat modules (Layer 3);
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
  it, `BalancedFlat` is replaced by `Module.Flat`. Tau Ceti's `TauCeti.flatModuleFilteredFree`
  (Lazard's theorem in one direction, for commutative rings) becomes a corollary of 2.3.
- Flatness here is flatness as a module. Intrinsic flatness inside the category of flat modules
  ([CI]) is not developed.
- [Operator K-theory](../OperatorKTheory/README.md), §8.2, owns the computations of `Ext` and
  `Tor` over `ℤ` (free presentations, cyclic groups, universal coefficients). The comparison of
  1.6 covers every commutative ring; no other `ℤ`-specific computation is done here.
- [Derived and module algebra](../DerivedModuleAlgebra/README.md) owns the derived tensor
  product and `Tor` amplitude over commutative rings. This roadmap uses derived categories only
  through Mathlib's `Abelian.Ext` (1.5).
- [Krull-Schmidt categories and Auslander-Reiten theory of Artin
  algebras](../RepresentationTheory/ArtinAlgebras/README.md), §7.2, owns the statements comparing
  left and right global dimension and the formula for semiprimary rings. Their proofs on main
  (`TauCeti/RingTheory/GlobalDimension/MulOpposite.lean`, through character modules) are replaced
  by the weak-dimension route of 3.4 once Layers 0–3 exist; the statements are kept (refactor
  consumer, 3.4). Layer 4 gives the route through perfect rings and does not restate them.
- Tau Ceti's ring `TauCeti.globalDimension` becomes the case `ModuleCat A` of the global dimension
  of an abelian category (3.2): a refactor of main, with no compatibility shims.
- Semiperfect rings are Tau Ceti's `TauCeti.IsSemiperfectRing`, with its idempotent
  characterization. This roadmap owns their projective covers and their characterization by
  projective covers (4.2). Minimal projective presentations are Tau Ceti's
  `TauCeti.IsMinimalProjectivePresentation`; this roadmap owns only their existence over a
  semiperfect ring (4.2).
- Outside this roadmap: the tensor product of additive categories and functors of several variables
  ([Mitchell, §2]); Morita theory for functor categories, beyond the finite-object comparison of
  1.7; the conditions of Theorem P on direct limits ([Bass, Theorem P (4), (5)]); Chase's theorem,
  coherent rings and products of flat modules (pointers in 2.6; kernels are in 3.5); flat covers
  (pointers in 2.4); purity beyond the purity test of 2.3 (pure-injective modules, pure global
  dimension); flat Mittag-Leffler modules; faithful flatness over noncommutative rings; the
  conditions on maximal submodules and socles ([AF, 28.4 (c), (f)]), on finitely generated
  submodules (Björk) and on principal left ideals with the ascending chain condition (Jonah);
  finitistic dimensions ([Bass, Part II]); `Tor` of bimodules and its module structure over a base
  ring; and Hoshino's flat-dominant dimension.

Suggested homes in Tau Ceti: `TauCeti/CategoryTheory/Preadditive/ModCat/` (0.1, 0.3–0.5, 0.7),
`TauCeti/CategoryTheory/Preadditive/SingleObj.lean` (0.2),
`TauCeti/LinearAlgebra/TensorProduct/Balanced/` (0.6),
`TauCeti/CategoryTheory/Preadditive/ModCat/Tor/` (1.1–1.6), `TauCeti/Algebra/Homology/BalancedTor/`
(ring `Tor`), `TauCeti/CategoryTheory/Preadditive/CategoryAlgebra.lean` (1.7),
`TauCeti/CategoryTheory/Preadditive/ModCat/Flat/` (2.1–2.6),
`TauCeti/CategoryTheory/Preadditive/ModCat/Baer.lean` (2.2), `TauCeti/RingTheory/Flat/Balanced/`
(ring items of Layer 2), `TauCeti/CategoryTheory/Abelian/GlobalDimension.lean` (3.2),
`TauCeti/CategoryTheory/Preadditive/ModCat/Dimension/` (3.1, 3.3–3.5),
`TauCeti/RingTheory/GlobalDimension/Weak.lean` (ring items of Layer 3),
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
6. `Tor^C_n(F, G)` and `Tor_n^A(M, N)` have the right module first, are derived in the left-module
   variable, and take values in `ModuleCat R` (1.1). Over a commutative ring, ring `Tor` is compared
   directly with Mathlib's `CategoryTheory.Tor` (1.6). Flatness (2.1) is defined with `R = ℤ` and
   does not depend on `R`; Layer 3 uses `R = ℤ` as well. By the independence of `R` (0.3, 0.6) this
   does not change the underlying groups. Modules live in `ModuleCat.{v} A` and `ModuleCat.{v} Aᵐᵒᵖ`
   with `[Small.{v} A]`, as for `TauCeti.globalDimension`; the instance `Small.{v} Aᵐᵒᵖ` is part of
   1.1.
7. Dimensions take values in `WithBot ℕ∞`, with `⊥` exactly for the zero module, as Mathlib's
   `CategoryTheory.projectiveDimension` and Tau Ceti's `TauCeti.globalDimension`. The global
   dimension of an abelian category is `TauCeti.Abelian.globalDimension` (3.2); for `C` the right
   global dimension is that of `ModCat C`, the left one that of `LeftModCat C`.
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
`TauCeti.Algebra.Category.ModuleCat.Flat.FilteredFree`,
`TauCeti.Algebra.Category.ModuleCat.Projective.TensorHom`,
`TauCeti.Algebra.Module.AuslanderReiten.TensorCokernel`,
`TauCeti.Algebra.Module.CharacterModule.MulOpposite`,
`TauCeti.CategoryTheory.FinitelyPresentedFunctor.Basic` and
`TauCeti.RingTheory.MatlisDuality.Basic`, which need Tau Ceti at that commit or later.

### From Mathlib

- Functor categories and modules over a category: `CategoryTheory.additiveFunctor`,
  `CategoryTheory.AdditiveFunctor` (`C ⥤+ D`), `ObjectProperty.FullSubcategory`,
  `ObjectProperty.lift`, `ObjectProperty.ιOfLE`; the closure classes `ObjectProperty.ContainsZero`,
  `ObjectProperty.IsClosedUnderKernels`, `ObjectProperty.IsClosedUnderCokernels`,
  `ObjectProperty.IsClosedUnderFiniteProducts`, `ObjectProperty.IsClosedUnderColimitsOfShape` with
  `hasColimitsOfShape_of_closedUnderColimits`, and the abelian instance for full subcategories
  (`Mathlib/CategoryTheory/Abelian/Subcategory.lean`);
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
  `CategoryTheory.HasProjectiveResolutions`, `ModuleCat.enoughProjectives`,
  `CategoryTheory.Functor.mapHomologicalComplex`, `HomologicalComplex.homologyFunctor`,
  `CategoryTheory.Functor.whiskeringLeft`. Named only as a future refactor path (1.1):
  `CategoryTheory.Functor.HasLeftDerivedFunctor`, `CategoryTheory.Functor.totalLeftDerived`,
  `CategoryTheory.LocalizerMorphism.IsLeftDerivabilityStructure`.
- `Ext`: `CategoryTheory.Abelian.Ext`, `CategoryTheory.HasExt`,
  `CategoryTheory.hasExt_of_enoughProjectives`, the instance `Module R (Ext X Y n)` for an
  `R`-linear category (`Mathlib/Algebra/Homology/DerivedCategory/Ext/Linear.lean`),
  `CategoryTheory.ProjectiveResolution.extEquivCohomologyClass`
  (`Mathlib/CategoryTheory/Abelian/Projective/Ext.lean`), and the scoped instance
  `ModuleCat.Algebra.instLinear`.
- Homology: `CategoryTheory.ShortComplex.ShortExact.δ` with `homology_exact₁`, `homology_exact₂`
  and `homology_exact₃`; `HomologicalComplex₂` and `HomologicalComplex₂.total`.
- Flat functors (Layer 2): `Subobject`, `imageSubobject`, `Limits.Sigma.desc`, `cokernel`,
  `CategoryTheory.Injective`, `PreservesFilteredColimitsOfSize`, the `AB5` instances
  (`Mathlib/Algebra/Category/Grp/AB.lean`); `IsFinitelyPresentable` and
  `ObjectProperty.isFinitelyPresentable` (`Mathlib/CategoryTheory/Presentable/Finite.lean`),
  `IsFinitelyAccessibleCategory` (`Mathlib/CategoryTheory/Presentable/LocallyPresentable.lean`;
  not `IsLocallyFinitelyPresentable`); `IsFiltered`, `IsCofiltered`, `CostructuredArrow`,
  `Functor.Elements`, `Functor.isCofiltered_elements`, `Cocone`, `IsColimit`, `colimit`,
  `Functor.DenseAt`, `Retract`, `Functor.ofSequence`, `Functor.ofOpSequence`; `IsIndObject` with
  `isIndObject_iff` and `isIndObject_iff_preservesFiniteLimits`; `PreservesFiniteLimits`,
  `HasCokernels`, `HasFiniteBiproducts`; `Functor.IsHomological` with the scoped instances of
  `Pretriangulated.Opposite`; `RepresentablyFlat` (named only to mark the difference).
- Morita equivalence: `IsMoritaEquivalent` and `MoritaEquivalence`
  (`Mathlib/RingTheory/Morita/Basic.lean`), for rings only.
- Dimensions: `CategoryTheory.projectiveDimension`, `CategoryTheory.HasProjectiveDimensionLT`,
  `CategoryTheory.HasProjectiveDimensionLE`, `projectiveDimension_le_iff`,
  `projectiveDimension_eq_bot_iff`, `CategoryTheory.injectiveDimension`,
  `CategoryTheory.HasInjectiveDimensionLE`; `HomologicalComplex.opcycles`, `QuasiIso`,
  `ChainComplex.single₀`; `CategoryTheory.IsNoetherianObject`
  (`Mathlib/CategoryTheory/Subobject/NoetherianObject.lean`); `IsCardinalPresentable` with
  `Cardinal.isRegular_aleph_one`. Mathlib has no global dimension, flat dimension or weak global
  dimension, and no finitely generated objects of a category.
- Checks of Layer 3: `DualNumber`, `Matrix.blockTriangularSubalgebra`, and `CategoryTheory.Free`
  (the `R`-linear category on a category, `Mathlib/Algebra/Category/ModuleCat/Adjunctions.lean`).
- Commutative counterparts: `TensorProduct` with `LinearMap.rTensor` and `LinearMap.lTensor`;
  `CategoryTheory.Tor` and `CategoryTheory.Tor'` on `ModuleCat R`; `Module.Flat` with
  `Module.Flat.iff_characterModule_injective`, `Module.Flat.iff_forall_isTrivialRelation`,
  `Module.Flat.exists_factorization_of_finitePresentation` and
  `Module.Flat.projective_of_finitePresentation`;
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
- Global dimension: `TauCeti.globalDimension` with `TauCeti.globalDimension_def`,
  `TauCeti.globalDimension_le_iff_hasProjectiveDimensionLE`, `TauCeti.globalDimension_le_tfae`,
  `TauCeti.globalDimension_eq_iSup_cyclic`, `TauCeti.globalDimension_eq_iSup_finite`,
  `TauCeti.globalDimension_eq_globalDimension`, `TauCeti.globalDimension_eq_bot_iff`,
  `TauCeti.globalDimension_eq_zero_of_isSemisimpleRing` and
  `TauCeti.globalDimension_eq_one_of_isPrincipalIdealRing` (`TauCeti.RingTheory.GlobalDimension`);
  the refactor consumers `TauCeti.globalDimension_le_globalDimension_mulOpposite`,
  `TauCeti.globalDimension_mulOpposite`, `TauCeti.globalDimension_mulOpposite_of_moduleFinite` and
  `TauCeti.hasInjectiveDimensionLE_characterModule_iff`
  (`TauCeti.RingTheory.GlobalDimension.MulOpposite`);
  `CategoryTheory.Equivalence.projectiveDimension_functor_obj`
  (`TauCeti.Algebra.Homology.Ext.Equivalence`).
- Left derived functors: `CategoryTheory.NatTrans.leftDerived_add`,
  `CategoryTheory.Functor.isZero_leftDerived_succ` and
  `CategoryTheory.ShortComplex.ShortExact.leftDerivedOneIsoKernel`
  (`TauCeti.CategoryTheory.Abelian.LeftDerived`); the acyclic assembly lemma
  `HomologicalComplex₂.quasiIso_totalAugmentation_of_rows`
  (`TauCeti.Algebra.Homology.TotalComplex.Basic`) and the instance
  `HomologicalComplex₂.totalComplexShapeSymmetryDownNat`
  (`TauCeti.Algebra.Homology.ComplexShape.Signs`).
- `Tor` over commutative rings: the results on Mathlib's `Tor` and `Tor'` in
  `TauCeti.Algebra.Category.ModuleCat.Monoidal.Tor` and `TauCeti.CategoryTheory.Monoidal.Tor`
  (1.6).
- Flat modules over commutative rings (2.3): `TauCeti.FiniteFreeModuleCat`,
  `TauCeti.finiteFreeModuleInclusion`, `TauCeti.FiniteFreeOver` and `TauCeti.flatModuleFilteredFree`
  (`TauCeti.Algebra.Category.ModuleCat.Flat.FilteredFree`), the last one a refactor consumer.
- Quivers and Morita theory (1.7): `TauCeti.quiverRepEquivalence`
  (`TauCeti.RepresentationTheory.Quiver.Representation.AsModule`), as the pattern;
  `TauCeti.Quiver.Kronecker.upperTriangularAlgEquiv`
  (`TauCeti.RepresentationTheory.Quiver.Kronecker.UpperTriangular`);
  `IsIdempotentElem.isMoritaEquivalent_corner` (`TauCeti.RingTheory.Morita.Corner`).
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
- The transpose and stable `Hom` (1.4): `TauCeti.AuslanderReitenTranspose`
  (`TauCeti.Algebra.Module.AuslanderReiten.Transpose`),
  `LinearMap.auslanderReitenTransposeTensorEquivCokernel` with
  `auslanderReitenTransposeTensorEquivCokernel_map`
  (`TauCeti.Algebra.Module.AuslanderReiten.TensorCokernel`),
  `TauCeti.ExactStructure.abelian`, `TauCeti.ExactStructure.projectiveStableFunctor` and
  `ModuleCat.tensorHomCokernelEquivProjectiveStableHom`
  (`TauCeti.Algebra.Category.ModuleCat.Projective.TensorHom`).
- Projective presentations: `TauCeti.FiniteProjectivePresentation` with `ofFinitePresentation`
  (`TauCeti.Algebra.Module.Projective.FinitePresentation`);
  `TauCeti.IsMinimalProjectivePresentation` and
  `TauCeti.IsProjectiveCover.isMinimalProjectivePresentation`
  (`TauCeti.Algebra.Module.MinimalProjectivePresentation.Basic`);
  `TauCeti.FiniteProjectivePresentation.exists_isMinimal`, for semiprimary Noetherian rings
  (`...MinimalProjectivePresentation.Finite`).

### From other roadmaps

None.

### From open pull requests

TauCetiProject/TauCeti#37151 (Auslander's defect formula, open):
`Function.Exact.contravariantDefectEquivKer` and `LinearMap.homCokernelMap`, for the ring form of
1.4. The roadmap does not depend on it; the ring form waits for the merge or goes through the
categorical form. The defect formula itself
(`Function.Exact.dualContravariantDefectEquivCovariantDefect`) is not a target here.

TauCetiProject/TauCeti#40807 (ArtinAlgebras §7.5, open): a consumer, not a supplier. It uses the
statements of `TauCeti.RingTheory.GlobalDimension.MulOpposite`, whose proofs 3.4 replaces; the left
bound of 3.4 strengthens what it needs.

## How to read the build

| Layer | Construction | Principal outputs |
| --- | --- | --- |
| [0](#layer-0-modules-over-a-preadditive-category-and-their-tensor-product) | Modules over a preadditive category | `Mod C`, rings as one-object categories, tensor product over `C`, projective factors, swap, ring API, duals |
| [1](#layer-1-tor) | `Tor` | Left derived functor, long exact sequences, balance, `Tor` of the transpose, `Tor`–`Ext` duality, comparisons, `Tor₁` of cyclic modules, category algebras |
| [2](#layer-2-flat-modules-and-flat-functors) | Flat modules and flat functors | Ideal test, `Tor` and Lambek tests, Baer criterion, Lazard block, purity, flat = left exact, triangulated case, representation theorem, Bass's module, closure |
| [3](#layer-3-flat-dimension-global-and-weak-global-dimension) | Dimensions | Flat dimension, global dimension of an abelian category, Auslander's lemma, weak global dimension, symmetry, `FP_∞` lemma, Auslander's theorem, kernels and countably presented flat modules |
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
  makes `Mod C` and the left modules abelian. They are also closed under colimits
  (`ObjectProperty.IsClosedUnderColimitsOfShape`; colimits commute with finite biproducts), so
  `Mod C` has the colimits of `AddCommGrpCat` (Layer 2 uses them).
- **Representables** (`TauCeti.ModCat.yoneda : C ⥤ ModCat.{v} C`, from Mathlib's
  `preadditiveYoneda`; `TauCeti.LeftModCat.coyoneda`). `Hom(-, X)` is projective, since
  `Hom(Hom(-, X), F) ≅ F(X)` by Yoneda. When `C` is `EssentiallySmall.{w}`, every module is a
  quotient of a coproduct of representables (lifted by `ULift` when `w ≠ v`), so `Mod C` has
  enough projectives ([Mitchell, §3, pp. 15–18]); so do the left modules, through `Hom(X, -)`.
- **`R`-linear structure** (`TauCeti.Functor.objModule`, `TauCeti.Functor.toModuleCat`, and an
  instance `Linear R (ModCat C)`). For `Linear R C`, `r` acts on `F(c)` by `F(r • 𝟙 c)`; every
  `F(f)` is then `R`-linear, so `F` becomes a functor to `ModuleCat R`, and every natural
  transformation is `R`-linear. `Mod C` is `R`-linear with `(r • α)_c = r • α_c`, and so are the
  left modules. [Mitchell, §11, p. 51]: for an `R`-linear `C`, the `R`-linear functors to
  `R`-modules are the additive functors to abelian groups.
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
Auslander-Reiten theory. Lambek's criterion with a general injective cogenerator `E` is 2.2 (6); it
follows from the adjunction, already over a commutative base ring in [OR, (1.1), p. 93].

*Needs:* 0.3; Mathlib `IsCoseparator`, `ShortComplex.ShortExact`; Tau Ceti `TauCeti.MatlisDual`.

### Examples

Rings (0.2, 0.6); `k`-linear categories of quivers, whose modules are representations; Tau Ceti's
`mod C` inside `Mod C`. The commutative comparison of 0.6 makes every Mathlib tensor computation an
example of `M ⊗_A N`.

### Dependencies

Mathlib and Tau Ceti only.

## Layer 1: `Tor`

Throughout, `C : Type u` is an `R`-linear category with `Category.{v} C` and
`EssentiallySmall.{w} C`, modules take values in `AddCommGrpCat.{w}`, and `Tor` takes values in
`ModuleCat.{w} R`. There is one `Tor`, derived in the left-module variable. The version that
resolves the right module is `Tor` over `Cᵒᵖ`, read through the swap of 0.5. Items 1.1–1.6 end
with their ring statements.

### 1.1 Definition

(`TauCeti.ModCat.tor R n : ModCat C ⥤ LeftModCat C ⥤ ModuleCat R`.) The object at `F` is
`((ModCat.tensor R).obj F).leftDerived n`, Mathlib's classical `Functor.leftDerived` of
`G ↦ F ⊗_C G`, and maps act by `NatTrans.leftDerived`. This is the shape of Mathlib's
`CategoryTheory.Tor`. It needs projective resolutions of left modules: enough projectives (0.1) and
Mathlib's instance `HasProjectiveResolutions` for abelian categories with enough projectives. API:

- degree zero (`TauCeti.ModCat.torZeroIso : tor R 0 ≅ tensor R`): `Functor.leftDerivedZeroIsoSelf`,
  since `F ⊗_C -` preserves colimits (0.3);
- vanishing (`TauCeti.ModCat.isZero_tor_succ_of_projective`): `Tor_{n+1}(F, G) = 0` for a
  projective left module `G` (`Functor.isZero_leftDerived_obj_projective_succ`);
- computation from any projective resolution `P` of `G` (`TauCeti.ModCat.torObjIsoHomology`):
  `Tor_n(F, G) ≅ H_n(F ⊗_C P)`, Mathlib's `ProjectiveResolution.isoLeftDerivedObj`;
- linearity: additive and `R`-linear in each variable; in `F` through `NatTrans.leftDerived`
  and Tau Ceti's `NatTrans.leftDerived_add`.

**Rings** (`TauCeti.BalancedTor R A n : ModuleCat.{v} Aᵐᵒᵖ ⥤ ModuleCat.{v} A ⥤ ModuleCat.{v} R`),
for an `R`-algebra `A` with `[Small.{v} A]`. Native, as Convention 5 asks: the object at `M` is
`((BalancedTensorProduct.functor R A).obj M).leftDerived n`, the left derived functor of the ring
bifunctor of 0.6. API as above (`TauCeti.balancedTorZeroIso`,
`TauCeti.isZero_balancedTor_succ_of_projective`), and the comparison
(`TauCeti.balancedTorIsoTorSingleObj`) with `Tor` over `SingleObj A` through the equivalences of
0.2, from 0.6's comparison of tensor products: the equivalences preserve projective resolutions.
This item includes the instance `Small.{v} Aᵐᵒᵖ` from `Small.{v} A` (`TauCeti.small_mulOpposite`),
used for resolutions of right modules.

**Future refactor.** Mathlib's `Functor.leftDerived` is the classical construction through the
homotopy category. Mathlib's TODO in `Mathlib/CategoryTheory/Abelian/LeftDerived.lean` is to
redefine it through derived categories and projective derivability structures, in the framework of
`Functor.HasLeftDerivedFunctor`, `Functor.totalLeftDerived` and
`LocalizerMorphism.IsLeftDerivabilityStructure`. When that lands, `tor` follows it; nothing here
depends on the construction beyond the API above.

*Needs:* 0.1, 0.3, 0.6; Mathlib `Functor.leftDerived`, `NatTrans.leftDerived`,
`Functor.leftDerivedZeroIsoSelf`, `Functor.isZero_leftDerived_obj_projective_succ`,
`ProjectiveResolution.isoLeftDerivedObj`, `HasProjectiveResolutions`; Tau Ceti
`NatTrans.leftDerived_add`.

### 1.2 Long exact sequences in the underived variable

For a short exact sequence `0 → F₁ → F₂ → F₃ → 0` of right modules and a projective resolution `Q`
of a left module `G`, the complexes `Fᵢ ⊗_C Q` form a short exact sequence of complexes: termwise,
right exactness (0.3) and the projective factors of 0.4 (`Q_q` projective, so `- ⊗_C Q_q`
preserves monomorphisms). Mathlib's homology sequence of a short exact sequence of complexes
(`ShortComplex.ShortExact.homology_exact₁`, `homology_exact₂`, `homology_exact₃`, with the
connecting map `ShortComplex.ShortExact.δ`) and 1.1's computation from `Q` then give
`δ : Tor_{n+1}(F₃, G) → Tor_n(F₁, G)` (`ShortComplex.ShortExact.torδ`) and exactness at the three
places (`TauCeti.ModCat.tor_exact₁`, `tor_exact₂`, `tor_exact₃`), natural in `G` and in the
sequence.

This is the only long exact sequence proved directly. The one in the derived variable comes from
the balance (1.3). So neither a horseshoe lemma nor a general long exact sequence for
`Functor.leftDerived` is needed; Mathlib has neither.

**Rings** (`ShortComplex.ShortExact.balancedTorδ`, `TauCeti.balancedTor_exact₁`,
`balancedTor_exact₂`, `balancedTor_exact₃`): the same for a short exact sequence of right
`A`-modules, by the same proof with 0.6's projective factors, or through 1.1's comparison.

*Needs:* 0.3, 0.4, 1.1; Mathlib `ShortComplex.ShortExact.δ`, `homology_exact₁`–`homology_exact₃`.

### 1.3 Balance

(`TauCeti.ModCat.torBalanceIso : tor R n ≅ (LeftModCat.toModCatOp C ⋙ tor R n).flip`.)
`Tor^C_n(F, G) ≅ Tor^{Cᵒᵖ}_n(G, F)`, `R`-linear and natural in both variables, where `G` is a right
`Cᵒᵖ`-module and `F` a left `Cᵒᵖ`-module as in 0.5. Route ([Weibel, Thm. 2.7.2, pp. 58–59]): for
projective resolutions `P` of `F` and `Q` of `G`, form the first-quadrant bicomplex `P_p ⊗_C Q_q`.
Its augmented rows `P_p ⊗ Q → P_p ⊗ G` and columns `P ⊗ Q_q → F ⊗ Q_q` are exact, since tensoring
with a projective is exact on both sides (0.3, 0.4). Tau Ceti's
`HomologicalComplex₂.quasiIso_totalAugmentation_of_rows`, applied to the bicomplex and to its flip
(with Tau Ceti's `HomologicalComplex₂.totalComplexShapeSymmetryDownNat`), identifies both
`H_n(F ⊗_C Q)` and `H_n(P ⊗_C G)` with the homology of the total complex; this is Weibel's acyclic
assembly argument ([Weibel, 2.7.3, p. 59]). The swap of 0.5 turns `P ⊗_C G` into `G ⊗_{Cᵒᵖ} P`,
whose homology is `Tor^{Cᵒᵖ}_n(G, F)` by 1.1 over `Cᵒᵖ`.

Consequences:

- higher `Tor` vanishes at a projective right module
  (`TauCeti.ModCat.isZero_tor_succ_of_projective_left`);
- the long exact sequence in the derived variable (`ShortComplex.ShortExact.torδ'`,
  `TauCeti.ModCat.tor_exact₁'`, `tor_exact₂'`, `tor_exact₃'`): 1.2 over `Cᵒᵖ`, transported by the
  balance.

**Rings.** The swap (`TauCeti.balancedTorSwapIso`): `Tor_n^A(M, N) ≅ Tor_n^{Aᵐᵒᵖ}(N, M)`,
naturally, with `N` a right `Aᵐᵒᵖ`-module through
`ModuleCat.restrictScalars (RingEquiv.opOp A).symm`; from the balance at `SingleObj A`, 1.1's
comparison and `TauCeti.singleObjMulOppositeEquiv` (0.2). Vanishing at a projective right module
(`TauCeti.isZero_balancedTor_succ_of_projective_left`) and the long exact sequence in the
left-module variable (`ShortComplex.ShortExact.balancedTorδ'`, `TauCeti.balancedTor_exact₁'`,
`balancedTor_exact₂'`, `balancedTor_exact₃'`) follow.

*Needs:* 0.3–0.5, 1.1, 1.2; Mathlib `HomologicalComplex₂`, `HomologicalComplex₂.total`; Tau Ceti
`HomologicalComplex₂.quasiIso_totalAugmentation_of_rows`,
`HomologicalComplex₂.totalComplexShapeSymmetryDownNat`.

### 1.4 `Tor` of the transpose

For a finitely presented module `X` with transpose `Tr X` and any module `N`,

    stable Hom(X, N) ≅ Tor_1(Tr X, N),

where the stable `Hom` is `Hom` modulo the maps that factor through a projective ([Auslander78, I,
Prop. 3.2]). Route (the owner's): Krause's snake-lemma step ([Krause-Defect]), without dualizing.
Take `0 → ΩN → P → N → 0` with `P` projective, and a presentation `P₁ → P₀ → X → 0` by finite
projectives. Put `H(M) = coker(Hom(P₀, M) → Hom(P₁, M))`. The snake lemma identifies `δ^*(X) =
coker(Hom(X, P) → Hom(X, N))` with `ker(H(ΩN) → H(P))`. Here `δ^*(X)` is the stable `Hom(X, N)`,
since a map from `X` that factors through a projective factors through `P → N`; and `H(M) ≅ Tr X ⊗
M` naturally in `M`. So the kernel is `ker(Tr X ⊗ ΩN → Tr X ⊗ P)`, which is `Tor_1(Tr X, N)` by the
long exact sequence of 1.3 and `Tor_1(Tr X, P) = 0` (1.1).

- **Category** (`TauCeti.ModCat.matrixMap`, `TauCeti.ModCat.transpose`,
  `TauCeti.ModCat.stableHomEquivTorTranspose`), a target. A finitely presented right module is the
  cokernel `X` of a map `⊕_j Hom(-, Y_j) → ⊕_i Hom(-, Z_i)` given by a matrix `α_ji : Y_j → Z_i`;
  its Auslander–Bridger transpose `Tr X` is the cokernel of the transposed matrix
  `⊕_i Hom(Z_i, -) → ⊕_j Hom(Y_j, -)`, a left module. Then `stable Hom(X, N) ≃ Tor_1(N, Tr X)`
  for every right module `N`, with Tau Ceti's projective stable category
  (`TauCeti.ExactStructure.projectiveStableFunctor` of `TauCeti.ExactStructure.abelian`). Here the
  needed long exact sequence is the one of 1.2, in the right-module variable. Left modules follow
  over `Cᵒᵖ`.
- **Rings** (`TauCeti.stableHomEquivBalancedTorTranspose`): for a presentation `f : P₁ → P₀`, `P₀ →
  X → 0` by finite projective left modules, `stable Hom_A(X, N) ≃ₗ[R] Tor_1^A(Tr X, N)`, with Tau
  Ceti's `TauCeti.AuslanderReitenTranspose f`. Route: `Function.Exact.contravariantDefectEquivKer`
  (the snake lemma step) from the open TauCetiProject/TauCeti#37151, and Tau Ceti's
  `LinearMap.auslanderReitenTransposeTensorEquivCokernel` (`H(M) ≅ Tr X ⊗ M`, natural by
  `auslanderReitenTransposeTensorEquivCokernel_map`), once #37151 merges; the roadmap does not
  depend on that PR. The stable `Hom` matches Tau Ceti's
  `ModuleCat.tensorHomCokernelEquivProjectiveStableHom`.

Auslander's defect formula `D δ^*(X) ≅ δ_*(D Tr X)` itself stays with
[ArtinAlgebras](../RepresentationTheory/ArtinAlgebras/README.md), §4.2, and #37151; it is a
supplier, not a target here. Layer 2 uses this item for "finitely presented flat modules are
projective" (2.3).

*Needs:* 1.1–1.3; Tau Ceti `TauCeti.AuslanderReitenTranspose`,
`LinearMap.auslanderReitenTransposeTensorEquivCokernel`,
`TauCeti.ExactStructure.projectiveStableFunctor`, `TauCeti.ExactStructure.abelian`,
`ModuleCat.tensorHomCokernelEquivProjectiveStableHom`; from
#37151 (open) `Function.Exact.contravariantDefectEquivKer`.

### 1.5 `Tor`–`Ext` duality

(`TauCeti.ModCat.torExtDualityEquiv`.) For an injective `R`-module `E`,

    Hom_R(Tor_n^C(F, G), E) ≃ₗ[R] Ext^n(F, G^E),

natural in `F` and `G`, where `G^E` is the dual of 0.7 and `Ext` is Mathlib's derived-category
`Abelian.Ext` (the `Ext` that Tau Ceti uses throughout). Mathlib's `Abelian.Ext` is an `R`-module
for an `R`-linear abelian category (`Mathlib/Algebra/Homology/DerivedCategory/Ext/Linear.lean`), so
the statement is `R`-linear. Route: compute `Tor` from a projective resolution `P` of `F` (by the
balance); then `Hom_R(H_n(P ⊗_C G), E) ≅ H^n(Hom_R(P ⊗_C G, E))`, since `Hom_R(-, E)` is exact; the
adjunction of 0.7 termwise gives `Hom_R(P ⊗_C G, E) ≅ Hom(P, G^E)`; and Mathlib's
`ProjectiveResolution.extEquivCohomologyClass`
(`Mathlib/CategoryTheory/Abelian/Projective/Ext.lean`) identifies `Ext^n(F, G^E)` with the
degree-`n` cohomology classes from `P`. No classical `Ext` and no comparison of `Ext`s is needed
([CE, VI, Prop. 5.1, p. 120]; [Lambek, p. 241] for `R = ℤ`, `E = ℚ ⧸ ℤ`). This item includes the
instance `HasExt.{w} (Mod C)` (Mathlib's `hasExt_of_enoughProjectives`, as for `ModuleCat`).

**Rings** (`TauCeti.balancedTorExtDualityEquiv`):
`Hom_R(Tor_n^A(M, N), E) ≃ₗ[R] Ext^n_{Aᵐᵒᵖ}(M, Hom_R(N, E))`, with `Hom_R(N, E)` Tau Ceti's
`MatlisDual R E N` (0.6) and the `R`-linear structure of `ModuleCat Aᵐᵒᵖ` from Mathlib's scoped
`ModuleCat.Algebra.instLinear`.

Consumers: Lambek's criterion in Layer 2 (`n = 1`, `E` an injective cogenerator), the
character-module formula for flat dimension in Layer 3, and Auslander-Reiten formulas with Matlis
duals (`E` an injective hull of the residue field of a commutative base, as in ArtinAlgebras).

*Needs:* 0.7, 1.1, 1.3; Mathlib `Abelian.Ext`, `HasExt`, `hasExt_of_enoughProjectives`,
`ProjectiveResolution.extEquivCohomologyClass`, the `Module R (Ext X Y n)` instance; Tau Ceti
`TauCeti.MatlisDual`.

### 1.6 Comparisons and first computations

- **Commutative rings** (`TauCeti.balancedTorIsoTor`). For `[CommRing R]`, `BalancedTor R R n` is
  naturally isomorphic to Mathlib's `CategoryTheory.Tor (ModuleCat R) n`, after restricting
  `ModuleCat R` to `ModuleCat Rᵐᵒᵖ` along `(RingEquiv.toOpposite R).symm`, by 0.6's
  `equivTensorProduct`. With the balance this gives (`TauCeti.torIsoTor'`)
  `CategoryTheory.Tor (ModuleCat R) n ≅ CategoryTheory.Tor' (ModuleCat R) n`, the comparison that
  Mathlib's `Mathlib/CategoryTheory/Monoidal/Tor.lean` leaves open; a candidate for upstreaming.
  Tau Ceti's results on Mathlib's `Tor` and `Tor'` over commutative rings
  (`TauCeti.Algebra.Category.ModuleCat.Monoidal.Tor`, `TauCeti.CategoryTheory.Monoidal.Tor`) then
  apply to `BalancedTor R R`.
- **Change of base and independence of `R`** (`TauCeti.ModCat.torRestrictScalarsIso`,
  `TauCeti.ModCat.torIntIso`; rings `TauCeti.balancedTorRestrictScalarsIso`,
  `TauCeti.balancedTorIntIso`): restricting `Tor` over `R'` to `R` gives `Tor` over `R`, when the
  `R`-structure comes from the `R'`-structure; the case `ℤ → R` says the underlying groups do not
  depend on `R`. Route: 1.1's computation from one resolution, and 0.3 or 0.6 termwise.
- **Cyclic modules** (`TauCeti.balancedTorOneQuotientEquiv`). For a right ideal
  `I : Submodule Aᵐᵒᵖ A` and a left ideal `K : Ideal A`, with `R = ℤ`,
  `Tor_1^A(A ⧸ I, A ⧸ K) ≃+ (I ∩ K) ⧸ IK`, where `IK` is the additive subgroup generated by the
  products ([Weibel, Exer. 3.1.3, p. 68]; for a two-sided ideal, `Tor_1^A(A ⧸ I, A ⧸ I) ≅ I ⧸ I²`).
  Route: 1.2 for `0 → I → A → A ⧸ I → 0`, the vanishing of `Tor_1(A, -)`, and the first check of
  0.6, which identifies `I ⊗_A (A ⧸ K) → A ⊗_A (A ⧸ K)` with `I ⧸ IK → A ⧸ K`; Tau Ceti's
  `ShortComplex.ShortExact.leftDerivedOneIsoKernel` (`TauCeti.CategoryTheory.Abelian.LeftDerived`)
  is the pattern for `Tor_1` as a kernel.

*Needs:* 0.3, 0.6, 1.1–1.3; Mathlib `CategoryTheory.Tor`, `CategoryTheory.Tor'`,
`ModuleCat.restrictScalars`.

### 1.7 Categories with finitely many objects

For a preadditive `C` with finitely many objects (`[Fintype C] [DecidableEq C]`), the **category
algebra** (`TauCeti.CategoryAlgebra C`) is `⊕_{x,y} Hom(x, y)`, the families `a x y : x ⟶ y` with
`(a * b) x z = ∑_y b x y ≫ a y z` and the identities on the diagonal as unit ([Mitchell, §7,
p. 33], where it is `[C]`). The product follows Mathlib's `SingleObj` convention `f ≫ g = g * f`,
so `CategoryAlgebra (SingleObj A) ≅ A`. For an `R`-linear `C` it is an `R`-algebra.

- **Morita equivalence** (`TauCeti.leftModCatEquivCategoryAlgebra :
  LeftModCat C ≌ ModuleCat (CategoryAlgebra C)` and `TauCeti.modCatEquivCategoryAlgebra :
  ModCat C ≌ ModuleCat (CategoryAlgebra C)ᵐᵒᵖ`), `R`-linear: `G ↦ ⊕_x G(x)`, with `a` acting by
  the `G(a x y)` ([Mitchell, Thm. 7.1, pp. 33–35]). The construction is the one of Tau Ceti's
  `TauCeti.quiverRepEquivalence : QuiverRep k Q ≌ ModuleCat (pathAlgebra k Q)` (carrier `⊕ᵥ Mᵥ`).
  Mathlib's `IsMoritaEquivalent` compares two rings; through these equivalences, two
  finite-object categories with `R`-linearly equivalent module categories have Morita equivalent
  category algebras. For a full subcategory `C' ⊆ C` on some of the objects, the category algebra
  of `C'` is the corner `e Λ e` of `Λ = CategoryAlgebra C` at `e = ∑_{x ∈ C'} 𝟙 x`, so Tau Ceti's
  `IsIdempotentElem.isMoritaEquivalent_corner` applies when `e` is full.
- **Tensor and `Tor`** (`TauCeti.tensorObjCategoryAlgebraIso`,
  `TauCeti.torCategoryAlgebraIso`): the equivalences carry `F ⊗_C G` to the balanced tensor product
  over the category algebra and `Tor^C_n` to `BalancedTor R (CategoryAlgebra C) n` ([Mitchell, §7,
  p. 37, (1)]). Route: by the adjunctions (0.3, 0.6) both tensor products represent the same
  functor; the equivalences preserve projective resolutions.

This generalizes the one-object comparisons of 0.2, 0.6 and 1.1. It sits in Layer 1 because its
point is the comparison of `Tor`; its tensor part uses only Layer 0.

**Check.** For the `k`-linear category `C` of the quiver `1 → 2` (0.1), the category algebra is the
path algebra `kA₂`, which Tau Ceti identifies with the upper triangular matrices `T₂(k)`
(`TauCeti.Quiver.Kronecker.upperTriangularAlgEquiv`; [Mitchell, §7, Example 1, p. 33] for posets).
So `Tor^C` is `Tor^{T₂(k)}`, and the checks below for `T₂(k)` can be computed with the
representables of `C`.

*Needs:* 0.1–0.3, 0.6, 1.1; Mathlib `Fintype`; Tau Ceti `TauCeti.quiverRepEquivalence` (pattern),
`TauCeti.Quiver.Kronecker.upperTriangularAlgEquiv`, `IsIdempotentElem.isMoritaEquivalent_corner`.

**Checks.**

- Representables: `Tor_0(Hom(-, X), G) ≅ G(X)` (1.1 and 0.3's Yoneda), and `Tor_{n+1}(Hom(-, X), G)
  = 0` (1.3, since `Hom(-, X)` is projective); symmetrically `Tor_0(F, Hom(X, -)) ≅ F(X)` and
  `Tor_{n+1}(F, Hom(X, -)) = 0` (1.1).
- `Tor_1^ℤ(ℤ ⧸ m, ℤ ⧸ n) ≅ ℤ ⧸ gcd(m, n)` (cyclic formula: `(mℤ ∩ nℤ) ⧸ mnℤ`).
- For `B = k[ε]/(ε²)`, `Tor_n^B(k, k) ≅ k` for every `n`: `k` has the periodic resolution
  `⋯ → B → B → k` by multiplication by `ε`, which becomes zero after tensoring with `k`.
- For `T = T₂(k)` with radical `J = k e₁₂`, `Tor_1^T(T ⧸ J, T ⧸ J) ≅ J ⧸ J² = J` is
  one-dimensional (cyclic formula), and `Tor_n^T(T ⧸ J, -) = 0` for `n ≥ 2`, since
  `J = e₁₂T ≅ e₂₂T` is projective. By 1.7 the same groups are computed over the quiver category
  of `1 → 2`, with the representables as projectives.

### Examples

Rings: `ℤ`, `B = k[ε]/(ε²)` and `T₂(k)` as in the checks. Categories: representables, and finite
quiver categories through their path algebras (1.7). The balance makes `Tor` computable from a
resolution of either variable.

### Dependencies

Layer 0.

## Layer 2: flat modules and flat functors

Throughout, `C : Type u` is preadditive with `Category.{v} C` and `EssentiallySmall.{v} C`. Flatness
is stated for modules in the universe `v` of the morphisms, where the representables live (0.1). A
category that is only `EssentiallySmall.{w}` passes to Mathlib's `SmallModel`, and flatness is
invariant under the equivalence. The sources state flatness for right modules ([OR], [St], [CB],
[Mitchell]) or for left modules ([Simson]). Here the definition is for left modules; each statement
for one side gives the other through the swap (0.5). Items 2.1–2.6 end with their ring statements.

### 2.1 Definition

(`TauCeti.ModCat.yonedaSpan β`, `TauCeti.LeftModCat.Flat G`, `TauCeti.ModCat.Flat F`.) For finitely
many morphisms `β_j : Y_j → X`, `yonedaSpan β ⊆ Hom(-, X)` is the image of
`⊕_j Hom(-, Y_j) → Hom(-, X)`; these are the finitely generated subfunctors of `Hom(-, X)`. A left
`C`-module `G` is **flat** if for every object `X` and every finitely generated subfunctor
`I ⊆ Hom(-, X)` the map `I ⊗_C G → Hom(-, X) ⊗_C G ≅ G(X)` is injective (a monomorphism in
`ModuleCat ℤ`; Yoneda, 0.3). This is the ideal test of [OR, Thm. 3.2 (3), p. 96]; for rings it is
the test on finitely generated right ideals ([Lam-LMR, (4.12), p. 125]). The definition is
universe-free: it quantifies over objects and finite families of morphisms of `C`, not over modules.
A right module `F` is flat when it is flat as a left `Cᵒᵖ`-module (`ModCat C` is `LeftModCat Cᵒᵖ`);
by the swap, this says that `F ⊗_C -` passes the ideal test.

- **Independence of `R`** (`TauCeti.LeftModCat.flat_iff_mono_tensor`): for an `R`-linear `C`, the
  ideal test with the tensor product over `R` is equivalent, by the independence of `R` (0.3).
- **Ambient and intrinsic flatness.** `Flat` is flatness as a module. An object of the full
  subcategory `Flat(C)` of flat modules may also be called flat *inside* that category, when every
  epimorphism onto it there is pure; this is a different notion ([CI]). The docstring of `Flat`
  says so. The intrinsic notion is not developed here.

**Rings** (`TauCeti.Module.BalancedFlat A M`), a native class for a left module `M` (Convention 5):
`I ⊗_A M → A ⊗_A M` is injective for every finitely generated right ideal `I`, over `R = ℤ`. A
right module `M` is flat when `BalancedFlat Aᵐᵒᵖ M`. Mathlib lists the generalization of
`Module.Flat` to noncommutative rings as a TODO (`Mathlib/RingTheory/Flat/Basic.lean`); if it is
made, `BalancedFlat` is replaced by `Module.Flat`. Bridges: flatness over `SingleObj A`
(`TauCeti.Module.balancedFlat_iff_flat_singleObj`, through 0.2 and 0.6), and for a commutative ring
Mathlib's `Module.Flat` (`TauCeti.Module.balancedFlat_iff_flat`, through 0.6).

*Needs:* 0.1–0.3, 0.5, 0.6; Mathlib `Subobject`, `imageSubobject`, `Limits.Sigma.desc`.

### 2.2 Tests

(`TauCeti.LeftModCat.flat_tfae`.) For a left module `G`, the following are equivalent:

1. `G` is flat (the ideal test);
2. `I ⊗_C G → G(X)` is injective for every subfunctor `I ⊆ Hom(-, X)` ([OR, Thm. 3.2 (3)]);
3. `- ⊗_C G` preserves monomorphisms, so it is exact on `Mod C` ([OR, Thm. 3.2 (1), p. 96];
   [Mitchell, §10, p. 48]). This holds for right modules in every universe; in Lean it is stated in
   the universe `v`, since `⊗_C` takes both modules in one universe (0.3);
4. `Tor_1(-, G) = 0`; then `Tor_n(-, G) = 0` for all `n ≥ 1`
   (`TauCeti.LeftModCat.Flat.isZero_tor_succ`; dimension shifting by 1.2 and 1.3);
5. `Tor_1(Hom(-, X) ⧸ I, G) = 0` for every finitely generated `I ⊆ Hom(-, X)`;
6. **Lambek**: the dual `G^E = Hom_R(G(-), E)` of 0.7 is injective in `Mod C`, for an injective
   cogenerator `E` of `R`-modules (`TauCeti.LeftModCat.flat_iff_injective_dual`; [Lambek, Theorem,
   p. 239] for rings and `E = ℚ ⧸ ℤ`; [St, Thm. 3 (d), p. 357] for functors). For a general `E` it
   follows from the adjunction of 0.7 ([OR, (1.1), p. 93]) and 0.7's one-map criterion.

Route: the textbook one, Lambek and Baer, organized as in [Lam-LMR, (4.12)]. (2) ⇒ (1) and
(3) ⇒ (2) are immediate. (1) ⇒ (2): an element of `I ⊗_C G` comes from `I' ⊗_C G` for a finitely
generated `I' ⊆ I`. (2) ⇒ (6): by 0.7, (2) says that every map from a subfunctor of a representable
to `G^E` extends to the representable; then the Baer criterion below. (6) ⇒ (3) by 0.7. (3) ⇔ (4)
and (4) ⇒ (5) ⇒ (1) by the long exact sequences of 1.2 and the vanishing of `Tor` at projective
right modules (1.3), applied to `0 → K → P → F → 0` and to `0 → I → Hom(-, X) → Hom(-, X) ⧸ I → 0`.
The [OR] route through the equational criterion and filtered colimits is not followed for this
item. Each test holds for right modules through the swap
(`TauCeti.ModCat.Flat.mono_tensor_obj_map` for (3)).

Two targets of this item:

- **Baer's criterion for `Mod C`** (`TauCeti.ModCat.Baer`, `TauCeti.ModCat.baer_iff_injective`): a
  right module `E` is injective exactly when every map from a subfunctor of a representable
  `Hom(-, X)` to `E` extends to `Hom(-, X)`. Route: Zorn's lemma on partial extensions, as
  Mathlib's `Module.Baer.injective`; the representables generate, since an element of `F(X)` is a
  map `Hom(-, X) → F`. Not in Mathlib (only `Module.Baer`) or Tau Ceti.
- **`Tor` commutes with filtered colimits** in the left-module variable
  (`TauCeti.ModCat.preservesFilteredColimits_tor_obj`). Route: compute `Tor` from a projective
  resolution `P` of the right module (1.3); each `P_p ⊗_C -` preserves colimits (0.3), and filtered
  colimits are exact in `ModuleCat R` (Mathlib's `AB5` instances). [OR, Lemma 3.1, p. 96] uses
  this; 2.3 and 2.6 need it.

**Rings** (`TauCeti.Module.balancedFlat_tfae`). For `[Small.{v} A]` and `M : Type v`, the following
are equivalent: `BalancedFlat A M`; `I ⊗_A M → M` is injective for every right ideal `I`; `i ⊗ M` is
injective for every injective map `i` of right modules in the universe `v`; `Tor_1^A(N, M) = 0` for
every right module `N`; `Tor_1^A(A ⧸ I, M) = 0` for every finitely generated right ideal `I`;
`Module.Injective Aᵐᵒᵖ M⁺` ([Lambek, Theorem, p. 239]; [Lam-LMR, (4.9), p. 125]). Route: the same,
with Mathlib's `Module.Baer.injective` over `Aᵐᵒᵖ` and the duals of 0.6, or through
`balancedFlat_iff_flat_singleObj`. Also: flat modules have no higher `Tor`
(`TauCeti.isZero_balancedTor_succ_of_balancedFlat`), and ring `Tor` commutes with filtered colimits
(`TauCeti.preservesFilteredColimits_balancedTor_obj`).

*Needs:* 0.3, 0.4, 0.7, 1.1–1.3; Mathlib `Subobject`, `Injective`, `IsCoseparator`,
`PreservesFilteredColimitsOfSize`, `AB5`, `Module.Baer.injective`.

### 2.3 The Lazard block

These characterizations use finite data ([OR, Thm. 3.2 (4)–(6)]; [Lazard, Ch. I]; [St]; [CB, §1.3]).
Over a preadditive `C` they use finite sums of representables `Hom(Z_1, -) ⊕ ⋯ ⊕ Hom(Z_m, -)`
(`TauCeti.LeftModCat.isFiniteFree`), not single representables: for `C = SingleObj ℤ` the elements
`e_1, e_2` of the flat module `ℤ²` have no common source `e_1 = a z`, `e_2 = b z`. Under finite
biproducts the single-representable forms are corollaries; no passage to `Mat_ C` is needed. For a
left module `G`, each of the following is equivalent to flatness:

- **equational criterion** (`TauCeti.LeftModCat.IsTrivialRelation`,
  `TauCeti.LeftModCat.flat_iff_forall_isTrivialRelation`): every relation
  `∑_j G(β_j)(y_j) = 0` in `G(X)` is trivial, that is, there are finitely many `z_i ∈ G(Z_i)` and
  maps `α_ij : Z_i → Y_j` with `y_j = ∑_i G(α_ij)(z_i)` and `∑_j α_ij ≫ β_j = 0` for all `i`
  ([OR, Thm. 3.2 (4), pp. 96–97]; for rings [Lam-LMR, (4.24), p. 130], which credits Chase;
  Mathlib's commutative `Module.Flat.iff_forall_isTrivialRelation`);
- **factorization** (`TauCeti.LeftModCat.flat_iff_forall_exists_factorization`): every map from a
  finitely presented module (Mathlib's `IsFinitelyPresentable`) to `G` factors through a finite sum
  of representables ([Lazard, Lemme 1.1 and Thm. 1.2, p. 84]; [St, Lemma 8 (c), p. 354]; [CB, §1.3
  (2), p. 1646]);
- **filtered category of elements** (`TauCeti.LeftModCat.FiniteFreeOver G`,
  `TauCeti.LeftModCat.flat_iff_isFiltered_finiteFreeOver`): the maps to `G` from finite sums of
  representables, a `CostructuredArrow` category with the shape of Tau Ceti's
  `TauCeti.FiniteFreeOver`, form a filtered category ([OR, Thm. 3.2 (6), p. 97]; [CB, §1.3 (3)]).
  It is the opposite of the covariant category of elements of `G`, which is cofiltered ([OR,
  Remark, p. 99]);
- **Lazard–Govorov** (`TauCeti.LeftModCat.flat_iff_exists_isColimit`): `G` is a filtered colimit of
  finite sums of representables ([OR, Thm. 3.2 (5), p. 97]; [Mitchell, Thm. 10.1b, p. 48]; [CB,
  §1.3 (4)]; [Lazard, Thm. 1.2]; for rings [Govorov], a direct limit of free modules; [St, Thm. 3
  (b)]: a direct limit of projectives);
- **purity** (`TauCeti.LeftModCat.IsPureEpi`, `TauCeti.LeftModCat.flat_iff_forall_isPureEpi`): every
  epimorphism onto `G` is pure, that is, maps from finitely presented modules lift along it ([St,
  §2 and Thm. 3, pp. 353–357]; [Lazard, Cor. 1.3, p. 85]).

Route: the chain of [OR, Thm. 3.2]. The ideal test gives the equational criterion, through the
ideal generated by the `β_j` and `(Hom(-, X) ⧸ I) ⊗_C G ≅ G(X) ⧸ IG` ([OR, Lemma 1.2, p. 94]). The
equational criterion gives the factorization, by dualizing a finite presentation ([Lazard, Lemme
1.1]; [Lam-LMR, (4.32), p. 133]). The factorization makes the category of elements filtered, and
`G` is the colimit over it (the pattern of Tau Ceti's `flatModuleFilteredFree`). A filtered colimit
of finite sums of representables is flat, since `Tor_1` commutes with filtered colimits and vanishes
on projectives (2.2). Purity is the factorization read as lifting. [CB]'s proof of the
factorization instead uses the transpose and the stable Hom,
`stable Hom(X, Y) ≅ Tor_1(Tr X, Y)` ([Auslander78, I, Prop. 3.2]); it is not followed here.

Consequences:

- **finitely presented flat modules are projective**
  (`TauCeti.LeftModCat.Flat.projective_of_isFinitelyPresentable`; [St, Lemma 7 (ii), p. 354];
  [Lazard, Cor. 1.4, p. 85]; [Mitchell, p. 49]). Route: by 1.4, `stable End(G) ≅ Tor_1(Tr G, G)`,
  which is `0` since `G` is flat (2.2); so the identity of `G` factors through a projective.
  Remark: the factorization above also gives it, since the identity factors through a finite sum
  of representables. This replaces the ring-only route through character modules;
- **flat and pure-projective modules are projective** (`TauCeti.LeftModCat.IsPureProjective`,
  `TauCeti.LeftModCat.Flat.projective_of_isPureProjective`): an epimorphism from a projective onto
  `G` is pure, so it splits;
- **flat does not imply pure-projective**: `ℚ` is a flat, not projective, `ℤ`-module (checks), so it
  is not pure-projective. Conversely `ℤ ⧸ 2` is finitely presented, hence pure-projective, and not
  flat;
- **additive categories** (`TauCeti.LeftModCat.flat_iff_isFiltered_costructuredArrow_coyoneda`):
  with finite biproducts, single representables suffice in each item ([CB, §1.3]; [OR, Cor. 3.3,
  p. 99]).

**Rings** (`TauCeti.Module.balancedFlat_iff_isFiltered_finiteFreeOver`,
`TauCeti.Module.BalancedFlat.denseAt`,
`TauCeti.Module.BalancedFlat.exists_factorization_of_finitePresentation`,
`TauCeti.Module.BalancedFlat.projective_of_finitePresentation`). `M` is flat exactly when Tau Ceti's
`FiniteFreeOver A M` is filtered; then `M` is the filtered colimit of the finite free modules over
it; every map from a finitely presented module to `M` factors through a finite free module; and a
finitely presented flat module is projective, by 1.4 as above ([Lazard, Thm. 1.2, Cor. 1.4];
[Lam-LMR, (4.30), (4.32)–(4.34), pp. 133–134]; Mathlib's commutative
`Module.Flat.exists_factorization_of_finitePresentation` and
`Module.Flat.projective_of_finitePresentation`). Over a left Noetherian ring every finite flat
module is projective (`Module.finitePresentation_of_finite`).

**Refactor consumer.** Tau Ceti's `TauCeti.flatModuleFilteredFree`
(`TauCeti.Algebra.Category.ModuleCat.Flat.FilteredFree`), one direction of Lazard's theorem for
commutative rings, becomes a corollary of `BalancedFlat.denseAt` and `balancedFlat_iff_flat`. It is
reproved this way, with no compatibility shims.

**Bridge to Mathlib's set-valued notions** (optional; `TauCeti.ModCat.flat_iff_isIndObject`,
`TauCeti.LeftModCat.flat_iff_isCofiltered_elements`). Over an additive `C`, a right module is flat
exactly when its underlying presheaf of sets is an ind-object (Mathlib's `IsIndObject`, with the
recognition theorem `isIndObject_iff`; [Krause-Smashing, §2.3, p. 115]: `Flat C = Ind C`), and a
left module `G` is flat exactly when `(G ⋙ forget).Elements` is cofiltered (Mathlib's type-valued
flatness, `Functor.isCofiltered_elements`). Mathlib's `isIndObject_iff_preservesFiniteLimits` is
then the set-valued form of 2.4. Mathlib's `RepresentablyFlat u` is a different notion: for an
additive `u : C ⥤ D` between additive categories it corresponds to flatness of the left
`C`-modules `D(d, u(-))` (the objects of `StructuredArrow d u` are maps `d → u(c)`); the right
modules `D(u(-), d)` belong to `RepresentablyCoflat`.

*Needs:* 1.4, 2.1, 2.2; Mathlib `IsFinitelyPresentable`, `CostructuredArrow`, `IsFiltered`,
`IsCofiltered`, `Functor.Elements`, `Cocone`, `IsColimit`, `IsIndObject`, `Functor.DenseAt`,
`Retract`; Tau Ceti `TauCeti.FiniteFreeOver`, `TauCeti.finiteFreeModuleInclusion`,
`TauCeti.flatModuleFilteredFree`.

### 2.4 Left exact functors, triangulated categories and the representation theorem

- **Flat = left exact** (`TauCeti.ModCat.flat_iff_preservesFiniteLimits`). For an additive `C`
  with cokernels, a right module `F` is flat exactly when it is left exact: it turns cokernels in
  `C` into kernels, that is, `F : Cᵒᵖ ⥤ Ab` preserves finite limits. So
  `Flat(Cᵒᵖ, Ab) = Lex(Cᵒᵖ, Ab)` ([Fisher, Thms. 1.3–1.4, pp. 279–280], for abelian `C`; [OR,
  Cor. 3.4, p. 99]; [CB, §2.2, p. 1649]; [Simson, Thm. 2.1 (b), pp. 94–95]). For left modules:
  over `C` with kernels, a flat left module is a left exact covariant functor.
- **Weak cokernels** (`TauCeti.IsWeakCokernel`,
  `TauCeti.ModCat.flat_iff_exact_of_isWeakCokernel`). If the additive `C` has weak cokernels, a
  right module `F` is flat exactly when `F(Z) → F(Y) → F(X)` is exact whenever `Y → Z` is a weak
  cokernel of `X → Y` ([CB, §1.2, Lemma 2, and §1.3, pp. 1644–1646], where weak cokernels are
  called pseudo-cokernels). Route: the filtered category
  of elements (2.3). The previous item follows: a cokernel is a weak cokernel, and a weak cokernel
  and the cokernel factor through each other.
- **Triangulated categories** (`TauCeti.ModCat.flat_iff_isHomological`). For a skeletally small
  triangulated `C`, a right module is flat exactly when it is cohomological, that is, homological
  on `Cᵒᵖ` (Mathlib's `Functor.IsHomological`, with the scoped pretriangulated structure of
  `Pretriangulated.Opposite`) ([Krause-Smashing, Lemma 2.7, p. 115]; independently [Beligiannis,
  Lemma 8.10, Prop. 8.11 and Rem. 8.12, pp. 180–181]). Krause's proof extends `F` to the abelian
  category of finitely presented functors and computes `Ext` from triangles. Both sources show
  that this is also equivalent to fp-injectivity; that part stays in prose.
- **Crawley-Boevey's representation theorem** (`TauCeti.FinitelyPresented`,
  `TauCeti.restrictedYonedaEquivFlat`). A finitely accessible additive category `𝒜` is equivalent,
  by the restricted Yoneda functor `X ↦ Hom(-, X)` on `fp(𝒜)`, to the flat right modules over
  `fp(𝒜)` ([CB, §1.4, Theorem, p. 1647]). "Finitely accessible" is Mathlib's
  `IsFinitelyAccessibleCategory`: filtered colimits and a small set of finitely presented objects
  that generate by filtered colimits, with no cocompleteness. [CB]'s "locally finitely presented"
  means this. Mathlib's `IsLocallyFinitelyPresentable` adds all colimits and would narrow the
  theorem ([CPT, pp. 1214 and 1218] distinguish the two). Conversely (`TauCeti.ModCat.flat`, an
  instance `IsFinitelyAccessibleCategory (ModCat.flat C).FullSubcategory`,
  `TauCeti.ModCat.isFinitelyPresentable_flat_iff`): for a small additive `C`, the flat right modules
  form a finitely accessible category, whose finitely presented objects are the retracts of
  representables (Mathlib's `Retract`) ([CB, §1.4 (1)]). When idempotents split in `C`, `C` is
  recovered as these finitely presented objects (prose only). The representation does not make
  `Flat(Cᵒᵖ, Ab)` abelian or Grothendieck.

Pointers, not targets: the representation theorem turns Theorem P (Layer 4) for `fp(𝒜)` into a
criterion for pure-semisimplicity of `𝒜` ([CB, §3.2, p. 1655]; [JL, Thm. B.12]). Flat covers are
outside this roadmap ([BEE, Thm. 3] for rings; [CPT, Cor. 3.3, p. 1218] for `Mod C`; [Rump];
[Krause-FlatCovers]).

*Needs:* 2.3; Mathlib `PreservesFiniteLimits`, `HasCokernels`, `HasFiniteBiproducts`,
`Functor.IsHomological`, `Pretriangulated.Opposite`, `IsFinitelyAccessibleCategory`,
`ObjectProperty.isFinitelyPresentable`, `Retract`.

### 2.5 Bass's flat module

For a chain `c_0 ← c_1 ← c_2 ← ⋯` in `C`, with `f_i : c_{i+1} → c_i`:

- **Definition** (`TauCeti.LeftModCat.bassDiagram`, `TauCeti.LeftModCat.bassModule`):
  `B = colim(Hom(c_0, -) → Hom(c_1, -) → ⋯)`, with maps `Hom(f_i, -)` (Mathlib's
  `Functor.ofSequence` and `colimit`).
- **Flat** (an instance): a filtered colimit of representables (2.3).
- **Telescope presentation** (`TauCeti.LeftModCat.bassTelescope`, `TauCeti.LeftModCat.bassπ`,
  `TauCeti.LeftModCat.bassTelescope_shortExact`): `0 → ⊕_i Hom(c_i, -) → ⊕_i Hom(c_i, -) → B → 0`,
  with `e_i ↦ e_i - Hom(f_i, -) e_{i+1}`. So `B` has projective dimension at most one.
- **Projective implies factorizable** (`TauCeti.IsFactorizable`,
  `TauCeti.LeftModCat.isFactorizable_of_projective_bassModule`). If `B` is projective, the inverse
  system `Functor.ofOpSequence f` is factorizable in Simson's sense ([Simson, Def. 3.1, p. 99]):
  for every `i` there is `j ≥ i` such that the map `c_j → c_i` factors through every later map
  `c_k → c_i`, `k ≥ j`. In particular, with `p_n = f_{n-1} ≫ ⋯ ≫ f_0 : c_n → c_0`, some `p_n`
  factors through every later `p_m`. The quantifiers matter: the reverse factorization is automatic,
  and one equation `p_n = g ≫ p_{n+1}` does not express stabilization. Route: a splitting of the
  telescope, read on finitely many coordinates; the tails of the chain have the same `B`, which
  gives every `i`.

Credits: this is the representable-module form of Bass's telescope ([Bass, Lemmas 1.1–1.3,
pp. 468–470]; the splitting argument is Lemma 1.3), and [Harada, Remark 1, pp. 339–340] adapts
Bass's construction to the ring with enough idempotents of a category. The categorical statement is
an adaptation of these, not a new result. [Simson] reaches factorizable systems from "flat implies
projective" through Mittag-Leffler objects instead (Thm. 5.4 (5)).

**Rings** (`TauCeti.bassRelations`, `TauCeti.balancedFlat_bassRelations`,
`TauCeti.exists_span_prod_eq_of_projective_bassRelations`). For `a : ℕ → A`, Bass's module
`(ℕ →₀ A) ⧸ ⟨eᵢ - aᵢ • eᵢ₊₁⟩` is `B` at `SingleObj A` with every `f_i = a_i`: `Hom(f_i, -)` is right
multiplication by `a_i` on `A` (Convention 4). It is flat, and if it is projective, the chain
`a₀A ⊇ a₀a₁A ⊇ ⋯` of principal right ideals is eventually constant ([Bass, Lemmas 1.1–1.3];
[Lam-FC, (24.24), pp. 367–368], right-handed). Layer 4 uses it for Theorem P (4.5).

*Needs:* 2.3; Mathlib `Functor.ofSequence`, `Functor.ofOpSequence`, `colimit`, `Limits.Sigma.desc`,
`ShortComplex.ShortExact`.

### 2.6 Closure properties

(`TauCeti.LeftModCat.Flat.of_projective`, an instance; `TauCeti.LeftModCat.Flat.of_retract`,
`TauCeti.LeftModCat.flat_sigma_iff`, `TauCeti.LeftModCat.flat_iff_of_shortExact`,
`TauCeti.LeftModCat.Flat.of_isColimit`, `TauCeti.LeftModCat.flat_iff_mono_tensor_of_shortExact`.)

- projective modules are flat (0.4);
- retracts of flat modules are flat (Mathlib's `Retract`);
- a direct sum is flat exactly when every summand is;
- in a short exact sequence `0 → G_1 → G_2 → G_3 → 0` with `G_3` flat, `G_2` is flat exactly when
  `G_1` is ([Mitchell, Cor. 10.4b, p. 49]; the long exact sequence of 1.3);
- filtered colimits of flat modules are flat (2.2: `Tor` commutes with filtered colimits;
  [Mitchell, p. 48]; [CB, §1.3]);
- **flat quotients**: for `0 → K → F → G → 0` with `F` flat, `G` is flat exactly when
  `N ⊗_C K → N ⊗_C F` is a monomorphism for every right module `N` ([Lam-FC, (24.23), p. 367], for
  rings, right-handed).

**Rings** (`TauCeti.Module.BalancedFlat.of_projective`,
`TauCeti.Module.BalancedFlat.of_linearEquiv`, `TauCeti.Module.balancedFlat_directSum_iff`,
`TauCeti.Module.balancedFlat_iff_of_exact` ([Lam-LMR, (4.13), p. 126]),
`TauCeti.Submodule.inf_smul_eq_smul_of_balancedFlat`): the same, and the quotient test: if `F` and
`F ⧸ K` are flat, then `K ⊓ I • F = I • K` for every two-sided ideal `I` ([Lam-LMR, (4.14), p. 126];
the case `N = A ⧸ I`). Layer 4 uses it (4.5).

Pointers, not targets: products of flat right modules are flat exactly when `C` has weak cokernels
([CB, Thm. 2.1, p. 1648]; [OR, Thm. 4.1, p. 101]; Chase for rings, [Lam-LMR, (4.47), p. 139]); the
flat right modules are closed under kernels exactly when the weak global dimension is at most two
([CB, Thm. 2.3, p. 1651]; a target of 3.5). Coherence and products are not developed.

*Needs:* 0.4, 2.2, 2.3; Mathlib `Retract`, `IsFiltered`.

**Checks.**

- `ℚ` is a flat `ℤ`-module (2.1 and Mathlib's `Module.Flat`) and is not projective
  (`TauCeti.balancedFlat_rat_and_not_projective`): a split embedding into a free abelian group
  would give a nonzero map `ℚ → ℤ`. So `ℚ` is not pure-projective (2.3).
- `ℤ ⧸ n` is not flat for `n ≥ 2` (`TauCeti.not_balancedFlat_zmod`; `Tor_1^ℤ(ℤ ⧸ n, ℤ ⧸ n) ≠ 0`,
  Layer 1 checks).
- Over `B = k[ε]/(ε²)`, `k` is not flat, since `Tor_1^B(k, k) ≅ k` (Layer 1 checks).
- Over `T₂(k)`, of the two simple left modules the projective one is flat and the other is not
  (2.3: it is finitely presented and not projective). Through 1.7 the same holds for the quiver
  category of `1 → 2`, whose category algebra is `T₂(k)`.
- Bass's module over `ℤ` for the constant sequence `p` is `ℤ[1/p]`: flat, not projective, and
  `pℤ ⊋ p²ℤ ⊋ ⋯`.
- Representables `Hom(X, -)` and `Hom(-, X)` are flat (projective, 2.6).
- A categorical Bass module: in the `k`-linear category of the linear quiver `⋯ → 3 → 2 → 1`, take
  the chain `c_i = i + 1` with `f_i` the arrow `i + 2 → i + 1`. Then `p_n : n + 1 → 1` is the
  nonzero path, and `Hom(n + 1, m + 1) = 0` for `m > n`, so `p_n` does not factor through `p_m`.
  The chain is not factorizable, and `B` is flat and not projective (2.5).

### Examples

Rings: `ℚ`, `ℤ[1/p]` and `ℤ ⧸ n` over `ℤ`; the simple modules of `T₂(k)` and of `k[ε]/(ε²)`.
Categories: representables; Bass modules of chains in quiver categories; left exact functors on
abelian categories; cohomological functors on triangulated categories.

### Dependencies

Layers 0 and 1.

## Layer 3: flat dimension, global and weak global dimension

Throughout, `C : Type u` is preadditive with `Category.{v} C` and `EssentiallySmall.{v} C`, and
modules live in the universe `v`, as in Layer 2. `Tor` is taken with `R = ℤ`; by 1.6 the dimensions
do not depend on `R`. Items 3.1–3.4 end with their ring statements. The categorical statements are
adaptations of the ring theorems cited with them, unless a categorical source is named.

### 3.1 Flat dimension

(`TauCeti.LeftModCat.HasFlatDimensionLT G n`, `TauCeti.LeftModCat.HasFlatDimensionLE`,
`TauCeti.LeftModCat.flatDimension`; right modules `TauCeti.ModCat.HasFlatDimensionLT`,
`TauCeti.ModCat.flatDimension`.) A left module `G` has **flat dimension `< n`** if
`Tor_i(Hom(-, X) ⧸ I, G) = 0` for every `i ≥ n`, every object `X` and every finitely generated
subfunctor `I = yonedaSpan β ⊆ Hom(-, X)` (2.1). `HasFlatDimensionLE G n` is
`HasFlatDimensionLT G (n + 1)`, and `flatDimension G : WithBot ℕ∞` is the infimum of the `d` with
`HasFlatDimensionLT G i` for all `i > d`. This is the shape of Mathlib's `projectiveDimension`,
which is also defined by vanishing (of `Ext`) and not by resolutions. The definition is
universe-free: it quantifies over objects and finite families of morphisms of `C`. At `n = 0`,
`HasFlatDimensionLE G 0` is 2.2 (5), so flat dimension `≤ 0` is Layer 2's flatness; at `i = 0`,
`Tor_0(Hom(-, X), G) = G(X)`, so `flatDimension G = ⊥` exactly when `G = 0`. A right module has the
flat dimension of a left `Cᵒᵖ`-module.

**The classical definition** (`TauCeti.LeftModCat.hasFlatDimensionLE_tfae`). For `n : ℕ` the
following are equivalent:

1. `HasFlatDimensionLE G n`;
2. `Tor_i(F, G) = 0` for every right module `F` and every `i > n`;
3. `Tor_{n+1}(F, G) = 0` for every right module `F`;
4. `G` has a flat resolution `0 → K_n → ⋯ → K_0 → G → 0` of length `≤ n`;
5. the `n`-th syzygy of every projective resolution `P` of `G` is flat;
6. the `n`-th syzygy of some projective resolution of `G` is flat.

The `n`-th syzygy is `P.complex.opcycles n = coker(P_{n+1} → P_n)`, which is `G` for `n = 0`.
Item 4 is the textbook definition. Route: dimension shifting in either variable (1.2, 1.3), with
the vanishing of higher `Tor` at projective modules. (3) ⇒ (2) shifts in `F`; (2) ⇒ (1) is
immediate; (1) ⇒ (5) is 2.2 (5) applied to the `n`-th syzygy `K`, since
`Tor_1(-, K) ≅ Tor_{n+1}(-, G)`; (5) ⇒ (6) ⇒ (4) truncate a projective resolution at its syzygy;
(4) ⇒ (3) computes `Tor` from the flat resolution (below). Item 2 holds for right modules in every
universe; Lean states it in the universe `v`.

API:

- `flatDimension G ≤ n ↔ HasFlatDimensionLE G n` (`TauCeti.LeftModCat.flatDimension_le_iff`);
  `flatDimension G = ⊥ ↔ G = 0` (`TauCeti.LeftModCat.flatDimension_eq_bot_iff`); flat dimension
  `≤ 0` is flatness (`TauCeti.LeftModCat.hasFlatDimensionLE_zero_iff`);
- `flatDimension G ≤ projectiveDimension G`
  (`TauCeti.LeftModCat.flatDimension_le_projectiveDimension`; projective modules are flat, 2.6);
- dimension shifting (`TauCeti.LeftModCat.hasFlatDimensionLE_succ_iff`): for `0 → K → F → M → 0`
  with `F` flat, `HasFlatDimensionLE M (n + 1) ↔ HasFlatDimensionLE K n`;
- `Tor` from flat resolutions (`TauCeti.ModCat.torObjIsoHomologyOfFlat`): for a flat resolution
  `K → G`, `Tor_n(F, G) ≅ H_n(F ⊗_C K)`. Route: both sides from a projective resolution of `F`
  (1.3), with `- ⊗_C K_q` exact (2.2);
- **duality** (`TauCeti.LeftModCat.flatDimension_eq_injectiveDimension_dual`): for an injective
  cogenerator `E` of `R`-modules, `flatDimension G = injectiveDimension (G^E)` in `Mod C`. Route:
  the `Tor`–`Ext` duality of 1.5 in every degree, and `E` detects zero (0.7). This is the
  general-`E` form of [Lam-LMR, (5.57), p. 184] (`E = ℚ ⧸ ℤ`, rings).

**Rings** (`TauCeti.HasFlatDimensionLT`, `TauCeti.HasFlatDimensionLE`, `TauCeti.flatDimension`),
native for `M : ModuleCat.{v} A` with `[Small.{v} A]`: `Tor_i^A(A ⧸ I, M) = 0` for every `i ≥ n` and
every finitely generated right ideal `I`. API as above: `TauCeti.flatDimension_eq_bot_iff`,
`TauCeti.hasFlatDimensionLE_zero_iff`, `TauCeti.hasFlatDimensionLE_tfae`,
`TauCeti.flatDimension_le_projectiveDimension`, `TauCeti.hasFlatDimensionLE_succ_iff`, and
`TauCeti.flatDimension_eq_injectiveDimension_characterModule`: `flatDimension M` is the injective
dimension of the character module `M⁺` in `ModuleCat Aᵐᵒᵖ` ([Lam-LMR, (5.57)]), the case `R = ℤ`,
`E = ℚ ⧸ ℤ` of the duality. Bridge (`TauCeti.hasFlatDimensionLT_iff_singleObj`): through 0.2, ring
flat dimension is flat dimension over `SingleObj A`.

*Needs:* 1.1–1.3, 1.5, 2.1, 2.2, 2.6; Mathlib `HomologicalComplex.opcycles`, `QuasiIso`,
`ChainComplex.single₀`, `ProjectiveResolution`, `injectiveDimension`.

### 3.2 Global dimension of an abelian category

(`TauCeti.Abelian.globalDimension 𝒜 := ⨆ X : 𝒜, projectiveDimension X`.) For an abelian category
`𝒜`, the global dimension is the supremum of Mathlib's `projectiveDimension` over the objects
([Mitchell, §9, p. 42], where the right and left global dimensions of a small additive `C` are those
of its two module categories). It needs no tensor product, so it is defined for every abelian
category. `Mod C` gives the right global dimension `Abelian.globalDimension (ModCat C)`, the left
modules the left global dimension `Abelian.globalDimension (LeftModCat C)`, and `ModuleCat A` the
ring case. API:

- `projectiveDimension X ≤ globalDimension 𝒜`
  (`TauCeti.Abelian.projectiveDimension_le_globalDimension`), `globalDimension 𝒜 ≤ n` exactly when
  every object has projective dimension `≤ n` (`TauCeti.Abelian.globalDimension_le_iff`), and
  `globalDimension 𝒜 = ⊥` exactly when every object is zero
  (`TauCeti.Abelian.globalDimension_eq_bot_iff`); all three have proofs in `Suggested.lean`;
- injective dimension (`TauCeti.Abelian.globalDimension_eq_iSup_injectiveDimension`): the same
  supremum over `injectiveDimension`, since both say that `Ext^i` vanishes above the bound; and
  `globalDimension 𝒜ᵒᵖ = globalDimension 𝒜` (`TauCeti.Abelian.globalDimension_opposite`; [Mitchell,
  §9, p. 42]);
- invariance under equivalence (`TauCeti.Abelian.globalDimension_eq_of_equivalence`), from Tau
  Ceti's `CategoryTheory.Equivalence.projectiveDimension_functor_obj`.

**Auslander's lemma for `Mod C`** (`TauCeti.ModCat.globalDimension_le_iff_cyclic`,
`TauCeti.LeftModCat.globalDimension_le_iff_cyclic`). `Abelian.globalDimension (ModCat C) ≤ n`
exactly when every cyclic module `Hom(-, X) ⧸ I`, for any subfunctor `I ⊆ Hom(-, X)`, has
projective dimension `≤ n`; for left modules, the cyclic modules `Hom(X, -) ⧸ I` ([Au, Thm. 1,
p. 68] for rings). Route: global dimension `≤ n` means injective dimension `≤ n` for every module;
for a module `E` take an injective coresolution to the `n`-th cosyzygy `E'`; `E'` is injective
exactly when it passes the Baer test of 2.2, that is, `Ext^1(Hom(-, X) ⧸ I, E') = 0`, which is
`Ext^{n+1}(Hom(-, X) ⧸ I, E) = 0`. The refinements over finite and over cyclic modules of Tau Ceti's
`TauCeti.globalDimension_le_tfae`, `globalDimension_eq_iSup_cyclic` and
`globalDimension_eq_iSup_finite` become corollaries for `C = SingleObj A`.

- **Sides** (`TauCeti.LeftModCat.globalDimension_eq_globalDimension_modCat_op`): the left global
  dimension of `C` is the right global dimension of `Cᵒᵖ`, through the equivalence of 0.5.
- **Universe independence** (`TauCeti.ModCat.globalDimension_eq_globalDimension`): for `C`
  essentially small in two universes, both global dimensions are computed on the cyclic modules
  of a small model, which live in one universe; this is the categorical form of Tau Ceti's
  `TauCeti.globalDimension_eq_globalDimension`.

**Rings, refactor of main.** Tau Ceti's `TauCeti.globalDimension A`
(`⨆ M : ModuleCat.{v} A, projectiveDimension M`) is `Abelian.globalDimension (ModuleCat.{v} A)`
(`TauCeti.globalDimension_eq_abelianGlobalDimension`, proved in `Suggested.lean` through
`TauCeti.globalDimension_def`). When 3.2 lands, the ring definition becomes this special case, and
its API is restated as corollaries, with no compatibility shims; `TauCeti.globalDimension_le_tfae`
is re-proved through Auslander's lemma. Bridge
(`TauCeti.globalDimension_eq_globalDimension_singleObj`): `TauCeti.globalDimension A` is the left
global dimension of `SingleObj A` (0.2).

*Needs:* 0.1, 0.2, 0.5, 2.2 (Baer); Mathlib `projectiveDimension`, `projectiveDimension_le_iff`,
`projectiveDimension_eq_bot_iff`, `injectiveDimension`, `Subobject`; Tau Ceti
`TauCeti.globalDimension`, `TauCeti.globalDimension_def`,
`CategoryTheory.Equivalence.projectiveDimension_functor_obj`.

### 3.3 Weak global dimension

(`TauCeti.LeftModCat.weakGlobalDimension C := ⨆ G : LeftModCat C, flatDimension G`.) It is defined
for small preadditive `C` and for rings; it needs the tensor product, so it is not defined for an
arbitrary abelian category. API:

- `weakGlobalDimension C ≤ n` exactly when `Tor_{n+1}` vanishes on all pairs
  (`TauCeti.LeftModCat.weakGlobalDimension_le_iff`);
- **symmetry** (`TauCeti.LeftModCat.weakGlobalDimension_op`,
  `TauCeti.LeftModCat.weakGlobalDimension_eq_iSup_modCat`):
  `weakGlobalDimension Cᵒᵖ = weakGlobalDimension C`, so it is also the supremum of the flat
  dimensions of the right modules. Route: the balance (1.3) and the previous item ([Au, p. 70];
  [Lam-LMR, (5.63), p. 185]);
- **universe-free tests** (`TauCeti.LeftModCat.weakGlobalDimension_le_tfae`): for `n : ℕ` the
  following are equivalent: `weakGlobalDimension C ≤ n`; every cyclic right module
  `Hom(-, X) ⧸ I` with `I` finitely generated has flat dimension `≤ n`; every finitely presented
  right module has flat dimension `≤ n` ([Lam-LMR, (5.69), p. 187], for cyclic modules over a
  ring). By the definition of flat dimension, the second item tests `Tor` only between finitely
  presented cyclic modules on both sides. Route: the first item gives the third by symmetry, and
  the third gives the second; by 3.1 the second says `Tor_{n+1}(Hom(-, X) ⧸ I, G) = 0` for every
  left module `G`, which is `HasFlatDimensionLE G n`;
- **bounds** (`TauCeti.LeftModCat.weakGlobalDimension_le_globalDimension`,
  `TauCeti.LeftModCat.weakGlobalDimension_le_globalDimension_modCat`): the weak global dimension
  is at most both global dimensions (3.1 and symmetry; [Lam-LMR, (5.58), p. 184]);
- **from projective dimension**
  (`TauCeti.LeftModCat.weakGlobalDimension_le_of_forall_isFinitelyPresentable`): if every finitely
  presented right module has projective dimension `≤ n`, then `weakGlobalDimension C ≤ n` (the tests
  and 3.1). Consumer: ArtinAlgebras §7.5, through TauCetiProject/TauCeti#40807;
- **degenerate cases** (`TauCeti.LeftModCat.weakGlobalDimension_eq_bot_iff`,
  `TauCeti.LeftModCat.weakGlobalDimension_le_zero_iff`): `⊥` exactly when every object of `C` is
  zero (so every module is zero); `≤ 0` exactly when every module is flat. A semisimple `C`, one of
  global dimension `0` ([Mitchell, §9, p. 42]), has weak global dimension `0` when it has a nonzero
  object.

**Rings** (`TauCeti.weakGlobalDimension A := ⨆ M : ModuleCat.{v} A, flatDimension M`), native:
`TauCeti.weakGlobalDimension_le_iff`, `TauCeti.weakGlobalDimension_mulOpposite`,
`TauCeti.weakGlobalDimension_le_globalDimension`,
`TauCeti.weakGlobalDimension_le_globalDimension_mulOpposite`, `TauCeti.weakGlobalDimension_le_tfae`
(finitely presented and cyclic right modules),
`TauCeti.weakGlobalDimension_le_of_forall_finitePresentation`,
`TauCeti.weakGlobalDimension_eq_bot_iff` (the zero ring) and
`TauCeti.weakGlobalDimension_eq_zero_of_isSemisimpleRing`. Equality with the categorical one
(`TauCeti.weakGlobalDimension_eq_weakGlobalDimension_singleObj`), through 0.2.

*Needs:* 1.3, 2.2, 3.1, 3.2; Mathlib `IsFinitelyPresentable`.

### 3.4 Auslander's theorem

Hypothesis: `C` is **left Noetherian**, that is, every representable `Hom(X, -)` is a Noetherian
object of the left modules (Mathlib's `IsNoetherianObject`: ascending chain condition on
subobjects). For `C = SingleObj A`, `Hom(∗, -)` is the regular left module, so this is
`IsNoetherianRing A`.

- **The `FP_∞` lemma**
  (`TauCeti.LeftModCat.flatDimension_eq_projectiveDimension_of_projectiveResolution`), a separate
  public target, with no Noetherian hypothesis. A module with a projective resolution by finitely
  presented projectives has equal flat and projective dimension. Route: if the flat dimension is
  `n`, the `n`-th syzygy `coker(P_{n+1} → P_n)` is flat (3.1) and finitely presented, hence
  projective by "finitely presented flat modules are projective" (2.3, through 1.4); so the
  projective dimension is at most `n`. Ring form
  (`TauCeti.flatDimension_eq_projectiveDimension_of_projectiveResolution`): a resolution by finite
  projectives. Over a left Noetherian ring every finite module has one
  (`TauCeti.flatDimension_eq_projectiveDimension_of_finite`, with
  `Module.finitePresentation_of_finite`).
- **Auslander's theorem** (`TauCeti.LeftModCat.globalDimension_eq_weakGlobalDimension`). If `C`
  is left Noetherian, then `Abelian.globalDimension (LeftModCat C) = weakGlobalDimension C`
  ([Au, Thm. 4, p. 70]; [Lam-LMR, (5.59), p. 184], for rings). Route: by 3.2 the global dimension
  is the supremum over the cyclic modules `Hom(X, -) ⧸ I`. Over a left Noetherian `C`, finite sums
  of representables are Noetherian objects, so their subobjects are finitely generated and the
  cyclic modules have resolutions by finitely presented projectives. The `FP_∞` lemma then gives
  projective dimension = flat dimension `≤ weakGlobalDimension C`; the other inequality is 3.3.
  The right-module form (`TauCeti.ModCat.globalDimension_eq_weakGlobalDimension`, every
  `Hom(-, X)` Noetherian) follows over `Cᵒᵖ` with 3.3's symmetry.

The categorical form is an adaptation of Auslander's ring theorem. [Mitchell, §9, pp. 42–45] defines
the global dimensions of a small additive category and compares them with its matrix ring, but its
pages 41–56 contain no weak dimension and no Noetherian comparison; the later pages were not read,
and no categorical source was found.

**Corollaries.**

- **Left bound** (`TauCeti.LeftModCat.globalDimension_le_of_forall_isFinitelyPresentable`): if `C`
  is left Noetherian and every finitely presented right module has projective dimension `≤ n`,
  then `Abelian.globalDimension (LeftModCat C) ≤ n` (3.3 and the theorem). No right Noetherian
  hypothesis. Ring form
  (`TauCeti.globalDimension_le_of_forall_finitePresentation_mulOpposite`): this strengthens the
  statement of the open TauCetiProject/TauCeti#40807 (ArtinAlgebras §7.5), which can use it once
  Layers 0–3 exist.
- **Symmetry** (`TauCeti.ModCat.globalDimension_eq_globalDimension_leftModCat`): if every
  `Hom(X, -)` and every `Hom(-, X)` is a Noetherian object, the left and right global dimensions
  agree ([Au, Cor. 5, p. 70]). For rings this is Tau Ceti's `TauCeti.globalDimension_mulOpposite`.

**Rings** (`TauCeti.globalDimension_eq_weakGlobalDimension`): for `[IsNoetherianRing A]` and
`[Small.{v} A]`, `globalDimension.{v} A = weakGlobalDimension.{v} A`.

**Downstream refactor of main's `TauCeti/RingTheory/GlobalDimension/MulOpposite.lean`.**
`TauCeti.globalDimension_le_globalDimension_mulOpposite`, `TauCeti.globalDimension_mulOpposite` and
`TauCeti.globalDimension_mulOpposite_of_moduleFinite` keep their statements (no users on main; the
open #40807 uses them). Their proofs are replaced by the weak-dimension route: Auslander's theorem
with the bounds and the symmetry of 3.3. `TauCeti.hasInjectiveDimensionLE_characterModule_iff` is
kept and re-proved as the case `R = ℤ`, `E = ℚ ⧸ ℤ` of the duality of 3.1 with the `FP_∞` lemma.
`TauCeti/Algebra/Module/CharacterModule/MulOpposite.lean` stays (the Lambek test of 2.2 for
`ℚ ⧸ ℤ`). Main's proofs stay until Layers 0–3 exist.

*Needs:* 2.3, 3.1–3.3; Mathlib `IsNoetherianObject`, `IsFinitelyPresentable`,
`Module.finitePresentation_of_finite`; Tau Ceti `TauCeti.globalDimension_mulOpposite` and the
other declarations of `TauCeti.RingTheory.GlobalDimension.MulOpposite` (refactor consumers).

### 3.5 Kernels of flat modules and countably presented flat modules

- **Kernels** (`TauCeti.ModCat.forall_flat_kernel_iff`). The flat right modules are closed under
  kernels exactly when `weakGlobalDimension C ≤ 2` ([CB, Thm. 2.3, p. 1651], for small additive
  `C`, where both are also equivalent to a factorization property of `C`). Route: dimension
  shifting along `0 → ker f → F → F' → coker f → 0` and, conversely, along a projective
  presentation `0 → K → P_1 → P_0 → M → 0`.
- **Sequential colimits of projectives**
  (`TauCeti.LeftModCat.hasProjectiveDimensionLE_one_colimit`): the colimit of a sequence
  `D_0 → D_1 → ⋯` of projective modules has projective dimension `≤ 1`, by the telescope
  `0 → ⊕ D_i → ⊕ D_i → colim D → 0` of 2.5.
- **Countably presented flat modules** (`TauCeti.LeftModCat.Flat.hasProjectiveDimensionLE_one`): a
  flat module that is countably presented (Mathlib's `IsCardinalPresentable` at `ℵ₁`) has
  projective dimension `≤ 1` (Jensen, as cited in [Mitchell, p. 49] and [Lazard, Thm. 3.2,
  p. 89]). Route: the Lazard block (2.3) writes it as a filtered colimit of finite sums of
  representables; a countable presentation gives a cofinal sequence, then the previous item; Bass's
  module (2.5) is the example. [Mitchell, pp. 49–50] warns that Lazard's displayed extraction of a
  countable subsystem is slightly wrong (a correction was communicated to Mitchell): the
  formalization builds the sequence with care and checks that its colimit is the whole module.
- **Pointer, not a target**: an `ℵ_n`-presented flat module has projective dimension `≤ n + 1`
  ([Simson, Thm. 2.12 (c), p. 98], for functor categories; Osofsky for rings, as cited in
  [Mitchell, pp. 49–50], with examples showing the bound is sharp).

Ring forms of 3.5 come through 0.2 and are not stated separately. Equality of flat and projective
dimension over a perfect `C` is a condition of Theorem P and stays in Layer 4 (4.5).

*Needs:* 2.3, 2.5, 3.1, 3.3; Mathlib `IsCardinalPresentable`, `Cardinal.isRegular_aleph_one`,
`colimit`, `kernel`.

**Checks.** In Lean (last section of `Suggested.lean`):

- a field has weak global dimension `0` (`TauCeti.weakGlobalDimension_field`) and the zero ring
  `⊥` (`TauCeti.weakGlobalDimension_punit`);
- `ℤ` has weak and global dimension `1` (`TauCeti.weakGlobalDimension_int`):
  `Tor_1^ℤ(ℤ ⧸ 2, ℤ ⧸ 2) ≠ 0`, and Tau Ceti's
  `TauCeti.globalDimension_eq_one_of_isPrincipalIdealRing`;
- `B = k[ε]/(ε²)` (Mathlib's `DualNumber k`) has weak and global dimension `⊤`
  (`TauCeti.weakGlobalDimension_dualNumber`; Layer 1 checks);
- `T₂(k)` (Mathlib's `Matrix.blockTriangularSubalgebra k k id` on `Fin 2`) has weak and global
  dimension `1` (`TauCeti.weakGlobalDimension_upperTriangular`): the simple module `T ⧸ J` is not
  flat (2.6 checks) and `J` is projective (Layer 1 checks);
- the `k`-linear category of the quiver `0 → 1` (Mathlib's `CategoryTheory.Free k (Fin 2)`) has
  global dimension `1` (`TauCeti.globalDimension_free_fin_two`), through its category algebra
  `T₂(k)` (1.7; [Mitchell, §9, p. 45, (6)]: equality for finitely many objects).

In prose, with locators:

- Small's ring `R = [[ℤ, ℚ], [0, ℚ]]` is right Noetherian and right hereditary, not left
  hereditary: `globalDimension Rᵐᵒᵖ = weakGlobalDimension R = 1 < globalDimension R`
  ([Lam-LMR, (5.62b), p. 185]; the facts on `R` are cited there to (2.33), not read). Auslander's
  theorem applies to `Rᵐᵒᵖ`; for `R` it fails, so `R` is not left Noetherian.
- Osofsky's Boolean ring: for a set `J` of cardinality `ℵ₂`, the free Boolean ring
  `B = 𝔽₂[x_j : j ∈ J] ⧸ (x_j² - x_j)` has weak global dimension `0` (it is von Neumann regular:
  every finitely presented module is projective, so 3.3 applies with `n = 0`) and global dimension
  `3`: for the ideal `I` generated by the `x_j`, [Osofsky-Card, Thm. A, p. 644] (with the
  definition of a nice family on p. 641) gives `pd I = 2`, so `pd(B ⧸ I) = 3`. The bound `≤ 3` is
  the classical bound for rings whose ideals are generated by `ℵ₂` elements; it was not checked
  here. So Auslander's theorem needs the Noetherian hypothesis.
- Jategaonkar's rings: for each `1 ≤ n ≤ ∞` there is a principal left ideal domain `D` with right
  global dimension `n` ([Jategaonkar, Thm. 4.10, pp. 438–439]). `D` is left Noetherian with left
  global dimension `1`, so `weakGlobalDimension D = 1`; for `n ≥ 2` the right global dimension
  differs. The symmetry corollary needs both Noetherian hypotheses.
- The `k`-linear category of the linear quiver `⋯ → 3 → 2 → 1` is hereditary on both sides, so
  its global and weak global dimensions are `1`; the Bass module of 2.5 is flat, not projective,
  with projective dimension `1` (telescope).

### Examples

Fields, `ℤ`, `k[ε]/(ε²)`, `T₂(k)` and the quiver category of `0 → 1`; Small's ring, Osofsky's
Boolean ring and Jategaonkar's rings as limits of the hypotheses; quiver categories, which are
hereditary.

### Dependencies

Layers 1 and 2.

## Layer 4: semiperfect and perfect rings, and Bass's Theorem P

*Under review: to be converted to the category-primary design of Layers 0–2; currently stated for
rings. The categorical summit is Simson's Theorem 5.4 for small preadditive categories (Summary);
Layer 2 supplies the categorical Bass module (2.5) for it. A flat module with a projective cover
is projective by the argument of [Simson, Thm. 5.4, (9′) ⇒ (1′), pp. 109–110], which uses
[Mares, Thm. 2.4, proof part (i), p. 349]. Equality of flat and projective dimension over a
perfect `C` is a condition of Theorem P (4.5) and is handled there; Layer 3 supplies flat
dimension (3.1) and the `FP_∞` lemma (3.4).*

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
  `K = K ⊓ J • P = J • K` (2.6), so `K = 0` by 4.1.
- (3) ⇒ (4): Bass's flat module (2.5).
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
  `[IsLeftPerfectRing Aᵐᵒᵖ]`, `globalDimension Aᵐᵒᵖ = globalDimension A` (with 3.3). In
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
Layers 2 and 3 and 4.1–4.4; 4.6 needs 4.5 and 3.3.

## Downstream consumers

- [ArtinAlgebras](../RepresentationTheory/ArtinAlgebras/README.md), §7.2: Auslander's theorem
  (3.4) gives the left-right symmetry of global dimension for Noetherian rings through weak
  dimension, and 4.6 gives it for semiprimary rings without a Noetherian hypothesis. Main's
  `TauCeti/RingTheory/GlobalDimension/MulOpposite.lean` is a refactor consumer: statements kept,
  proofs replaced by the weak-dimension route (3.4).
- Tau Ceti's `TauCeti.globalDimension` (`TauCeti/RingTheory/GlobalDimension.lean`) becomes the
  case `ModuleCat A` of `TauCeti.Abelian.globalDimension` (3.2); its cyclic and finite
  characterizations become corollaries of Auslander's lemma.
- ArtinAlgebras, §7.5, the forward direction: for an additive generator `M` of `mod A`, every
  finitely presented right `End_A(M)`-module has projective dimension at most two, and
  `TauCeti.globalDimension_le_of_forall_finitePresentation_mulOpposite` (3.4) turns this into
  `globalDimension (Module.End A M) ≤ 2` using only that `End_A(M)` is left Noetherian.
- ArtinAlgebras, §§4.1–4.2, through Tau Ceti's
  `LinearMap.auslanderReitenTransposeTensorEquivCokernel`
  (`Tr M ⊗_A N` as the cokernel of `Hom_A(P₀, N) → Hom_A(P₁, N)`) and
  `ModuleCat.tensorHomCokernelEquivProjectiveStableHom` (the stable Hom as the cokernel of
  `Hom_A(M, A) ⊗_A N → Hom_A(M, N)`): 1.4 identifies `Tor_1^A(Tr M, N)` with the stable
  `Hom_A(M, N)` for finitely presented `M` ([Auslander78, I, Prop. 3.2]).
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
- [Auslander78] M. Auslander, *Functors and morphisms determined by objects*, in *Representation
  Theory of Algebras* (Philadelphia, 1976), Lecture Notes in Pure and Applied Mathematics 37,
  Dekker (1978), 1–244. I, Prop. 3.2 (`stable Hom(X, Y) ≅ Tor_1(Tr X, Y)` for finitely presented
  `X`), read in a retyped version (its pp. 12–14), not in the printed pages.
- [Au] M. Auslander, *On the dimension of modules and algebras III. Global dimension*, Nagoya Math.
  J. 9 (1955), 67–77. Thm. 1, p. 68; weak dimensions, Thm. 4 and Cor. 5, p. 70; Cor. 8, p. 72;
  Cor. 9, p. 73.
- [Bass] H. Bass, *Finitistic dimension and a homological generalization of semi-primary rings*,
  Trans. Amer. Math. Soc. 95 (1960), 466–488. T-nilpotence, p. 466; Theorem P, pp. 467–468;
  Lemmas 1.1–1.3, pp. 468–470 (the telescope module and its splitting; the splitting argument is
  Lemma 1.3); Theorem 2.1, p. 471; §3, Examples, p. 475.
- [BEE] L. Bican, R. El Bashir, E. Enochs, *All modules have flat covers*, Bull. London Math. Soc.
  33 (2001), 385–390. Theorem 3. Pointer only.
- [Beligiannis] A. Beligiannis, *On the Freyd categories of an additive category*, Homology Homotopy
  Appl. 2 (2000), 147–185. §8.2: Lemma 8.10, Prop. 8.11 and Rem. 8.12, pp. 180–181 (flat and
  fp-injective modules over weak abelian categories).
- [CB] W. Crawley-Boevey, *Locally finitely presented additive categories*, Comm. Algebra 22 (1994),
  1641–1674. §1.2, Lemmas 1–2, pp. 1644–1645 (the category of elements; pseudo-cokernels); §1.3,
  Theorem, pp. 1645–1646 (flat functors; the proof of (1) ⇒ (2) uses
  `stable Hom(X, Y) ≅ Tor_1(Tr X, Y)`, with the stable `Hom` underlined on p. 1646 and lost in text
  extraction); §1.4, Theorem and Corollary, pp. 1646–1648 (representation theorem); §2.1, Theorem,
  p. 1648; §2.2, pp. 1649–1651 (flat = left exact); §2.3, Theorem, p. 1651; §3.1, pp. 1653–1654;
  §3.2, Theorem, p. 1655. His "locally finitely presented" means finitely accessible additive.
- [CE] H. Cartan, S. Eilenberg, *Homological Algebra*, Princeton University Press (1956). Ch. VI,
  §5, Prop. 5.1, p. 120 (`Ext_Λ(A, Hom_Γ(B, C)) ≅ Hom_Γ(Tor^Λ(A, B), C)` for `Γ`-injective `C`);
  Prop. 5.3, p. 120 (the dual formula, for a left Noetherian ring and a finitely generated `A`).
  Ch. VI, Exer. 3 (flat and projective dimension of finite modules over a Noetherian ring), cited
  through [Au, p. 70]; not read.
- [CI] M. Cortés-Izurdiaga, *Flatness in finitely accessible additive categories*,
  arXiv:2505.07742v1: the definitions before Proposition `p:CharacterizationFlats` (flat modules
  versus flat objects inside the category of flat modules). No published numbering.
- [CPT] S. Crivei, M. Prest, B. Torrecillas, *Covers in finitely accessible categories*, Proc. Amer.
  Math. Soc. 138 (2010), 1213–1221. pp. 1214 and 1218 (finitely accessible versus locally finitely
  presented); Cor. 3.3, p. 1218 (flat covers in `Mod C`).
- [Fisher] J. L. Fisher, *The tensor product of functors, satellites, and derived functors*,
  J. Algebra 8 (1968), 277–294. Thms. 1.3–1.4, pp. 279–280 (left exact functors on a small abelian
  category as filtered colimits of representables); Thm. 2.4 and Cor. 2.9, pp. 284–285.
- [Govorov] V. E. Govorov, *On flat modules*, Sibirsk. Mat. Zh. 6 (1965), 300–304 (Russian): a flat
  module is a direct limit of free modules. Read in the original.
- [Harada] M. Harada, *Perfect categories I*, Osaka J. Math. 10 (1973), 329–341. Introduction,
  pp. 329–330: perfect Grothendieck categories, and Theorem P for the functor category `(C, Ab)`
  of a small additive category `C`; Lemma 6 and Theorems 3–4, p. 337; Theorem 5 and Remark 1,
  pp. 339–340 (Bass's module over the ring with enough idempotents of a category; p. 339 checked on
  the page image, the rest through a reading of the text extraction). *Perfect categories II*,
  ibid., 343–355: Theorem 2′, p. 346, stated without proof. Parts III–IV have no flatness.
- [Jategaonkar] A. V. Jategaonkar, *A counter-example in ring theory and homological algebra*,
  J. Algebra 12 (1969), 418–440. Thm. 4.10, pp. 438–439 (principal left ideal domains of any right
  global dimension).
- [JL] C. U. Jensen, H. Lenzing, *Model Theoretic Algebra*, Gordon and Breach (1989). Appendix B,
  Theorems B.12 and B.14, read in an electronic text whose page numbers were not checked.
- [Krause] H. Krause, *Krull-Schmidt categories and projective covers*, Expo. Math. 33 (2015),
  535–549; arXiv:1410.2822. Lemma 3.6 and Proposition 4.1, read in the arXiv TeX source; the
  journal page range and numbering were not checked.
- [Krause-Defect] H. Krause, *A short proof for Auslander's defect formula*, Linear Algebra Appl.
  365 (2003), 267–270. The snake-lemma step, as cited and formalized in
  TauCetiProject/TauCeti#37151; not read here.
- [Krause-FlatCovers] H. Krause, *Morphisms determined by objects and flat covers*, Forum Math. 28
  (2016), 425–435. Theorems 1.1 and 2.2, read in arXiv:1403.6039v2 (numbering of v2). Pointer
  only.
- [Krause-Smashing] H. Krause, *Smashing subcategories and the telescope conjecture — an algebraic
  approach*, Invent. Math. 139 (2000), 99–133. §2.3, p. 115: `Flat C = Ind C`, and Lemma 2.7 (for
  a skeletally small triangulated `C`: flat, cohomological and fp-injective agree), with Lemma
  1.6.
- [Lam-FC] T. Y. Lam, *A First Course in Noncommutative Rings*, 2nd ed., Graduate Texts in
  Mathematics 131, Springer (2001). (23.13)–(23.16), pp. 351–352; (23.19), p. 353; (23.20),
  p. 354; (23.22), p. 356; (24.7), p. 360; (24.12), p. 361; (24.16), p. 364; (24.18)–(24.20),
  p. 365; (24.22), p. 366; (24.23)–(24.24), pp. 367–368; (24.25), pp. 369–370. (4.14) is cited in
  the proof of (24.25) and was not read.
- [Lam-LMR] T. Y. Lam, *Lectures on Modules and Rings*, Graduate Texts in Mathematics 189,
  Springer (1999). (4.9) and (4.12), p. 125; (4.13)–(4.14), p. 126; (4.23)–(4.24), pp. 129–130;
  (4.30), p. 133; (4.32)–(4.34), pp. 133–134; (4.47), p. 139; (5.53)–(5.57),
  pp. 183–184; (5.58)–(5.59), p. 184; (5.62b) and (5.63), p. 185; (5.69)–(5.70), p. 187; (5.71),
  p. 188. (2.33), cited in (5.62b), was not read.
- [Lambek] J. Lambek, *A module is flat if and only if its character module is injective*, Canad.
  Math. Bull. 7 (1964), 237–243. Theorem, p. 239; Proposition 1 and `Ext(N, M*) ≅ Tor(N, M)*`,
  p. 241.
- [Lazard] D. Lazard, *Autour de la platitude*, Bull. Soc. Math. France 97 (1969), 81–128. Ch. I
  (noncommutative rings, p. 83): Lemme 1.1 and Thm. 1.2, p. 84; Cor. 1.3–1.4, p. 85; Thm. 3.2,
  p. 89. The 1964 announcement (C. R. Acad. Sci. Paris 258, 6313–6316) was not obtained.
- [Mares] E. A. Mares, *Semi-perfect modules*, Math. Z. 82 (1963), 347–360 (volume 82; Simson's
  bibliography has 83). Theorem 2.4, proof part (i), p. 349 (an endomorphism of a projective with
  small image has invertible `1 - s`); added-in-proof note, p. 360. For Layer 4.
- [ML] S. Mac Lane, *Categories for the Working Mathematician*, 2nd ed., Graduate Texts in
  Mathematics 5, Springer (1998). IX.6, p. 226: coends; the tensor product over a ring as a coend,
  with modules as additive functors on the one-object category; the tensor product of functors.
- [Mitchell] B. Mitchell, *Rings with several objects*, Adv. Math. 8 (1972), 1–161. §3,
  pp. 15–18: functor categories, representables, free and finitely presented functors; §6,
  pp. 26–27: the tensor product `F ⊗_C G`, its value on representables (1), the adjunction (2),
  preservation of colimits in both variables, the swap as a definition, the explicit quotient, and
  cogenerating injectives from `ℚ ⧸ ℤ`; §6, p. 32: `Tor` and `Ext` of functors, computed from a
  projective resolution of one variable; §7, pp. 33–38: the ring `[C]` of an additive category
  (p. 33), triangular matrix rings for a finite totally ordered set (Example 1, p. 33), Thm. 7.1
  (pp. 33–35: modules over `C` and over `[C]`, an equivalence when `C` has finitely many objects),
  and the compatibility with `⊗` and `Tor` (p. 37, (1)); §9, pp. 42–45: homological and global
  dimension of an abelian category, the right and left global dimension of a small additive
  category, `gl dim 𝒜ᵒᵖ = gl dim 𝒜` (p. 42), and the comparison with the ring `[C]` (p. 45, (6));
  §10, Prop. 10.1 and Cor. 10.2, p. 47: projectives are retracts of free functors, and tensoring
  with a projective is exact; §10, pp. 48–50: flat functors, Thm. 10.1b and Cor. 10.2b, p. 48
  (Lazard–Govorov), Cor. 10.4b, p. 49, finitely presented flat functors are projective, p. 49, and
  the dimension of flat functors, pp. 49–50 (Jensen's countable case, Osofsky's `ℵ_n` case,
  Lazard's slightly erroneous countable argument and its correction); §11, pp. 50–52:
  `K`-categories, `K`-linear functors to `K`-modules as additive functors to abelian groups
  (p. 51), the tensor product over `K` and its independence of `K` (p. 52). Pages 57–161 were not
  read. Mitchell writes morphisms on the right and his modules are covariant; the statements are
  mirrored here.
- [OR] U. Oberst, H. Röhrl, *Flat and coherent functors*, J. Algebra 14 (1970), 91–105. (1.1),
  p. 93 (the adjunction over a commutative base ring); Lemma 1.2, p. 94; Lemma 2.4, p. 95;
  Lemma 3.1 and Thm. 3.2 (1)–(6), pp. 96–98, with proof; Cor. 3.3–3.5 and Remark, p. 99;
  Thm. 4.1, p. 101.
- [Osofsky-Card] B. L. Osofsky, *Homological dimension and cardinality*, Trans. Amer. Math. Soc.
  151 (1970), 641–649. Nice families, p. 641; Thm. A, p. 644.
- [Rump] W. Rump, *Flat covers in abelian and in non-abelian categories*, Adv. Math. 225 (2010),
  1589–1615. Theorem 2 and Corollary 2, pp. 1603–1604, read in a transcription. Pointer only.
- [Sandomierski] F. L. Sandomierski, *On semiperfect and perfect rings*, Proc. Amer. Math. Soc. 21
  (1969), 205–207. Proposition 1 (d) and Lemma 2, p. 205; Theorem 4, p. 206 (stated for right
  modules).
- [Simson] D. Simson, *On pure global dimension of locally finitely presented Grothendieck
  categories*, Fund. Math. 96 (1977), 91–116. §1, pp. 92–93: "additive" means preadditive (finite
  sums are added only in Cor. 1.3 (b), p. 94), the radical `J(C)`, and semisimple categories; Thm.
  2.1, pp. 94–95; Thm. 2.12 (c), p. 98 (`ℵ_n`-presented flat functors); Def. 3.1, pp. 98–99
  (factorizable inverse systems); Thm. 5.4, p. 108 (statement checked on the page image), with the
  proofs of (3′) ⇒ (4), (7) ⇒ (8) and (9′) ⇒ (1′), pp. 108–110; Thm. 5.6, p. 110. The steps through
  Thm. 3.16 and (5) ⇒ (4) were not fully read. The earlier paper *Functor categories in which every
  flat object is projective*, Bull. Acad. Polon. Sci. 22 (1974), 375–380, was not obtained.
- [St] B. Stenström, *Purity in functor categories*, J. Algebra 8 (1968), 352–361. §2 and
  Lemmas 7–8, pp. 353–354; Thm. 3, pp. 357–359.
- [Weibel] C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994). Thm. 2.7.2, pp. 58–59 (balance of `Tor`
  through the bicomplex `P ⊗ Q`); Acyclic Assembly Lemma 2.7.3, p. 59; Exer. 3.1.3, p. 68
  (`Tor_1^R(R ⧸ I, R ⧸ J) ≅ (I ∩ J) ⧸ IJ` for a right ideal `I` and a left ideal `J`).
- [Wisbauer] R. Wisbauer, *Foundations of Module and Ring Theory*, Gordon and Breach (1991).
  18.5 (1), p. 152 (a projective module that maps onto every simple module is a generator; the
  argument of the generation step), stated in `σ[M]`; 19.7, p. 161 (projective covers of simple
  modules have local endomorphism rings).
- M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. 94 (1969). `Tor₁` of the
  transpose; not read.
- [Ho] M. Hoshino, *On dominant dimension of Noetherian rings*, Osaka J. Math. 26 (1989), 275–280;
  [Xi] C. Xi, *Frobenius bimodules and flat-dominant dimensions*, arXiv:1903.07921v1. Cited for
  the consumer only, as in ArtinAlgebras.
